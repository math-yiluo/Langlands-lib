import Langlands.GroupScheme.Torus.MultiplicativeTypeRelativeRigidity
import Langlands.GroupScheme.Reductive.MultiplicativeTypeNormalCentralStatement
import Langlands.GroupScheme.GeometricConnectedness

/-! # Normal subgroups of multiplicative type of a group with connected fibres are central

Let `G` be a smooth affine group scheme over `S` with connected fibres and `h : H ⟶ G` a
monomorphism from a group of multiplicative type whose image is normal. Conjugation by points of
`G` preserves the points of `H`, so it is a family of endomorphisms of `H` parametrized by `G`.
The structure morphism of `G` is geometrically connected, so by rigidity
(`MultiplicativeTypeRigidity.eq_of_isMultiplicativeType`) conjugation by a point `g` agrees with
conjugation by `1`, which is the identity: `H` is central.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false

namespace MultiplicativeTypeNormalCentral

open RelativeMultiplicativeType

variable {S : Scheme.{u}}

/-- A smooth affine group scheme whose residue fibres are connected is geometrically connected
over the base: each residue fibre is a connected group scheme of finite type over a field, hence
geometrically connected. -/
theorem geometricallyConnected_of_residueFiber (G : GroupScheme S) [Smooth G.X.hom]
    [IsAffineHom G.X.hom]
    (hG : ∀ s : S, ConnectedSpace (RelativeIdentityComponent.residueFiber G s).X.left) :
    GeometricallyConnected G.X.hom := by
  rw [GeometricallyConnected.iff_geometricallyConnected_fiber]
  intro s
  have := hG s
  have : LocallyOfFiniteType (RelativeIdentityComponent.residueFiber G s).X.hom := by
    change LocallyOfFiniteType (pullback.snd G.X.hom (S.fromSpecResidueField s))
    infer_instance
  have : QuasiCompact (RelativeIdentityComponent.residueFiber G s).X.hom := by
    change QuasiCompact (pullback.snd G.X.hom (S.fromSpecResidueField s))
    infer_instance
  exact geometricallyConnected_of_connected (k := S.residueField s)
    (RelativeIdentityComponent.residueFiber G s)

section Conjugation

variable {G H : GroupScheme S} (h : H ⟶ G) (hn : (SubgroupFunctor.range h).IsNormal)

/-- Conjugation of a point `x` of `H` by a point `g` of `G` over the same test scheme, as a point
of `H`: it exists by normality of the image of `h`. -/
def conj (V : Over S) (g : V ⟶ G.X) (x : V ⟶ H.X) : V ⟶ H.X :=
  Classical.choose (hn V g (x ≫ h.hom.hom) (Subgroup.mem_top g) ⟨x, rfl⟩)

theorem conj_comp (V : Over S) (g : V ⟶ G.X) (x : V ⟶ H.X) :
    conj h hn V g x ≫ h.hom.hom = g * (x ≫ h.hom.hom) * g⁻¹ :=
  Classical.choose_spec (hn V g (x ≫ h.hom.hom) (Subgroup.mem_top g) ⟨x, rfl⟩)

variable [Mono h.hom.hom]

theorem conj_mul (V : Over S) (g : V ⟶ G.X) (x₁ x₂ : V ⟶ H.X) :
    conj h hn V g (x₁ * x₂) = conj h hn V g x₁ * conj h hn V g x₂ := by
  apply (cancel_mono h.hom.hom).mp
  rw [MonObj.mul_comp, conj_comp, conj_comp, conj_comp, MonObj.mul_comp]
  group

theorem conj_naturality {V W : Over S} (f : W ⟶ V) (g : V ⟶ G.X) (x : V ⟶ H.X) :
    conj h hn W (f ≫ g) (f ≫ x) = f ≫ conj h hn V g x := by
  apply (cancel_mono h.hom.hom).mp
  simp only [Category.assoc, conj_comp, MonObj.comp_mul, GrpObj.comp_inv]

theorem conj_one (V : Over S) (x : V ⟶ H.X) : conj h hn V 1 x = x := by
  apply (cancel_mono h.hom.hom).mp
  rw [conj_comp, one_mul, inv_one, mul_one]

end Conjugation

/-- **A normal subgroup of multiplicative type of a group with geometrically connected structure
morphism is central.** -/
theorem isCentral_of_isNormal {G H : GroupScheme S} [GeometricallyConnected G.X.hom]
    (hH : IsMultiplicativeType H) (h : H ⟶ G) [Mono h.hom.hom]
    (hn : (SubgroupFunctor.range h).IsNormal) : IsCentral h := by
  intro T x T' a g
  have e := MultiplicativeTypeRigidity.eq_of_isMultiplicativeType (X := G.X) hH hH
    (conj h hn) (conj_mul h hn) (conj_naturality h hn) g 1 (a ≫ x)
  rw [conj_one] at e
  have e2 := congrArg (· ≫ h.hom.hom) e
  simp only [conj_comp] at e2
  rw [← Category.assoc]
  exact (mul_inv_eq_iff_eq_mul.mp e2).symm

/-- **Part 1 of Conrad, Lemma 3.3.1.** Let `G` be a smooth affine group scheme over `S` with
connected fibres. A normal closed subgroup of `G` of multiplicative type is central. -/
theorem isCentral_of_isNormal_of_isClosedSubgroup (G : GroupScheme S) [Smooth G.X.hom]
    [IsAffineHom G.X.hom]
    (hG : ∀ s : S, ConnectedSpace (RelativeIdentityComponent.residueFiber G s).X.left)
    {H : GroupScheme S} (h : H ⟶ G) (hh : IsClosedSubgroup h) (hH : IsMultiplicativeType H)
    (hn : (SubgroupFunctor.range h).IsNormal) : IsCentral h := by
  have : GeometricallyConnected G.X.hom := geometricallyConnected_of_residueFiber G hG
  have : IsClosedImmersion h.hom.hom.left := hh
  have : Mono h.hom.hom := Over.mono_of_mono_left _
  exact isCentral_of_isNormal hH h hn

end MultiplicativeTypeNormalCentral

end Langlands.GroupScheme
