import Langlands.GroupScheme.SplitComponent.LargestTorus
import Langlands.GroupScheme.AffineCorepresented
import Langlands.GroupScheme.Rational.Characters

/-! # From natural homomorphisms to homomorphisms of group schemes

For corepresented group functors, every homomorphism of the corresponding affine group schemes
comes from a natural homomorphism, composition is respected, centrality of the scheme
homomorphism (the published `IsCentral`) is centrality of the natural homomorphism, and a
surjective classifying map gives a closed subgroup. The lattice torus of `FreeAbelianGroup I` is
the split torus `splitTorus S I`.
-/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SplitComponent

open Corepresented Corepresented.LinearEmbedding

section Bridge

variable {R : CommRingCat.{u}} {F F' F'' : CommAlgCat.{u} R ⥤ GrpCat.{u}}
  {B B' B'' : CommAlgCat.{u} R}
  (e : (F ⋙ forget GrpCat).CorepresentableBy B)
  (d : (F' ⋙ forget GrpCat).CorepresentableBy B')
  (c : (F'' ⋙ forget GrpCat).CorepresentableBy B'')

/-- The natural homomorphism of point functors induced by a homomorphism of group schemes. -/
def natOfHom (φ : groupScheme F e ⟶ groupScheme F' d) : F ⟶ F' :=
  Corepresented.pointsTrans e d φ

theorem natOfHom_app (φ : groupScheme F e ⟶ groupScheme F' d) (S : CommAlgCat.{u} R)
    (x : F.obj S) : (natOfHom e d φ).app S x =
      affinePointsEquiv F' d S ((affinePointsEquiv F e S).symm x ≫ φ.hom.hom) := rfl

/-- Every homomorphism of corepresented group schemes comes from a natural homomorphism. -/
theorem groupSchemeMap_natOfHom (φ : groupScheme F e ⟶ groupScheme F' d) :
    groupSchemeMap e d (natOfHom e d φ) = φ :=
  Corepresented.groupSchemeMap_pointsTrans e d φ

theorem groupSchemeMap_comp (α : F ⟶ F') (β : F' ⟶ F'') :
    groupSchemeMap e c (α ≫ β) = groupSchemeMap e d α ≫ groupSchemeMap d c β :=
  (Corepresented.groupSchemeMap_comp e d c α β).symm

/-- Centrality of a natural homomorphism gives the published centrality of the group-scheme
homomorphism. -/
theorem isCentral_groupSchemeMap {α : F ⟶ F'} (hα : IsCentralNat α) :
    IsCentral (groupSchemeMap e d α) :=
  Corepresented.isCentral_groupSchemeMap e d α hα

/-- The published centrality of the group-scheme homomorphism gives centrality of the natural
homomorphism. -/
theorem isCentralNat_of_isCentral {α : F ⟶ F'} (h : IsCentral (groupSchemeMap e d α)) :
    IsCentralNat α := by
  intro S x y
  have hc := (h _ ((affinePointsEquiv F e S).symm x)) _ (𝟙 _) ((affinePointsEquiv F' d S).symm y)
  rw [Category.id_comp] at hc
  have := congrArg (affinePointsEquiv F' d S) hc.eq
  rw [map_mul, map_mul, groupSchemeMap_affinePoints, MulEquiv.apply_symm_apply,
    MulEquiv.apply_symm_apply] at this
  exact this

/-- A surjective classifying map gives a closed subgroup. -/
theorem isClosedSubgroup_groupSchemeMap {α : F ⟶ F'}
    (h : Function.Surjective (classify e d α).hom) :
    IsClosedSubgroup (groupSchemeMap e d α) := by
  change IsClosedImmersion (groupSchemeMap e d α).hom.hom.left
  rw [groupSchemeMap_hom]
  exact IsClosedImmersion.spec_of_surjective _ h

end Bridge

/-! ### The lattice torus of a free abelian group is the split torus -/

section Torus

variable (R : CommRingCat.{u}) (I : Type u) [Finite I]

/-- Characters of `FreeAbelianGroup I` are `I`-families of units. -/
def freeCharEquiv (A : CommAlgCat.{u} R) :
    (latticeFunctor R (FreeAbelianGroup I)).obj A ≃* (I → Aˣ) where
  toFun χ i := asChar χ (Multiplicative.ofAdd (FreeAbelianGroup.of i))
  invFun u := AddMonoidHom.toMultiplicativeLeft (FreeAbelianGroup.lift fun i => Additive.ofMul (u i))
  left_inv χ := by
    apply AddMonoidHom.toMultiplicativeLeft.symm.injective
    rw [Equiv.symm_apply_apply]
    apply FreeAbelianGroup.lift_ext
    intro i
    rw [FreeAbelianGroup.lift_apply_of]
    rfl
  right_inv u := by
    funext i
    change Additive.toMul (FreeAbelianGroup.lift (fun i => Additive.ofMul (u i))
      (FreeAbelianGroup.of i)) = u i
    rw [FreeAbelianGroup.lift_apply_of]
    rfl
  map_mul' χ ψ := rfl

/-- The lattice torus of `FreeAbelianGroup I` is the split torus `𝔾_m^I`. -/
def torusIso :
    groupScheme (latticeFunctor R (FreeAbelianGroup I)) (latticeCorep R (FreeAbelianGroup I)) ≅
      splitTorus (Spec R) I :=
  isoOfPointModels (fun T : Over (Spec R) => I → (Γ(T.left, ⊤))ˣ)
    (fun a => splitTorus.unitsRestrict I a)
    (fun T => (pointsEquiv _ (latticeCorep R (FreeAbelianGroup I)) T).trans
      (freeCharEquiv R I ((algΓ R).obj T).unop))
    (fun T => splitTorus.pointsEquiv I T)
    (fun a x => by
      change freeCharEquiv R I _
        (pointsEquiv _ (latticeCorep R (FreeAbelianGroup I)) _ (a ≫ x)) = _
      rw [pointsEquiv_naturality]
      rfl)
    (fun a y => splitTorus.pointsEquiv_naturality I a y)

end Torus

end Langlands.GroupScheme.SplitComponent
