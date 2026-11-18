import Langlands.GroupScheme.IdempotentRetractClopen
import Langlands.GroupScheme.Reductive.IdempotentImage
import Langlands.GroupScheme.Reductive.BaseChange
import Langlands.GroupScheme.SimplyConnected.AlmostSimpleFactorDescentProperties

/-! # The actual clopen decomposition of a normal idempotent -/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

variable {S : Scheme.{u}} {G : GroupScheme S}

/-- Almost-simplicity of a chosen geometric fibre reflects to its residue fibre. -/
theorem isAlmostSimple_residueFiber_of_geometric (s : S)
    (h : IsAlmostSimple (geometricFiber G s)) :
    IsAlmostSimple ((baseChange (S.fromSpecResidueField s)).obj G) := by
  apply IsAlmostSimple.of_fieldExtension (k := S.residueField s)
    (K := AlgebraicClosure (S.residueField s))
  exact h.of_iso
    (baseChangeCompIso (S.fromSpecResidueField s) (toAlgebraicClosure (S.residueField s)) G).symm

/-- The trivial and identity endomorphisms of an almost-simple field group differ. -/
theorem IsAlmostSimple.zero_ne_id {k : Type u} [Field k]
    {H : GroupScheme (Spec (CommRingCat.of k))} (hH : IsAlmostSimple H) :
    (0 : H ⟶ H) ≠ 𝟙 H := by
  intro h
  apply hH.noncommutative
  intro T x y
  have hx : x = 1 := by
    have he := congrArg (fun f : H ⟶ H => x ≫ f.hom.hom) h
    change x ≫ (1 : H.X ⟶ H.X) = x ≫ 𝟙 H.X at he
    simpa only [MonObj.comp_one, Category.comp_id] using he.symm
  rw [hx]
  exact Commute.one_left _

/-- Full relative conjugation equivariance implies normality of the pointwise image. -/
theorem normal_range_of_conjugation_equivariant (ψ : G ⟶ G)
    (h : ∀ (T : Over S) (g x : T ⟶ G.X),
      (g * x * g⁻¹) ≫ ψ.hom.hom = g * (x ≫ ψ.hom.hom) * g⁻¹) :
    (SubgroupFunctor.range ψ).IsNormal := by
  intro T g z _ hz
  obtain ⟨x, rfl⟩ := SubgroupFunctor.mem_range.mp hz
  exact SubgroupFunctor.mem_range.mpr ⟨g * x * g⁻¹, h T g x⟩

/-- An actual base decomposition, with exact identity and trivial restrictions. -/
structure NormalIdempotentDecomposition (ψ : G ⟶ G) where
  identityPart : S.Opens
  zeroPart : S.Opens
  clopen : IsClopen (identityPart : Set S)
  cover : identityPart ⊔ zeroPart = ⊤
  disjoint : Disjoint identityPart zeroPart
  identity_eq : (baseChange identityPart.ι).map ψ =
    𝟙 ((baseChange identityPart.ι).obj G)
  zero_eq : (baseChange zeroPart.ι).map ψ = 0

/-- A normal-image idempotent on a reductive group with almost-simple
geometric fibres is exactly identity and trivial on complementary base opens. -/
def normalIdempotentDecomposition (hG : IsReductive G)
    (hAS : ∀ s : S, IsAlmostSimple (geometricFiber G s))
    (ψ : G ⟶ G) (hidem : ψ ≫ ψ = ψ)
    (hn : (SubgroupFunctor.range ψ).IsNormal) :
    NormalIdempotentDecomposition ψ := by
  let : Smooth G.X.hom := hG.smooth
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : GeometricallyConnected G.X.hom :=
    ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun k _ b =>
      (hG.isConnectedReductive_baseChange b).connectedSpace⟩
  let P := idempotentRetract ψ hidem
  let : Smooth P.group.X.hom := P.smooth
  let : GeometricallyConnected P.group.X.hom := P.geometricallyConnected
  have hd (s : S) : (baseChange (S.fromSpecResidueField s)).map ψ = 0 ∨
      (baseChange (S.fromSpecResidueField s)).map ψ =
        𝟙 ((baseChange (S.fromSpecResidueField s)).obj G) := by
    let F := baseChange (S.fromSpecResidueField s)
    apply (isAlmostSimple_residueFiber_of_geometric s (hAS s)).idempotent_eq_zero_or_id
    · rw [← F.map_comp, hidem]
    · rw [SubgroupFunctor.range_baseChangeHom]
      exact hn.baseChange _
  have hnt (s : S) : (0 : (baseChange (S.fromSpecResidueField s)).obj G ⟶
      (baseChange (S.fromSpecResidueField s)).obj G) ≠ 𝟙 _ :=
    (isAlmostSimple_residueFiber_of_geometric s (hAS s)).zero_ne_id
  exact ⟨P.identityOpen, P.zeroOpen, P.isClopen_identityOpen hd hnt,
    P.identityOpen_sup_zeroOpen hd, P.disjoint_identityOpen_zeroOpen hnt,
    P.map_eq_id_on_identityOpen, P.map_eq_zero_on_zeroOpen⟩

end Langlands.GroupScheme
