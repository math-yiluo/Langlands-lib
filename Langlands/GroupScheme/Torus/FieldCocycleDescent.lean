import Langlands.GroupScheme.Torus.OpenSections

/-! # Split-torus cocycles over fields -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

namespace Cocycle

/-- An open neighbourhood of a point of the spectrum of a field is the whole base. -/
theorem opens_eq_top_of_field {k : Type u} [Field k]
    (W : (Spec (CommRingCat.of k)).Opens) (y : Spec (CommRingCat.of k)) (hy : y ∈ W) :
    W = ⊤ := by
  apply top_unique
  intro x _
  exact (Subsingleton.elim x y) ▸ hy

/-- Over a field, every cocycle of a split torus on an affine faithfully flat cover
is a coboundary on that same cover. -/
theorem isTrivial_of_isSplitTorus_overField {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} {U : Over (Spec (CommRingCat.of k))}
    [IsAffineHom U.hom] [Flat U.hom] [Surjective U.hom]
    (hG : IsSplitTorus G) (ξ : Cocycle G U) : ξ.IsTrivial := by
  let y : Spec (CommRingCat.of k) := (⊥ : PrimeSpectrum k)
  let L := Classical.choice (nonempty_localTrivialization_of_isSplitTorus hG ξ y)
  have hW : L.openSet = ⊤ := opens_eq_top_of_field L.openSet y L.mem_openSet
  have hV : U.hom ⁻¹ᵁ L.openSet = ⊤ := by rw [hW]; rfl
  let r : Over.mk ((U.hom ⁻¹ᵁ L.openSet).ι ≫ U.hom) ⟶ U :=
    Over.homMk (U.hom ⁻¹ᵁ L.openSet).ι
  have hr : IsIso r.left := by
    change IsIso (U.hom ⁻¹ᵁ L.openSet).ι
    rw [hV]
    exact inferInstanceAs (IsIso U.left.topIso.hom)
  have : IsIso ((Over.forget _).map r) := hr
  have : IsIso r := isIso_of_reflects_iso r (Over.forget _)
  refine ⟨inv r ≫ L.cochain, fun a b => ?_⟩
  have h := L.coboundary (a ≫ inv r) (b ≫ inv r)
  simpa only [r, Category.assoc, IsIso.inv_hom_id, Category.comp_id] using h

/-- A chosen trivializing cochain on the supplied cover of a field spectrum. -/
def fieldTrivializingCochain {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} {U : Over (Spec (CommRingCat.of k))}
    [IsAffineHom U.hom] [Flat U.hom] [Surjective U.hom]
    (hG : IsSplitTorus G) (ξ : Cocycle G U) : U ⟶ G.X :=
  (isTrivial_of_isSplitTorus_overField hG ξ).choose

/-- The chosen cochain retains the original cocycle's all-test identity. -/
theorem fieldTrivializingCochain_spec {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} {U : Over (Spec (CommRingCat.of k))}
    [IsAffineHom U.hom] [Flat U.hom] [Surjective U.hom]
    (hG : IsSplitTorus G) (ξ : Cocycle G U) {Z : Over (Spec (CommRingCat.of k))}
    (a b : Z ⟶ U) :
    ξ.toFun a b =
      (a ≫ fieldTrivializingCochain hG ξ) * (b ≫ fieldTrivializingCochain hG ξ)⁻¹ :=
  (isTrivial_of_isSplitTorus_overField hG ξ).choose_spec a b

end Cocycle

end Langlands.GroupScheme
