import Langlands.AlgebraicGeometry.Picard.DvrAbelianAmpleSpecializationStatement
import Langlands.AbelianScheme.AffineSectionAmple
import Langlands.AlgebraicGeometry.Picard.DvrAbelianAffineSection

/-! # Generic-to-special ampleness on an abelian scheme over a DVR: proof -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard

set_option backward.isDefEq.respectTransparency.types false in
/-- A section of a positive power whose generation open is affine and meets the closed fibre
makes the closed residue-field fibre bundle ample. -/
theorem isAmple_closedFibre_of_section (R : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] (A : Langlands.AbelianScheme (Spec (CommRingCat.of R)))
    (L : LineBundle A.X.left) {m : ℕ} (hm : 1 ≤ m) (τ : L.powSections m)
    (haff : IsAffineOpen (L.sectionOpen τ)) {x : A.X.left} (hxτ : x ∈ L.sectionOpen τ)
    (hfx : A.X.hom x = IsLocalRing.closedPoint R) :
    ((LineBundle.pullback (A.X.hom.fiberι (IsLocalRing.closedPoint R))).obj L).IsAmple := by
  let s₀ : Spec (CommRingCat.of R) := IsLocalRing.closedPoint R
  let b := (Spec (CommRingCat.of R)).fromSpecResidueField s₀
  let As := (Langlands.AbelianScheme.baseChange b).obj A
  let ι : As.X.left ⟶ A.X.left := A.X.hom.fiberι s₀
  have : IsAffineHom b := isAffineHom_of_isAffine b
  have : IsAffineHom ι := MorphismProperty.pullback_fst _ _ (inferInstance : IsAffineHom b)
  have hopen := LineBundle.sectionOpen_pullbackPowSection ι L τ
  refine Langlands.AbelianScheme.AffineSectionAmple.isAmple_of_isAffineOpen_sectionOpen
    ((Spec (CommRingCat.of R)).residueField s₀) As ((LineBundle.pullback ι).obj L) m hm
    (L.pullbackPowSection ι τ) ?_ ?_
  · rw [hopen]
    have hx : x ∈ A.X.hom ⁻¹' {s₀} := hfx
    refine ⟨(A.X.hom.fiberHomeo s₀).symm ⟨x, hx⟩, ?_⟩
    change ι _ ∈ L.sectionOpen τ
    rw [show ι ((A.X.hom.fiberHomeo s₀).symm ⟨x, hx⟩) = x from
      A.X.hom.fiberι_fiberHomeo_symm s₀ ⟨x, hx⟩]
    exact hxτ
  · rw [hopen]
    exact haff.preimage ι

/-- On an abelian scheme over a discrete valuation domain, a specified total line bundle
that is ample on the generic residue-field fibre is ample on the closed residue-field
fibre. -/
theorem dvrAbelianAmpleSpecialization : DvrAbelianAmpleSpecializationStatement.{u} := by
  intro R _ _ _ A L hη
  obtain ⟨m, hm, τ, haff, x, hxτ, hfx⟩ :=
    DvrAbelianGeometry.exists_affine_section_meeting_closedFibre A L hη
  exact isAmple_closedFibre_of_section R A L hm τ haff hxτ hfx

end Langlands.AlgebraicGeometry.Picard
