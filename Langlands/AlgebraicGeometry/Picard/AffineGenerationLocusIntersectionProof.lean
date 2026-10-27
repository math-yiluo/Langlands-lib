import Langlands.AlgebraicGeometry.Picard.AffineGenerationLocusIntersectionStatement
import Langlands.AlgebraicGeometry.Modules.LineBundleFrameOpen
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # Affineness of an affine open intersected with a line-bundle section locus -/

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

set_option backward.isDefEq.respectTransparency false

namespace Langlands.SchemeModule

variable {X : Scheme.{u}}

/-- The coefficient on a smaller open is the restriction of the coefficient. -/
lemma unitEndCoefficient_res (φ : structureModule X ⟶ structureModule X)
    {U V : X.Opens} (i : U ⟶ V) :
    unitEndCoefficient φ U = X.presheaf.map i.op (unitEndCoefficient φ V) := by
  have h := unitEnd_naturality φ i (1 : Γ(X, V))
  rw [map_one] at h
  exact h

/-- An endomorphism of the structure module is a stalk isomorphism exactly on the
basic open of its global coefficient. -/
theorem unitEnd_stalkIso_iff_mem_basicOpen (φ : structureModule X ⟶ structureModule X)
    (x : X) :
    IsIso ((TopCat.Presheaf.stalkFunctor Ab.{u} x).map φ.mapPresheaf) ↔
      x ∈ X.basicOpen (unitEndCoefficient φ ⊤) := by
  constructor
  · intro h
    obtain ⟨V, hxV, hV⟩ := unitEnd_localUnit φ x
    have hB : X.basicOpen (unitEndCoefficient φ V) = V := X.basicOpen_of_isUnit hV
    rw [unitEndCoefficient_res φ (homOfLE le_top : V ⟶ ⊤), Scheme.basicOpen_res] at hB
    have hx : x ∈ V ⊓ X.basicOpen (unitEndCoefficient φ ⊤) := by
      rw [hB]
      exact hxV
    exact hx.2
  · intro hx
    let B := X.basicOpen (unitEndCoefficient φ ⊤)
    have hB : IsUnit (unitEndCoefficient φ B) := by
      rw [unitEndCoefficient_res φ (homOfLE (X.basicOpen_le _) : B ⟶ ⊤)]
      exact X.toRingedSpace.isUnit_res_basicOpen _
    have := unitEnd_restrict_isIso φ B hB
    exact (isIso_stalk_restrict_iff φ B ⟨x, hx⟩).mp (by infer_instance)

open Langlands.AlgebraicGeometry.Picard

/-- On an open trivializing a line bundle, the section locus is a basic open. -/
theorem exists_inf_trivializationOpen_eq_basicOpen (L : LineBundle X)
    (s : GlobalSections L.obj) (W : X.Opens)
    (e : L.obj.restrict W.ι ≅ SheafOfModules.unit W.toScheme.ringCatSheaf) :
    ∃ a : Γ(X, W), W ⊓ trivializationOpen L.obj s = X.basicOpen a := by
  let φ := sectionHom L.obj s
  let ψ : structureModule W.toScheme ⟶ structureModule W.toScheme :=
    (Scheme.Modules.restrictUnitIso W.ι).inv ≫
      (Scheme.Modules.restrictFunctor W.ι).map φ ≫ e.hom
  have hψ (y : W.toScheme) :
      IsIso ((TopCat.Presheaf.stalkFunctor Ab.{u} y).map ψ.mapPresheaf) ↔
        IsStalkFrame L.obj s (W.ι y) := by
    change IsIso (((Scheme.Modules.toPresheaf W.toScheme) ⋙
      TopCat.Presheaf.stalkFunctor Ab.{u} y).map ψ) ↔ _
    simp only [ψ, Functor.map_comp, isIso_comp_left_iff, isIso_comp_right_iff]
    exact isIso_stalk_restrict_iff φ W y
  have hframe (x : X) : IsStalkFrame L.obj s x ↔ x ∈ trivializationOpen L.obj s :=
    Set.ext_iff.mp (lineBundle_stalkFrame_set_eq L s) x
  refine ⟨W.topIso.hom (unitEndCoefficient ψ ⊤), ?_⟩
  rw [← Scheme.Opens.ι_image_basicOpen_topIso_inv, Iso.hom_inv_id_apply]
  apply le_antisymm
  · rintro x ⟨hxW, hxs⟩
    refine ⟨⟨x, hxW⟩, ?_, rfl⟩
    exact (unitEnd_stalkIso_iff_mem_basicOpen ψ _).mp ((hψ _).mpr ((hframe x).mpr hxs))
  · rintro x ⟨y, hy, rfl⟩
    exact ⟨y.2, (hframe _).mp ((hψ y).mp ((unitEnd_stalkIso_iff_mem_basicOpen ψ y).mpr hy))⟩

end Langlands.SchemeModule

namespace Langlands.AlgebraicGeometry.Picard

open Langlands.SchemeModule

/-- An affine open intersected with the whole section locus of a line bundle is affine. -/
theorem affineGenerationLocusIntersection : AffineGenerationLocusIntersectionStatement.{u} := by
  intro X L s U hU
  let S : Set Γ(X, U) := {g | IsAffineOpen (X.basicOpen g ⊓ trivializationOpen L.obj s)}
  have hS : Ideal.span S = ⊤ := by
    rw [← hU.self_le_iSup_basicOpen_iff]
    intro x hxU
    obtain ⟨W, hxW, ⟨e⟩⟩ := L.property x
    obtain ⟨a, ha⟩ := exists_inf_trivializationOpen_eq_basicOpen L s W e
    obtain ⟨g, hgW, hxg⟩ := hU.exists_basicOpen_le (V := W) ⟨x, hxW⟩ hxU
    have hg : g ∈ S := by
      change IsAffineOpen (X.basicOpen g ⊓ trivializationOpen L.obj s)
      have hga : X.basicOpen g ⊓ trivializationOpen L.obj s =
          X.basicOpen (X.presheaf.map (homOfLE hgW).op a) := by
        rw [Scheme.basicOpen_res, ← ha, ← inf_assoc, inf_eq_left.mpr hgW]
      rw [hga]
      exact (hU.basicOpen g).basicOpen _
    exact Opens.mem_iSup.mpr ⟨⟨g, hg⟩, hxg⟩
  let ρ := X.presheaf.map (homOfLE (inf_le_left : U ⊓ trivializationOpen L.obj s ≤ U)).op
  apply isAffineOpen_of_isAffineOpen_basicOpen (U ⊓ trivializationOpen L.obj s) (ρ.hom '' S)
  · rw [← Ideal.map_span ρ.hom, hS, Ideal.map_top]
  · rintro _ ⟨g, hg, rfl⟩
    change IsAffineOpen (X.basicOpen (X.presheaf.map _ g))
    rw [Scheme.basicOpen_res, inf_comm, ← inf_assoc, inf_eq_left.mpr (X.basicOpen_le g)]
    exact hg

end Langlands.AlgebraicGeometry.Picard
