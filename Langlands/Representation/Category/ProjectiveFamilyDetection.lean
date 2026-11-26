import Langlands.Representation.Category.ProjectiveGeneration

/-! # Detection of nonzero maps by a family of projective smooth representations

If every member of a class of smooth representations is projective and every irreducible
smooth representation receives a nonzero map from some member, then every nonzero map of
smooth representations is detected by a map from some member.
-/

noncomputable section

open CategoryTheory
open Langlands.CategoryTheory.Renard

namespace Langlands.SmoothRep

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G]

/-- A class `Q` of projective smooth representations such that every irreducible smooth
representation receives a nonzero map from a member of `Q` detects every nonzero map: for
`d : X ⟶ Y` nonzero there are `P` in `Q` and `s : P ⟶ X` with `s ≫ d ≠ 0`. -/
theorem exists_comp_ne_zero_of_projective_family
    (Q : ObjectProperty (SmoothRep.{0, uG, uV} ℂ G))
    (hproj : ∀ P, Q P → Projective P)
    (hdet : ∀ D : SmoothRep.{0, uG, uV} ℂ G, D.IsIrreducible →
      ∃ P, Q P ∧ ∃ a : P ⟶ D, a ≠ 0)
    {X Y : SmoothRep.{0, uG, uV} ℂ G} (d : X ⟶ Y) (hd : d ≠ 0) :
    ∃ P, Q P ∧ ∃ s : P ⟶ X, s ≫ d ≠ 0 := by
  classical
  have hv : ∃ v : X, hom d v ≠ 0 := by
    by_contra hn
    apply hd
    ext v
    exact Classical.not_not.mp (not_exists.mp hn v)
  obtain ⟨v, hv⟩ := hv
  let R := image d
  let : Nontrivial R :=
    ⟨⟨⟨hom d v, ⟨v, rfl⟩⟩, 0, fun h => hv (congrArg Subtype.val h)⟩⟩
  obtain ⟨D, hD, hDR⟩ := exists_isIrreducible_isSubquotient_of_nontrivial R
  obtain ⟨P, hP, a, ha⟩ := hdet D hD
  let : Projective P := hproj P hP
  obtain ⟨C, i, q, hi, hq⟩ := isSubquotient_iff_exists.mp hDR
  let : Epi q := (epi_iff_surjective q).mpr hq
  let : Mono i := (mono_iff_injective i).mpr hi
  let r : P ⟶ C := Projective.factorThru a q
  have hr : r ≫ q = a := Projective.factorThru_comp a q
  let b : P ⟶ R := r ≫ i
  have hb : b ≠ 0 := by
    intro h
    have hr0 : r = 0 := (cancel_mono i).mp (by simpa [b] using h)
    exact ha (hr.symm.trans (by simp [hr0]))
  let qX : X ⟶ R := ofHom {
    toLinearMap := (hom d).toLinearMap.rangeRestrict
    isIntertwining' g := by
      ext w
      exact Subtype.ext (Representation.IntertwiningMap.isIntertwining _ _ (hom d) g w) }
  let : Epi qX := (epi_iff_surjective qX).mpr (LinearMap.surjective_rangeRestrict _)
  let : Mono (imageι d) := (mono_iff_injective (imageι d)).mpr (subtype_injective _ _)
  have hqd : qX ≫ imageι d = d := by ext w; rfl
  have hbi : b ≫ imageι d ≠ 0 := by
    intro h
    exact hb ((cancel_mono (imageι d)).mp (by simpa using h))
  let s : P ⟶ X := Projective.factorThru b qX
  have hs : s ≫ d = b ≫ imageι d := by
    calc
      s ≫ d = s ≫ (qX ≫ imageι d) := congrArg (fun t => s ≫ t) hqd.symm
      _ = (s ≫ qX) ≫ imageι d := (Category.assoc _ _ _).symm
      _ = b ≫ imageι d :=
        congrArg (fun t => t ≫ imageι d) (Projective.factorThru_comp b qX)
  exact ⟨P, hP, s, fun h => hbi (hs.symm.trans h)⟩

end Langlands.SmoothRep
