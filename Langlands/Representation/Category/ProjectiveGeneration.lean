import Langlands.Representation.Category.Abelian
import Langlands.Representation.Category.IrreducibleSubquotientExistence
import Langlands.Representation.Category.FiniteGenerationExhaustion
import Langlands.Representation.Classification.SupercuspidalSupport
import Langlands.Representation.Filtration.SubquotientAlgebraProof
import Langlands.CategoryTheory.Renard.HomFunctors
import Mathlib.CategoryTheory.Preadditive.Projective.Basic

/-! Projective generation detected by actual irreducible subquotients. -/

noncomputable section

open CategoryTheory
open Langlands.CategoryTheory.Renard

namespace Langlands.SmoothRep

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G]

/-- A projective smooth object that maps nontrivially to every irreducible
subquotient of the target detects every nonzero map to that target. -/
theorem exists_comp_ne_zero_of_projective_subquotients
    (P : SmoothRep.{0, uG, uV} ℂ G) [Projective P]
    {X Y : SmoothRep.{0, uG, uV} ℂ G} (d : X ⟶ Y) (hd : d ≠ 0)
    (hdet : ∀ D : SmoothRep.{0, uG, uV} ℂ G,
      D.IsIrreducible → IsSubquotient D Y → ∃ a : P ⟶ D, a ≠ 0) :
    ∃ s : P ⟶ X, s ≫ d ≠ 0 := by
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
  have hRY : IsSubquotient R Y :=
    (subrepresentation_isSubrepresentation (hom d).range).isSubquotient
  have hDY : IsSubquotient D Y :=
    Langlands.smoothSubquotientTransitivity ℂ G Y R D hDR hRY
  obtain ⟨a, ha⟩ := hdet D hD hDY
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
  exact ⟨s, fun h => hbi (hs.symm.trans h)⟩

/-- A chosen map detecting a nonzero map, obtained by lifting through an actual
irreducible subquotient of its image. -/
def projectiveSubquotientDetector
    (P : SmoothRep.{0, uG, uV} ℂ G) [Projective P]
    {X Y : SmoothRep.{0, uG, uV} ℂ G} (d : X ⟶ Y) (hd : d ≠ 0)
    (hdet : ∀ D : SmoothRep.{0, uG, uV} ℂ G,
      D.IsIrreducible → IsSubquotient D Y → ∃ a : P ⟶ D, a ≠ 0) : P ⟶ X :=
  Classical.choose (exists_comp_ne_zero_of_projective_subquotients P d hd hdet)

theorem projectiveSubquotientDetector_comp_ne_zero
    (P : SmoothRep.{0, uG, uV} ℂ G) [Projective P]
    {X Y : SmoothRep.{0, uG, uV} ℂ G} (d : X ⟶ Y) (hd : d ≠ 0)
    (hdet : ∀ D : SmoothRep.{0, uG, uV} ℂ G,
      D.IsIrreducible → IsSubquotient D Y → ∃ a : P ⟶ D, a ≠ 0) :
    projectiveSubquotientDetector P d hd hdet ≫ d ≠ 0 :=
  Classical.choose_spec (exists_comp_ne_zero_of_projective_subquotients P d hd hdet)

/-- A full smooth subcategory needs no abelian structure for this generation
criterion: ambient projectivity and detection of its irreducible subquotients
make the actual integer-module-valued Hom functor faithful. -/
theorem faithful_preadditiveCoyonedaInt_of_projective_subquotients
    (Q : ObjectProperty (SmoothRep.{0, uG, uV} ℂ G))
    (P : Q.FullSubcategory) [Projective P.obj]
    (hdet : ∀ Y : Q.FullSubcategory,
      ∀ D : SmoothRep.{0, uG, uV} ℂ G,
        D.IsIrreducible → IsSubquotient D Y.obj → ∃ a : P.obj ⟶ D, a ≠ 0) :
    (preadditiveCoyonedaInt P).Faithful where
  map_injective := by
    intro X Y f g hfg
    apply ObjectProperty.hom_ext
    apply sub_eq_zero.mp
    by_contra hn
    obtain ⟨s, hs⟩ := exists_comp_ne_zero_of_projective_subquotients
      P.obj (f.hom - g.hom) hn (hdet Y)
    let s' : P ⟶ X := ObjectProperty.homMk s
    have h : s' ≫ f = s' ≫ g := congrArg (fun m => m s') hfg
    have h' : s ≫ f.hom = s ≫ g.hom := congrArg (fun m => m.hom) h
    exact hs (by rw [Preadditive.comp_sub, h', sub_self])

end Langlands.SmoothRep
