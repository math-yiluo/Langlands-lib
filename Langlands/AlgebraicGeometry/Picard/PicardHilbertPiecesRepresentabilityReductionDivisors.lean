import Langlands.AlgebraicGeometry.Picard.PicardHilbertPiecesRepresentabilityReductionClasses

/-! # Picard classes of relative effective divisors under base change -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory Opposite

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard.PicardHilbertPiecesReduction

open StructureKernelModule

section Divisors

variable {Y Y' : Scheme.{u}}

lemma pb_comp_apply {Y₁ Y₂ Y₃ : Scheme.{u}} (a : Y₁ ⟶ Y₂) (b : Y₂ ⟶ Y₃) (x : Group Y₃) :
    Group.pullback (a ≫ b) x = Group.pullback a (Group.pullback b x) := by
  rw [Group.pullback_comp]
  rfl

/-- The Picard class of the divisor line bundle `O(D)` of an effective Cartier ideal. -/
def dcl (I : Y.IdealSheafData) (hI : IsEffectiveCartierIdeal I) : Group Y :=
  (EffectiveCartierDivisor.lineBundle ⟨I, hI⟩).classOf

lemma dcl_congr {I J : Y.IdealSheafData} (h : I = J) (hI : IsEffectiveCartierIdeal I)
    (hJ : IsEffectiveCartierIdeal J) : dcl I hI = dcl J hJ := by
  subst h
  rfl

lemma dcl_eq (I : Y.IdealSheafData) (hI : IsEffectiveCartierIdeal I) :
    dcl I hI = -(EffectiveCartierDivisor.idealLineBundle ⟨I, hI⟩).classOf :=
  classOf_dual _

/-- Divisor classes are pulled back along an identification of the ideal kernels. -/
lemma dcl_of_kernelIso (φ : Y' ⟶ Y) (I : Y.IdealSheafData) (J : Y'.IdealSheafData)
    (hI : IsEffectiveCartierIdeal I) (hJ : IsEffectiveCartierIdeal J)
    (e : (Scheme.Modules.pullback φ).obj (kernelModule I.subschemeι) ≅
      kernelModule J.subschemeι) :
    dcl J hJ = Group.pullback φ (dcl I hI) := by
  rw [dcl_eq, dcl_eq, map_neg, Group.pullback_lineBundle_classOf]
  congr 1
  exact (LineBundle.classOf_eq_iff _ _).2 ⟨e.symm⟩

/-- The pullback square of the closed subscheme of a pulled-back ideal. -/
lemma isPullback_comap (φ : Y' ⟶ Y) (I : Y.IdealSheafData) :
    IsPullback ((I.comapIso φ).hom ≫ pullback.snd φ I.subschemeι) (I.comap φ).subschemeι
      I.subschemeι φ := by
  refine (IsPullback.of_iso_pullback ⟨?_⟩ (I.comapIso φ) (I.comapIso_hom_fst φ) rfl).flip
  rw [← I.comapIso_hom_fst φ, Category.assoc, Category.assoc, pullback.condition]

/-- Flat pullback of a relative effective divisor, with its divisor class. -/
lemma flat_comap {T : Scheme.{u}} (φ : Y' ⟶ Y) [Flat φ] (p : Y ⟶ T) (I : Y.IdealSheafData)
    (hI : IsRelativeEffectiveCartierIdeal p I) :
    ∃ h : IsRelativeEffectiveCartierIdeal (φ ≫ p) (I.comap φ),
      dcl (I.comap φ) h.1 = Group.pullback φ (dcl I hI.1) := by
  let e := StructureKernelFlatBaseChange.kernelModuleFlatBaseChangeIso φ I.subschemeι
    (I.comap φ).subschemeι ((I.comapIso φ).hom ≫ pullback.snd φ I.subschemeι)
    (isPullback_comap φ I)
  have h1 : IsEffectiveCartierIdeal (I.comap φ) := (hI.1.pullback φ).of_iso e
  have : Flat (I.subschemeι ≫ p) := hI.2
  have h2 : Flat ((I.comap φ).subschemeι ≫ φ ≫ p) := by
    rw [← I.comapIso_hom_fst φ, Category.assoc, pullback.condition_assoc]
    infer_instance
  exact ⟨⟨h1, h2⟩, dcl_of_kernelIso φ I _ hI.1 h1 e⟩

/-- Base change of a relative effective divisor along a cartesian square, with its divisor
class, from the base-change statement. -/
lemma bc_comap (hbc : RelativeEffectiveDivisorBaseChangeStatement.{u})
    {T T' : Scheme.{u}} {h : Y' ⟶ Y} {q : Y' ⟶ T'} {p : Y ⟶ T} {g : T' ⟶ T}
    (sq : IsPullback h q p g) (I : Y.IdealSheafData) (hI : IsRelativeEffectiveCartierIdeal p I) :
    ∃ hJ : IsRelativeEffectiveCartierIdeal q (I.comap h),
      dcl (I.comap h) hJ.1 = Group.pullback h (dcl I hI.1) := by
  obtain ⟨h1, e, -⟩ := hbc T Y p I hI T' g
  have hdJ := dcl_of_kernelIso (pullback.snd g p) I _ hI.1 h1.1 e
  let φ := sq.flip.isoPullback
  obtain ⟨h3, hd3⟩ := flat_comap φ.hom (pullback.fst g p) _ h1
  have hq : φ.hom ≫ pullback.fst g p = q := sq.flip.isoPullback_hom_fst
  have hh : φ.hom ≫ pullback.snd g p = h := sq.flip.isoPullback_hom_snd
  have hI' : I.comap h = (I.comap (pullback.snd g p)).comap φ.hom := by
    rw [← hh, Scheme.IdealSheafData.comap_comp]
  rw [hq, ← hI'] at h3
  refine ⟨h3, ?_⟩
  rw [dcl_congr hI' h3.1 (by rw [← hI']; exact h3.1), hd3, hdJ, ← pb_comp_apply, hh]

end Divisors

section Families

variable {S X : Scheme.{u}} (f : X ⟶ S)

/-- The comparison map `X ×_S T' ⟶ X ×_S T` over a morphism `T' ⟶ T` of `S`-schemes, as in the
statements. -/
abbrev mapX {T T' : Scheme.{u}} {s : T ⟶ S} {s' : T' ⟶ S} (h : T' ⟶ T) (w : h ≫ s = s') :
    pullback f s' ⟶ pullback f s :=
  pullback.map f s' f s (𝟙 X) h (𝟙 _) (by simp) (by simp [w])

@[reassoc]
lemma mapX_fst {T T' : Scheme.{u}} {s : T ⟶ S} {s' : T' ⟶ S} (h : T' ⟶ T) (w : h ≫ s = s') :
    mapX f h w ≫ pullback.fst f s = pullback.fst f s' :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

@[reassoc]
lemma mapX_snd {T T' : Scheme.{u}} {s : T ⟶ S} {s' : T' ⟶ S} (h : T' ⟶ T) (w : h ≫ s = s') :
    mapX f h w ≫ pullback.snd f s = pullback.snd f s' ≫ h :=
  pullback.lift_snd _ _ _

lemma isPullback_mapX {T T' : Scheme.{u}} {s : T ⟶ S} {s' : T' ⟶ S} (h : T' ⟶ T)
    (w : h ≫ s = s') :
    IsPullback (mapX f h w) (pullback.snd f s') (pullback.snd f s) h := by
  subst w
  refine IsPullback.of_right ?_ (mapX_snd f h rfl) (IsPullback.of_hasPullback f s)
  rw [mapX_fst]
  exact IsPullback.of_hasPullback f (h ≫ s)

lemma mapX_comp {T T' T'' : Scheme.{u}} {s : T ⟶ S} {s' : T' ⟶ S} {s'' : T'' ⟶ S}
    (h : T' ⟶ T) (w : h ≫ s = s') (h' : T'' ⟶ T') (w' : h' ≫ s' = s'') :
    mapX f h' w' ≫ mapX f h w = mapX f (h' ≫ h) (by rw [Category.assoc, w, w']) := by
  apply pullback.hom_ext
  · rw [Category.assoc, mapX_fst, mapX_fst, mapX_fst]
  · rw [Category.assoc, mapX_snd, mapX_snd_assoc, mapX_snd]

/-- Base change of the classes of relative effective divisors on `X ×_S T`. -/
lemma divBC (hbc : RelativeEffectiveDivisorBaseChangeStatement.{u}) {T T' : Scheme.{u}}
    {s : T ⟶ S} {s' : T' ⟶ S} (h : T' ⟶ T) (w : h ≫ s = s')
    (I : (pullback f s).IdealSheafData) (hI : IsRelativeEffectiveCartierIdeal (pullback.snd f s) I) :
    ∃ hJ : IsRelativeEffectiveCartierIdeal (pullback.snd f s') (I.comap (mapX f h w)),
      dcl (I.comap (mapX f h w)) hJ.1 = Group.pullback (mapX f h w) (dcl I hI.1) :=
  bc_comap hbc (isPullback_mapX f h w) I hI

lemma pb_mapX_fst {T T' : Scheme.{u}} {s : T ⟶ S} {s' : T' ⟶ S} (h : T' ⟶ T)
    (w : h ≫ s = s') (x : Group X) :
    Group.pullback (mapX f h w) (Group.pullback (pullback.fst f s) x) =
      Group.pullback (pullback.fst f s') x := by
  rw [← pb_comp_apply, mapX_fst]

end Families

end Langlands.AlgebraicGeometry.Picard.PicardHilbertPiecesReduction
