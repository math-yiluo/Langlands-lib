import Langlands.AlgebraicGeometry.AffineCechDeRhamRegluingTransitions
import Langlands.AlgebraicGeometry.AffineCechDeRhamRegluingSchemes

/-! # Marked scheme lifts obtained by regluing from a lifted Hodge summand -/

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open Langlands.Scheme
open Langlands.AlgebraicGeometry.TwistedOpenGluing

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

namespace Langlands.AlgebraicGeometry.AffineCechDeRham.HodgeSummandCocycles

variable {R : Type u} [CommRing R] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)}
  {U : Scheme.AffineOpenCover.{u} X} [Smooth f] [IsSeparated f] [Finite U.I₀]
  {κ : Type u} [Fintype κ] {I : Ideal R} {b : κ → closedForms f U} {M : Submodule R (H1 f U)}
  (G : HodgeSummandCocycles I b M)
  (E : SheafOfModules.free (R := X.ringCatSheaf) κ ≅ relativeDifferentials f) (hI : I * I = ⊥)

set_option quotPrecheck false in
local notation "O" => coverOpens U

omit [Smooth f] [Finite U.I₀] [Fintype κ] in
include f in
private lemma affineInf {W V : X.Opens} (hW : IsAffineOpen W) (hV : IsAffineOpen V) :
    IsAffineOpen (W ⊓ V) := by
  let : X.IsSeparated := ⟨by rw [← Limits.terminal.comp_from f]; infer_instance⟩
  exact hW.inf hV

omit [Smooth f] [Finite U.I₀] [Fintype κ] in
include f in
private lemma affinePair (i j : U.I₀) : IsAffineOpen (O i ⊓ O j) :=
  affineInf (f := f) (isAffineOpen_opensRange (U.f i)) (isAffineOpen_opensRange (U.f j))

private abbrev localTransition {W : X.Opens} (hW : IsAffineOpen W) {i j : U.I₀}
    (hi : W ≤ O i) (hj : W ≤ O j) :=
  affineOpenEndomorphism hW (G.transition E hI hW hi hj)

@[reassoc]
private lemma localTransition_restrict {W V : X.Opens} (hW : IsAffineOpen W) (hV : IsAffineOpen V)
    {i j : U.I₀} (d : W ≤ V) (hi : V ≤ O i) (hj : V ≤ O j) :
    G.localTransition E hI hW (d.trans hi) (d.trans hj) ≫ X.homOfLE d =
      X.homOfLE d ≫ G.localTransition E hI hV hi hj :=
  affineOpenEndomorphism_homOfLE hW hV d _ _ (G.transition_restrict E hI hW hV d hi hj)

private abbrev theta (i j : U.I₀) : (O i ⊓ O j).toScheme ⟶ X :=
  G.localTransition E hI (affinePair (f := f) i j) inf_le_left inf_le_right ≫ (O i ⊓ O j).ι

private lemma theta_pointwise (i j : U.I₀) : IsPointwiseInclusion (G.theta E hI i j) :=
  affineOpenEndomorphism_pointwise I hI (affinePair (f := f) i j) _
    (G.transition_sub_mem E hI (affinePair (f := f) i j) inf_le_left inf_le_right)

private lemma restrictTo_theta {W Q : X.Opens} (hW : IsAffineOpen W)
    (i j : U.I₀) (e : W ≤ O i ⊓ O j) (d : W ≤ Q) :
    TwistedOpenGluing.restrictTo (G.theta E hI i j) (G.theta_pointwise E hI i j) e d =
      G.localTransition E hI hW (e.trans inf_le_left) (e.trans inf_le_right) ≫ X.homOfLE d := by
  rw [← cancel_mono Q.ι, restrictTo_ι, Category.assoc, Scheme.homOfLE_ι]
  change X.homOfLE e ≫ G.localTransition E hI (affinePair (f := f) i j) inf_le_left inf_le_right ≫
    (O i ⊓ O j).ι = _
  rw [← G.localTransition_restrict_assoc E hI hW (affinePair (f := f) i j) e _ _,
    Scheme.homOfLE_ι]

/-- Compose the cocycle's affine transitions to glue the original charts
as a new scheme over the thicker base. -/
def regluingData : Data X where
  J := U.I₀
  V := O
  θ := G.theta E hI
  pointwise := G.theta_pointwise E hI
  self i := by
    change affineOpenEndomorphism (affinePair (f := f) i i)
      (G.transition E hI _ (inf_le_left : O i ⊓ O i ≤ O i) inf_le_right) ≫ (O i ⊓ O i).ι = _
    rw [G.transition_self, affineOpenEndomorphism_id, Category.id_comp]
  cocycle i j l := by
    let W := O i ⊓ O j ⊓ O l
    let hW := affineInf (f := f) (affinePair (f := f) i j) (isAffineOpen_opensRange (U.f l))
    let hi : W ≤ O i := inf_le_left.trans inf_le_left
    let hj : W ≤ O j := inf_le_left.trans inf_le_right
    let hl : W ≤ O l := inf_le_right
    change TwistedOpenGluing.restrictTo (G.theta E hI j l) (G.theta_pointwise E hI j l)
      (le_inf hj hl) inf_le_left ≫ G.theta E hI i j =
      X.homOfLE (le_inf hi hl) ≫ G.theta E hI i l
    rw [G.restrictTo_theta E hI hW, Category.assoc]
    have he (a c : U.I₀) (d : W ≤ O a ⊓ O c) :
        X.homOfLE d ≫ G.theta E hI a c =
          G.localTransition E hI hW (d.trans inf_le_left) (d.trans inf_le_right) ≫ W.ι := by
      change X.homOfLE d ≫ G.localTransition E hI (affinePair (f := f) a c)
        inf_le_left inf_le_right ≫ (O a ⊓ O c).ι = _
      rw [← G.localTransition_restrict_assoc E hI hW (affinePair (f := f) a c) d _ _,
        Scheme.homOfLE_ι]
    rw [he i j, he i l, ← Category.assoc]
    change (affineOpenEndomorphism hW (G.transition E hI hW hj hl) ≫
      affineOpenEndomorphism hW (G.transition E hI hW hi hj)) ≫ W.ι =
      affineOpenEndomorphism hW (G.transition E hI hW hi hl) ≫ W.ι
    rw [affineOpenEndomorphism_comp, G.transition_comp]

lemma regluingData_over : (G.regluingData E hI).IsOver f := by
  intro i j
  change (affineOpenEndomorphism (affinePair (f := f) i j)
    (G.transition E hI _ (inf_le_left : O i ⊓ O j ≤ O i) inf_le_right) ≫ (O i ⊓ O j).ι) ≫ f = _
  rw [Category.assoc, affineOpenEndomorphism_over]
  rfl

/-- On an open in two pieces, the two maps to the reglued scheme are
related by the affine transition. -/
lemma regluedChart_transition {W : X.Opens} (hW : IsAffineOpen W) {i j : U.I₀}
    (hi : W ≤ O i) (hj : W ≤ O j) :
    X.homOfLE hj ≫ (G.regluingData E hI).ι j =
      affineOpenEndomorphism hW (G.transition E hI hW hi hj) ≫
        X.homOfLE hi ≫ (G.regluingData E hI).ι i := by
  let D := G.regluingData E hI
  let e : W ≤ O i ⊓ O j := le_inf hi hj
  let d : (O i ⊓ O j) ≤ O i := inf_le_left
  let c : (O i ⊓ O j) ≤ O j := inf_le_right
  let s := TwistedOpenGluing.restrictTo (D.θ i j) (D.pointwise i j) le_rfl d
  have hs : X.homOfLE e ≫ s =
      G.localTransition E hI hW hi hj ≫ X.homOfLE hi := by
    rw [← cancel_mono (O i).ι, Category.assoc]
    have hθ : s ≫ (O i).ι = G.theta E hI i j := by
      dsimp only [s]
      rw [TwistedOpenGluing.restrictTo_ι, Scheme.homOfLE_rfl, Category.id_comp]
      rfl
    rw [hθ, Category.assoc, Scheme.homOfLE_ι]
    change X.homOfLE e ≫ G.localTransition E hI (affinePair (f := f) i j) inf_le_left inf_le_right ≫
      (O i ⊓ O j).ι = _
    rw [← G.localTransition_restrict_assoc E hI hW (affinePair (f := f) i j) e _ _,
      Scheme.homOfLE_ι]
  calc
    _ = X.homOfLE e ≫ X.homOfLE c ≫ D.ι j := by
      rw [← Category.assoc, Scheme.homOfLE_homOfLE]
    _ = X.homOfLE e ≫ s ≫ D.ι i := congrArg (X.homOfLE e ≫ ·) (D.glue i j)
    _ = _ := by rw [← Category.assoc, hs, Category.assoc]

/-- The structural map on the reglued scheme. -/
abbrev regluedMap := (G.regluingData E hI).toBase (G.regluingData_over E hI)

private abbrev q := quotientBaseMap I
private abbrev redChart (i : U.I₀) := quotientReductionMap f I ⁻¹ᵁ O i

private lemma regluingData_θT (i j : U.I₀) :
    Data.θT (G.regluingData_over E hI) (q (I := I)) i j = (redChart (f := f) (I := I) i ⊓
      redChart (f := f) (I := I) j).ι := by
  apply pullback.hom_ext
  · rw [Data.θT_fst]
    let P := O i ⊓ O j
    let hP := affinePair (f := f) i j
    let a := G.transition E hI hP (inf_le_left : P ≤ O i) inf_le_right
    let r := quotientReductionMap f I
    change r.resLE P (r ⁻¹ᵁ P) le_rfl ≫ affineOpenEndomorphism hP a ≫ P.ι = (r ⁻¹ᵁ P).ι ≫ r
    rw [← Category.assoc, affineOpenEndomorphism_reduction I hP a
      (G.transition_sub_mem E hI hP inf_le_left inf_le_right), Scheme.Hom.resLE_comp_ι]
  · exact Data.θT_snd (G.regluingData_over E hI) (q (I := I)) i j

omit [Smooth f] [IsSeparated f] [Finite U.I₀] in
private lemma reduction_cover :
    ⨆ i : U.I₀, redChart (f := f) (I := I) i = ⊤ :=
  (quotientReductionMap f I).iSup_preimage_eq_top U.openCover.iSup_opensRange

private lemma reduction_compatible (i j : U.I₀) :
    (quotientReduction f I).homOfLE (inf_le_right :
      redChart (f := f) (I := I) i ⊓ redChart (f := f) (I := I) j ≤ _) ≫ (redChart (f := f) (I := I) j).ι =
    TwistedOpenGluing.restrictTo (((G.regluingData E hI).baseChange (G.regluingData_over E hI)
      (q (I := I))).θ i j) (((G.regluingData E hI).baseChange (G.regluingData_over E hI)
      (q (I := I))).pointwise i j) le_rfl inf_le_left ≫ (redChart (f := f) (I := I) i).ι := by
  rw [Scheme.homOfLE_ι]
  let D := (G.regluingData E hI).baseChange (G.regluingData_over E hI) (q (I := I))
  have ht : D.θ i j = (D.V i ⊓ D.V j).ι := G.regluingData_θT E hI i j
  change (D.V i ⊓ D.V j).ι =
    TwistedOpenGluing.restrictTo (D.θ i j) (D.pointwise i j) le_rfl inf_le_left ≫ (D.V i).ι
  rw [TwistedOpenGluing.restrictTo_ι, Scheme.homOfLE_rfl, Category.id_comp, ht]

private abbrev redInclusion (i : U.I₀) : (redChart (f := f) (I := I) i).toScheme ⟶ quotientReduction f I :=
  (redChart (f := f) (I := I) i).ι

omit [Smooth f] [IsSeparated f] [Finite U.I₀] in
private lemma reduction_preimage (i j : U.I₀) :
    (redInclusion (f := f) (I := I) j) ⁻¹ᵁ (redInclusion (f := f) (I := I) i).opensRange ≤
      (redChart (f := f) (I := I) j).ι ⁻¹ᵁ redChart (f := f) (I := I) i := by
  rw [redInclusion, Scheme.Opens.opensRange_ι]

/-- The reglued scheme has the given quotient reduction with matched charts. -/
def regluedMarking : quotientReduction f I ≅ quotientReduction (G.regluedMap E hI) I :=
  Data.liftIso (G.regluingData_over E hI) (q (I := I)) (redInclusion (f := f) (I := I))
    (by simp only [redInclusion, Scheme.Opens.opensRange_ι]; exact reduction_cover)
    reduction_preimage (G.reduction_compatible E hI)

lemma regluedMarking_over :
    (G.regluedMarking E hI).hom ≫ pullback.snd (G.regluedMap E hI) (q (I := I)) =
      pullback.snd f (q (I := I)) :=
  Data.liftIso_hom_snd _ _ _ _ _ _ _ (fun _ => rfl)

/-- The affine cover given by the open immersions of the reglued pieces. -/
def regluedCover : (G.regluingData E hI).glued.AffineOpenCover :=
  let D := G.regluingData E hI
  Scheme.AffineOpenCover.ofIsOpenCover (fun i : U.I₀ => (D.ι i).opensRange)
    (IsOpenCover.mk D.iSup_opensRange) (fun i => by
      let : IsAffine (D.V i).toScheme := isAffineOpen_opensRange (U.f i)
      exact isAffineOpen_opensRange (D.ι i))

lemma coverOpens_regluedCover (i : U.I₀) :
    coverOpens (G.regluedCover E hI) i = ((G.regluingData E hI).ι i).opensRange := by
  exact IsAffineOpen.opensRange_fromSpec _

instance : Finite (G.regluedCover E hI).I₀ :=
  inferInstanceAs (Finite U.I₀)

private lemma regluedMarking_on_chart (i : U.I₀) :
    redInclusion (f := f) (I := I) i ≫ (G.regluedMarking E hI).hom =
      Data.κ (G.regluingData_over E hI) (q (I := I)) i := by
  let D := G.regluingData E hI
  let hπ := G.regluingData_over E hI
  let D₀ := D.baseChange hπ (q (I := I))
  let e := D₀.recognize (redInclusion (f := f) (I := I))
    (by simp only [redInclusion, Scheme.Opens.opensRange_ι]; exact reduction_cover)
    reduction_preimage (G.reduction_compatible E hI)
  have he : D₀.ι i ≫ e.hom = redInclusion (f := f) (I := I) i :=
    Data.ι_recognize_hom D₀ (redInclusion (f := f) (I := I))
      (by simp only [redInclusion, Scheme.Opens.opensRange_ι]; exact reduction_cover)
      reduction_preimage (G.reduction_compatible E hI) (i : D₀.J)
  change redInclusion (f := f) (I := I) i ≫ e.inv ≫ (D.baseChangeIso hπ (q (I := I))).hom = _
  rw [← he, Category.assoc, Iso.hom_inv_id_assoc, Data.ι_baseChangeIso_hom]

lemma regluedChart_reduces (i : U.I₀) :
    (quotientReductionMap f I).resLE (O i) (redChart (f := f) (I := I) i) le_rfl ≫
      (G.regluingData E hI).ι i =
    (redChart (f := f) (I := I) i).ι ≫ (G.regluedMarking E hI).hom ≫
      quotientReductionMap (G.regluedMap E hI) I := by
  rw [← Category.assoc, regluedMarking_on_chart, Data.κ_fst, Scheme.Hom.resLE_eq_morphismRestrict]
  rfl

lemma regluedMarking_matches_charts (i : U.I₀) :
    quotientReductionMap f I ⁻¹ᵁ O i =
      ((G.regluedMarking E hI).hom ≫ quotientReductionMap (G.regluedMap E hI) I) ⁻¹ᵁ
        coverOpens (G.regluedCover E hI) i := by
  rw [coverOpens_regluedCover, Scheme.Hom.comp_preimage,
    ← Data.opensRange_κ (G.regluingData_over E hI) (q (I := I)) i]
  apply Opens.ext
  ext x
  let e := G.regluedMarking E hI
  change x ∈ redChart (f := f) (I := I) i ↔
    ∃ z : (redChart (f := f) (I := I) i).toScheme,
      Data.κ (G.regluingData_over E hI) (q (I := I)) i z = e.hom x
  rw [← G.regluedMarking_on_chart E hI i]
  change x ∈ redChart (f := f) (I := I) i ↔
    ∃ z : (redChart (f := f) (I := I) i).toScheme,
      e.hom (redInclusion (f := f) (I := I) i z) = e.hom x
  constructor
  · exact fun hx => ⟨⟨x, hx⟩, rfl⟩
  · rintro ⟨z, hz⟩
    have he (y : quotientReduction f I) : e.inv (e.hom y) = y := by
      rw [← Scheme.Hom.comp_apply, e.hom_inv_id]
      rfl
    have hx := congrArg (fun y => e.inv y) hz
    rw [he, he] at hx
    rw [← hx]
    exact z.property

lemma smooth_regluedMap : Smooth (G.regluedMap E hI) :=
  Data.smooth_toBase (G.regluingData_over E hI)

lemma proper_regluedMap [IsProper (pullback.snd f (quotientBaseMap I))] :
    IsProper (G.regluedMap E hI) := by
  have hnil : I ≤ nilradical R := by
    intro r hr
    refine ⟨2, ?_⟩
    have h := Ideal.mul_mem_mul hr hr
    rwa [hI, Ideal.mem_bot, ← pow_two] at h
  have : Surjective (q (I := I)) :=
    ⟨(PrimeSpectrum.comap_quotientMk_bijective_of_le_nilradical hnil).2⟩
  exact Data.isProper_toBase (G.regluingData_over E hI) (q (I := I))
    (pullback.snd f (q (I := I))) (redInclusion (f := f) (I := I))
    (by simp only [redInclusion, Scheme.Opens.opensRange_ι]; exact reduction_cover)
    reduction_preimage (G.reduction_compatible E hI) (fun _ => rfl)

end Langlands.AlgebraicGeometry.AffineCechDeRham.HodgeSummandCocycles
