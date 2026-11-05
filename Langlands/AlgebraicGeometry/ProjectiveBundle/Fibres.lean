import Langlands.AlgebraicGeometry.ProjectiveBundle.Tautological
import Langlands.AlgebraicGeometry.Picard.LineBundleIsoLemmas
import Mathlib.AlgebraicGeometry.Fiber

/-! # Actual projective frame fibres and their degree-one bundles -/

noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open Langlands.Scheme.Modules Langlands.AlgebraicGeometry.Picard

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.ProjectiveBundle.FrameBundle

variable {S : Scheme.{u}} {M : S.Modules} {n : ℕ}
    (hM : IsLocallyFreeOfRank M (n + 1))

/-- The projective chart pulled back along an actual map into its base open. -/
def chartBaseChangeMap {T : Scheme.{u}} (U : FrameOpen M n) (b : T ⟶ U.val.toScheme) :
    RelativeProjectiveSpace T n ⟶ frameBundle M n hM :=
  RelativeProjectiveSpace.map n b ≫ chart hM U

@[reassoc (attr := simp)]
lemma chartBaseChangeMap_toBase {T : Scheme.{u}}
    (U : FrameOpen M n) (b : T ⟶ U.val.toScheme) :
    chartBaseChangeMap hM U b ≫ toBase hM =
      RelativeProjectiveSpace.toBase T n ≫ b ≫ U.val.ι := by
  simp [chartBaseChangeMap]

/-- Any change of base factoring through a frame open trivializes the actual
projective frame bundle on that base. -/
lemma isPullback_chartBaseChangeMap {T : Scheme.{u}}
    (U : FrameOpen M n) (b : T ⟶ U.val.toScheme) :
    IsPullback (RelativeProjectiveSpace.toBase T n) (chartBaseChangeMap hM U b)
      (b ≫ U.val.ι) (toBase hM) :=
  (RelativeProjectiveSpace.isPullback_map n b).paste_vert (isPullback_chart hM U)

/-- The resulting actual Cartesian pullback isomorphism. -/
def chartBaseChangeIso {T : Scheme.{u}} (U : FrameOpen M n) (b : T ⟶ U.val.toScheme) :
    RelativeProjectiveSpace T n ≅ pullback (toBase hM) (b ≫ U.val.ι) :=
  (isPullback_chartBaseChangeMap hM U b).flip.isoPullback

@[reassoc (attr := simp)]
lemma chartBaseChangeIso_hom_fst {T : Scheme.{u}}
    (U : FrameOpen M n) (b : T ⟶ U.val.toScheme) :
    (chartBaseChangeIso hM U b).hom ≫ pullback.fst _ _ =
      chartBaseChangeMap hM U b :=
  (isPullback_chartBaseChangeMap hM U b).flip.isoPullback_hom_fst

@[reassoc (attr := simp)]
lemma chartBaseChangeIso_hom_snd {T : Scheme.{u}}
    (U : FrameOpen M n) (b : T ⟶ U.val.toScheme) :
    (chartBaseChangeIso hM U b).hom ≫ pullback.snd _ _ =
      RelativeProjectiveSpace.toBase T n :=
  (isPullback_chartBaseChangeMap hM U b).flip.isoPullback_hom_snd

/-- The actual degree-one comparison on this changed projective chart. -/
def chartBaseChangeTwistIso {T : Scheme.{u}}
    (U : FrameOpen M n) (b : T ⟶ U.val.toScheme) :
    (LineBundle.pullback (chartBaseChangeMap hM U b)).obj (twistOne hM) ≅
      RelativeProjectiveSpace.twistOne T n :=
  ((LineBundle.pullbackComp (RelativeProjectiveSpace.map n b) (chart hM U)).app
      (twistOne hM)).symm ≪≫
    (LineBundle.pullback (RelativeProjectiveSpace.map n b)).mapIso
      (twistOnePullbackIso hM U) ≪≫
    RelativeProjectiveSpace.twistOnePullbackIso n b

/-- The original residue-field point factors through every open containing it. -/
def residueBaseLift (U : FrameOpen M n) (s : S) (hs : s ∈ U.val) :
    Spec (S.residueField s) ⟶ U.val.toScheme :=
  IsOpenImmersion.lift U.val.ι (S.fromSpecResidueField s) (by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    change S.fromSpecResidueField s z ∈ U.val
    rw [Scheme.fromSpecResidueField_apply]
    exact hs)

@[reassoc (attr := simp)]
lemma residueBaseLift_ι (U : FrameOpen M n) (s : S) (hs : s ∈ U.val) :
    residueBaseLift U s hs ≫ U.val.ι = S.fromSpecResidueField s :=
  IsOpenImmersion.lift_fac _ _ _

/-- The actual map of projective spaces into the global frame bundle over a
residue-field point, expressed in a frame near that point. -/
def fibreChartMap (U : FrameOpen M n) (s : S) (hs : s ∈ U.val) :
    RelativeProjectiveSpace (Spec (S.residueField s)) n ⟶ frameBundle M n hM :=
  chartBaseChangeMap hM U (residueBaseLift U s hs)

/-- The residue-field projective space is the actual fibre, not merely a
neighbourhood or an open subscheme of it. -/
lemma isPullback_fibreChartMap (U : FrameOpen M n) (s : S) (hs : s ∈ U.val) :
    IsPullback (RelativeProjectiveSpace.toBase (Spec (S.residueField s)) n)
      (fibreChartMap hM U s hs) (S.fromSpecResidueField s) (toBase hM) := by
  simpa only [fibreChartMap, residueBaseLift_ι] using
    isPullback_chartBaseChangeMap hM U (residueBaseLift U s hs)

/-- A chosen nearby frame identifies the full actual fibre with projective
space over the original residue field. -/
def fibreChartIso (U : FrameOpen M n) (s : S) (hs : s ∈ U.val) :
    RelativeProjectiveSpace (Spec (S.residueField s)) n ≅ (toBase hM).fiber s :=
  (isPullback_fibreChartMap hM U s hs).flip.isoPullback

@[reassoc (attr := simp)]
lemma fibreChartIso_hom_fiberι (U : FrameOpen M n) (s : S) (hs : s ∈ U.val) :
    (fibreChartIso hM U s hs).hom ≫ (toBase hM).fiberι s = fibreChartMap hM U s hs :=
  (isPullback_fibreChartMap hM U s hs).flip.isoPullback_hom_fst

@[reassoc (attr := simp)]
lemma fibreChartIso_hom_toResidueField (U : FrameOpen M n) (s : S) (hs : s ∈ U.val) :
    (fibreChartIso hM U s hs).hom ≫ (toBase hM).fiberToSpecResidueField s =
      RelativeProjectiveSpace.toBase (Spec (S.residueField s)) n :=
  (isPullback_fibreChartMap hM U s hs).flip.isoPullback_hom_snd

/-- Under the actual fibre isomorphism, the restriction of the global
degree-one line bundle is the usual relative degree-one line bundle. -/
def fibreChartTwistIso (U : FrameOpen M n) (s : S) (hs : s ∈ U.val) :
    (LineBundle.pullback (fibreChartIso hM U s hs).hom).obj
        ((LineBundle.pullback ((toBase hM).fiberι s)).obj (twistOne hM)) ≅
      RelativeProjectiveSpace.twistOne (Spec (S.residueField s)) n :=
  LineBundle.pullbackCompEqIso _ _ (fibreChartIso_hom_fiberι hM U s hs) _ ≪≫
    chartBaseChangeTwistIso hM U (residueBaseLift U s hs)

/-- A frame open near the given point, supplied by fixed-rank local freeness. -/
def fibreFrameOpen (s : S) : FrameOpen M n :=
  (exists_frameOpen M n hM s).choose

lemma mem_fibreFrameOpen (s : S) : s ∈ (fibreFrameOpen hM s).val :=
  (exists_frameOpen M n hM s).choose_spec

/-- Each full fibre has an actual projective-space isomorphism, with no
additional choice of local frame as a premise. -/
def fibreProjectiveIso (s : S) :
    RelativeProjectiveSpace (Spec (S.residueField s)) n ≅ (toBase hM).fiber s :=
  fibreChartIso hM (fibreFrameOpen hM s) s (mem_fibreFrameOpen hM s)

/-- The chosen whole-fibre projective isomorphism is over the original residue
field spectrum. -/
@[reassoc (attr := simp)]
lemma fibreProjectiveIso_hom_toResidueField (s : S) :
    (fibreProjectiveIso hM s).hom ≫ (toBase hM).fiberToSpecResidueField s =
      RelativeProjectiveSpace.toBase (Spec (S.residueField s)) n :=
  fibreChartIso_hom_toResidueField hM _ _ _

/-- The chosen whole-fibre isomorphism preserves the actual degree-one bundle. -/
def fibreProjectiveTwistIso (s : S) :
    (LineBundle.pullback (fibreProjectiveIso hM s).hom).obj
        ((LineBundle.pullback ((toBase hM).fiberι s)).obj (twistOne hM)) ≅
      RelativeProjectiveSpace.twistOne (Spec (S.residueField s)) n :=
  fibreChartTwistIso hM _ _ _

end Langlands.AlgebraicGeometry.ProjectiveBundle.FrameBundle
