import Langlands.Geometry.Analytic.AffinoidFieldCharacters
import Langlands.Geometry.Analytic.TopChartAffinoidComparison
import Langlands.Geometry.Analytic.GeneralizedAffinoid.FaithfulCharacterQuotient
import Langlands.Geometry.Analytic.SmallAffinoidSpectrum

/-! # Faithful full field points as tests of bounded pullbacks -/

noncomputable section

universe u v w uL

namespace Langlands.Analytic

open Set CategoryTheory PresentedAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {L : Type uL} [NormedField L] [NormedAlgebra K L]

namespace AffinoidAtlasPresentation.FieldPoint

variable {A B : AffinoidAtlasPresentation.{u, v, w} K}

/-- An injective chart evaluation detects the entire bounded pullback from
any common admissible target chart. -/
theorem pullback_eq_of_map_eq
    (p : FieldPoint L A) (hA : A.atlas.HasAllLocalDomains)
    (i : A.atlas.Index) (hi : p.point ∈ range (A.atlas.chart i))
    (hinj : Function.Injective (p.eval i hi))
    (f g : StrongHom A B) (j : B.atlas.Index)
    (hf : f.baseMap '' range (A.atlas.chart i) ⊆ range (B.atlas.chart j))
    (hg : g.baseMap '' range (A.atlas.chart i) ⊆ range (B.atlas.chart j))
    (heq : p.map f hA = p.map g hA) :
    f.pullback i j hf = g.pullback i j hg := by
  have hfj : (p.map f hA).point ∈ range (B.atlas.chart j) := hf ⟨p.point, hi, rfl⟩
  have hgj : (p.map g hA).point ∈ range (B.atlas.chart j) := hg ⟨p.point, hi, rfl⟩
  have h := eval_congr heq j hfj hgj
  rw [p.map_eval f hA j hfj i hi hf, p.map_eval g hA j hgj i hi hg] at h
  exact BoundedAlgHom.ext fun a => hinj (AlgHom.congr_fun h a)

/-- On global-chart sources and targets a faithful evaluation detects the
complete strong morphism from the image of one full field point. -/
theorem strongHom_eq_of_map_eq
    (p : FieldPoint L A) (hA : A.atlas.HasAllLocalDomains)
    (i : A.atlas.Index) (hi : range (A.atlas.chart i) = univ)
    (hinj : Function.Injective (p.eval i (hi.symm ▸ mem_univ _)))
    (j : B.atlas.Index) (hj : range (B.atlas.chart j) = univ)
    (f g : StrongHom A B) (heq : p.map f hA = p.map g hA) : f = g := by
  let X : TopChartPresentation.{u, v, w} K :=
    ⟨A, i, fun _ => hi.symm ▸ subset_univ _⟩
  let Y : TopChartPresentation.{u, v, w} K :=
    ⟨B, j, fun _ => hj.symm ▸ subset_univ _⟩
  apply TopChartPresentation.topPullback_injective (A := X) (B := Y)
  exact pullback_eq_of_map_eq p hA i _ hinj f g j _ _ heq

variable [CompleteSpace L]

/-- Extend a bounded global-chart character into a full field point using
the canonical domain residue comparison. -/
def ofGlobalCharacter
    (hd : DomainCompletedResidueSurjectivityStatement.{u})
    (i : A.atlas.Index) (hi : range (A.atlas.chart i) = univ)
    (χ : BoundedAlgHom K (A.atlas.algebra i) L) : FieldPoint L A :=
  (globalChartCharacterEquiv hd i hi).symm χ

@[simp]
theorem boundedEval_ofGlobalCharacter
    (hd : DomainCompletedResidueSurjectivityStatement.{u})
    (i : A.atlas.Index) (hi : range (A.atlas.chart i) = univ)
    (χ : BoundedAlgHom K (A.atlas.algebra i) L) :
    (ofGlobalCharacter hd i hi χ).boundedEval i (hi.symm ▸ mem_univ _) = χ :=
  (globalChartCharacterEquiv hd i hi).apply_symm_apply χ

/-- A faithful bounded character remains faithful as the global evaluation
of its extended full field point. -/
theorem eval_ofGlobalCharacter_injective
    (hd : DomainCompletedResidueSurjectivityStatement.{u})
    (i : A.atlas.Index) (hi : range (A.atlas.chart i) = univ)
    (χ : BoundedAlgHom K (A.atlas.algebra i) L) (hχ : Function.Injective χ) :
    Function.Injective ((ofGlobalCharacter hd i hi χ).eval i (hi.symm ▸ mem_univ _)) := by
  intro a b hab
  apply hχ
  have he := boundedEval_ofGlobalCharacter hd i hi χ
  exact (congrArg (fun c : BoundedAlgHom K (A.atlas.algebra i) L => c a) he).symm.trans
    (hab.trans (congrArg (fun c : BoundedAlgHom K (A.atlas.algebra i) L => c b) he))

end AffinoidAtlasPresentation.FieldPoint

namespace SmallAffinoidSpectrum

open AffinoidAtlasPresentation

variable (R : PresentedAffinoidAlgebra K) [Small.{v} (BanachSpectrum R)]

/-- The unchanged singleton chart, retained inside the saturated small atlas. -/
def globalIndex : (saturated.{u, v} R).presentation.atlas.Index :=
  (presentation.{u, v} R).atlas.originalSaturatedIndex PUnit.unit

theorem globalRange :
    range ((saturated.{u, v} R).presentation.atlas.chart (globalIndex R)) = univ :=
  ((presentation.{u, v} R).atlas.saturatedAtlas_original_range PUnit.unit).trans
    (spectrumHomeomorph R).surjective.range_eq

theorem globalAlgebra :
    (saturated.{u, v} R).presentation.atlas.algebra (globalIndex R) = R :=
  (presentation R).atlas.saturatedAtlas_original_algebra PUnit.unit

/-- Regard a bounded character as a character of the retained global chart. -/
def globalCharacter (χ : BoundedAlgHom K R L) :
    BoundedAlgHom K ((saturated.{u, v} R).presentation.atlas.algebra (globalIndex R)) L :=
  (globalAlgebra R).symm ▸ χ

omit [CompleteSpace K] in
private theorem transportedCharacter_injective
    {S T : PresentedAffinoidAlgebra K} (h : S = T)
    (χ : BoundedAlgHom K T L) (hχ : Function.Injective χ) :
    Function.Injective (h.symm ▸ χ) := by
  subst T
  exact hχ

theorem globalCharacter_injective (χ : BoundedAlgHom K R L)
    (hχ : Function.Injective χ) : Function.Injective (globalCharacter R χ) :=
  transportedCharacter_injective (globalAlgebra R) χ hχ

variable [CompleteSpace L]

/-- The full field point of a small saturated spectrum prescribed by a character. -/
def fieldPoint (hd : DomainCompletedResidueSurjectivityStatement.{u})
    (χ : BoundedAlgHom K R L) : FieldPoint L (saturated.{u, v} R).presentation :=
  FieldPoint.ofGlobalCharacter hd (globalIndex R) (globalRange R) (globalCharacter R χ)

theorem fieldPoint_eval_injective (hd : DomainCompletedResidueSurjectivityStatement.{u})
    (χ : BoundedAlgHom K R L) (hχ : Function.Injective χ) :
    Function.Injective ((fieldPoint R hd χ).eval (globalIndex R)
      ((globalRange R).symm ▸ mem_univ _)) :=
  FieldPoint.eval_ofGlobalCharacter_injective hd _ _ _ (globalCharacter_injective R χ hχ)

/-- One faithful full field point detects maps from a small spectrum to
any saturated target carrying a global chart. -/
theorem hom_eq_of_fieldPoint_map_eq (hd : DomainCompletedResidueSurjectivityStatement.{u})
    (χ : BoundedAlgHom K R L) (hχ : Function.Injective χ)
    {B : SaturatedAtlasPresentation.{u, v, v} K}
    (j : B.presentation.atlas.Index) (hj : range (B.presentation.atlas.chart j) = univ)
    (f g : saturated.{u, v} R ⟶ B)
    (heq : (fieldPoint R hd χ).map f (saturated R).hasAllLocalDomains =
      (fieldPoint R hd χ).map g (saturated R).hasAllLocalDomains) : f = g :=
  FieldPoint.strongHom_eq_of_map_eq _ (saturated R).hasAllLocalDomains
    (globalIndex R) (globalRange R) (fieldPoint_eval_injective R hd χ hχ) j hj f g heq

end SmallAffinoidSpectrum

namespace PresentedAffinoidAlgebra.FaithfulCharacterQuotient

open AffinoidAtlasPresentation

variable {R : PresentedAffinoidAlgebra K} [Small.{v} (BanachSpectrum R)]
  [CompleteSpace L] (χ : BoundedAlgHom K R L)

/-- The kernel quotient is an actual saturated test object in the original
small space universe. -/
def testSource : SaturatedAtlasPresentation.{u, v, v} K :=
  letI := small_spectrum.{u, v} χ
  SmallAffinoidSpectrum.saturated (algebra χ)

/-- The quotient's injective character extends to a full field-valued test point. -/
def testPoint (hd : DomainCompletedResidueSurjectivityStatement.{u}) :
    FieldPoint L (testSource.{u, v} χ).presentation :=
  letI := small_spectrum.{u, v} χ
  SmallAffinoidSpectrum.fieldPoint (algebra χ) hd (character χ)

/-- Equality at the quotient test point identifies complete strong maps
to any saturated global-chart target. -/
theorem hom_eq_of_testPoint_map_eq
    (hd : DomainCompletedResidueSurjectivityStatement.{u})
    {B : SaturatedAtlasPresentation.{u, v, v} K}
    (j : B.presentation.atlas.Index) (hj : range (B.presentation.atlas.chart j) = univ)
    (f g : testSource.{u, v} χ ⟶ B)
    (heq : (testPoint χ hd).map f (testSource χ).hasAllLocalDomains =
      (testPoint χ hd).map g (testSource χ).hasAllLocalDomains) : f = g := by
  let := small_spectrum.{u, v} χ
  exact SmallAffinoidSpectrum.hom_eq_of_fieldPoint_map_eq (algebra χ) hd
    (character χ) (character_injective χ) j hj f g heq

end PresentedAffinoidAlgebra.FaithfulCharacterQuotient

end Langlands.Analytic
