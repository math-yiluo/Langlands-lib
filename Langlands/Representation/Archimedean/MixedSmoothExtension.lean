import Langlands.HarmonicAnalysis.HarishChandraSchwartz.SchwartzActionFamily
import Langlands.Automorphic.CuspidalFixedSmoothAgreement
import Langlands.Representation.Archimedean.MixedSmoothFunctional

/-! # Continuous finite-level extensions and finite translation -/

noncomputable section
set_option autoImplicit false

open scoped Manifold ContDiff

namespace Langlands.Archimedean.MixedSmooth

open Langlands.HarishChandraSchwartz SmoothInvariantSubspace

universe uA uG uL uE uV

variable {A : Type uA} [NormedAddCommGroup A] [NormedSpace ℝ A]
  {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace A G] [LieGroup 𝓘(ℝ, A) ∞ G]
  {L : Type uL} [Group L] [TopologicalSpace L]
  {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  {V₀ : Type uV} [AddCommGroup V₀] [Module ℂ V₀] (ρ : Representation ℂ L V₀)
  (σ : L →* (E →L[ℂ] E)) (π : G →* (E →L[ℂ] E))
  (hcomm : ∀ g l x, π g (σ l x) = σ l (π g x))

local notation "I" => 𝓘(ℝ, A)
local notation "K" => CompactOpenSubgroup L
local notation "V∞" => Langlands.Archimedean.smoothVectors I π
local notation "W" => Vectors (A := A) σ π hcomm
local notation "D∞" => DerivativeSmoothVectors I π

variable (j : V₀ →ₗ[ℂ] Langlands.Archimedean.smoothVectors 𝓘(ℝ, A) π)
  (ℓ : L → V₀ →ₗ[ℂ] ℂ)

/-- Extensions of the original evaluations with continuity and agreement at
each specified finite level. -/
structure EvaluationExtensions where
  level : L → K → V∞ →ₗ[ℂ] ℂ
  continuous_level (d : L) (J : K) : IsContinuousOnSmoothVectors I π (level d J)
  agrees (d : L) (J : K) (v : V₀) (hv : v ∈ Langlands.fixedVectors ρ J.toSubgroup) :
    level d J (j v) = ℓ d v

variable (exts : EvaluationExtensions ρ π j ℓ)

private abbrev smoothImageAtLevel (J : K)
    (v : Langlands.fixedVectors ρ J.toSubgroup) : V∞ :=
  j v.val

/-- Density of the original smooth images at the compact open levels. -/
def DenseFixedImages : Prop :=
  ∀ J : K, Dense (fixedSmoothImageOf (A := A) σ J.toSubgroup π (smoothImageAtLevel ρ π j J))

/-- Two continuous functionals agreeing on the dense fixed image give the
same value on every genuine smooth vector fixed at that level. -/
theorem continuousFunctional_eq_of_fixedImage (J : K)
    (hd : Dense (fixedSmoothImageOf (A := A) σ J.toSubgroup π (smoothImageAtLevel ρ π j J)))
    (f g : V∞ →ₗ[ℂ] ℂ) (hf : IsContinuousOnSmoothVectors I π f)
    (hg : IsContinuousOnSmoothVectors I π g)
    (h : ∀ v : Langlands.fixedVectors ρ J.toSubgroup, f (j v.val) = g (j v.val))
    (w : V∞) (hw : w.val ∈ fixedSubspace σ J.toSubgroup) : f w = g w := by
  let e := DerivativeSmoothVectors.toSmooth I π
  let x := e.symm w
  have hx : x ∈ ambientFixedSmoothSubspace σ J.toSubgroup π I :=
    (mem_ambientSmoothSubspace π (fixedSubspace σ J.toSubgroup) I x).mpr
      (by simpa only [x, e, LinearEquiv.apply_symm_apply] using hw)
  have he := eqOn_fixedSmoothImageOf σ J.toSubgroup π (smoothImageAtLevel ρ π j J) hd
    (f := fun z : D∞ => f (e z)) (g := fun z : D∞ => g (e z))
    (continuous_of_isContinuousOnSmoothVectors I π f hf)
    (continuous_of_isContinuousOnSmoothVectors I π g hg)
    (by simpa only [e, LinearEquiv.apply_symm_apply] using h) ⟨x, hx⟩
  simpa only [x, LinearEquiv.apply_symm_apply] using he

variable [NonarchimedeanGroup L] (hd : DenseFixedImages ρ σ π j)

omit [LieGroup 𝓘(ℝ, A) ∞ G] in
/-- A finite intertwiner from a smooth original representation lands in
the mixed smooth part, with the same genuine smooth values. -/
def sourceToMixed (hρ : Langlands.IsSmooth ρ)
    (hj : ∀ a v, finiteOnSmooth σ π hcomm a (j v) = j (ρ a v)) :
    ρ.IntertwiningMap (finiteRepresentation (A := A) σ π hcomm) :=
  Langlands.smoothLift hρ
    (j.intertwiningMap_of_isIntertwiningMap ρ (finiteOnSmooth σ π hcomm) fun a v => (hj a v).symm)

omit [LieGroup 𝓘(ℝ, A) ∞ G] in
@[simp]
theorem sourceToMixed_val (hρ : Langlands.IsSmooth ρ)
    (hj : ∀ a v, finiteOnSmooth σ π hcomm a (j v) = j (ρ a v)) (v : V₀) :
    (sourceToMixed ρ σ π hcomm j hρ hj v).val = j v :=
  rfl

include hd in
/-- Independent extensions agree on vectors fixed at both levels. -/
theorem compatibleLevels (d : L) : CompatibleLevels σ π (exts.level d) := by
  intro J J' w hJ hJ'
  let B := J.inf J'
  have hcompare (C : K) (hBC : B.toSubgroup ≤ C.toSubgroup)
      (hw : w.val ∈ fixedSubspace σ C.toSubgroup) : exts.level d B w = exts.level d C w := by
    refine continuousFunctional_eq_of_fixedImage ρ σ π j C (hd C)
      (exts.level d B) (exts.level d C) (exts.continuous_level d B) (exts.continuous_level d C) ?_ w hw
    intro v
    exact (exts.agrees d B v.val (fun k => v.property ⟨k.val, hBC k.property⟩)).trans
      (exts.agrees d C v.val v.property).symm
  exact (hcompare J (CompactOpenSubgroup.inf_le_left J J') hJ).symm.trans
    (hcompare J' (CompactOpenSubgroup.inf_le_right J J') hJ')

variable [LocallyCompactSpace L]

/-- For each compact open fixed level the mixed functional is the restriction
of a derivative-continuous functional on the genuine smooth vectors. -/
def IsContinuousAtEachLevel (P : W →ₗ[ℂ] ℂ) : Prop :=
  ∀ J : K, ∃ f : V∞ →ₗ[ℂ] ℂ, IsContinuousOnSmoothVectors I π f ∧
    ∀ w : W, w.val.val ∈ fixedSubspace σ J.toSubgroup → P w = f w.val

/-- The prescribed evaluation extends to the whole mixed smooth space. -/
def extendedEvaluation (d : L) : W →ₗ[ℂ] ℂ :=
  glueFunctional σ π hcomm (exts.level d) (compatibleLevels ρ σ π j ℓ exts hd d)

/-- At every compact open fixed level, the extended evaluation is the
given continuous functional evaluated on the same smooth vector. -/
theorem extendedEvaluation_at_level (d : L) (w : W) (J : K)
    (hw : w.val.val ∈ fixedSubspace σ J.toSubgroup) :
    extendedEvaluation ρ σ π hcomm j ℓ exts hd d w = exts.level d J w.val :=
  glueFunctional_eq_of_fixed σ π hcomm (exts.level d)
    (compatibleLevels ρ σ π j ℓ exts hd d) w J hw

/-- The mixed evaluation retains derivative continuity at each level. -/
theorem isContinuousAtEachLevel_extendedEvaluation (d : L) :
    IsContinuousAtEachLevel σ π hcomm (extendedEvaluation ρ σ π hcomm j ℓ exts hd d) :=
  fun J => ⟨exts.level d J, exts.continuous_level d J,
    fun w hw => extendedEvaluation_at_level ρ σ π hcomm j ℓ exts hd d w J hw⟩

/-- A finite translation of an extended evaluation agrees with the
extension at the translated argument, provided the original data obey
the exact finite covariance identities. -/
theorem extendedEvaluation_finite
    (hj : ∀ a v, finiteOnSmooth σ π hcomm a (j v) = j (ρ a v))
    (hℓ : ∀ d a v, ℓ d (ρ a v) = ℓ (d * a) v)
    (d a : L) (w : W) :
    extendedEvaluation ρ σ π hcomm j ℓ exts hd d (finiteRepresentation σ π hcomm a w) =
      extendedEvaluation ρ σ π hcomm j ℓ exts hd (d * a) w := by
  obtain ⟨J, hJ⟩ := exists_compactLevel σ π hcomm w
  have hw := finiteOnSmooth_fixed_conj σ π hcomm a J w.val hJ
  rw [extendedEvaluation_at_level ρ σ π hcomm j ℓ exts hd d _ (J.conj a) hw,
    extendedEvaluation_at_level ρ σ π hcomm j ℓ exts hd (d * a) w J hJ,
    finiteRepresentation_val]
  let P := (exts.level d (J.conj a)).comp (finiteOnSmooth σ π hcomm a)
  have hP : IsContinuousOnSmoothVectors I π P :=
    SmoothIntertwiner.isContinuousOnSmoothVectors_comp I π π (σ a)
      (fun g x => (hcomm g a x).symm) _ (exts.continuous_level d (J.conj a))
  refine continuousFunctional_eq_of_fixedImage ρ σ π j J (hd J) P
    (exts.level (d * a) J) hP (exts.continuous_level (d * a) J) ?_ w.val hJ
  intro v
  change exts.level d (J.conj a) (finiteOnSmooth σ π hcomm a (j v.val)) =
    exts.level (d * a) J (j v.val)
  rw [hj, exts.agrees _ _ _ (rho_mem_fixedVectors_conj (H := J) v.property a),
    hℓ, exts.agrees _ _ _ v.property]

/-- A formula for the translated evaluations of original fixed vectors
computes the identity evaluation on every mixed translate of an original
vector. -/
theorem extendedEvaluation_translate_source
    (hρ : Langlands.IsSmooth ρ)
    (hj : ∀ a v, finiteOnSmooth σ π hcomm a (j v) = j (ρ a v))
    (hℓ : ∀ d a v, ℓ d (ρ a v) = ℓ (d * a) v)
    (values : G → L → V₀ → ℂ)
    (hvalue : ∀ a d (J : K) v, v ∈ Langlands.fixedVectors ρ J.toSubgroup →
      exts.level d J (smoothRepresentation I π a (j v)) = values a d v)
    (a : G) (d : L) (v : V₀) :
    extendedEvaluation ρ σ π hcomm j ℓ exts hd 1
      (finiteRepresentation σ π hcomm d
        (archimedeanRepresentation σ π hcomm a (sourceToMixed ρ σ π hcomm j hρ hj v))) =
      values a d v := by
  let x := sourceToMixed ρ σ π hcomm j hρ hj v
  have hx : x.val = j v := sourceToMixed_val ρ σ π hcomm j hρ hj v
  obtain ⟨J₀, hJ₀⟩ := hρ v
  obtain ⟨K₀, hK₀, hKJ⟩ := openSubgroupContainsCompactOpen L J₀
  let J : K := ⟨K₀, hK₀⟩
  have hv : v ∈ Langlands.fixedVectors ρ J.toSubgroup :=
    fun k => hJ₀ ⟨k.val, hKJ k.property⟩
  have hJ : x.val.val ∈ fixedSubspace σ J.toSubgroup := by
    apply (mem_fixedVectors_finiteOnSmooth σ π hcomm J.toSubgroup x.val).mp
    intro k
    have hkv : ρ k.val v = v := hv k
    change finiteOnSmooth σ π hcomm k.val x.val = x.val
    rw [hx, hj, hkv]
  have ha := smoothRepresentation_fixed σ π hcomm a J.toSubgroup x.val hJ
  change extendedEvaluation ρ σ π hcomm j ℓ exts hd 1
    (finiteRepresentation σ π hcomm d (archimedeanRepresentation σ π hcomm a x)) = _
  rw [extendedEvaluation_finite ρ σ π hcomm j ℓ exts hd hj hℓ, one_mul,
    extendedEvaluation_at_level ρ σ π hcomm j ℓ exts hd d _ J ha, archimedeanRepresentation_val, hx]
  exact hvalue a d J v hv

/-- A scalar covariance identity on the original fixed vectors at every
level extends to the glued identity functional. -/
theorem extendedEvaluation_covariance_of_fixedImages
    (hj : ∀ a v, finiteOnSmooth σ π hcomm a (j v) = j (ρ a v))
    (hℓ : ∀ d a v, ℓ d (ρ a v) = ℓ (d * a) v)
    (a : G) (d : L) (c : ℂ)
    (hcov : ∀ (J : K) (v : Langlands.fixedVectors ρ J.toSubgroup),
      exts.level d J (smoothRepresentation I π a (j v.val)) = c * exts.level 1 J (j v.val))
    (w : W) :
    extendedEvaluation ρ σ π hcomm j ℓ exts hd 1
      (finiteRepresentation σ π hcomm d (archimedeanRepresentation σ π hcomm a w)) =
      c * extendedEvaluation ρ σ π hcomm j ℓ exts hd 1 w := by
  obtain ⟨J, hJ⟩ := exists_compactLevel σ π hcomm w
  have ha := smoothRepresentation_fixed σ π hcomm a J.toSubgroup w.val hJ
  rw [extendedEvaluation_finite ρ σ π hcomm j ℓ exts hd hj hℓ, one_mul,
    extendedEvaluation_at_level ρ σ π hcomm j ℓ exts hd d _ J ha,
    archimedeanRepresentation_val, extendedEvaluation_at_level ρ σ π hcomm j ℓ exts hd 1 w J hJ]
  let p := (exts.level d J).comp (smoothRepresentation I π a)
  let q : V∞ →ₗ[ℂ] ℂ := c • exts.level 1 J
  have hp : IsContinuousOnSmoothVectors I π p :=
    SmoothAction.isContinuousOnSmoothVectors_comp I π a _ (exts.continuous_level d J)
  have hq : IsContinuousOnSmoothVectors I π q :=
    isContinuousOnSmoothVectors_of_continuous I π q
      (continuous_const.mul (continuous_of_isContinuousOnSmoothVectors I π _ (exts.continuous_level 1 J)))
  exact continuousFunctional_eq_of_fixedImage ρ σ π j J (hd J) p q hp hq (hcov J) w.val hJ

end Langlands.Archimedean.MixedSmooth
