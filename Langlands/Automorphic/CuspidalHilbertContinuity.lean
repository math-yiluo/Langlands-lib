import Langlands.Automorphic.CuspidalAdelicHilbertAction
import Langlands.Representation.Hecke.ActionIntegrand

/-! # Strong continuity of the actual Hilbert realization -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 20000
set_option Elab.async false

namespace Langlands.UnitaryEmbeddingFamily
universe uA uV uE uH

/-- Weak scalar continuity and constant norm imply strong continuity in a
complex inner-product space. -/
theorem continuous_of_inner_continuous_const_norm
    {A : Type uA} [TopologicalSpace A]
    {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (f : A → H) (hnorm : ∀ a c, ‖f a‖ = ‖f c‖)
    (hw : ∀ w : H, Continuous (fun a => Inner.inner ℂ w (f a))) :
    Continuous f := by
  apply continuous_iff_continuousAt.mpr
  intro a
  have heq (c : A) : ‖f c - f a‖ =
      Real.sqrt (‖f a‖ ^ 2 - 2 * (Inner.inner ℂ (f a) (f c)).re + ‖f a‖ ^ 2) := by
    have hs := norm_sub_sq (𝕜 := ℂ) (f a) (f c)
    rw [norm_sub_rev, hnorm c a] at hs
    exact (Real.sqrt_sq (norm_nonneg (f c - f a))).symm.trans (congrArg Real.sqrt hs)
  have hc : Continuous (fun c : A => ‖f c - f a‖) := by
    have hr : Continuous (fun c : A =>
        Real.sqrt (‖f a‖ ^ 2 - 2 * (Inner.inner ℂ (f a) (f c)).re + ‖f a‖ ^ 2)) :=
      ((continuous_const.sub
      (continuous_const.mul (Complex.continuous_re.comp (hw (f a))))).add
        continuous_const).sqrt
    exact hr.congr (fun c => (heq c).symm)
  apply tendsto_iff_dist_tendsto_zero.mpr
  simpa only [dist_eq_norm, sub_self, norm_zero] using hc.tendsto a

/-- Joint continuity of an isometric family follows from weak scalar
continuity on a prescribed dense carrier. -/
theorem continuous_family_of_dense_inner_continuous
    {A : Type uA} [TopologicalSpace A] {V : Type uV}
    {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (j : V → E) (hj : DenseRange j) (J : A → E →ₗᵢ[ℂ] H)
    (hw : ∀ v (w : H), Continuous (fun a => Inner.inner ℂ w (J a (j v)))) :
    Continuous (fun p : A × E => J p.1 p.2) := by
  apply continuous_prod_of_dense_continuous_lipschitzWith' _ 1 hj
    (fun a => (J a).isometry.lipschitzWith)
  rintro _ ⟨v, rfl⟩
  exact continuous_of_inner_continuous_const_norm _
    (fun a c => ((J a).norm_map (j v)).trans ((J c).norm_map (j v)).symm) (hw v)

/-- A continuous family can be evaluated at a locally constant parameter,
without imposing any topology on that parameter's carrier. -/
theorem continuous_locallyConstant_parameter
    {A : Type uA} [TopologicalSpace A] {B : Type*} [TopologicalSpace B]
    {V : Type uV} {H : Type uH} [TopologicalSpace H]
    (p : A → B) (hp : Continuous p) (v : A → V) (hv : IsLocallyConstant v)
    (k : B → V → H) (hk : ∀ w, Continuous (fun b => k b w)) :
    Continuous (fun a => k (p a) (v a)) := by
  apply continuous_iff_continuousAt.mpr
  intro a
  apply ((hk (v a)).comp hp).continuousAt.congr_of_eventuallyEq
  exact (hv.eventually_eq a).mono fun c hc => congrArg (k (p c)) hc

variable {A : Type uA} [TopologicalSpace A] {V : Type uV}
  {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Joint norm continuity of the supplied embedding family. -/
def JointlyContinuousEmbeddings (J : A → E →ₗᵢ[ℂ] H) : Prop :=
  Continuous (fun p : A × E => J p.1 p.2)

/-- Algebraic target values suffice for the weak-continuity test. -/
theorem jointlyContinuousEmbeddings_of_dense_values
    (j : V → E) (hj : DenseRange j) (J : A → E →ₗᵢ[ℂ] H)
    (k : A → V → H) (hvalue : ∀ a v, J a (j v) = k a v)
    (hw : ∀ v (w : H), Continuous (fun a => Inner.inner ℂ w (k a v))) :
    JointlyContinuousEmbeddings J :=
  continuous_family_of_dense_inner_continuous j hj J fun v w =>
    (hw v w).congr fun a => (congrArg (Inner.inner ℂ w) (hvalue a v)).symm

variable {G : Type*} [Group G] [TopologicalSpace G]

/-- Joint norm continuity of a bounded representation. -/
def JointlyContinuousRepresentation (U : G →* (E →L[ℂ] E)) : Prop :=
  Continuous (fun p : G × E => U p.1 p.2)

/-- The identity isometry reflects the joint continuity of the given target family. -/
theorem jointlyContinuousRepresentation (B : Langlands.UnitaryEmbeddingFamily G E H)
    (hB : JointlyContinuousEmbeddings B.embedding) :
    JointlyContinuousRepresentation B.toContinuousLinearRepresentation :=
  B.continuous_action fun _x => hB.comp (continuous_id.prodMk continuous_const)

end Langlands.UnitaryEmbeddingFamily

namespace Langlands.Automorphic
open Langlands.Global MeasureTheory
open scoped NumberField
universe u
variable {F : Type u} [Field F] [NumberField F]
  [CompactSpace (AdeleQuotient F)] {r : ℕ}

local instance continuityRationalGroup (n : ℕ) :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance continuityContinuousGroup (n : ℕ) :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance continuitySmoothGroup (n : ℕ) :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance continuityFormsGroup (n : ℕ) :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance continuityStableGroup (n : ℕ) :
    AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _
local instance continuitySpaceGroup (S : OperatorRealization F (r + 1)) :
    AddCommGroup S.Space := Submodule.addCommGroup _

namespace OperatorDeterminantSlice
variable (T : CuspidalOperatorRealization F r)

/-- The retained genuine smooth-coefficient premise supplies weak continuity
of every original vector's actual infinite orbit. -/
theorem continuous_inner_translatedToL2_infinite
    (hcoeff : CuspidalHilbertOrbitCoefficientStatement.{u})
    (hT : Langlands.ClassField.Global.RelativeWeilGroup.HasUnitaryCentralCharacter T)
    (f : T.Space) (w : CuspidalHilbertOrbitCoefficient.BandHilbertSpace F r) :
    Continuous (fun g : InfiniteAdelicGL F (r + 1) =>
      Inner.inner ℂ w (translatedToL2 T.realization T.cuspidal
        (AdelicGL.ofInfinite F (r + 1) g) f)) := by
  refine Exists.elim (hcoeff F r T hT w).2 fun C hC => ?_
  exact (ArchimedeanGL.continuous F (r + 1) (C f)).congr fun g =>
    (hC.1 f g).trans (inner_translatedToL2_left T w
      (AdelicGL.ofInfinite F (r + 1) g) f).symm

/-- Finite source orbits are locally constant, so weak continuity holds
for the full actual adelic translated source orbit. -/
theorem continuous_inner_translatedToL2
    (hcoeff : CuspidalHilbertOrbitCoefficientStatement.{u})
    (hT : Langlands.ClassField.Global.RelativeWeilGroup.HasUnitaryCentralCharacter T)
    (f : T.Space) (w : CuspidalHilbertOrbitCoefficient.BandHilbertSpace F r) :
    Continuous (fun a : AdelicGL F (r + 1) =>
      Inner.inner ℂ w (translatedToL2 T.realization T.cuspidal a f)) := by
  have hc := Langlands.UnitaryEmbeddingFamily.continuous_locallyConstant_parameter
    (AdelicGL.infinite F (r + 1)) (AdelicGL.infinite F (r + 1)).continuous
    (fun a => T.realization.finiteRepresentation (AdelicGL.finite F (r + 1) a) f)
    ((Langlands.Hecke.orbitMap_locallyConstant T.realization.finiteRepresentation
      (T.realization.finiteRepresentation_isSmooth f)).comp_continuous
        (AdelicGL.finite F (r + 1)).continuous)
    (fun g v => Inner.inner ℂ w (translatedToL2 T.realization T.cuspidal
      (AdelicGL.ofInfinite F (r + 1) g) v))
    (fun v => continuous_inner_translatedToL2_infinite T hcoeff hT v w)
  exact hc.congr fun a => (congrArg (Inner.inner ℂ w)
    (translatedToL2_finite_factor T.realization T.cuspidal a f)).symm

variable (hcoeff : CuspidalHilbertOrbitCoefficientStatement.{u})
  (χ : NumberField.IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ)
  (hχ : ∀ z, ‖(χ z : ℂ)‖ = 1) (hTχ : T.realization.HasCentralCharacter χ)
  (b : T.realization.UnitaryForm)
  (hb : ∀ f g : T.Space, b.inner f g =
    ∫ q, Inner.inner ℂ (toQuotient F (r + 1) T.realization f q)
      (toQuotient F (r + 1) T.realization g q)
      ∂(quotientHaarMeasure F (r + 1)).restrict (band F (r + 1)))

include hcoeff in
/-- The prescribed actual translated embeddings are jointly norm-continuous
on the full adelic group and the same source completion. -/
theorem jointlyContinuous_translatedHilbertEmbedding :
    Langlands.UnitaryEmbeddingFamily.JointlyContinuousEmbeddings
      (translatedHilbertEmbedding T.realization T.cuspidal (Nat.succ_ne_zero r)
        χ hχ hTχ b hb) :=
  Langlands.UnitaryEmbeddingFamily.jointlyContinuousEmbeddings_of_dense_values
    b.finiteForm.toHilbert b.finiteForm.denseRange_toHilbert
    (translatedHilbertEmbedding T.realization T.cuspidal (Nat.succ_ne_zero r)
      χ hχ hTχ b hb)
    (fun a v => translatedToL2 T.realization T.cuspidal a v)
    (translatedHilbertEmbedding_toHilbert T.realization T.cuspidal (Nat.succ_ne_zero r)
      χ hχ hTχ b hb)
    (continuous_inner_translatedToL2 T hcoeff ⟨χ, hχ, hTχ⟩)

/-- The conditional actual full adelic representation is jointly continuous. -/
theorem jointlyContinuous_adelicHilbertRepresentation :
    Langlands.UnitaryEmbeddingFamily.JointlyContinuousRepresentation
      (adelicHilbertRepresentation T hcoeff χ hχ hTχ b hb) :=
  Langlands.UnitaryEmbeddingFamily.jointlyContinuousRepresentation
    (adelicHilbertEmbeddingFamily T hcoeff χ hχ hTχ b hb)
    (jointlyContinuous_translatedHilbertEmbedding T hcoeff χ hχ hTχ b hb)

end OperatorDeterminantSlice

/-- Joint continuity of the actual constructed action, retaining the coefficient
premise and the prescribed band form. -/
def CuspidalAdelicHilbertContinuityStatement : Prop :=
  ∀ (hcoeff : CuspidalHilbertOrbitCoefficientStatement.{u})
    (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (r : ℕ) (T : CuspidalOperatorRealization F r)
    (χ : NumberField.IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ)
    (hχ : ∀ z, ‖(χ z : ℂ)‖ = 1) (hTχ : T.realization.HasCentralCharacter χ)
    (b : T.realization.UnitaryForm)
    (hb : ∀ f g : T.Space, b.inner f g =
      ∫ q, Inner.inner ℂ (OperatorDeterminantSlice.toQuotient F (r + 1) T.realization f q)
        (OperatorDeterminantSlice.toQuotient F (r + 1) T.realization g q)
        ∂(OperatorDeterminantSlice.quotientHaarMeasure F (r + 1)).restrict
          (OperatorDeterminantSlice.band F (r + 1))),
    Langlands.UnitaryEmbeddingFamily.JointlyContinuousRepresentation
      (OperatorDeterminantSlice.adelicHilbertRepresentation T hcoeff χ hχ hTχ b hb)

theorem cuspidalAdelicHilbertContinuity : CuspidalAdelicHilbertContinuityStatement.{u} := by
  intro hcoeff F _ _ _ r T χ hχ hTχ b hb
  exact OperatorDeterminantSlice.jointlyContinuous_adelicHilbertRepresentation
    T hcoeff χ hχ hTχ b hb

end Langlands.Automorphic
