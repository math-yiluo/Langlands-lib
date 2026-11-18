import Langlands.Automorphic.CuspidalTranslatedHilbertEmbedding
import Langlands.Representation.Unitary.EmbeddingFamily

/-! # The genuine translated Gram identity for the actual band embeddings -/

noncomputable section
universe u
set_option autoImplicit false
set_option maxHeartbeats 20000
set_option Elab.async false

namespace Langlands.UnitaryEmbeddingFamily

universe uG uV uE uH

/-- A translated Gram identity can be checked on any prescribed dense carrier. -/
theorem gram_of_dense
    {G : Type uG} [Group G] {V : Type uV}
    {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (j : V → E) (hj : DenseRange j) (J : G → E →ₗᵢ[ℂ] H)
    (hgram : ∀ g h v w, Inner.inner ℂ (J g (j v)) (J (g * h) (j w)) =
      Inner.inner ℂ (J 1 (j v)) (J h (j w))) (g h : G) (x y : E) :
    Inner.inner ℂ (J g x) (J (g * h) y) = Inner.inner ℂ (J 1 x) (J h y) := by
  refine hj.induction_on₂
    (p := fun x y : E => Inner.inner ℂ (J g x) (J (g * h) y) =
      Inner.inner ℂ (J 1 x) (J h y)) ?_ (hgram g h) x y
  exact isClosed_eq
    (((J g).continuous.comp continuous_fst).inner ((J (g * h)).continuous.comp continuous_snd))
    (((J 1).continuous.comp continuous_fst).inner ((J h).continuous.comp continuous_snd))

end Langlands.UnitaryEmbeddingFamily

namespace Langlands.Automorphic

open Langlands.Global MeasureTheory
open scoped NumberField

variable {F : Type u} [Field F] [NumberField F] {n : ℕ}

local instance actionRationalGroup : AddCommGroup (RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance actionContinuousGroup : AddCommGroup (ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance actionSmoothGroup : AddCommGroup (FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance actionFormsGroup : AddCommGroup (AutomorphicForms F n) :=
  Submodule.addCommGroup _
local instance actionStableGroup : AddCommGroup (StableAutomorphicFunctions F n) :=
  Submodule.addCommGroup _
local instance actionSpaceGroup (S : OperatorRealization F n) : AddCommGroup S.Space :=
  Submodule.addCommGroup _

namespace OperatorDeterminantSlice

local instance actionIsAffine :
    _root_.AlgebraicGeometry.IsAffine (matrixGroupScheme F n).X.left :=
  Langlands.GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of F)
local instance actionSmooth :
    _root_.AlgebraicGeometry.Smooth (matrixGroupScheme F n).X.hom :=
  Langlands.GroupScheme.GeneralLinear.smoothStatement (Fin n) (CommRingCat.of F)

/-- Actual right translation composes in the original matrix multiplication order. -/
theorem translate_mul_apply (a b : AdelicGL F n) (q : Quotient F n) :
    translate F n (a * b) q = translate F n b (translate F n a q) := by
  obtain ⟨x, rfl⟩ := point_surjective F n q
  simp only [translate_point, mul_assoc]

variable (S : OperatorRealization F n)

/-- The common unitary central phase cancels in an actual translated pair. -/
theorem inner_translate_pair_central (S : OperatorRealization F n)
    (χ : NumberField.IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ)
    (hχ : ∀ z, ‖(χ z : ℂ)‖ = 1) (hSχ : S.HasCentralCharacter χ)
    (z : Ideles F) (a b c : AdelicGL F n) (f g : S.Space) (q : Quotient F n) :
    Inner.inner ℂ
      (toQuotient F n S f (translate F n ((AdelicGL.scalar F n z * c) * a) q))
      (toQuotient F n S g (translate F n ((AdelicGL.scalar F n z * c) * b) q)) =
      Inner.inner ℂ (toQuotient F n S f (translate F n (c * a) q))
        (toQuotient F n S g (translate F n (c * b) q)) := by
  have hf := (congrArg (fun t : AdelicGL F n => toQuotient F n S f (translate F n t q))
    (mul_assoc (AdelicGL.scalar F n z) c a)).trans
      (toQuotient_central F n S χ hSχ z f (c * a) q)
  have hg := (congrArg (fun t : AdelicGL F n => toQuotient F n S g (translate F n t q))
    (mul_assoc (AdelicGL.scalar F n z) c b)).trans
      (toQuotient_central F n S χ hSχ z g (c * b) q)
  exact (congrArg₂ (Inner.inner ℂ) hf hg).trans (inner_phase _ _ _ (hχ _))

/-- Simultaneous insertion of an arbitrary adelic element preserves the Gram
pairing of two separately translated source functions. -/
theorem integral_inner_translate_pair (hn : n ≠ 0)
    (χ : NumberField.IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ)
    (hχ : ∀ z, ‖(χ z : ℂ)‖ = 1) (hSχ : S.HasCentralCharacter χ)
    (a b c : AdelicGL F n) (f g : S.Space) :
    (∫ q, Inner.inner ℂ (toQuotient F n S f (translate F n (c * a) q))
      (toQuotient F n S g (translate F n (c * b) q))
      ∂(quotientHaarMeasure F n).restrict (band F n)) =
    (∫ q, Inner.inner ℂ (toQuotient F n S f (translate F n a q))
      (toQuotient F n S g (translate F n b q))
      ∂(quotientHaarMeasure F n).restrict (band F n)) := by
  refine Exists.elim (exists_normalized_rightTranslate F n hn c) fun z hz => ?_
  let d := AdelicGL.scalar F n z * c
  have hd := measurePreserving_translate_band F n (quotientHaarMeasure F n) d hz
    (measurePreserving_translate F n d)
  have hp (q : Quotient F n) :
      Inner.inner ℂ (toQuotient F n S f (translate F n (d * a) q))
        (toQuotient F n S g (translate F n (d * b) q)) =
      Inner.inner ℂ (toQuotient F n S f (translate F n (c * a) q))
        (toQuotient F n S g (translate F n (c * b) q)) :=
    inner_translate_pair_central S χ hχ hSχ z a b c f g q
  calc
    _ = ∫ q, Inner.inner ℂ (toQuotient F n S f (translate F n (d * a) q))
        (toQuotient F n S g (translate F n (d * b) q))
        ∂(quotientHaarMeasure F n).restrict (band F n) :=
      integral_congr_ae (ae_of_all _ fun q => (hp q).symm)
    _ = ∫ q, Inner.inner ℂ (toQuotient F n S f (translate F n a (translate F n d q)))
        (toQuotient F n S g (translate F n b (translate F n d q)))
        ∂(quotientHaarMeasure F n).restrict (band F n) := by
      apply integral_congr_ae
      exact ae_of_all _ fun q => congrArg₂ (Inner.inner ℂ)
        (congrArg (toQuotient F n S f) (translate_mul_apply d a q))
        (congrArg (toQuotient F n S g) (translate_mul_apply d b q))
    _ = _ := hd.integral_comp (translate F n d).toMeasurableEquiv.measurableEmbedding
      (fun q => Inner.inner ℂ (toQuotient F n S f (translate F n a q))
        (toQuotient F n S g (translate F n b q)))

variable [CompactSpace (AdeleQuotient F)]

/-- The actual band inner product of two different translates is their
pointwise integral against the unchanged canonical band measure. -/
theorem inner_translatedToL2_pair (hS : S.IsCuspidal)
    (a b : AdelicGL F n) (f g : S.Space) :
    Inner.inner ℂ (translatedToL2 S hS a f) (translatedToL2 S hS b g) =
      ∫ q, Inner.inner ℂ (toQuotient F n S f (translate F n a q))
        (toQuotient F n S g (translate F n b q))
        ∂(quotientHaarMeasure F n).restrict (band F n) := by
  refine (L2.inner_def (translatedToL2 S hS a f) (translatedToL2 S hS b g)).trans ?_
  apply integral_congr_ae
  filter_upwards [(memLp_translate_of_cuspidal S hS a f).coeFn_toLp,
    (memLp_translate_of_cuspidal S hS b g).coeFn_toLp] with q hf hg
  exact congrArg₂ (Inner.inner ℂ) hf hg

variable (hS : S.IsCuspidal) (hn : n ≠ 0)
  (χ : NumberField.IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ)
  (hχ : ∀ z, ‖(χ z : ℂ)‖ = 1) (hSχ : S.HasCentralCharacter χ)

include hn χ hχ hSχ in
/-- The actual translated algebraic images have the coherent Gram identity
needed to reconstruct multiplication on the original Hilbert completion. -/
theorem inner_translatedToL2_gram (a b : AdelicGL F n) (f g : S.Space) :
    Inner.inner ℂ (translatedToL2 S hS a f) (translatedToL2 S hS (a * b) g) =
      Inner.inner ℂ (translatedToL2 S hS 1 f) (translatedToL2 S hS b g) := by
  have h := integral_inner_translate_pair S hn χ hχ hSχ 1 b a f g
  simp only [mul_one] at h
  exact (inner_translatedToL2_pair S hS a (a * b) f g).trans
    (h.trans (inner_translatedToL2_pair S hS 1 b f g).symm)

variable (b : S.UnitaryForm)
  (hb : ∀ f g : S.Space, b.inner f g =
    ∫ q, Inner.inner ℂ (toQuotient F n S f q) (toQuotient F n S g q)
      ∂(quotientHaarMeasure F n).restrict (band F n))

/-- The completed actual translated embeddings satisfy the Gram identity
on the same prescribed source Hilbert space. -/
theorem inner_translatedHilbertEmbedding_gram (a c : AdelicGL F n)
    (x y : b.finiteForm.HilbertCompletion) :
    Inner.inner ℂ (translatedHilbertEmbedding S hS hn χ hχ hSχ b hb a x)
      (translatedHilbertEmbedding S hS hn χ hχ hSχ b hb (a * c) y) =
    Inner.inner ℂ (translatedHilbertEmbedding S hS hn χ hχ hSχ b hb 1 x)
      (translatedHilbertEmbedding S hS hn χ hχ hSχ b hb c y) := by
  apply Langlands.UnitaryEmbeddingFamily.gram_of_dense b.finiteForm.toHilbert
    b.finiteForm.denseRange_toHilbert
    (translatedHilbertEmbedding S hS hn χ hχ hSχ b hb)
  intro a c f g
  exact (congrArg₂ (Inner.inner ℂ)
    (translatedHilbertEmbedding_toHilbert S hS hn χ hχ hSχ b hb a f)
    (translatedHilbertEmbedding_toHilbert S hS hn χ hχ hSχ b hb (a * c) g)).trans
      ((inner_translatedToL2_gram S hS hn χ hχ hSχ a c f g).trans
        (congrArg₂ (Inner.inner ℂ)
          (translatedHilbertEmbedding_toHilbert S hS hn χ hχ hSχ b hb 1 f)
          (translatedHilbertEmbedding_toHilbert S hS hn χ hχ hSχ b hb c g)).symm)

end OperatorDeterminantSlice

/-- Coherence of the actual translated embeddings of any supplied canonical
band form completion. -/
def CuspidalTranslatedGramIdentityStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (n : ℕ) (S : OperatorRealization F n) (hS : S.IsCuspidal) (hn : n ≠ 0)
    (χ : NumberField.IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ)
    (hχ : ∀ z, ‖(χ z : ℂ)‖ = 1) (hSχ : S.HasCentralCharacter χ)
    (b : S.UnitaryForm)
    (hb : ∀ f g : S.Space, b.inner f g =
      ∫ q, Inner.inner ℂ (OperatorDeterminantSlice.toQuotient F n S f q)
        (OperatorDeterminantSlice.toQuotient F n S g q)
        ∂(OperatorDeterminantSlice.quotientHaarMeasure F n).restrict
          (OperatorDeterminantSlice.band F n))
    (a c : AdelicGL F n) (x y : b.finiteForm.HilbertCompletion),
    Inner.inner ℂ
      (OperatorDeterminantSlice.translatedHilbertEmbedding S hS hn χ hχ hSχ b hb a x)
      (OperatorDeterminantSlice.translatedHilbertEmbedding S hS hn χ hχ hSχ b hb (a * c) y) =
    Inner.inner ℂ
      (OperatorDeterminantSlice.translatedHilbertEmbedding S hS hn χ hχ hSχ b hb 1 x)
      (OperatorDeterminantSlice.translatedHilbertEmbedding S hS hn χ hχ hSχ b hb c y)

theorem cuspidalTranslatedGramIdentity : CuspidalTranslatedGramIdentityStatement.{u} := by
  intro F _ _ _ n S hS hn χ hχ hSχ b hb a c x y
  exact OperatorDeterminantSlice.inner_translatedHilbertEmbedding_gram
    S hS hn χ hχ hSχ b hb a c x y

end Langlands.Automorphic
