import Langlands.Automorphic.CuspidalBandOrbitClosure
import Langlands.Automorphic.CuspidalTranslatedGramIdentity
import Langlands.Automorphic.CuspidalL2.Basics

/-! # The actual adelic Hilbert action from the explicit coefficient premise -/

noncomputable section
universe u
set_option autoImplicit false
set_option maxHeartbeats 20000
set_option Elab.async false

namespace Langlands.UnitaryEmbeddingFamily
universe uV uE uH

/-- Containment in the original isometric range can be checked on a dense carrier. -/
theorem range_mem_of_dense
    {V : Type uV} {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (j : V → E) (hj : DenseRange j) (J K : E →ₗᵢ[ℂ] H)
    (h : ∀ v, K (j v) ∈ Set.range J) (x : E) :
    K x ∈ Set.range J := by
  refine hj.induction_on x ?_ h
  exact J.isometry.isClosedEmbedding.isClosed_range.preimage K.continuous

/-- A closed range formula and algebraic containment give full image containment
without changing either supplied isometry. -/
theorem range_mem_of_dense_closure
    {V : Type uV} {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (j : V → E) (hj : DenseRange j) (J K : E →ₗᵢ[ℂ] H) (l k : V → H)
    (hk : ∀ v, K (j v) = k v) (hJ : Set.range J = closure (Set.range l))
    (hmem : ∀ v, k v ∈ closure (Set.range l)) (x : E) :
    K x ∈ Set.range J := by
  apply range_mem_of_dense j hj J K
  intro v
  exact (hk v).symm ▸ (hJ.symm ▸ hmem v)

variable {G : Type*} [Group G]
    {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- A bounded group action realizes the specified translated embeddings and
preserves the original source inner product. -/
def RealizesEmbeddings (J : G → E →ₗᵢ[ℂ] H) (U : G →* (E →L[ℂ] E)) : Prop :=
  (∀ a x, J 1 (U a x) = J a x) ∧
    ∀ a x y, Inner.inner ℂ (U a x) (U a y) = Inner.inner ℂ x y

/-- The generic reconstructed representation retains both defining properties. -/
theorem realizesEmbeddings (A : Langlands.UnitaryEmbeddingFamily G E H) :
    RealizesEmbeddings A.embedding A.toContinuousLinearRepresentation :=
  ⟨A.embedding_transport, A.inner_toContinuousLinearRepresentation⟩

end Langlands.UnitaryEmbeddingFamily

namespace Langlands.Automorphic
open Langlands.Global MeasureTheory
open scoped NumberField
variable {F : Type u} [Field F] [NumberField F] {n : ℕ}

local instance adelicActionRationalGroup : AddCommGroup (RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance adelicActionContinuousGroup : AddCommGroup (ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance adelicActionSmoothGroup : AddCommGroup (FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance adelicActionFormsGroup : AddCommGroup (AutomorphicForms F n) :=
  Submodule.addCommGroup _
local instance adelicActionStableGroup : AddCommGroup (StableAutomorphicFunctions F n) :=
  Submodule.addCommGroup _
local instance adelicActionSpaceGroup (S : OperatorRealization F n) : AddCommGroup S.Space :=
  Submodule.addCommGroup _


namespace OperatorDeterminantSlice
variable [CompactSpace (AdeleQuotient F)] (S : OperatorRealization F n)

/-- An arbitrary adelic translate reduces to an infinite translate of an
original finite-translated source vector, with its actual function unchanged. -/
theorem translatedToL2_finite_factor (hS : S.IsCuspidal)
    (a : AdelicGL F n) (f : S.Space) :
    translatedToL2 S hS a f =
      translatedToL2 S hS (AdelicGL.ofInfinite F n (AdelicGL.infinite F n a))
        (S.finiteRepresentation (AdelicGL.finite F n a) f) := by
  apply Lp.ext
  filter_upwards [(memLp_translate_of_cuspidal S hS a f).coeFn_toLp,
    (memLp_translate_of_cuspidal S hS
      (AdelicGL.ofInfinite F n (AdelicGL.infinite F n a))
      (S.finiteRepresentation (AdelicGL.finite F n a) f)).coeFn_toLp] with q hf hg
  exact hf.trans ((congrArg
    (fun t : AdelicGL F n => toQuotient F n S f (translate F n t q))
    (AdelicGL.eq_ofInfinite_mul_ofFinite F n a)).trans
      ((congrArg (toQuotient F n S f)
        (translate_mul_apply _ _ q)).trans
          ((toQuotient_finite F n S (AdelicGL.finite F n a) f _).symm.trans hg.symm)))

variable {r : ℕ} (T : CuspidalOperatorRealization F r)

/-- The explicit coefficient premise gives containment for every adelic
translate of the original carrier, including its finite component. -/
theorem translatedToL2_mem_sourceBandClosure_adelic
    (hcoeff : CuspidalHilbertOrbitCoefficientStatement.{u})
    (hT : Langlands.ClassField.Global.RelativeWeilGroup.HasUnitaryCentralCharacter T)
    (a : AdelicGL F (r + 1)) (f : T.Space) :
    translatedToL2 T.realization T.cuspidal a f ∈ sourceBandClosure T := by
  have h := translatedToL2_mem_sourceBandClosure_of_coefficients T hcoeff hT
    (AdelicGL.infinite F (r + 1) a)
    (T.realization.finiteRepresentation (AdelicGL.finite F (r + 1) a) f)
  exact (translatedToL2_finite_factor T.realization T.cuspidal a f).symm ▸ h

variable (hcoeff : CuspidalHilbertOrbitCoefficientStatement.{u})
  (χ : NumberField.IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ)
  (hχ : ∀ z, ‖(χ z : ℂ)‖ = 1) (hTχ : T.realization.HasCentralCharacter χ)
  (b : T.realization.UnitaryForm)
  (hb : ∀ f g : T.Space, b.inner f g =
    ∫ q, Inner.inner ℂ (toQuotient F (r + 1) T.realization f q)
      (toQuotient F (r + 1) T.realization g q)
      ∂(quotientHaarMeasure F (r + 1)).restrict (band F (r + 1)))

include hcoeff in
/-- Density upgrades actual translated source containment to containment
of each entire prescribed Hilbert completion image. -/
theorem translatedHilbertEmbedding_range_mem_of_coefficients
    (a : AdelicGL F (r + 1)) (x : b.finiteForm.HilbertCompletion) :
    translatedHilbertEmbedding T.realization T.cuspidal (Nat.succ_ne_zero r)
      χ hχ hTχ b hb a x ∈ Set.range
        (translatedHilbertEmbedding T.realization T.cuspidal (Nat.succ_ne_zero r)
          χ hχ hTχ b hb 1) :=
  Langlands.UnitaryEmbeddingFamily.range_mem_of_dense_closure b.finiteForm.toHilbert
    b.finiteForm.denseRange_toHilbert
    (translatedHilbertEmbedding T.realization T.cuspidal (Nat.succ_ne_zero r)
      χ hχ hTχ b hb 1)
    (translatedHilbertEmbedding T.realization T.cuspidal (Nat.succ_ne_zero r)
      χ hχ hTχ b hb a)
    (translatedToL2 T.realization T.cuspidal 1)
    (translatedToL2 T.realization T.cuspidal a)
    (translatedHilbertEmbedding_toHilbert T.realization T.cuspidal (Nat.succ_ne_zero r)
      χ hχ hTχ b hb a)
    (range_translatedHilbertEmbedding T.realization T.cuspidal (Nat.succ_ne_zero r)
      χ hχ hTχ b hb 1)
    (translatedToL2_mem_sourceBandClosure_adelic T hcoeff ⟨χ, hχ, hTχ⟩ a) x

/-- The actual translated family on the original prescribed Hilbert completion.
The scalar-coefficient premise remains explicit in its range-containment proof. -/
def adelicHilbertEmbeddingFamily :
    Langlands.UnitaryEmbeddingFamily (AdelicGL F (r + 1))
      b.finiteForm.HilbertCompletion
      (CuspidalHilbertOrbitCoefficient.BandHilbertSpace F r) where
  embedding := translatedHilbertEmbedding T.realization T.cuspidal (Nat.succ_ne_zero r)
    χ hχ hTχ b hb
  range_mem a x := translatedHilbertEmbedding_range_mem_of_coefficients T hcoeff χ hχ hTχ b hb a x
  gram := inner_translatedHilbertEmbedding_gram T.realization T.cuspidal
    (Nat.succ_ne_zero r) χ hχ hTχ b hb

/-- A full adelic group homomorphism into bounded operators on the same supplied
Hilbert completion, constructed from the actual translated functions. -/
def adelicHilbertRepresentation :
    AdelicGL F (r + 1) →*
      (b.finiteForm.HilbertCompletion →L[ℂ] b.finiteForm.HilbertCompletion) :=
  (adelicHilbertEmbeddingFamily T hcoeff χ hχ hTχ b hb).toContinuousLinearRepresentation

/-- The actual representation agrees with the prescribed translations and
is unitary for the original supplied form completion. -/
theorem adelicHilbertRepresentation_realizes :
    Langlands.UnitaryEmbeddingFamily.RealizesEmbeddings
      (translatedHilbertEmbedding T.realization T.cuspidal (Nat.succ_ne_zero r)
        χ hχ hTχ b hb)
      (adelicHilbertRepresentation T hcoeff χ hχ hTχ b hb) :=
  Langlands.UnitaryEmbeddingFamily.realizesEmbeddings
    (adelicHilbertEmbeddingFamily T hcoeff χ hχ hTχ b hb)

end OperatorDeterminantSlice
end Langlands.Automorphic
