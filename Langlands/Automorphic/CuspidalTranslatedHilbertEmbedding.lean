import Langlands.Automorphic.CuspidalTranslatedBandIntegrability
import Langlands.Automorphic.OperatorHilbertCompletion
import Mathlib.Analysis.Normed.Operator.Extend

/-! # Actual translated cusp completions inside the full band Hilbert space -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 20000
set_option Elab.async false

namespace Langlands.InvariantPositiveForm

universe uG uV uH

variable {G : Type uG} [Group G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {ρ : Representation ℂ G V}

/-- Extend an inner-product-preserving algebraic map into an actual complete
inner-product space using the original form completion. -/
def hilbertEmbeddingOfInner (b : InvariantPositiveForm ρ) (j : V →ₗ[ℂ] H)
    (hj : ∀ v w, Inner.inner ℂ (j v) (j w) = b.inner v w) :
    b.HilbertCompletion →ₗᵢ[ℂ] H :=
  j.extendOfIsometry (e := b.toHilbert) b.denseRange_toHilbert fun v =>
    (norm_eq_sqrt_re_inner (𝕜 := ℂ) (j v)).trans
      ((congrArg (fun z : ℂ => Real.sqrt z.re) (hj v v)).trans
        (b.norm_toHilbert v).symm)

@[simp]
theorem hilbertEmbeddingOfInner_toHilbert (b : InvariantPositiveForm ρ)
    (j : V →ₗ[ℂ] H) (hj : ∀ v w, Inner.inner ℂ (j v) (j w) = b.inner v w) (v : V) :
    b.hilbertEmbeddingOfInner j hj (b.toHilbert v) = j v :=
  LinearMap.extendOfIsometry_eq _ _ _ _

/-- The isometric image is closed because the original form completion is complete. -/
theorem isClosed_range_hilbertEmbeddingOfInner (b : InvariantPositiveForm ρ)
    (j : V →ₗ[ℂ] H) (hj : ∀ v w, Inner.inner ℂ (j v) (j w) = b.inner v w) :
    IsClosed (Set.range (b.hilbertEmbeddingOfInner j hj)) :=
  (b.hilbertEmbeddingOfInner j hj).isometry.isClosedEmbedding.isClosed_range

/-- The completed map has exactly the closure of the prescribed algebraic image. -/
theorem range_hilbertEmbeddingOfInner (b : InvariantPositiveForm ρ)
    (j : V →ₗ[ℂ] H) (hj : ∀ v w, Inner.inner ℂ (j v) (j w) = b.inner v w) :
    Set.range (b.hilbertEmbeddingOfInner j hj) = closure (Set.range j) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨x, rfl⟩
    refine b.denseRange_toHilbert.induction_on x ?_ ?_
    · exact isClosed_closure.preimage (b.hilbertEmbeddingOfInner j hj).continuous
    · intro v
      exact subset_closure ⟨v, (b.hilbertEmbeddingOfInner_toHilbert j hj v).symm⟩
  · refine closure_minimal ?_ (b.isClosed_range_hilbertEmbeddingOfInner j hj)
    rintro _ ⟨v, rfl⟩
    exact ⟨b.toHilbert v, b.hilbertEmbeddingOfInner_toHilbert j hj v⟩

end Langlands.InvariantPositiveForm

namespace Langlands.Automorphic

open Langlands.Global MeasureTheory
open scoped NumberField
universe u

variable {F : Type u} [Field F] [NumberField F] {n : ℕ}

local instance embeddingRationalGroup : AddCommGroup (RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance embeddingContinuousGroup : AddCommGroup (ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance embeddingSmoothGroup : AddCommGroup (FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance embeddingFormsGroup : AddCommGroup (AutomorphicForms F n) :=
  Submodule.addCommGroup _
local instance embeddingStableGroup : AddCommGroup (StableAutomorphicFunctions F n) :=
  Submodule.addCommGroup _
local instance embeddingSpaceGroup (S : OperatorRealization F n) : AddCommGroup S.Space :=
  Submodule.addCommGroup _

namespace OperatorDeterminantSlice

local instance embeddingIsAffine :
    _root_.AlgebraicGeometry.IsAffine (matrixGroupScheme F n).X.left :=
  Langlands.GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of F)
local instance embeddingSmooth :
    _root_.AlgebraicGeometry.Smooth (matrixGroupScheme F n).X.hom :=
  Langlands.GroupScheme.GeneralLinear.smoothStatement (Fin n) (CommRingCat.of F)

variable [CompactSpace (AdeleQuotient F)] (S : OperatorRealization F n)

/-- The actual translated quotient function, as a vector of the unchanged full
band `L²` space. The source vector remains in the original operator carrier. -/
def translatedToL2 (hS : S.IsCuspidal) (a : AdelicGL F n) :
    S.Space →ₗ[ℂ] Lp ℂ 2 ((quotientHaarMeasure F n).restrict (band F n)) where
  toFun f := (memLp_translate_of_cuspidal S hS a f).toLp
    (fun q => toQuotient F n S f (translate F n a q))
  map_add' f g := by
    have h := (memLp_translate_of_cuspidal S hS a f).toLp_add
      (memLp_translate_of_cuspidal S hS a g)
    simp only [map_add, ContinuousMap.coe_add, Pi.add_apply]
    exact h
  map_smul' c f := by
    have h := (memLp_translate_of_cuspidal S hS a f).toLp_const_smul c
    simp only [map_smul, ContinuousMap.coe_smul, Pi.smul_apply, RingHom.id_apply]
    exact h

/-- The algebraic translated map retains the actual band integral pairing. -/
theorem inner_translatedToL2 (hS : S.IsCuspidal) (a : AdelicGL F n) (f g : S.Space) :
    Inner.inner ℂ (translatedToL2 S hS a f) (translatedToL2 S hS a g) =
      ∫ q, Inner.inner ℂ (toQuotient F n S f (translate F n a q))
        (toQuotient F n S g (translate F n a q))
        ∂(quotientHaarMeasure F n).restrict (band F n) := by
  refine (L2.inner_def (translatedToL2 S hS a f) (translatedToL2 S hS a g)).trans ?_
  apply integral_congr_ae
  filter_upwards [(memLp_translate_of_cuspidal S hS a f).coeFn_toLp,
    (memLp_translate_of_cuspidal S hS a g).coeFn_toLp] with q hf hg
  exact congrArg₂ (Inner.inner ℂ) hf hg

variable (hS : S.IsCuspidal) (hn : n ≠ 0)
  (χ : NumberField.IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ)
  (hχ : ∀ z, ‖(χ z : ℂ)‖ = 1) (hSχ : S.HasCentralCharacter χ)
  (b : S.UnitaryForm)
  (hb : ∀ f g : S.Space, b.inner f g =
    ∫ q, Inner.inner ℂ (toQuotient F n S f q) (toQuotient F n S g q)
      ∂(quotientHaarMeasure F n).restrict (band F n))

include hn χ hχ hSχ hb in
/-- Unitary central character and the prescribed band form preserve the inner
product for every actual adelic translation. -/
theorem inner_translatedToL2_eq (a : AdelicGL F n) (f g : S.Space) :
    Inner.inner ℂ (translatedToL2 S hS a f) (translatedToL2 S hS a g) =
      b.inner f g :=
  (inner_translatedToL2 S hS a f g).trans
    ((integral_inner_translate F n S hn (quotientHaarMeasure F n) χ hχ hSχ
      (fun a _ => measurePreserving_translate F n a) a f g).trans (hb f g).symm)

/-- Each actual adelic translate gives an isometric embedding of the same source
completion into the full actual band `L²` space. -/
def translatedHilbertEmbedding (a : AdelicGL F n) :
    b.finiteForm.HilbertCompletion →ₗᵢ[ℂ]
      Lp ℂ 2 ((quotientHaarMeasure F n).restrict (band F n)) :=
  b.finiteForm.hilbertEmbeddingOfInner (translatedToL2 S hS a)
    (inner_translatedToL2_eq S hS hn χ hχ hSχ b hb a)

@[simp]
theorem translatedHilbertEmbedding_toHilbert (a : AdelicGL F n) (f : S.Space) :
    translatedHilbertEmbedding S hS hn χ hχ hSχ b hb a (b.finiteForm.toHilbert f) =
      translatedToL2 S hS a f :=
  Langlands.InvariantPositiveForm.hilbertEmbeddingOfInner_toHilbert b.finiteForm _ _ f

/-- The embedding has precisely the closure of the prescribed translated image. -/
theorem range_translatedHilbertEmbedding (a : AdelicGL F n) :
    Set.range (translatedHilbertEmbedding S hS hn χ hχ hSχ b hb a) =
      closure (Set.range (translatedToL2 S hS a)) :=
  Langlands.InvariantPositiveForm.range_hilbertEmbeddingOfInner b.finiteForm _ _

end OperatorDeterminantSlice
end Langlands.Automorphic
