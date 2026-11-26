import Langlands.Automorphic.RegularAlgebraic
import Langlands.Automorphic.OperatorArithmeticTransportClasses

/-!
# Arithmetic transport of the regular algebraic type at infinity

For an isomorphism `e : K ≃+* L` of number fields, the arithmetic transport
`mixedEquiv e` of the mixed archimedean coordinates permutes the coordinates
`embeddingComponent` of the complex embeddings: the index `j` of `L` is sent to
an index of `K` over the pulled-back place, with the two indices of a complex
place exchanged exactly when the chosen embedding of the pulled-back place is
the conjugate of the composite embedding. The enveloping algebra isomorphism
`ArchimedeanLieTransport.envelopingEquiv n e` carries the complexified real
generators, diagonal and strictly upper triangular, to those of `L`.

Consequently a highest-weight vector of weight `μ` for `L` gives a
highest-weight vector of the reindexed weight for `K`, in the cyclic quotient
of the enveloping algebra of `K`, and Clozel's regular algebraic infinitesimal
characters (Clozel 1990, Définitions 1.8 and 3.12) are preserved by composition
with `ArchimedeanLieTransport.centerEquiv n e`. Since arithmetic pullback of an
operator realization intertwines the differential actions along
`envelopingEquiv n e`, the regular algebraic type is preserved and reflected by
arithmetic pullback.
-/

noncomputable section

universe uK uL

open NumberField NumberField.InfinitePlace

open scoped Classical

set_option autoImplicit false

namespace Langlands.Global.ArchimedeanLieTransport

open AdelicFunctoriality ArchimedeanGL ArchimedeanGLTransport

variable {K : Type uK} {L : Type uL} [Field K] [NumberField K] [Field L] [NumberField L]

section Embeddings

variable (K) in
/-- The complex embedding of `K` read off by an embedding index: the chosen embedding of
a real place, the chosen embedding of a complex place, or its conjugate. -/
def indexEmbedding : EmbeddingIndex K → (K →+* ℂ)
  | .inl w => w.1.embedding
  | .inr (w, false) => w.1.embedding
  | .inr (w, true) => ComplexEmbedding.conjugate w.1.embedding

omit [NumberField K] in
/-- On the image of the field, the coordinate at an embedding index is the
corresponding complex embedding. -/
theorem embeddingComponent_mixedEmbedding (j : EmbeddingIndex K) (a : K) :
    embeddingComponent K j (mixedEmbedding K a) = indexEmbedding K j a := by
  rcases j with w | ⟨w, _ | _⟩
  · rw [embeddingComponent_inl, mixedEmbedding.mixedEmbedding_apply_isReal,
      embedding_of_isReal_apply]
    rfl
  · rw [embeddingComponent_inr_false, mixedEmbedding.mixedEmbedding_apply_isComplex]
    rfl
  · rw [embeddingComponent_inr_true, mixedEmbedding.mixedEmbedding_apply_isComplex]
    rfl

omit [NumberField K] in
/-- Each embedding coordinate of the mixed space is continuous. -/
theorem continuous_embeddingComponent (j : EmbeddingIndex K) :
    Continuous (embeddingComponent K j) := by
  rcases j with w | ⟨w, _ | _⟩
  · exact (continuous_congr (embeddingComponent_inl K w)).mpr
      (Complex.continuous_ofReal.comp ((continuous_apply w).comp continuous_fst))
  · exact (continuous_congr (embeddingComponent_inr_false K w)).mpr
      ((continuous_apply w).comp continuous_snd)
  · exact (continuous_congr (embeddingComponent_inr_true K w)).mpr
      (Complex.continuous_conj.comp ((continuous_apply w).comp continuous_snd))

/-- The image of the field is dense in its mixed archimedean space. -/
theorem denseRange_mixedEmbedding : DenseRange (mixedEmbedding K) := by
  have h := (InfiniteAdeleRing.ringEquiv_mixedSpace K).surjective.denseRange.comp
    (InfiniteAdeleRing.denseRange_algebraMap K) (continuous_infiniteAdeleCoordinates K)
  convert h using 1
  funext a
  exact InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp K

/-- Arithmetic transport of mixed coordinates extends the field isomorphism. -/
theorem mixedEquiv_mixedEmbedding (e : K ≃+* L) (a : K) :
    mixedEquiv e (mixedEmbedding K a) = mixedEmbedding L (e a) := by
  rw [InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp K,
    InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp L]
  change InfiniteAdeleRing.ringEquiv_mixedSpace L (infiniteAdeleEquiv e
      ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm
        (InfiniteAdeleRing.ringEquiv_mixedSpace K (algebraMap K (InfiniteAdeleRing K) a)))) = _
  rw [RingEquiv.symm_apply_apply, infiniteAdeleEquiv_diagonal]

omit [NumberField K] [NumberField L] in
/-- Pullback of infinite places along a field isomorphism preserves real places. -/
theorem isReal_infinitePlaceEquiv_iff (e : K ≃+* L) (w : InfinitePlace L) :
    IsReal (infinitePlaceEquiv e w) ↔ IsReal w :=
  isReal_comap_iff e

omit [NumberField K] [NumberField L] in
/-- Pullback of infinite places along a field isomorphism preserves complex places. -/
theorem isComplex_infinitePlaceEquiv_iff (e : K ≃+* L) (w : InfinitePlace L) :
    IsComplex (infinitePlaceEquiv e w) ↔ IsComplex w := by
  rw [← not_isReal_iff_isComplex, ← not_isReal_iff_isComplex, isReal_infinitePlaceEquiv_iff]

omit [NumberField K] [NumberField L] in
/-- The chosen embedding of the pulled-back place is the composite embedding or its
conjugate. -/
theorem embedding_infinitePlaceEquiv (e : K ≃+* L) (w : InfinitePlace L) :
    (infinitePlaceEquiv e w).embedding = w.embedding.comp e.toRingHom ∨
      (infinitePlaceEquiv e w).embedding =
        ComplexEmbedding.conjugate (w.embedding.comp e.toRingHom) := by
  have h : infinitePlaceEquiv e w = InfinitePlace.mk (w.embedding.comp e.toRingHom) := by
    change w.comap e.toRingHom = _
    rw [← comap_mk, mk_embedding]
  rw [h]
  exact embedding_mk_eq _

/-- Whether the chosen embedding of the pulled-back place differs from the composite
of the chosen embedding of `w` with `e`. -/
def conjFlip (e : K ≃+* L) (w : InfinitePlace L) : Bool :=
  decide ((infinitePlaceEquiv e w).embedding ≠ w.embedding.comp e.toRingHom)

/-- Exclusive or with a fixed Boolean, as a permutation. -/
def boolXorEquiv (c : Bool) : Bool ≃ Bool where
  toFun b := xor b c
  invFun b := xor b c
  left_inv b := by cases b <;> cases c <;> rfl
  right_inv b := by cases b <;> cases c <;> rfl

/-- The reindexing of embedding indices induced by a field isomorphism `e : K ≃+* L`:
a place of `L` goes to its pullback along `e`, and the two indices of a complex place
are exchanged exactly when `conjFlip e` holds. -/
def embeddingIndexEquiv (e : K ≃+* L) : EmbeddingIndex L ≃ EmbeddingIndex K :=
  Equiv.sumCongr
    ((infinitePlaceEquiv e).subtypeEquiv fun w => (isReal_infinitePlaceEquiv_iff e w).symm)
    (Equiv.prodShear
      ((infinitePlaceEquiv e).subtypeEquiv fun w => (isComplex_infinitePlaceEquiv_iff e w).symm)
      fun w => boolXorEquiv (conjFlip e w.1))

omit [NumberField K] [NumberField L] in
@[simp] theorem embeddingIndexEquiv_inl (e : K ≃+* L) (w : {w : InfinitePlace L // IsReal w}) :
    embeddingIndexEquiv e (.inl w) =
      .inl ⟨infinitePlaceEquiv e w.1, (isReal_infinitePlaceEquiv_iff e w.1).mpr w.2⟩ := rfl

omit [NumberField K] [NumberField L] in
@[simp] theorem embeddingIndexEquiv_inr (e : K ≃+* L)
    (w : {w : InfinitePlace L // IsComplex w}) (b : Bool) :
    embeddingIndexEquiv e (.inr (w, b)) =
      .inr (⟨infinitePlaceEquiv e w.1, (isComplex_infinitePlaceEquiv_iff e w.1).mpr w.2⟩,
        xor b (conjFlip e w.1)) := rfl

omit [NumberField K] [NumberField L] in
/-- The embedding read off by the reindexed index is the composite with `e`. -/
theorem indexEmbedding_comp (e : K ≃+* L) (j : EmbeddingIndex L) :
    (indexEmbedding L j).comp e.toRingHom = indexEmbedding K (embeddingIndexEquiv e j) := by
  rcases j with w | ⟨w, b⟩
  · rw [embeddingIndexEquiv_inl]
    exact (comap_embedding_of_isReal e.toRingHom
      ((isReal_infinitePlaceEquiv_iff e w.1).mpr w.2)).symm
  · rw [embeddingIndexEquiv_inr]
    rcases embedding_infinitePlaceEquiv e w.1 with h | h
    · have hf : conjFlip e w.1 = false := decide_eq_false (not_not.mpr h)
      rw [hf]
      cases b
      · exact h.symm
      · change (ComplexEmbedding.conjugate w.1.embedding).comp e.toRingHom =
          ComplexEmbedding.conjugate (infinitePlaceEquiv e w.1).embedding
        rw [h, ComplexEmbedding.conjugate_comp]
    · have hne : (infinitePlaceEquiv e w.1).embedding ≠ w.1.embedding.comp e.toRingHom := by
        intro h'
        rw [h] at h'
        have hr : ComplexEmbedding.IsReal (w.1.embedding.comp e.toRingHom) :=
          ComplexEmbedding.isReal_iff.mpr h'
        exact (isComplex_iff.mp w.2) (ComplexEmbedding.isReal_comp_iff.mp hr)
      have hf : conjFlip e w.1 = true := decide_eq_true hne
      rw [hf]
      cases b
      · change w.1.embedding.comp e.toRingHom =
          ComplexEmbedding.conjugate (infinitePlaceEquiv e w.1).embedding
        rw [h]
        exact (ComplexEmbedding.involutive_conjugate _ _).symm
      · change (ComplexEmbedding.conjugate w.1.embedding).comp e.toRingHom =
          (infinitePlaceEquiv e w.1).embedding
        rw [h, ComplexEmbedding.conjugate_comp]

/-- Arithmetic transport of mixed coordinates permutes the coordinates of the complex
embeddings along `embeddingIndexEquiv e`. -/
theorem embeddingComponent_mixedEquiv (e : K ≃+* L) (j : EmbeddingIndex L)
    (x : mixedEmbedding.mixedSpace K) :
    embeddingComponent L j (mixedEquiv e x) =
      embeddingComponent K (embeddingIndexEquiv e j) x := by
  have h := (denseRange_mixedEmbedding (K := K)).equalizer
    ((continuous_embeddingComponent j).comp (continuous_mixedEquiv e))
    (continuous_embeddingComponent (embeddingIndexEquiv e j)) (by
      funext a
      simp only [Function.comp_apply]
      rw [mixedEquiv_mixedEmbedding, embeddingComponent_mixedEmbedding,
        embeddingComponent_mixedEmbedding, ← indexEmbedding_comp]
      rfl)
  exact congrFun h x

end Embeddings

section Weights

variable (n : ℕ)

/-- Diagonal weights are reindexed by `embeddingIndexEquiv e`. -/
theorem diagonalWeight_mixedEquiv (e : K ≃+* L) (μ : EmbeddingIndex L → Fin n → ℂ)
    (d : Fin n → mixedEmbedding.mixedSpace K) :
    diagonalWeight L n μ (fun i => mixedEquiv e (d i)) =
      diagonalWeight K n (fun k => μ ((embeddingIndexEquiv e).symm k)) d := by
  unfold diagonalWeight
  simp_rw [embeddingComponent_mixedEquiv]
  exact Fintype.sum_equiv (embeddingIndexEquiv e) _ _ (fun j => by simp)

/-- Entrywise arithmetic transport of a diagonal real archimedean matrix. -/
theorem matrixRealLinearEquiv_diagonal (e : K ≃+* L) (d : Fin n → mixedEmbedding.mixedSpace K) :
    matrixRealLinearEquiv n e (Matrix.diagonal d) =
      Matrix.diagonal (fun i => mixedEquiv e (d i)) := by
  refine Matrix.ext fun i j => ?_
  rw [matrixRealLinearEquiv_apply]
  by_cases h : i = j
  · subst h
    simp only [Matrix.diagonal_apply_eq]
  · simp only [Matrix.diagonal_apply_ne _ h, map_zero]

/-- Entrywise arithmetic transport of a matrix unit with one archimedean entry. -/
theorem matrixRealLinearEquiv_single (e : K ≃+* L) (i j : Fin n)
    (a : mixedEmbedding.mixedSpace K) :
    matrixRealLinearEquiv n e (Matrix.single i j a) = Matrix.single i j (mixedEquiv e a) := by
  refine Matrix.ext fun i' j' => ?_
  rw [matrixRealLinearEquiv_apply]
  by_cases h : i = i' ∧ j = j'
  · simp only [Matrix.single_apply, h, and_self, ite_true]
  · simp only [Matrix.single_apply, h, ite_false, map_zero]

/-- The enveloping algebra transport sends the complexified real generator of a matrix
to that of its entrywise arithmetic transport. -/
theorem envelopingEquiv_realGenerator (e : K ≃+* L) (X : ArchimedeanMatrix K n) :
    envelopingEquiv n e (realGenerator K n X) =
      realGenerator L n (matrixRealLinearEquiv n e X) := by
  rw [realGenerator, realGenerator, envelopingEquiv_generator, complexLieEquiv_complexify]
  congr 2

/-- The left ideal of elements of the enveloping algebra of `K` whose transport
annihilates a given vector of a module over the enveloping algebra of `L`. -/
def transportAnnihilator (e : K ≃+* L) {W : ModuleCat.{uL} (EnvelopingAlgebra L n)} (w : W) :
    Submodule (EnvelopingAlgebra K n) (EnvelopingAlgebra K n) where
  carrier := {a | envelopingEquiv n e a • w = 0}
  add_mem' {a b} ha hb := by
    change envelopingEquiv n e (a + b) • w = 0
    change envelopingEquiv n e a • w = 0 at ha
    change envelopingEquiv n e b • w = 0 at hb
    rw [map_add, add_smul, ha, hb, add_zero]
  zero_mem' := by
    change envelopingEquiv n e 0 • w = 0
    rw [map_zero, zero_smul]
  smul_mem' c a ha := by
    change envelopingEquiv n e (c * a) • w = 0
    change envelopingEquiv n e a • w = 0 at ha
    rw [map_mul, mul_smul, ha, smul_zero]

/-- A highest-weight character of `L` composed with the center transport is a
highest-weight character of `K`, for the weight reindexed by `embeddingIndexEquiv e`.
The highest-weight vector is the class of `1` in the cyclic quotient by
`transportAnnihilator`. -/
theorem isHighestWeightCharacter_comp_centerEquiv (e : K ≃+* L)
    {μ : EmbeddingIndex L → Fin n → ℂ} {χ : EnvelopingCenter L n →ₐ[ℂ] ℂ}
    (h : IsHighestWeightCharacter L n μ χ) :
    IsHighestWeightCharacter K n (fun k => μ ((embeddingIndexEquiv e).symm k))
      (χ.comp (centerEquiv n e).toAlgHom) := by
  obtain ⟨W, w, ⟨hw, hdiag, hup⟩, hz⟩ := h
  let I := transportAnnihilator n e w
  have key (a b : EnvelopingAlgebra K n) :
      (Submodule.Quotient.mk a : EnvelopingAlgebra K n ⧸ I) = Submodule.Quotient.mk b ↔
        envelopingEquiv n e a • w = envelopingEquiv n e b • w := by
    rw [Submodule.Quotient.eq]
    change envelopingEquiv n e (a - b) • w = 0 ↔ _
    rw [map_sub, sub_smul, sub_eq_zero]
  have hmk (a : EnvelopingAlgebra K n) :
      a • (Submodule.Quotient.mk 1 : EnvelopingAlgebra K n ⧸ I) = Submodule.Quotient.mk a := by
    rw [← Submodule.Quotient.mk_smul, smul_eq_mul, mul_one]
  refine ⟨ModuleCat.of (EnvelopingAlgebra K n) (EnvelopingAlgebra K n ⧸ I),
    (Submodule.Quotient.mk 1 : EnvelopingAlgebra K n ⧸ I), ⟨?_, ?_, ?_⟩, ?_⟩
  · intro h0
    have h1 : (Submodule.Quotient.mk 1 : EnvelopingAlgebra K n ⧸ I) =
        Submodule.Quotient.mk 0 := h0
    rw [key, map_one, map_zero, one_smul, zero_smul] at h1
    exact hw h1
  · intro d
    change _ • (Submodule.Quotient.mk 1 : EnvelopingAlgebra K n ⧸ I) =
      _ • (Submodule.Quotient.mk 1 : EnvelopingAlgebra K n ⧸ I)
    rw [hmk, hmk, key, envelopingEquiv_realGenerator, matrixRealLinearEquiv_diagonal,
      AlgEquiv.commutes, hdiag, diagonalWeight_mixedEquiv]
  · intro i j hij a
    change _ • (Submodule.Quotient.mk 1 : EnvelopingAlgebra K n ⧸ I) = 0
    rw [hmk, ← Submodule.Quotient.mk_zero, key, envelopingEquiv_realGenerator,
      matrixRealLinearEquiv_single, map_zero, zero_smul]
    exact hup i j hij _
  · intro z
    change _ • (Submodule.Quotient.mk 1 : EnvelopingAlgebra K n ⧸ I) =
      _ • (Submodule.Quotient.mk 1 : EnvelopingAlgebra K n ⧸ I)
    rw [hmk, hmk, key, AlgEquiv.commutes]
    exact hz (centerEquiv n e z)

/-- Regular algebraic infinitesimal characters are preserved by composition with the
center transport; the highest weight is reindexed by `embeddingIndexEquiv e`. -/
theorem isRegularAlgebraicCharacter_comp_centerEquiv (e : K ≃+* L)
    {χ : EnvelopingCenter L n →ₐ[ℂ] ℂ} (h : IsRegularAlgebraicCharacter L n χ) :
    IsRegularAlgebraicCharacter K n (χ.comp (centerEquiv n e).toAlgHom) := by
  obtain ⟨μ, hμ, hχ⟩ := h
  have h' := isHighestWeightCharacter_comp_centerEquiv n e hχ
  exact ⟨fun k => μ ((embeddingIndexEquiv e).symm k), fun k => hμ _, h'⟩

end Weights

end Langlands.Global.ArchimedeanLieTransport

namespace Langlands.Automorphic

open Langlands.Global Langlands.Global.ArchimedeanLieTransport

variable {K : Type uK} {L : Type uL} [Field K] [NumberField K] [Field L] [NumberField L]
  {n : ℕ}

local instance regularAlgebraicTransportRationalAddCommGroup {F : Type*} [Field F]
    [NumberField F] (m : ℕ) : AddCommGroup (RationalInvariantFunctions F m) :=
  Submodule.addCommGroup _
local instance regularAlgebraicTransportContinuousAddCommGroup {F : Type*} [Field F]
    [NumberField F] (m : ℕ) : AddCommGroup (ContinuousRationalFunctions F m) :=
  Submodule.addCommGroup _
local instance regularAlgebraicTransportSmoothAddCommGroup {F : Type*} [Field F]
    [NumberField F] (m : ℕ) : AddCommGroup (FiniteSmoothRationalFunctions F m) :=
  Submodule.addCommGroup _
local instance regularAlgebraicTransportFormsAddCommGroup {F : Type*} [Field F]
    [NumberField F] (m : ℕ) : AddCommGroup (AutomorphicForms F m) :=
  Submodule.addCommGroup _
local instance regularAlgebraicTransportStableAddCommGroup {F : Type*} [Field F]
    [NumberField F] (m : ℕ) : AddCommGroup (StableAutomorphicFunctions F m) :=
  Submodule.addCommGroup _

namespace OperatorRealization

local instance regularAlgebraicTransportSpaceAddCommGroup {F : Type*} [Field F]
    [NumberField F] {m : ℕ} (T : OperatorRealization F m) : AddCommGroup T.Space :=
  Submodule.addCommGroup _

/-- The arithmetic pullback has the transported infinitesimal character
`χ ∘ centerEquiv n e`. -/
theorem HasInfinitesimalCharacter.arithmeticComap (e : K ≃+* L) {S : OperatorRealization L n}
    {χ : ArchimedeanGL.EnvelopingCenter L n →ₐ[ℂ] ℂ} (h : S.HasInfinitesimalCharacter χ) :
    (S.arithmeticComap e).HasInfinitesimalCharacter (χ.comp (centerEquiv n e).toAlgHom) := by
  intro z f
  obtain ⟨g, rfl⟩ := (S.arithmeticComapEquiv e).surjective f
  have hz := h (centerEquiv n e z) g
  have hd := S.arithmeticComapEquiv_differential e (z : ArchimedeanGL.EnvelopingAlgebra K n) g
  rw [hd]
  exact (congrArg (S.arithmeticComapEquiv e) hz).trans ((S.arithmeticComapEquiv e).map_smul _ _)

/-- Arithmetic pullback preserves the regular algebraic type. -/
theorem IsRegularAlgebraic.arithmeticComap (e : K ≃+* L) {S : OperatorRealization L n}
    (h : S.IsRegularAlgebraic) : (S.arithmeticComap e).IsRegularAlgebraic := by
  obtain ⟨χ, hχ, hS⟩ := h
  exact ⟨χ.comp (centerEquiv n e).toAlgHom,
    isRegularAlgebraicCharacter_comp_centerEquiv n e hχ, hS.arithmeticComap e⟩

/-- Arithmetic pullback preserves and reflects the regular algebraic type. -/
theorem arithmeticComap_isRegularAlgebraic_iff (e : K ≃+* L) (S : OperatorRealization L n) :
    (S.arithmeticComap e).IsRegularAlgebraic ↔ S.IsRegularAlgebraic := by
  refine ⟨fun h => ?_, fun h => h.arithmeticComap e⟩
  have h' := h.arithmeticComap e.symm
  rwa [arithmeticComap_symm_arithmeticComap] at h'

end OperatorRealization

namespace CuspidalOperatorRealization

variable [CompactSpace (AdeleQuotient K)] [CompactSpace (AdeleQuotient L)] {r : ℕ}

/-- The class of the arithmetic pullback of an actual irreducible cuspidal realization
has regular algebraic type exactly when the class of the realization has. -/
theorem arithmeticComap_isoClass_isRegularAlgebraic_iff (e : K ≃+* L)
    (S : CuspidalOperatorRealization L r) :
    (S.arithmeticComap e).isoClass.IsRegularAlgebraic ↔ S.isoClass.IsRegularAlgebraic := by
  rw [isoClass_isRegularAlgebraic_iff, isoClass_isRegularAlgebraic_iff, arithmeticComap_realization]
  exact OperatorRealization.arithmeticComap_isRegularAlgebraic_iff e S.realization

/-- Descent to cuspidal classes: arithmetic pullback preserves and reflects regular
algebraic type. -/
theorem IsoClass.arithmeticComap_isRegularAlgebraic_iff (e : K ≃+* L) (c : IsoClass L r) :
    (IsoClass.arithmeticComap e c).IsRegularAlgebraic ↔ c.IsRegularAlgebraic := by
  refine Quotient.inductionOn c ?_
  intro S
  exact arithmeticComap_isoClass_isRegularAlgebraic_iff e S

end CuspidalOperatorRealization

end Langlands.Automorphic
