import Langlands.Global.ArchimedeanCompact
import Langlands.Global.ArchimedeanGLTransport
import Langlands.Global.AdelicGLTransport
import Mathlib.Algebra.Order.Archimedean.Real.Hom

/-! # Arithmetic transport preserves the standard archimedean compact subgroup

For a field isomorphism `e : K ≃+* L` of number fields, the entrywise arithmetic map
on the infinite adelic matrix groups sends real places to real places by the identity
of `ℝ` and complex places to complex places by the identity or the conjugation of `ℂ`.
Hence it preserves the standard orthogonal/unitary compact subgroup in both directions.
-/

noncomputable section
universe uK uL uM

set_option autoImplicit false

namespace Langlands.Global.ArchimedeanCompactTransport

open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion
  AdelicFunctoriality

variable {K : Type uK} {L : Type uL} {M : Type uM}
variable [Field K] [NumberField K] [Field L] [NumberField L] [Field M] [NumberField M]

omit [NumberField K] [NumberField L] [NumberField M] in
theorem isReal_infinitePlaceEquiv_iff (e : K ≃+* L) (w : InfinitePlace L) :
    IsReal (infinitePlaceEquiv e w) ↔ IsReal w :=
  isReal_comap_iff e

omit [NumberField K] [NumberField L] [NumberField M] in
theorem isComplex_infinitePlaceEquiv_iff (e : K ≃+* L) (w : InfinitePlace L) :
    IsComplex (infinitePlaceEquiv e w) ↔ IsComplex w := by
  rw [← not_isReal_iff_isComplex, ← not_isReal_iff_isComplex,
    isReal_infinitePlaceEquiv_iff]

/-- The real place of `K` below a real place of `L`. -/
def realPlace (e : K ≃+* L) (w : {w : InfinitePlace L // IsReal w}) :
    {v : InfinitePlace K // IsReal v} :=
  ⟨infinitePlaceEquiv e w.1, (isReal_infinitePlaceEquiv_iff e w.1).mpr w.2⟩

/-- The complex place of `K` below a complex place of `L`. -/
def complexPlace (e : K ≃+* L) (w : {w : InfinitePlace L // IsComplex w}) :
    {v : InfinitePlace K // IsComplex v} :=
  ⟨infinitePlaceEquiv e w.1, (isComplex_infinitePlaceEquiv_iff e w.1).mpr w.2⟩

omit [NumberField K] [NumberField L] [NumberField M] in
/-- At a real place the completed transport is the identity of `ℝ` in the real embeddings. -/
theorem extensionEmbeddingOfIsReal_infiniteCompletionMap (e : K ≃+* L)
    {w : InfinitePlace L} (hw : IsReal w) (hq : IsReal (infinitePlaceEquiv e w))
    (z : (infinitePlaceEquiv e w).Completion) :
    extensionEmbeddingOfIsReal hw (infiniteCompletionMap e.toRingHom w z) =
      extensionEmbeddingOfIsReal hq z := by
  have h : (extensionEmbeddingOfIsReal hw).comp ((infiniteCompletionMap e.toRingHom w).comp
      (ringEquivRealOfIsReal hq).symm.toRingHom) = RingHom.id ℝ := Subsingleton.elim _ _
  have hz := RingHom.congr_fun h (ringEquivRealOfIsReal hq z)
  change extensionEmbeddingOfIsReal hw (infiniteCompletionMap e.toRingHom w
    ((ringEquivRealOfIsReal hq).symm (ringEquivRealOfIsReal hq z))) =
      ringEquivRealOfIsReal hq z at hz
  rwa [RingEquiv.symm_apply_apply] at hz

omit [NumberField K] [NumberField L] [NumberField M] in
/-- At a complex place the completed transport is the identity or the conjugation of `ℂ`
in the complex embeddings. -/
theorem extensionEmbedding_infiniteCompletionMap (e : K ≃+* L)
    (w : InfinitePlace L) (hq : IsComplex (infinitePlaceEquiv e w)) :
    (∀ z : (infinitePlaceEquiv e w).Completion,
        extensionEmbedding w (infiniteCompletionMap e.toRingHom w z) =
          extensionEmbedding (infinitePlaceEquiv e w) z) ∨
      (∀ z : (infinitePlaceEquiv e w).Completion,
        extensionEmbedding w (infiniteCompletionMap e.toRingHom w z) =
          starRingEnd ℂ (extensionEmbedding (infinitePlaceEquiv e w) z)) := by
  let φ : ℂ →+* ℂ := (extensionEmbedding w).comp ((infiniteCompletionMap e.toRingHom w).comp
    (ringEquivComplexOfIsComplex hq).symm.toRingHom)
  have hsymm : Continuous (ringEquivComplexOfIsComplex hq).symm :=
    (isometryEquivComplexOfIsComplex hq).symm.continuous
  have hφ : Continuous φ :=
    (isometry_extensionEmbedding w).continuous.comp
      ((continuous_infiniteCompletionMap e.toRingHom w).comp hsymm)
  rcases Complex.ringHom_eq_id_or_conj_of_continuous hφ with h | h
  · left
    intro z
    have hz := RingHom.congr_fun h (ringEquivComplexOfIsComplex hq z)
    change extensionEmbedding w (infiniteCompletionMap e.toRingHom w
      ((ringEquivComplexOfIsComplex hq).symm (ringEquivComplexOfIsComplex hq z))) =
        ringEquivComplexOfIsComplex hq z at hz
    rwa [RingEquiv.symm_apply_apply] at hz
  · right
    intro z
    have hz := RingHom.congr_fun h (ringEquivComplexOfIsComplex hq z)
    change extensionEmbedding w (infiniteCompletionMap e.toRingHom w
      ((ringEquivComplexOfIsComplex hq).symm (ringEquivComplexOfIsComplex hq z))) =
        starRingEnd ℂ (ringEquivComplexOfIsComplex hq z) at hz
    rwa [RingEquiv.symm_apply_apply] at hz

/-- Real mixed coordinates of the transported infinite adele. -/
theorem mixedSpace_infiniteAdeleEquiv_fst (e : K ≃+* L) (y : InfiniteAdeleRing K)
    (w : {w : InfinitePlace L // IsReal w}) :
    (InfiniteAdeleRing.ringEquiv_mixedSpace L (infiniteAdeleEquiv e y)).1 w =
      (InfiniteAdeleRing.ringEquiv_mixedSpace K y).1 (realPlace e w) := by
  rw [InfiniteAdeleRing.ringEquiv_mixedSpace_apply, InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
  exact extensionEmbeddingOfIsReal_infiniteCompletionMap e w.2 (realPlace e w).2 _

/-- Complex mixed coordinates of the transported infinite adele: one of the two continuous
field automorphisms of `ℂ`, depending only on the place. -/
theorem mixedSpace_infiniteAdeleEquiv_snd (e : K ≃+* L)
    (w : {w : InfinitePlace L // IsComplex w}) :
    (∀ y : InfiniteAdeleRing K,
        (InfiniteAdeleRing.ringEquiv_mixedSpace L (infiniteAdeleEquiv e y)).2 w =
          (InfiniteAdeleRing.ringEquiv_mixedSpace K y).2 (complexPlace e w)) ∨
      (∀ y : InfiniteAdeleRing K,
        (InfiniteAdeleRing.ringEquiv_mixedSpace L (infiniteAdeleEquiv e y)).2 w =
          starRingEnd ℂ ((InfiniteAdeleRing.ringEquiv_mixedSpace K y).2 (complexPlace e w))) := by
  rcases extensionEmbedding_infiniteCompletionMap e w.1 (complexPlace e w).2 with h | h
  · left
    intro y
    rw [InfiniteAdeleRing.ringEquiv_mixedSpace_apply, InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
    exact h _
  · right
    intro y
    rw [InfiniteAdeleRing.ringEquiv_mixedSpace_apply, InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
    exact h _

variable (n : ℕ)

private theorem map_star_mem_unitaryGroup {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    A.map (starRingEnd ℂ) ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  let f := (starRingEnd ℂ).mapMatrix (m := Fin n)
  have hf : ∀ B : Matrix (Fin n) (Fin n) ℂ, star (f B) = f (star B) := by
    intro B
    ext i j
    simp [f, Matrix.star_apply]
  have hfA : f A = A.map (starRingEnd ℂ) := rfl
  rw [← hfA]
  rw [Unitary.mem_iff] at hA ⊢
  refine ⟨?_, ?_⟩
  · rw [hf, ← map_mul, hA.1, map_one]
  · rw [hf, ← map_mul, hA.2, map_one]

/-- The arithmetic infinite matrix map sends the standard compact subgroup into itself. -/
theorem infiniteEquiv_mem_standardInfiniteCompact (e : K ≃+* L)
    {g : Matrix.GeneralLinearGroup (Fin n) (InfiniteAdeleRing K)}
    (hg : g ∈ standardInfiniteCompact K n) :
    AdelicGLTransport.infiniteEquiv n e g ∈ standardInfiniteCompact L n := by
  rw [mem_standardInfiniteCompact_iff] at hg ⊢
  refine ⟨fun w => ?_, fun w => ?_⟩
  · have h : ArchimedeanGL.realMatrix L n
        (archimedeanGLCoordinates L n (AdelicGLTransport.infiniteEquiv n e g)) w =
        ArchimedeanGL.realMatrix K n (archimedeanGLCoordinates K n g) (realPlace e w) := by
      ext i j
      exact mixedSpace_infiniteAdeleEquiv_fst e (g i j) w
    rw [h]
    exact hg.1 _
  · rcases mixedSpace_infiniteAdeleEquiv_snd e w with hw | hw
    · have h : ArchimedeanGL.complexMatrix L n
          (archimedeanGLCoordinates L n (AdelicGLTransport.infiniteEquiv n e g)) w =
          ArchimedeanGL.complexMatrix K n (archimedeanGLCoordinates K n g) (complexPlace e w) := by
        ext i j
        exact hw (g i j)
      rw [h]
      exact hg.2 _
    · have h : ArchimedeanGL.complexMatrix L n
          (archimedeanGLCoordinates L n (AdelicGLTransport.infiniteEquiv n e g)) w =
          (ArchimedeanGL.complexMatrix K n (archimedeanGLCoordinates K n g)
            (complexPlace e w)).map (starRingEnd ℂ) := by
        ext i j
        exact hw (g i j)
      rw [h]
      exact map_star_mem_unitaryGroup n (hg.2 _)

/-- Preimage of the standard compact subgroup under arithmetic transport. -/
theorem comap_infiniteEquiv_standardInfiniteCompact (e : K ≃+* L) :
    (standardInfiniteCompact L n).comap
        (AdelicGLTransport.infiniteEquiv n e).toMonoidHom =
      standardInfiniteCompact K n := by
  ext g
  constructor
  · intro hg
    have hg' : AdelicGLTransport.infiniteEquiv n e g ∈ standardInfiniteCompact L n := hg
    have h := infiniteEquiv_mem_standardInfiniteCompact n e.symm hg'
    have hinv : AdelicGLTransport.infiniteEquiv n e.symm
        (AdelicGLTransport.infiniteEquiv n e g) = g := by
      rw [← ContinuousMulEquiv.trans_apply, ← AdelicGLTransport.infiniteEquiv_trans]
      simp
    rwa [hinv] at h
  · exact infiniteEquiv_mem_standardInfiniteCompact n e

/-- The induced multiplicative equivalence of standard compact subgroups. -/
def compactEquiv (e : K ≃+* L) :
    standardInfiniteCompact K n ≃* standardInfiniteCompact L n where
  toFun k := ⟨AdelicGLTransport.infiniteEquiv n e k,
    infiniteEquiv_mem_standardInfiniteCompact n e k.2⟩
  invFun k := ⟨AdelicGLTransport.infiniteEquiv n e.symm k,
    infiniteEquiv_mem_standardInfiniteCompact n e.symm k.2⟩
  left_inv k := by
    apply Subtype.ext
    change AdelicGLTransport.infiniteEquiv n e.symm (AdelicGLTransport.infiniteEquiv n e k) = k
    rw [← ContinuousMulEquiv.trans_apply, ← AdelicGLTransport.infiniteEquiv_trans]
    simp
  right_inv k := by
    apply Subtype.ext
    change AdelicGLTransport.infiniteEquiv n e (AdelicGLTransport.infiniteEquiv n e.symm k) = k
    rw [← ContinuousMulEquiv.trans_apply, ← AdelicGLTransport.infiniteEquiv_trans]
    simp
  map_mul' k l := Subtype.ext (map_mul (AdelicGLTransport.infiniteEquiv n e)
    (k : Matrix.GeneralLinearGroup (Fin n) (InfiniteAdeleRing K)) l)

@[simp] theorem compactEquiv_val (e : K ≃+* L) (k : standardInfiniteCompact K n) :
    (compactEquiv n e k : Matrix.GeneralLinearGroup (Fin n) (InfiniteAdeleRing L)) =
      AdelicGLTransport.infiniteEquiv n e k := rfl

@[simp] theorem compactEquiv_refl (k : standardInfiniteCompact K n) :
    compactEquiv n (RingEquiv.refl K) k = k := by
  apply Subtype.ext
  rw [compactEquiv_val, AdelicGLTransport.infiniteEquiv_refl]
  rfl

theorem compactEquiv_trans (e : K ≃+* L) (f : L ≃+* M) (k : standardInfiniteCompact K n) :
    compactEquiv n (e.trans f) k = compactEquiv n f (compactEquiv n e k) := by
  apply Subtype.ext
  rw [compactEquiv_val, compactEquiv_val, compactEquiv_val, AdelicGLTransport.infiniteEquiv_trans]
  rfl

@[simp] theorem compactEquiv_apply_symm (e : K ≃+* L) (k : standardInfiniteCompact L n) :
    compactEquiv n e (compactEquiv n e.symm k) = k :=
  (compactEquiv n e).apply_symm_apply k

@[simp] theorem compactEquiv_symm_apply (e : K ≃+* L) (k : standardInfiniteCompact K n) :
    compactEquiv n e.symm (compactEquiv n e k) = k :=
  (compactEquiv n e).symm_apply_apply k

end Langlands.Global.ArchimedeanCompactTransport
