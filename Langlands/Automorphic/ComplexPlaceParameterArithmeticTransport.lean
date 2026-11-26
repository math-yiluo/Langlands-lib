import Langlands.Representation.Archimedean.ComplexStandardModuleConjugation
import Langlands.Automorphic.ArchimedeanPlaceParameter
import Langlands.Automorphic.OperatorArithmeticTransport
import Langlands.Automorphic.IsobaricComplexPlaceParameter
import Langlands.Global.ArchimedeanCompactTransport
import Langlands.Global.ArchimedeanLieTransport
import Langlands.Global.ArchimedeanPlaceCompact
import Langlands.Global.ArchimedeanPlaceLie
import Langlands.Global.HeckeCharacterTransport
import Langlands.Automorphic.Unramified.ComplexPlaceParameterNorm

/-!
# Arithmetic transport of complex-place parameters

Let `e : K ≃+* L` be an isomorphism of number fields and `w` a complex place of `L`, with
corresponding complex place `u = w ∘ e` of `K` (`ArchimedeanCompactTransport.complexPlace`).
In the selected coordinates of the completions, `e` induces the identity of `ℂ` when the
embedding of `w` composed with `e` is the embedding of `u` (`IsAligned e w`), and complex
conjugation otherwise. Accordingly:

* arithmetic transport sends the unitary factor and the real Lie directions at `u` to those
  at `w`, unchanged or entrywise conjugated (`compactEquiv_complexPlaceCompactInclusion`,
  `realLieEquiv_complexPlaceLieInclusion`);
* the arithmetic pullback along `e` of an actual automorphic realization with the
  standard-module parameter `ds` at `w` has at `u` the parameter `parameterList e w ds`:
  `ds` in the first case and the conjugate blocks `ds.map ComplexCharacterData.conj` in the
  second (`hasComplexPlaceParameter_arithmeticComap`, and
  `cuspidal_hasComplexPlaceParameter_arithmeticComap` for cuspidal classes);
* the pullback along `e` of a Hecke character with parameter `d` at `w` has at `u` the
  parameter `parameter e w d` (`hasComplexPlaceParameter_comap`);
* for compatible isomorphisms `e : K₁ ≃+* K₂` and `e' : L₁ ≃+* L₂` of extensions, the
  Langlands sum of singleton blocks over the places of `L₁` above `v`, read at `v ∘ e⁻¹`, is
  the Langlands sum over the corresponding places of `L₂` of the blocks read along `e'⁻¹`
  (`parameterList_complexPlaceLanglandsSum`).

The parameter statement carries the actual witness: the embedding of the `U(n)`-finite
functions of the standard module is composed with the arithmetic pullback, and in the
conjugate case first with precomposition by entrywise conjugation of `GL_n(ℂ)`
(`Langlands.Representation.Archimedean.ComplexStandardModuleConjugation`).
-/

noncomputable section

universe uK uL u₁ u₂ u₃ u₄

open scoped TensorProduct Manifold ContDiff Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic.ComplexPlaceArithmeticTransport

open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open Langlands.Global Langlands.Global.AdelicFunctoriality Langlands.LocalFactor.Archimedean
open Langlands.Global.ArchimedeanCompactTransport
open Langlands.Archimedean.ComplexConjugation Langlands.Automorphic.Unramified

variable {K : Type uK} {L : Type uL} [Field K] [NumberField K] [Field L] [NumberField L]

local notation "CPL" =>
  {w : NumberField.InfinitePlace L // NumberField.InfinitePlace.IsComplex w}

/-! ## Orientation of a complex place under an isomorphism -/

/-- The embedding of the complex place `w` of `L`, composed with `e`, is the embedding of the
corresponding complex place of `K`. -/
def IsAligned (e : K ≃+* L) (w : CPL) : Prop :=
  w.1.embedding.comp e.toRingHom = (complexPlace e w).1.embedding

open Classical in
/-- A complex character block at `w`, read at the corresponding place of `K`: unchanged when
`IsAligned e w`, conjugated otherwise. -/
def parameter (e : K ≃+* L) (w : CPL) (d : ComplexCharacterData) : ComplexCharacterData :=
  if IsAligned e w then d else d.conj

open Classical in
/-- A list of complex character blocks at `w`, read at the corresponding place of `K`. -/
def parameterList (e : K ≃+* L) (w : CPL) (ds : List ComplexCharacterData) :
    List ComplexCharacterData :=
  if IsAligned e w then ds else ds.map ComplexCharacterData.conj

omit [NumberField K] [NumberField L] in
private theorem extensionEmbedding_algebraMap' {F : Type*} [Field F]
    (v : NumberField.InfinitePlace F)
    (a : F) : extensionEmbedding v (algebraMap F v.Completion a) = v.embedding a :=
  extensionEmbedding_coe v (WithAbs.toAbs v.1 a)

omit [NumberField K] [NumberField L] in
private theorem embedding_apply_eq (e : K ≃+* L) (w : CPL)
    (h : ∀ z : (infinitePlaceEquiv e w.1).Completion,
      extensionEmbedding w.1 (infiniteCompletionMap e.toRingHom w.1 z) =
        extensionEmbedding (infinitePlaceEquiv e w.1) z) (x : K) :
    w.1.embedding (e x) = (infinitePlaceEquiv e w.1).embedding x := by
  calc w.1.embedding (e x)
      = extensionEmbedding w.1 (algebraMap L w.1.Completion (e x)) :=
        (extensionEmbedding_algebraMap' _ _).symm
    _ = extensionEmbedding w.1 (infiniteCompletionMap e.toRingHom w.1
          (algebraMap K (infinitePlaceEquiv e w.1).Completion x)) :=
        congrArg (extensionEmbedding w.1) (infiniteCompletionMap_coe e.toRingHom w.1 x).symm
    _ = extensionEmbedding (infinitePlaceEquiv e w.1)
          (algebraMap K (infinitePlaceEquiv e w.1).Completion x) := h _
    _ = _ := extensionEmbedding_algebraMap' _ _

omit [NumberField K] [NumberField L] in
private theorem embedding_apply_eq_conj (e : K ≃+* L) (w : CPL)
    (h : ∀ z : (infinitePlaceEquiv e w.1).Completion,
      extensionEmbedding w.1 (infiniteCompletionMap e.toRingHom w.1 z) =
        starRingEnd ℂ (extensionEmbedding (infinitePlaceEquiv e w.1) z)) (x : K) :
    w.1.embedding (e x) = starRingEnd ℂ ((infinitePlaceEquiv e w.1).embedding x) := by
  calc w.1.embedding (e x)
      = extensionEmbedding w.1 (algebraMap L w.1.Completion (e x)) :=
        (extensionEmbedding_algebraMap' _ _).symm
    _ = extensionEmbedding w.1 (infiniteCompletionMap e.toRingHom w.1
          (algebraMap K (infinitePlaceEquiv e w.1).Completion x)) :=
        congrArg (extensionEmbedding w.1) (infiniteCompletionMap_coe e.toRingHom w.1 x).symm
    _ = starRingEnd ℂ (extensionEmbedding (infinitePlaceEquiv e w.1)
          (algebraMap K (infinitePlaceEquiv e w.1).Completion x)) := h _
    _ = _ := congrArg (starRingEnd ℂ) (extensionEmbedding_algebraMap' _ _)

omit [NumberField K] [NumberField L] in
/-- When `IsAligned e w`, the completed transport is the identity in the selected
coordinates. -/
theorem extensionEmbedding_infiniteCompletionMap_of_isAligned (e : K ≃+* L) (w : CPL)
    (h : IsAligned e w) (z : (infinitePlaceEquiv e w.1).Completion) :
    extensionEmbedding w.1 (infiniteCompletionMap e.toRingHom w.1 z) =
      extensionEmbedding (infinitePlaceEquiv e w.1) z := by
  rcases extensionEmbedding_infiniteCompletionMap e w.1 (complexPlace e w).2 with h1 | h2
  · exact h1 z
  · exfalso
    have hreal : ComplexEmbedding.IsReal (infinitePlaceEquiv e w.1).embedding := by
      rw [ComplexEmbedding.isReal_iff]
      apply RingHom.ext
      intro x
      have h3 := embedding_apply_eq_conj e w h2 x
      have h4 : w.1.embedding (e x) = (infinitePlaceEquiv e w.1).embedding x :=
        congrArg (fun φ : K →+* ℂ => φ x) h
      change starRingEnd ℂ ((infinitePlaceEquiv e w.1).embedding x) = _
      rw [← h3, h4]
    exact (not_isReal_iff_isComplex.mpr (complexPlace e w).2) (isReal_iff.mpr hreal)

omit [NumberField K] [NumberField L] in
/-- Otherwise the completed transport is complex conjugation in the selected coordinates. -/
theorem extensionEmbedding_infiniteCompletionMap_of_not_isAligned (e : K ≃+* L) (w : CPL)
    (h : ¬IsAligned e w) (z : (infinitePlaceEquiv e w.1).Completion) :
    extensionEmbedding w.1 (infiniteCompletionMap e.toRingHom w.1 z) =
      starRingEnd ℂ (extensionEmbedding (infinitePlaceEquiv e w.1) z) := by
  rcases extensionEmbedding_infiniteCompletionMap e w.1 (complexPlace e w).2 with h1 | h2
  · exfalso
    apply h
    apply RingHom.ext
    intro x
    exact embedding_apply_eq e w h1 x
  · exact h2 z

open Classical in
/-- Complex mixed coordinates of a transported infinite adele, with the case decided by
`IsAligned`. -/
theorem ringEquiv_mixedSpace_infiniteAdeleEquiv_snd (e : K ≃+* L) (y : InfiniteAdeleRing K)
    (w : CPL) :
    (InfiniteAdeleRing.ringEquiv_mixedSpace L (infiniteAdeleEquiv e y)).2 w =
      if IsAligned e w then (InfiniteAdeleRing.ringEquiv_mixedSpace K y).2 (complexPlace e w)
      else starRingEnd ℂ ((InfiniteAdeleRing.ringEquiv_mixedSpace K y).2 (complexPlace e w)) := by
  rw [InfiniteAdeleRing.ringEquiv_mixedSpace_apply, InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
  split_ifs with h
  · exact extensionEmbedding_infiniteCompletionMap_of_isAligned e w h _
  · exact extensionEmbedding_infiniteCompletionMap_of_not_isAligned e w h _

open Classical in
/-- Complex mixed coordinates of arithmetic transport. -/
theorem mixedEquiv_snd (e : K ≃+* L) (x : mixedEmbedding.mixedSpace K) (w : CPL) :
    (ArchimedeanGLTransport.mixedEquiv e x).2 w =
      if IsAligned e w then x.2 (complexPlace e w)
      else starRingEnd ℂ (x.2 (complexPlace e w)) := by
  obtain ⟨y, rfl⟩ := (InfiniteAdeleRing.ringEquiv_mixedSpace K).surjective x
  change (InfiniteAdeleRing.ringEquiv_mixedSpace L (infiniteAdeleEquiv e
    ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm
      (InfiniteAdeleRing.ringEquiv_mixedSpace K y)))).2 w = _
  rw [RingEquiv.symm_apply_apply]
  exact ringEquiv_mixedSpace_infiniteAdeleEquiv_snd e y w

/-- Real mixed coordinates of arithmetic transport. -/
theorem mixedEquiv_fst (e : K ≃+* L) (x : mixedEmbedding.mixedSpace K)
    (w : {w : NumberField.InfinitePlace L // NumberField.InfinitePlace.IsReal w}) :
    (ArchimedeanGLTransport.mixedEquiv e x).1 w = x.1 (realPlace e w) := by
  obtain ⟨y, rfl⟩ := (InfiniteAdeleRing.ringEquiv_mixedSpace K).surjective x
  change (InfiniteAdeleRing.ringEquiv_mixedSpace L (infiniteAdeleEquiv e
    ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm
      (InfiniteAdeleRing.ringEquiv_mixedSpace K y)))).1 w = _
  rw [RingEquiv.symm_apply_apply]
  exact mixedSpace_infiniteAdeleEquiv_fst e y w

omit [NumberField K] [NumberField L] in
theorem complexPlace_injective (e : K ≃+* L) : Function.Injective (complexPlace e) := by
  intro w w' h
  exact Subtype.ext ((infinitePlaceEquiv e).injective (congrArg Subtype.val h))

private theorem starRingEnd_one_apply {n : ℕ} (i j : Fin n) :
    starRingEnd ℂ ((1 : Matrix (Fin n) (Fin n) ℂ) i j) = (1 : Matrix (Fin n) (Fin n) ℂ) i j := by
  rw [Matrix.one_apply]
  split_ifs <;> simp

/-! ## The single-place compact and Lie inclusions -/

variable (n : ℕ)

open Classical in
/-- The unitary matrix at `w` corresponding to `k` at the place `w ∘ e` of `K`. -/
def placeUnitary (e : K ≃+* L) (w : CPL) (k : Matrix.unitaryGroup (Fin n) ℂ) :
    Matrix.unitaryGroup (Fin n) ℂ :=
  if IsAligned e w then k
  else ⟨matrixConj n (k : Matrix (Fin n) (Fin n) ℂ), matrixConj_mem_unitaryGroup k.2⟩

open Classical in
/-- Arithmetic transport of the unitary factor at `w ∘ e` is the unitary factor at `w`, read
through `placeUnitary`. -/
theorem compactEquiv_complexPlaceCompactInclusion (e : K ≃+* L) (w : CPL)
    (k : Matrix.unitaryGroup (Fin n) ℂ) :
    compactEquiv n e (complexPlaceCompactInclusion K n (complexPlace e w) k) =
      complexPlaceCompactInclusion L n w (placeUnitary n e w k) := by
  apply Subtype.ext
  apply (archimedeanGLCoordinates L n).injective
  apply Units.ext
  apply Matrix.ext
  intro i j
  apply Prod.ext
  · funext w'
    have hl := congrFun (congrFun
      (realMatrix_complexPlaceCompactInclusion K n (complexPlace e w) (realPlace e w') k) i) j
    have hr := congrFun (congrFun
      (realMatrix_complexPlaceCompactInclusion L n w w' (placeUnitary n e w k)) i) j
    change (InfiniteAdeleRing.ringEquiv_mixedSpace L (infiniteAdeleEquiv e
      ((complexPlaceCompactInclusion K n (complexPlace e w) k).val i j))).1 w' = _
    rw [mixedSpace_infiniteAdeleEquiv_fst]
    exact hl.trans hr.symm
  · funext w'
    have hl := congrFun (congrFun
      (complexMatrix_complexPlaceCompactInclusion K n (complexPlace e w) (complexPlace e w') k) i) j
    have hr := congrFun (congrFun
      (complexMatrix_complexPlaceCompactInclusion L n w w' (placeUnitary n e w k)) i) j
    change (InfiniteAdeleRing.ringEquiv_mixedSpace L (infiniteAdeleEquiv e
      ((complexPlaceCompactInclusion K n (complexPlace e w) k).val i j))).2 w' =
        ArchimedeanGL.complexMatrix L n
          (archimedeanGLCoordinates L n (complexPlaceCompactInclusion L n w
            (placeUnitary n e w k)).val) w' i j
    rw [ringEquiv_mixedSpace_infiniteAdeleEquiv_snd, hr]
    change (if IsAligned e w' then ArchimedeanGL.complexMatrix K n
        (archimedeanGLCoordinates K n (complexPlaceCompactInclusion K n (complexPlace e w) k).val)
          (complexPlace e w') i j
      else starRingEnd ℂ (ArchimedeanGL.complexMatrix K n
        (archimedeanGLCoordinates K n (complexPlaceCompactInclusion K n (complexPlace e w) k).val)
          (complexPlace e w') i j)) = _
    rw [hl]
    by_cases hw : w' = w
    · subst hw
      simp only [Pi.mulSingle_eq_same, placeUnitary]
      split_ifs <;> rfl
    · have hu : complexPlace e w' ≠ complexPlace e w := fun h => hw (complexPlace_injective e h)
      rw [Pi.mulSingle_eq_of_ne hu, Pi.mulSingle_eq_of_ne hw]
      split_ifs
      · rfl
      · exact starRingEnd_one_apply i j

open Classical in
/-- The real direction at `w` corresponding to `X` at the place `w ∘ e` of `K`. -/
def placeMatrix (e : K ≃+* L) (w : CPL) (X : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  if IsAligned e w then X else matrixConj n X

open Classical in
/-- Arithmetic transport of a direction at `w ∘ e` is the direction at `w`, read through
`placeMatrix`. -/
theorem realLieEquiv_complexPlaceLieInclusion (e : K ≃+* L) (w : CPL)
    (X : Matrix (Fin n) (Fin n) ℂ) :
    ArchimedeanLieTransport.realLieEquiv n e
        (ArchimedeanGL.complexPlaceLieInclusion K n (complexPlace e w) X) =
      ArchimedeanGL.complexPlaceLieInclusion L n w (placeMatrix n e w X) := by
  apply (ArchimedeanGL.realLieAlgebraToMatrix L n).injective
  apply Matrix.ext
  intro i j
  rw [ArchimedeanLieTransport.realLieEquiv_entry]
  apply Prod.ext
  · funext w'
    rw [mixedEquiv_fst]
    have hl := congrFun (congrFun
      (ArchimedeanGL.realProjection_complexInclusion K n (realPlace e w') (complexPlace e w) X) i) j
    have hr := congrFun (congrFun
      (ArchimedeanGL.realProjection_complexInclusion L n w' w (placeMatrix n e w X)) i) j
    exact hl.trans hr.symm
  · funext w'
    rw [mixedEquiv_snd]
    have hl := congrFun (congrFun
      (ArchimedeanGL.complexProjection_complexInclusion K n (complexPlace e w')
        (complexPlace e w) X) i) j
    have hr := congrFun (congrFun
      (ArchimedeanGL.complexProjection_complexInclusion L n w' w (placeMatrix n e w X)) i) j
    change (if IsAligned e w' then ArchimedeanGL.complexPlaceLieProjection K n (complexPlace e w')
        (ArchimedeanGL.complexPlaceLieInclusion K n (complexPlace e w) X) i j
      else starRingEnd ℂ (ArchimedeanGL.complexPlaceLieProjection K n (complexPlace e w')
        (ArchimedeanGL.complexPlaceLieInclusion K n (complexPlace e w) X) i j)) =
      ArchimedeanGL.complexPlaceLieProjection L n w'
        (ArchimedeanGL.complexPlaceLieInclusion L n w (placeMatrix n e w X)) i j
    rw [hl, hr]
    by_cases hw : w' = w
    · subst hw
      simp only [Pi.single_eq_same, placeMatrix]
      split_ifs <;> simp
    · have hu : complexPlace e w' ≠ complexPlace e w := fun h => hw (complexPlace_injective e h)
      rw [Pi.single_eq_of_ne hu, Pi.single_eq_of_ne hw]
      split_ifs <;> simp

/-- The complexified form of `realLieEquiv_complexPlaceLieInclusion`. -/
theorem complexLieEquiv_complexPlaceComplexLieInclusion (e : K ≃+* L) (w : CPL)
    (X : Matrix (Fin n) (Fin n) ℂ) :
    ArchimedeanLieTransport.complexLieEquiv n e
        (ArchimedeanGL.complexPlaceComplexLieInclusion K n (complexPlace e w) ((1 : ℂ) ⊗ₜ X)) =
      ArchimedeanGL.complexPlaceComplexLieInclusion L n w ((1 : ℂ) ⊗ₜ placeMatrix n e w X) := by
  rw [ArchimedeanGL.complexPlaceComplexLieInclusion_tmul,
    ArchimedeanLieTransport.complexLieEquiv_tmul, realLieEquiv_complexPlaceLieInclusion,
    ArchimedeanGL.complexPlaceComplexLieInclusion_tmul]

/-! ## Parameters of arithmetic pullbacks -/

section Realization

variable {n}

local instance placeTransportRationalAddCommGroup {F : Type*} [Field F] [NumberField F] :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance placeTransportContinuousAddCommGroup {F : Type*} [Field F] [NumberField F] :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance placeTransportSmoothAddCommGroup {F : Type*} [Field F] [NumberField F] :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance placeTransportFormsAddCommGroup {F : Type*} [Field F] [NumberField F] :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance placeTransportStableAddCommGroup {F : Type*} [Field F] [NumberField F] :
    AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _
local instance placeTransportSpaceAddCommGroup {F : Type*} [Field F] [NumberField F]
    (T : OperatorRealization F n) : AddCommGroup T.Space := Submodule.addCommGroup _

private theorem map_conj_map_conj (ds : List ComplexCharacterData) :
    (ds.map ComplexCharacterData.conj).map ComplexCharacterData.conj = ds := by
  simp [List.map_map, Function.comp_def, Unramified.ComplexCharacterDataLemmas.conj_conj]

/-- The compact action at `w ∘ e` on the arithmetic pullback is the compact action at `w`,
read through `placeUnitary`. -/
theorem complexPlaceCompactRepresentation_arithmeticComapEquiv (e : K ≃+* L)
    (S : OperatorRealization L n) (w : CPL) (k : Matrix.unitaryGroup (Fin n) ℂ)
    (x : S.Space) :
    (S.arithmeticComap e).complexPlaceCompactRepresentation (complexPlace e w) k
        (S.arithmeticComapEquiv e x) =
      S.arithmeticComapEquiv e
        (S.complexPlaceCompactRepresentation w (placeUnitary n e w k) x) := by
  calc (S.arithmeticComap e).complexPlaceCompactRepresentation (complexPlace e w) k
        (S.arithmeticComapEquiv e x)
      = (S.arithmeticComap e).compactRepresentation
          (complexPlaceCompactInclusion K n (complexPlace e w) k)
          (S.arithmeticComapEquiv e x) := rfl
    _ = S.arithmeticComapEquiv e (S.compactRepresentation
          (compactEquiv n e (complexPlaceCompactInclusion K n (complexPlace e w) k)) x) :=
        S.arithmeticComapEquiv_compact e _ x
    _ = S.arithmeticComapEquiv e (S.compactRepresentation
          (complexPlaceCompactInclusion L n w (placeUnitary n e w k)) x) :=
        congrArg (fun g => S.arithmeticComapEquiv e (S.compactRepresentation g x))
          (compactEquiv_complexPlaceCompactInclusion n e w k)
    _ = _ := rfl

/-- The Lie action at `w ∘ e` on the arithmetic pullback is the Lie action at `w`, read
through `placeMatrix`. -/
theorem complexPlaceLieAction_arithmeticComapEquiv (e : K ≃+* L)
    (S : OperatorRealization L n) (w : CPL) (X : Matrix (Fin n) (Fin n) ℂ) (x : S.Space) :
    (S.arithmeticComap e).complexPlaceLieAction (complexPlace e w) ((1 : ℂ) ⊗ₜ X)
        (S.arithmeticComapEquiv e x) =
      S.arithmeticComapEquiv e
        (S.complexPlaceLieAction w ((1 : ℂ) ⊗ₜ placeMatrix n e w X) x) := by
  calc (S.arithmeticComap e).complexPlaceLieAction (complexPlace e w) ((1 : ℂ) ⊗ₜ X)
        (S.arithmeticComapEquiv e x)
      = (S.arithmeticComap e).envelopingAction (ArchimedeanGL.envelopingGenerator K n
          (ArchimedeanGL.complexPlaceComplexLieInclusion K n (complexPlace e w) ((1 : ℂ) ⊗ₜ X)))
          (S.arithmeticComapEquiv e x) := rfl
    _ = S.arithmeticComapEquiv e (S.envelopingAction
          (ArchimedeanLieTransport.envelopingEquiv n e (ArchimedeanGL.envelopingGenerator K n
            (ArchimedeanGL.complexPlaceComplexLieInclusion K n (complexPlace e w)
              ((1 : ℂ) ⊗ₜ X)))) x) :=
        S.arithmeticComapEquiv_differential e _ x
    _ = S.arithmeticComapEquiv e (S.envelopingAction
          (ArchimedeanGL.envelopingGenerator L n (ArchimedeanLieTransport.complexLieEquiv n e
            (ArchimedeanGL.complexPlaceComplexLieInclusion K n (complexPlace e w)
              ((1 : ℂ) ⊗ₜ X)))) x) :=
        congrArg (fun a => S.arithmeticComapEquiv e (S.envelopingAction a x))
          (ArchimedeanLieTransport.envelopingEquiv_generator n e _)
    _ = S.arithmeticComapEquiv e (S.envelopingAction
          (ArchimedeanGL.envelopingGenerator L n (ArchimedeanGL.complexPlaceComplexLieInclusion L n
            w ((1 : ℂ) ⊗ₜ placeMatrix n e w X))) x) :=
        congrArg (fun Y => S.arithmeticComapEquiv e
            (S.envelopingAction (ArchimedeanGL.envelopingGenerator L n Y) x))
          (complexLieEquiv_complexPlaceComplexLieInclusion n e w X)
    _ = _ := rfl

private theorem compactStep (e : K ≃+* L) (S : OperatorRealization L n) (w : CPL)
    {k k' : Matrix.unitaryGroup (Fin n) ℂ} (hk : placeUnitary n e w k = k') (x : S.Space) :
    (S.arithmeticComap e).complexPlaceCompactRepresentation (complexPlace e w) k
        (S.arithmeticComapEquiv e x) =
      S.arithmeticComapEquiv e (S.complexPlaceCompactRepresentation w k' x) := by
  subst hk
  exact complexPlaceCompactRepresentation_arithmeticComapEquiv e S w k x

private theorem lieStep (e : K ≃+* L) (S : OperatorRealization L n) (w : CPL)
    {X X' : Matrix (Fin n) (Fin n) ℂ} (hX : placeMatrix n e w X = X') (x : S.Space) :
    (S.arithmeticComap e).complexPlaceLieAction (complexPlace e w) ((1 : ℂ) ⊗ₜ X)
        (S.arithmeticComapEquiv e x) =
      S.arithmeticComapEquiv e (S.complexPlaceLieAction w ((1 : ℂ) ⊗ₜ X') x) := by
  subst hX
  exact complexPlaceLieAction_arithmeticComapEquiv e S w X x

set_option maxHeartbeats 1600000 in
/-- The arithmetic pullback along `e` of a realization with the standard-module parameter `ds`
at the complex place `w` of `L` has at the corresponding place `w ∘ e` of `K` the parameter
`parameterList e w ds`. The witness is the original embedding of the standard module composed
with the pullback, and in the conjugate case also with precomposition by entrywise conjugation
of `GL_n(ℂ)`. -/
theorem hasComplexPlaceParameter_arithmeticComap (e : K ≃+* L) (S : OperatorRealization L n)
    {w : CPL} {ds : List ComplexCharacterData} (h : S.HasComplexPlaceParameter w ds) :
    (S.arithmeticComap e).HasComplexPlaceParameter (complexPlace e w)
      (parameterList e w ds) := by
  classical
  obtain ⟨hlen, A, hA, hK, hL⟩ := h
  by_cases hal : IsAligned e w
  · have hds : parameterList e w ds = ds := by simp [parameterList, hal]
    rw [hds]
    refine ⟨hlen, (S.arithmeticComapEquiv e).toLinearMap ∘ₗ A,
      (S.arithmeticComapEquiv e).injective.comp hA, fun k f => ⟨(hK k f).1, ?_⟩,
      fun X f => ⟨(hL X f).1, ?_⟩⟩
    · have hk : placeUnitary n e w ⟨((k : Langlands.GeneralLinear n ℂ) :
          Matrix (Fin n) (Fin n) ℂ), k.2⟩ = ⟨_, k.2⟩ := by simp [placeUnitary, hal]
      have h1 := compactStep e S w hk (A f)
      exact (congrArg (S.arithmeticComapEquiv e) (hK k f).2).trans h1.symm
    · have hX : placeMatrix n e w X = X := by simp [placeMatrix, hal]
      have h1 := lieStep e S w hX (A f)
      exact (congrArg (S.arithmeticComapEquiv e) (hL X f).2).trans h1.symm
  · have hds : parameterList e w ds = ds.map ComplexCharacterData.conj := by
      simp [parameterList, hal]
    rw [hds]
    have hmem : ∀ f ∈ complexStandardKFinite n (ds.map ComplexCharacterData.conj),
        conjComp n f ∈ complexStandardKFinite n ds := by
      intro f hf
      have h := conjComp_mem_kFiniteFunctions hf
      rwa [map_conj_map_conj] at h
    let Ψ : complexStandardKFinite n (ds.map ComplexCharacterData.conj) →ₗ[ℂ]
        complexStandardKFinite n ds := (conjComp n).restrict hmem
    have hΨ : Function.Injective Ψ := by
      intro f g hfg
      apply Subtype.ext
      have h := congrArg (fun x : complexStandardKFinite n ds =>
        conjComp n (x : Langlands.GeneralLinear n ℂ → ℂ)) hfg
      simpa [Ψ] using h
    refine ⟨by rw [List.length_map]; exact hlen,
      (S.arithmeticComapEquiv e).toLinearMap ∘ₗ A ∘ₗ Ψ,
      (S.arithmeticComapEquiv e).injective.comp (hA.comp hΨ), fun k f => ?_, fun X f => ?_⟩
    · have hkf := Archimedean.rightTranslation_mem_kFiniteFunctions_complexStandardModule n
        (ds.map ComplexCharacterData.conj) f.2 k.2
      refine ⟨hkf, ?_⟩
      let kc : Archimedean.unitaryCompact ℂ n :=
        ⟨glConj n (k : Langlands.GeneralLinear n ℂ), glConj_mem_unitaryCompact k.2⟩
      obtain ⟨hf', hK'⟩ := hK kc (Ψ f)
      have hΨk : Ψ ⟨_, hkf⟩ = ⟨_, hf'⟩ :=
        Subtype.ext (conjComp_rightTranslation (k : Langlands.GeneralLinear n ℂ) f)
      have hk : placeUnitary n e w ⟨((k : Langlands.GeneralLinear n ℂ) :
          Matrix (Fin n) (Fin n) ℂ), k.2⟩ =
          ⟨((kc : Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ), kc.2⟩ := by
        apply Subtype.ext
        simp [placeUnitary, hal, kc]
      have h1 := compactStep e S w hk (A (Ψ f))
      exact (congrArg (fun y => S.arithmeticComapEquiv e (A y)) hΨk).trans
        ((congrArg (S.arithmeticComapEquiv e) hK').trans h1.symm)
    · have hXf := Archimedean.rightDerivative_mem_kFiniteFunctions_complexStandardModule n
        (ds.map ComplexCharacterData.conj) f.2 X
      refine ⟨hXf, ?_⟩
      have hLX := hL (matrixConj n X) (Ψ f)
      obtain ⟨hf', hL'⟩ := hLX
      have hsm : ContMDiff (Archimedean.matrixModel ℂ n) 𝓘(ℝ, ℂ) ∞
          (f : Langlands.GeneralLinear n ℂ → ℂ) :=
        contMDiff_of_mem_kFiniteFunctions f.2
      have hΨX0 : conjComp n (Archimedean.rightDerivative (Archimedean.matrixModel ℂ n) X
            (f : Langlands.GeneralLinear n ℂ → ℂ)) =
          Archimedean.rightDerivative (Archimedean.matrixModel ℂ n) (matrixConj n X)
            (conjComp n (f : Langlands.GeneralLinear n ℂ → ℂ)) :=
        conjComp_rightDerivative hsm X
      have hΨX : Ψ ⟨_, hXf⟩ = ⟨_, hf'⟩ := Subtype.ext hΨX0
      have hX : placeMatrix n e w X = matrixConj n X := by simp [placeMatrix, hal]
      have h1 := lieStep e S w hX (A (Ψ f))
      exact (congrArg (fun y => S.arithmeticComapEquiv e (A y)) hΨX).trans
        ((congrArg (S.arithmeticComapEquiv e) hL').trans h1.symm)

/-- The form of `hasComplexPlaceParameter_arithmeticComap` for actual cuspidal
realizations and their isomorphism classes. -/
theorem cuspidal_hasComplexPlaceParameter_arithmeticComap
    [CompactSpace (AdeleQuotient K)] [CompactSpace (AdeleQuotient L)] {r : ℕ}
    (e : K ≃+* L) (S : CuspidalOperatorRealization L r) {w : CPL}
    {ds : List ComplexCharacterData} (h : S.isoClass.HasComplexPlaceParameter w ds) :
    (S.arithmeticComap e).isoClass.HasComplexPlaceParameter (complexPlace e w)
      (parameterList e w ds) :=
  hasComplexPlaceParameter_arithmeticComap e S.realization h

end Realization

/-- The pullback along `e` of a Hecke character with parameter `d` at the complex place `w`
of `L` has at the corresponding place `w ∘ e` of `K` the parameter `parameter e w d`. -/
theorem hasComplexPlaceParameter_comap (e : K ≃+* L) {χ : HeckeCharacter L} {w : CPL}
    {d : ComplexCharacterData} (h : χ.HasComplexPlaceParameter w d) :
    (HeckeCharacter.comap e χ).HasComplexPlaceParameter (complexPlace e w)
      (parameter e w d) := by
  classical
  intro x
  change (HeckeCharacter.comap e χ).infiniteComponent (infinitePlaceEquiv e w.1) x = _
  rw [HeckeCharacter.comap_infiniteComponent, h]
  unfold parameter
  split_ifs with hal
  · congr 1
    apply Units.ext
    change extensionEmbedding w.1 (infiniteCompletionEquiv e w.1
        x.val) =
      extensionEmbedding (infinitePlaceEquiv e w.1) x.val
    rw [infiniteCompletionEquiv_apply]
    exact extensionEmbedding_infiniteCompletionMap_of_isAligned e w hal _
  · change _ = d.character (complexConjugation _)
    congr 1
    apply Units.ext
    rw [coe_complexConjugation]
    change extensionEmbedding w.1 (infiniteCompletionEquiv e w.1
        x.val) =
      starRingEnd ℂ (extensionEmbedding (infinitePlaceEquiv e w.1)
        x.val)
    rw [infiniteCompletionEquiv_apply]
    exact extensionEmbedding_infiniteCompletionMap_of_not_isAligned e w hal _

/-! ## Induced parameter lists along compatible isomorphisms -/

section Lists

omit [NumberField K] [NumberField L] in
/-- Reading lists at another place preserves `List.Perm`. -/
theorem perm_parameterList {e : K ≃+* L} {w : CPL} {l₁ l₂ : List ComplexCharacterData}
    (h : l₁.Perm l₂) : (parameterList e w l₁).Perm (parameterList e w l₂) := by
  classical
  unfold parameterList
  split_ifs
  · exact h
  · exact h.map _

omit [NumberField K] [NumberField L] in
theorem parameterList_flatten_ofFn (e : K ≃+* L) (w : CPL) {d : ℕ}
    (f : Fin d → List ComplexCharacterData) :
    parameterList e w (List.ofFn f).flatten =
      (List.ofFn fun i => parameterList e w (f i)).flatten := by
  classical
  unfold parameterList
  split_ifs
  · rfl
  · rw [List.map_flatten, List.map_ofFn]
    rfl

end Lists

section Compatible

variable {K₁ : Type u₁} {L₁ : Type u₂} {K₂ : Type u₃} {L₂ : Type u₄}
  [Field K₁] [NumberField K₁] [Field L₁] [NumberField L₁] [Algebra K₁ L₁]
  [Field K₂] [NumberField K₂] [Field L₂] [NumberField L₂] [Algebra K₂ L₂]
  (e : K₁ ≃+* K₂) (e' : L₁ ≃+* L₂)
  (he : ∀ x, e' (algebraMap K₁ L₁ x) = algebraMap K₂ L₂ (e x))

omit [NumberField K₁] [NumberField L₁] [NumberField K₂] [NumberField L₂] in
private theorem liesOver_of_comap_eq {F : Type*} {E : Type*} [Field F] [Field E] [Algebra F E]
    {q : NumberField.InfinitePlace E} {p : NumberField.InfinitePlace F}
    (h : q.comap (algebraMap F E) = p) : q.LiesOver p := by
  constructor
  rw [← h]
  ext x
  rfl

include he in
omit [NumberField K₁] [NumberField L₁] [NumberField K₂] [NumberField L₂] in
private theorem algebraMap_symm (x : K₂) :
    e'.symm (algebraMap K₂ L₂ x) = algebraMap K₁ L₁ (e.symm x) := by
  apply e'.injective
  rw [e'.apply_symm_apply, he, e.apply_symm_apply]

/-- The places of `L₁` above the complex place `v` of `K₁` correspond under `e'` to the
places of `L₂` above the corresponding place `v ∘ e⁻¹` of `K₂`. -/
def placesAboveEquiv (v : {v : NumberField.InfinitePlace K₁ //
      NumberField.InfinitePlace.IsComplex v}) :
    InfinitePlacesAbove L₁ v.1 ≃ InfinitePlacesAbove L₂ (complexPlace e.symm v).1 where
  toFun w := ⟨infinitePlaceEquiv e'.symm w.1, by
    have := w.2
    apply liesOver_of_comap_eq
    have hc : e'.symm.toRingHom.comp (algebraMap K₂ L₂) =
        (algebraMap K₁ L₁).comp e.symm.toRingHom := RingHom.ext (algebraMap_symm e e' he)
    change (w.1.comap e'.symm.toRingHom).comap (algebraMap K₂ L₂) = v.1.comap e.symm.toRingHom
    rw [← NumberField.InfinitePlace.comap_comp, hc, NumberField.InfinitePlace.comap_comp,
      NumberField.InfinitePlace.LiesOver.comap_eq w.1 v.1]⟩
  invFun w := ⟨infinitePlaceEquiv e' w.1, by
    have := w.2
    apply liesOver_of_comap_eq
    have hc : e'.toRingHom.comp (algebraMap K₁ L₁) = (algebraMap K₂ L₂).comp e.toRingHom :=
      RingHom.ext he
    change (w.1.comap e'.toRingHom).comap (algebraMap K₁ L₁) = v.1
    rw [← NumberField.InfinitePlace.comap_comp, hc, NumberField.InfinitePlace.comap_comp,
      NumberField.InfinitePlace.LiesOver.comap_eq w.1 (complexPlace e.symm v).1]
    ext x
    change v.1 (e.symm (e x)) = v.1 x
    rw [e.symm_apply_apply]⟩
  left_inv w := by
    apply Subtype.ext
    ext x
    change w.1 (e'.symm (e' x)) = w.1 x
    rw [e'.symm_apply_apply]
  right_inv w := by
    apply Subtype.ext
    ext x
    change w.1 (e' (e'.symm x)) = w.1 x
    rw [e'.apply_symm_apply]

omit [NumberField K₁] [NumberField L₁] [NumberField K₂] [NumberField L₂] in
/-- Two embeddings defining the same complex place agree exactly when both or neither are
the selected embedding of the place. -/
private theorem eq_iff_of_mk_eq {F : Type*} [Field F] (u : NumberField.InfinitePlace F)
    (hu : u.IsComplex) {X Y : F →+* ℂ} (hX : NumberField.InfinitePlace.mk X = u)
    (hY : NumberField.InfinitePlace.mk Y = u) :
    X = Y ↔ (X = u.embedding ↔ Y = u.embedding) := by
  have hne : ComplexEmbedding.conjugate u.embedding ≠ u.embedding := fun h =>
    (not_isReal_iff_isComplex.mpr hu) (isReal_iff.mpr (ComplexEmbedding.isReal_iff.mpr h))
  have h2 : ∀ {Z : F →+* ℂ}, NumberField.InfinitePlace.mk Z = u →
      Z = u.embedding ∨ Z = ComplexEmbedding.conjugate u.embedding := by
    intro Z hZ
    rcases mk_eq_iff.mp (hZ.trans u.mk_embedding.symm) with h | h
    · exact Or.inl h
    · exact Or.inr (by rw [← h]; exact (star_star Z).symm)
  rcases h2 hX with rfl | rfl <;> rcases h2 hY with rfl | rfl <;> simp [hne, Ne.symm hne]

private theorem iff_aux {a b c : Prop} : (b ↔ (a ↔ b)) ↔ (c ↔ (a ↔ c)) := by
  tauto

omit [NumberField K₂] in
/-- The orientation bookkeeping of one place: the parities of the four identity-or-conjugation
choices (at `v` along `e⁻¹`, from `w` to `v`, from the corresponding place of `L₂` to
`v ∘ e⁻¹`, and at `w` along `e'⁻¹`) agree. -/
theorem isAligned_iff_iff (v : {v : NumberField.InfinitePlace K₁ //
      NumberField.InfinitePlace.IsComplex v}) (w : InfinitePlacesAbove L₁ v.1) :
    (IsAligned e.symm v ↔ w.1.embedding.comp (algebraMap K₁ L₁) = v.1.embedding) ↔
      ((placesAboveEquiv e e' he v w).1.embedding.comp (algebraMap K₂ L₂) =
          (complexPlace e.symm v).1.embedding ↔
        IsAligned e'.symm (complexPlaceAbove v w)) := by
  have := w.2
  let u := complexPlace e.symm v
  let w₂ := placesAboveEquiv e e' he v w
  have := w₂.2
  let V : K₂ →+* ℂ := v.1.embedding.comp e.symm.toRingHom
  let P : K₂ →+* ℂ := (w.1.embedding.comp (algebraMap K₁ L₁)).comp e.symm.toRingHom
  let Qm : K₂ →+* ℂ := w₂.1.embedding.comp (algebraMap K₂ L₂)
  let Φ : L₂ →+* ℂ := w.1.embedding.comp e'.symm.toRingHom
  have hmkV : NumberField.InfinitePlace.mk V = u.1 := by
    change NumberField.InfinitePlace.mk (v.1.embedding.comp e.symm.toRingHom) =
      v.1.comap e.symm.toRingHom
    rw [← comap_mk, mk_embedding]
  have hmkP : NumberField.InfinitePlace.mk P = u.1 := by
    change NumberField.InfinitePlace.mk ((w.1.embedding.comp (algebraMap K₁ L₁)).comp
      e.symm.toRingHom) = v.1.comap e.symm.toRingHom
    rw [← comap_mk, ← comap_mk, mk_embedding,
      NumberField.InfinitePlace.LiesOver.comap_eq w.1 v.1]
  have hmkQ : NumberField.InfinitePlace.mk Qm = u.1 := by
    change NumberField.InfinitePlace.mk (w₂.1.embedding.comp (algebraMap K₂ L₂)) = u.1
    rw [← comap_mk, mk_embedding, NumberField.InfinitePlace.LiesOver.comap_eq w₂.1 u.1]
  have hmkΦ : NumberField.InfinitePlace.mk Φ = w₂.1 := by
    change NumberField.InfinitePlace.mk (w.1.embedding.comp e'.symm.toRingHom) =
      w.1.comap e'.symm.toRingHom
    rw [← comap_mk, mk_embedding]
  have hP : P = Φ.comp (algebraMap K₂ L₂) := by
    apply RingHom.ext
    intro x
    change w.1.embedding (algebraMap K₁ L₁ (e.symm x)) =
      w.1.embedding (e'.symm (algebraMap K₂ L₂ x))
    rw [algebraMap_symm e e' he]
  have h2 : w.1.embedding.comp (algebraMap K₁ L₁) = v.1.embedding ↔ P = V := by
    constructor
    · intro h
      change (w.1.embedding.comp (algebraMap K₁ L₁)).comp e.symm.toRingHom =
        v.1.embedding.comp e.symm.toRingHom
      rw [h]
    · intro h
      apply RingHom.ext
      intro x
      have hx := RingHom.congr_fun h (e x)
      change w.1.embedding (algebraMap K₁ L₁ (e.symm (e x))) = v.1.embedding (e.symm (e x)) at hx
      rwa [e.symm_apply_apply] at hx
  have hPreal : ¬ComplexEmbedding.IsReal P := isComplex_mk_iff.mp (hmkP ▸ u.2)
  have h4 : IsAligned e'.symm (complexPlaceAbove v w) ↔ P = Qm := by
    change Φ = w₂.1.embedding ↔ P = Qm
    constructor
    · intro h
      rw [hP, h]
    · intro h
      rcases mk_eq_iff.mp (hmkΦ.trans w₂.1.mk_embedding.symm) with hΦ | hΦ
      · exact hΦ
      · exfalso
        apply hPreal
        rw [ComplexEmbedding.isReal_iff]
        have hQ : Qm = ComplexEmbedding.conjugate P := by
          change w₂.1.embedding.comp (algebraMap K₂ L₂) = _
          rw [← hΦ, hP]
          rfl
        rw [← hQ, h]
  have hV := eq_iff_of_mk_eq u.1 u.2 (X := P) (Y := V) hmkP hmkV
  have hQ := eq_iff_of_mk_eq u.1 u.2 (X := P) (Y := Qm) hmkP hmkQ
  change (V = u.1.embedding ↔ _) ↔ (Qm = u.1.embedding ↔ _)
  rw [h2, h4, hV, hQ]
  exact iff_aux

/-- One induced block: reading the block of `w` in the coordinates of `v` and then at
`v ∘ e⁻¹` is reading it at the corresponding place of `L₂` and then in the coordinates of
`v ∘ e⁻¹`. -/
theorem parameterList_complexPlaceParameterTransport
    (v : {v : NumberField.InfinitePlace K₁ // NumberField.InfinitePlace.IsComplex v})
    (w : InfinitePlacesAbove L₁ v.1) (x : ComplexCharacterData) :
    parameterList e.symm v (complexPlaceParameterTransport v w [x]) =
      complexPlaceParameterTransport (complexPlace e.symm v) (placesAboveEquiv e e' he v w)
        [parameter e'.symm (complexPlaceAbove v w) x] := by
  classical
  have key := isAligned_iff_iff e e' he v w
  unfold parameterList complexPlaceParameterTransport parameter
  split_ifs <;> simp_all [Unramified.ComplexCharacterDataLemmas.conj_conj]

/-- The Langlands sum of singletons above `v`, read at `v ∘ e⁻¹`, is the Langlands sum above
`v ∘ e⁻¹` of the singletons read along `e'⁻¹`, in the transported enumeration. -/
theorem parameterList_complexPlaceLanglandsSum
    (v : {v : NumberField.InfinitePlace K₁ // NumberField.InfinitePlace.IsComplex v}) {d : ℕ}
    (en : Fin d ≃ InfinitePlacesAbove L₁ v.1)
    (dξ : InfinitePlacesAbove L₁ v.1 → ComplexCharacterData) :
    parameterList e.symm v (complexPlaceLanglandsSum v en fun w => [dξ w]) =
      complexPlaceLanglandsSum (complexPlace e.symm v) (en.trans (placesAboveEquiv e e' he v))
        fun w => [parameter e'.symm (complexPlaceAbove v ((placesAboveEquiv e e' he v).symm w))
          (dξ ((placesAboveEquiv e e' he v).symm w))] := by
  unfold complexPlaceLanglandsSum
  rw [parameterList_flatten_ofFn]
  congr 1
  congr 1
  funext i
  simp only [Equiv.trans_apply, Equiv.symm_apply_apply]
  exact parameterList_complexPlaceParameterTransport e e' he v (en i) (dξ (en i))

end Compatible

end Langlands.Automorphic.ComplexPlaceArithmeticTransport
