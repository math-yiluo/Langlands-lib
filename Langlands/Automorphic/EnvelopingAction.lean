import Langlands.Automorphic.FiniteLevelSlices
import Langlands.Global.ArchimedeanEnvelopingLawsProof

/-! # Genuine differential action on finite-smooth adelic functions -/

noncomputable section
universe u

namespace Langlands.Automorphic

open Langlands.Global NumberField ContinuousRationalFunctions

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

/-- The actual smooth infinite slice of a finite-smooth adelic function. -/
def finiteSmoothSlice (b : FiniteAdelicGL K n) :
    FiniteSmoothRationalFunctions K n →ₗ[ℂ] ArchimedeanGL.SmoothFunctions K n where
  toFun f := ⟨infiniteSlice K n b f.val, by
    have h := f.property.1
    change f.val ∈ (⨅ b : FiniteAdelicGL K n,
      (ArchimedeanGL.smoothFunctions K n).comap (infiniteSlice K n b)) at h
    exact (Submodule.mem_iInf _).mp h b⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem finiteSmoothSlice_apply (b : FiniteAdelicGL K n)
    (f : FiniteSmoothRationalFunctions K n) (a : InfiniteAdelicGL K n) :
    (finiteSmoothSlice K n b f).val a =
      evaluate K n f.val (AdelicGL.pair K n a b) := rfl

@[simp]
theorem finiteSmoothSlice_reconstruct (L : OpenSubgroup (FiniteAdelicGL K n))
    (F : FiniteLevelSmoothSliceFamilies K n L) (b : FiniteAdelicGL K n) :
    finiteSmoothSlice K n b (reconstructFiniteSmoothSlices K n L F) = F.val b := by
  apply Subtype.ext
  funext a
  exact evaluate_reconstructFiniteSmoothSlices K n L F a b

/-- The slice-family map is faithful to actual adelic functions. -/
theorem finiteSmoothSlice_injective :
    Function.Injective (fun f : FiniteSmoothRationalFunctions K n =>
      fun b => finiteSmoothSlice K n b f) := by
  intro f g h
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  funext x
  have he := congrArg (fun F =>
    (F (AdelicGL.finite K n x) : ArchimedeanGL.SmoothFunctions K n).val
      (AdelicGL.infinite K n x)) h
  change evaluate K n f.val x = evaluate K n g.val x
  simpa only [finiteSmoothSlice_apply, AdelicGL.pair_projections] using he

/-- Each finite-smooth function yields a rational-covariant family at any level fixing it. -/
def slicesAtLevel (L : OpenSubgroup (FiniteAdelicGL K n))
    (f : FiniteSmoothRationalFunctions K n)
    (hf : f.val ∈ levelSubmodule K n L.toSubgroup) :
    FiniteLevelSmoothSliceFamilies K n L :=
  ⟨fun b => finiteSmoothSlice K n b f, by
    constructor
    · intro b l
      apply Subtype.ext
      funext a
      have h := congrArg (fun g : ContinuousRationalFunctions K n =>
        evaluate K n g (AdelicGL.pair K n a b)) (hf l)
      change evaluate K n f.val (AdelicGL.pair K n a b * AdelicGL.ofFinite K n l.val) =
        evaluate K n f.val (AdelicGL.pair K n a b) at h
      simpa only [finiteSmoothSlice_apply, AdelicGL.ofFinite_eq_pair,
        AdelicGL.pair_mul, mul_one] using h
    · intro γ b a
      have h := evaluate_rational K n f.val γ (AdelicGL.pair K n a b)
      rw [← AdelicGL.pair_projections K n (AdelicGL.rational K n γ),
        AdelicGL.pair_mul] at h
      exact h⟩

/-- The genuine enveloping differential preserves a family's covariance and fixed level. -/
def differentiateSliceFamily (L : OpenSubgroup (FiniteAdelicGL K n))
    (u : ArchimedeanGL.EnvelopingAlgebra K n) :
    FiniteLevelSmoothSliceFamilies K n L →ₗ[ℂ]
      FiniteLevelSmoothSliceFamilies K n L where
  toFun F := ⟨fun b => ArchimedeanGL.envelopingAction K n u (F.val b), by
    constructor
    · intro b l
      dsimp only
      rw [F.property.1 b l]
    · intro γ b a
      have hcov :
          ArchimedeanGL.smoothLeftTranslation K n
            (AdelicGL.infinite K n (AdelicGL.rational K n γ))
            (F.val (AdelicGL.finite K n (AdelicGL.rational K n γ) * b)) = F.val b := by
        apply Subtype.ext
        funext x
        exact F.property.2 γ b x
      rw [← ArchimedeanGL.envelopingAction_leftTranslation_eval, hcov]⟩
  map_add' F G := by
    apply Subtype.ext
    funext b
    exact map_add _ _ _
  map_smul' c F := by
    apply Subtype.ext
    funext b
    exact (ArchimedeanGL.envelopingAction K n u).map_smul c (F.val b)

/-- Choose a finite stabilizer solely to establish joint continuity of differentiation. -/
def finiteSmoothDifferential (u : ArchimedeanGL.EnvelopingAlgebra K n)
    (f : FiniteSmoothRationalFunctions K n) : FiniteSmoothRationalFunctions K n :=
  let L := Classical.choose f.property.2
  let hL := Classical.choose_spec f.property.2
  reconstructFiniteSmoothSlices K n L
    (differentiateSliceFamily K n L u (slicesAtLevel K n L f hL))

@[simp]
theorem finiteSmoothSlice_differential (u : ArchimedeanGL.EnvelopingAlgebra K n)
    (f : FiniteSmoothRationalFunctions K n) (b : FiniteAdelicGL K n) :
    finiteSmoothSlice K n b (finiteSmoothDifferential K n u f) =
      ArchimedeanGL.envelopingAction K n u (finiteSmoothSlice K n b f) := by
  apply Subtype.ext
  funext a
  exact evaluate_reconstructFiniteSmoothSlices K n _ _ a b

/-- The actual adelic differential is independent of the stabilizer used to reconstruct it. -/
theorem finiteSmoothDifferential_eq_reconstruct
    (u : ArchimedeanGL.EnvelopingAlgebra K n) (L : OpenSubgroup (FiniteAdelicGL K n))
    (f : FiniteSmoothRationalFunctions K n)
    (hf : f.val ∈ levelSubmodule K n L.toSubgroup) :
    finiteSmoothDifferential K n u f = reconstructFiniteSmoothSlices K n L
      (differentiateSliceFamily K n L u (slicesAtLevel K n L f hf)) := by
  apply finiteSmoothSlice_injective K n
  funext b
  dsimp only
  rw [finiteSmoothSlice_differential, finiteSmoothSlice_reconstruct]
  rfl

/-- The genuine universal enveloping action on actual finite-smooth adelic functions. -/
def finiteSmoothEnvelopingAction :
    ArchimedeanGL.EnvelopingAlgebra K n →ₐ[ℂ]
      Module.End ℂ (FiniteSmoothRationalFunctions K n) where
  toFun u :=
    { toFun := finiteSmoothDifferential K n u
      map_add' f g := by
        apply finiteSmoothSlice_injective K n
        funext b
        dsimp only
        simp only [finiteSmoothSlice_differential, map_add]
      map_smul' c f := by
        apply finiteSmoothSlice_injective K n
        funext b
        dsimp only
        simp only [finiteSmoothSlice_differential, map_smul, RingHom.id_apply] }
  map_one' := by
    apply LinearMap.ext
    intro f
    apply finiteSmoothSlice_injective K n
    funext b
    change finiteSmoothSlice K n b (finiteSmoothDifferential K n 1 f) =
      finiteSmoothSlice K n b f
    rw [finiteSmoothSlice_differential, map_one, Module.End.one_apply]
  map_mul' u v := by
    apply LinearMap.ext
    intro f
    apply finiteSmoothSlice_injective K n
    funext b
    change finiteSmoothSlice K n b (finiteSmoothDifferential K n (u * v) f) =
      finiteSmoothSlice K n b
        (finiteSmoothDifferential K n u (finiteSmoothDifferential K n v f))
    simp only [finiteSmoothSlice_differential, map_mul, Module.End.mul_apply]
  map_zero' := by
    apply LinearMap.ext
    intro f
    apply finiteSmoothSlice_injective K n
    funext b
    change finiteSmoothSlice K n b (finiteSmoothDifferential K n 0 f) =
      finiteSmoothSlice K n b 0
    simp only [finiteSmoothSlice_differential, map_zero, LinearMap.zero_apply]
  map_add' u v := by
    apply LinearMap.ext
    intro f
    apply finiteSmoothSlice_injective K n
    funext b
    change finiteSmoothSlice K n b (finiteSmoothDifferential K n (u + v) f) =
      finiteSmoothSlice K n b
        (finiteSmoothDifferential K n u f + finiteSmoothDifferential K n v f)
    simp only [finiteSmoothSlice_differential, map_add, LinearMap.add_apply]
  commutes' c := by
    apply LinearMap.ext
    intro f
    apply finiteSmoothSlice_injective K n
    funext b
    change finiteSmoothSlice K n b
        (finiteSmoothDifferential K n (algebraMap ℂ _ c) f) =
      finiteSmoothSlice K n b (c • f)
    rw [finiteSmoothSlice_differential, AlgHom.commutes, map_smul]
    rfl

@[simp]
theorem finiteSmoothSlice_envelopingAction (u : ArchimedeanGL.EnvelopingAlgebra K n)
    (f : FiniteSmoothRationalFunctions K n) (b : FiniteAdelicGL K n) :
    finiteSmoothSlice K n b (finiteSmoothEnvelopingAction K n u f) =
      ArchimedeanGL.envelopingAction K n u (finiteSmoothSlice K n b f) :=
  finiteSmoothSlice_differential K n u f b

theorem evaluate_finiteSmoothEnvelopingAction (u : ArchimedeanGL.EnvelopingAlgebra K n)
    (f : FiniteSmoothRationalFunctions K n) (a : InfiniteAdelicGL K n)
    (b : FiniteAdelicGL K n) :
    evaluate K n (finiteSmoothEnvelopingAction K n u f).val (AdelicGL.pair K n a b) =
      (ArchimedeanGL.envelopingAction K n u (finiteSmoothSlice K n b f)).val a :=
  congrArg (fun s : ArchimedeanGL.SmoothFunctions K n => s.val a)
    (finiteSmoothSlice_envelopingAction K n u f b)

/-- Every specified open finite level is preserved by the actual differential. -/
theorem finiteSmoothEnvelopingAction_preserves_level
    (u : ArchimedeanGL.EnvelopingAlgebra K n) (L : OpenSubgroup (FiniteAdelicGL K n))
    (f : FiniteSmoothRationalFunctions K n)
    (hf : f.val ∈ levelSubmodule K n L.toSubgroup) :
    (finiteSmoothEnvelopingAction K n u f).val ∈ levelSubmodule K n L.toSubgroup := by
  intro l
  apply Subtype.ext
  apply Subtype.ext
  funext x
  change evaluate K n (finiteSmoothEnvelopingAction K n u f).val
      (x * AdelicGL.ofFinite K n l.val) =
    evaluate K n (finiteSmoothEnvelopingAction K n u f).val x
  rw [← AdelicGL.pair_projections K n x, AdelicGL.ofFinite_eq_pair,
    AdelicGL.pair_mul]
  simp only [mul_one, evaluate_finiteSmoothEnvelopingAction]
  have h : finiteSmoothSlice K n (AdelicGL.finite K n x * l.val) f =
      finiteSmoothSlice K n (AdelicGL.finite K n x) f :=
    (slicesAtLevel K n L f hf).property.1 _ l
  rw [h]

/-- Compact finite level, when present, is retained with the same subgroup. -/
theorem finiteSmoothEnvelopingAction_hasFiniteLevel
    (u : ArchimedeanGL.EnvelopingAlgebra K n) (f : FiniteSmoothRationalFunctions K n)
    (hf : HasFiniteLevel K n f.val) :
    HasFiniteLevel K n (finiteSmoothEnvelopingAction K n u f).val := by
  obtain ⟨L, ho, hc, hL⟩ := hf
  exact ⟨L, ho, hc, finiteSmoothEnvelopingAction_preserves_level K n u ⟨L, ho⟩ f hL⟩

/-- On a real Lie generator the descended action is the actual coordinate derivative. -/
theorem evaluate_finiteSmoothEnvelopingAction_real_generator
    (X : ArchimedeanGL.RealLieAlgebra K n) (f : FiniteSmoothRationalFunctions K n)
    (a : InfiniteAdelicGL K n) (b : FiniteAdelicGL K n) :
    evaluate K n (finiteSmoothEnvelopingAction K n
      (ArchimedeanGL.envelopingGenerator K n (ArchimedeanGL.complexify K n X)) f).val
        (AdelicGL.pair K n a b) =
      fderiv ℝ (ArchimedeanGL.coordinateExtension K n (finiteSmoothSlice K n b f))
        (archimedeanGLCoordinates K n a : ArchimedeanMatrix K n)
        ((archimedeanGLCoordinates K n a : ArchimedeanMatrix K n) *
          ArchimedeanGL.realLieAlgebraToMatrix K n X) := by
  rw [evaluate_finiteSmoothEnvelopingAction]
  exact ArchimedeanGL.envelopingAction_real_generator_apply K n X _ a

/-- Restriction to the actual center of the complex enveloping algebra. -/
def finiteSmoothCenterAction :
    ArchimedeanGL.EnvelopingCenter K n →ₐ[ℂ]
      Module.End ℂ (FiniteSmoothRationalFunctions K n) :=
  (finiteSmoothEnvelopingAction K n).comp (ArchimedeanGL.centerInclusion K n)

@[simp]
theorem finiteSmoothSlice_centerAction (z : ArchimedeanGL.EnvelopingCenter K n)
    (f : FiniteSmoothRationalFunctions K n) (b : FiniteAdelicGL K n) :
    finiteSmoothSlice K n b (finiteSmoothCenterAction K n z f) =
      ArchimedeanGL.centerAction K n z (finiteSmoothSlice K n b f) :=
  finiteSmoothSlice_envelopingAction K n (ArchimedeanGL.centerInclusion K n z) f b

end Langlands.Automorphic
