import Langlands.Automorphic.SmoothArithmeticTransport
import Langlands.Automorphic.DifferentialCenterFinite
import Langlands.Global.ArchimedeanDifferentialTransport

/-! # Arithmetic pullback on simultaneous adelic center-finite functions -/

noncomputable section
universe uK uL uM

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic.ContinuousRationalFunctions

open Langlands.Global AdelicGLTransport ArchimedeanLieTransport

variable {K : Type uK} {L : Type uL} {M : Type uM}
variable [Field K] [NumberField K] [Field L] [NumberField L] [Field M] [NumberField M]

/-- Pull back each smooth slice and reindex the entire actual finite-argument family. -/
def sliceFamilyEquiv (n : ℕ) (e : K ≃+* L) :
    SmoothSliceFamily L n ≃ₗ[ℂ] SmoothSliceFamily K n where
  toFun F b := ArchimedeanGLTransport.smoothEquiv n e (F (finiteEquiv n e b))
  invFun F b := (ArchimedeanGLTransport.smoothEquiv n e).symm
    (F ((finiteEquiv n e).symm b))
  left_inv F := by
    funext b
    simp only [ContinuousMulEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply]
  right_inv F := by
    funext b
    simp only [ContinuousMulEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply]
  map_add' F H := by
    funext b
    exact map_add _ _ _
  map_smul' c F := by
    funext b
    exact map_smul _ c _

@[simp] theorem sliceFamilyEquiv_apply (n : ℕ) (e : K ≃+* L)
    (F : SmoothSliceFamily L n) (b : FiniteAdelicGL K n) :
    sliceFamilyEquiv n e F b =
      ArchimedeanGLTransport.smoothComap n e (F (finiteEquiv n e b)) := rfl

@[simp] theorem sliceFamilyEquiv_refl (n : ℕ) :
    sliceFamilyEquiv n (RingEquiv.refl K) = LinearEquiv.refl ℂ _ := by
  apply LinearEquiv.ext
  intro F
  funext b
  simp only [sliceFamilyEquiv_apply, finiteEquiv_refl, ContinuousMulEquiv.refl_apply,
    ArchimedeanGLTransport.smoothComap_refl, LinearEquiv.refl_apply]

theorem sliceFamilyEquiv_trans (n : ℕ) (e : K ≃+* L) (a : L ≃+* M) :
    sliceFamilyEquiv n (e.trans a) =
      (sliceFamilyEquiv n a).trans (sliceFamilyEquiv n e) := by
  apply LinearEquiv.ext
  intro F
  funext b
  simp only [LinearEquiv.trans_apply, sliceFamilyEquiv_apply, finiteEquiv_trans,
    ContinuousMulEquiv.trans_apply, ArchimedeanGLTransport.smoothComap_trans]

@[simp] theorem sliceFamilyEquiv_symm (n : ℕ) (e : K ≃+* L) :
    sliceFamilyEquiv n e.symm = (sliceFamilyEquiv n e).symm := by
  apply LinearEquiv.ext
  intro F
  apply (sliceFamilyEquiv n e).injective
  have h := congrArg (fun E : SmoothSliceFamily K n ≃ₗ[ℂ] SmoothSliceFamily K n => E F)
    (sliceFamilyEquiv_trans n e e.symm)
  simpa using h.symm

/-- Every center operator intertwines on the entire family, with one common arithmetic map. -/
theorem sliceFamilyEquiv_centerFamilyAction (n : ℕ) (e : K ≃+* L)
    (z : ArchimedeanGL.EnvelopingCenter K n) (F : SmoothSliceFamily L n) :
    sliceFamilyEquiv n e (centerFamilyAction L n (centerEquiv n e z) F) =
      centerFamilyAction K n z (sliceFamilyEquiv n e F) := by
  funext b
  exact ArchimedeanDifferentialTransport.smoothComap_centerAction n e z
    (F (finiteEquiv n e b))

/-- The common annihilator is exactly the arithmetic preimage of the target ideal. -/
theorem centerFamilyAnnihilator_sliceFamilyEquiv (n : ℕ) (e : K ≃+* L)
    (F : SmoothSliceFamily L n) :
    centerFamilyAnnihilator K n (sliceFamilyEquiv n e F) =
      Ideal.comap (centerEquiv n e).toRingHom (centerFamilyAnnihilator L n F) := by
  ext z
  change centerFamilyAction K n z (sliceFamilyEquiv n e F) = 0 ↔
    centerFamilyAction L n (centerEquiv n e z) F = 0
  rw [← sliceFamilyEquiv_centerFamilyAction]
  exact (sliceFamilyEquiv n e).map_eq_zero_iff

/-- The full common center orbit, rather than separate slice orbits, is the linear image. -/
theorem centerFamilyOrbitSpan_sliceFamilyEquiv (n : ℕ) (e : K ≃+* L)
    (F : SmoothSliceFamily L n) :
    centerFamilyOrbitSpan K n (sliceFamilyEquiv n e F) =
      (centerFamilyOrbitSpan L n F).map (sliceFamilyEquiv n e).toLinearMap := by
  rw [centerFamilyOrbitSpan_eq_range, centerFamilyOrbitSpan_eq_range]
  apply le_antisymm
  · rintro _ ⟨z, rfl⟩
    exact ⟨centerFamilyAction L n (centerEquiv n e z) F,
      ⟨centerEquiv n e z, rfl⟩, sliceFamilyEquiv_centerFamilyAction n e z F⟩
  · rintro _ ⟨H, ⟨z, rfl⟩, rfl⟩
    obtain ⟨w, rfl⟩ := (centerEquiv n e).surjective z
    exact ⟨w, (sliceFamilyEquiv_centerFamilyAction n e w F).symm⟩

/-- An actual complex-linear equivalence of the full common center-orbit spans. -/
def centerFamilyOrbitEquiv (n : ℕ) (e : K ≃+* L) (F : SmoothSliceFamily L n) :
    centerFamilyOrbitSpan L n F ≃ₗ[ℂ]
      centerFamilyOrbitSpan K n (sliceFamilyEquiv n e F) :=
  (sliceFamilyEquiv n e).ofSubmodules _ _
    (centerFamilyOrbitSpan_sliceFamilyEquiv n e F).symm

/-- Simultaneous center finiteness is preserved and reflected. -/
theorem isCenterFiniteFamily_sliceFamilyEquiv_iff (n : ℕ) (e : K ≃+* L)
    (F : SmoothSliceFamily L n) :
    IsCenterFiniteFamily K n (sliceFamilyEquiv n e F) ↔ IsCenterFiniteFamily L n F :=
  (LinearMap.finite_iff_of_bijective
    (centerFamilyOrbitEquiv n e F).toLinearMap
    (centerFamilyOrbitEquiv n e F).bijective).symm

/-- The family construction is the actual smooth adelic arithmetic pullback on every slice. -/
theorem smoothSliceFamily_smoothEquiv (n : ℕ) (e : K ≃+* L)
    (f : SmoothRationalFunctions L n) :
    smoothSliceFamily K n (smoothEquiv n e f) =
      sliceFamilyEquiv n e (smoothSliceFamily L n f) := by
  funext b
  apply Subtype.ext
  funext a
  exact infiniteSlice_arithmeticComap n e b f.val a

/-- The common annihilating ideal of an actual function transforms by arithmetic preimage. -/
theorem centerFamilyAnnihilator_smoothEquiv (n : ℕ) (e : K ≃+* L)
    (f : SmoothRationalFunctions L n) :
    centerFamilyAnnihilator K n (smoothSliceFamily K n (smoothEquiv n e f)) =
      Ideal.comap (centerEquiv n e).toRingHom
        (centerFamilyAnnihilator L n (smoothSliceFamily L n f)) := by
  rw [smoothSliceFamily_smoothEquiv, centerFamilyAnnihilator_sliceFamilyEquiv]

theorem isCenterFinite_smoothEquiv_iff (n : ℕ) (e : K ≃+* L)
    (f : SmoothRationalFunctions L n) :
    IsCenterFinite K n (smoothEquiv n e f) ↔ IsCenterFinite L n f := by
  change IsCenterFiniteFamily K n (smoothSliceFamily K n (smoothEquiv n e f)) ↔ _
  rw [smoothSliceFamily_smoothEquiv]
  exact isCenterFiniteFamily_sliceFamilyEquiv_iff n e _

private theorem centerFiniteSmoothFunctions_map (n : ℕ) (e : K ≃+* L) :
    (centerFiniteSmoothFunctions L n).map (smoothEquiv n e).toLinearMap =
      centerFiniteSmoothFunctions K n := by
  ext f
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact (isCenterFinite_smoothEquiv_iff n e h).mpr hh
  · intro hf
    obtain ⟨h, rfl⟩ := (smoothEquiv n e).surjective f
    exact ⟨h, (isCenterFinite_smoothEquiv_iff n e h).mp hf, rfl⟩

/-- Genuine pullback on actual simultaneous center-finite smooth adelic functions. -/
def centerFiniteSmoothEquiv (n : ℕ) (e : K ≃+* L) :
    CenterFiniteSmoothRationalFunctions L n ≃L[ℂ] CenterFiniteSmoothRationalFunctions K n :=
  (smoothEquiv n e).ofSubmodules _ _ (centerFiniteSmoothFunctions_map n e)

@[simp] theorem centerFiniteSmoothEquiv_val (n : ℕ) (e : K ≃+* L)
    (f : CenterFiniteSmoothRationalFunctions L n) :
    (centerFiniteSmoothEquiv n e f).val = smoothEquiv n e f.val := rfl

@[simp] theorem evaluate_centerFiniteSmoothEquiv (n : ℕ) (e : K ≃+* L)
    (f : CenterFiniteSmoothRationalFunctions L n) (x : AdelicGL K n) :
    evaluate K n (centerFiniteSmoothEquiv n e f).val.val x =
      evaluate L n f.val.val (adelicEquiv n e x) := rfl

@[simp] theorem evaluate_centerFiniteSmoothEquiv_symm (n : ℕ) (e : K ≃+* L)
    (f : CenterFiniteSmoothRationalFunctions K n) (x : AdelicGL L n) :
    evaluate L n ((centerFiniteSmoothEquiv n e).symm f).val.val x =
      evaluate K n f.val.val (adelicEquiv n e.symm x) := rfl

@[simp] theorem centerFiniteSmoothEquiv_refl (n : ℕ)
    (f : CenterFiniteSmoothRationalFunctions K n) :
    centerFiniteSmoothEquiv n (RingEquiv.refl K) f = f := by
  apply Subtype.ext
  exact smoothEquiv_refl n f.val

theorem centerFiniteSmoothEquiv_trans (n : ℕ) (e : K ≃+* L) (a : L ≃+* M)
    (f : CenterFiniteSmoothRationalFunctions M n) :
    centerFiniteSmoothEquiv n (e.trans a) f =
      centerFiniteSmoothEquiv n e (centerFiniteSmoothEquiv n a f) := by
  apply Subtype.ext
  exact smoothEquiv_trans n e a f.val

@[simp] theorem centerFiniteSmoothEquiv_symm (n : ℕ) (e : K ≃+* L) :
    (centerFiniteSmoothEquiv n e).symm = centerFiniteSmoothEquiv n e.symm := by
  apply ContinuousLinearEquiv.ext
  funext f
  apply Subtype.ext
  rfl

/-- Covariance of the finite adelic action on the simultaneous center-finite space. -/
theorem centerFiniteSmoothEquiv_finiteRightAction (n : ℕ) (e : K ≃+* L)
    (d : FiniteAdelicGL K n) (f : CenterFiniteSmoothRationalFunctions L n) :
    centerFiniteSmoothEquiv n e
        (centerFiniteSmoothFiniteRightAction L n (finiteEquiv n e d) f) =
      centerFiniteSmoothFiniteRightAction K n d (centerFiniteSmoothEquiv n e f) := by
  apply Subtype.ext
  change smoothEquiv n e
      (smoothRightAction L n (AdelicGL.ofFinite L n (finiteEquiv n e d)) f.val) =
    smoothRightAction K n (AdelicGL.ofFinite K n d) (smoothEquiv n e f.val)
  rw [← adelicEquiv_ofFinite]
  exact smoothEquiv_rightAction n e _ f.val

/-- Faithful finite-smooth slices have the same arithmetic pullback formula. -/
theorem finiteSmoothSlice_finiteSmoothEquiv (n : ℕ) (e : K ≃+* L)
    (b : FiniteAdelicGL K n) (f : FiniteSmoothRationalFunctions L n) :
    finiteSmoothSlice K n b (finiteSmoothEquiv n e f) =
      ArchimedeanGLTransport.smoothComap n e
        (finiteSmoothSlice L n (finiteEquiv n e b) f) := by
  apply Subtype.ext
  funext a
  exact infiniteSlice_arithmeticComap n e b f.val a

/-- The actual adelic enveloping action intertwines without choosing compatible stabilizers. -/
theorem finiteSmoothEquiv_envelopingAction (n : ℕ) (e : K ≃+* L)
    (u : ArchimedeanGL.EnvelopingAlgebra K n) (f : FiniteSmoothRationalFunctions L n) :
    finiteSmoothEquiv n e (finiteSmoothEnvelopingAction L n (envelopingEquiv n e u) f) =
      finiteSmoothEnvelopingAction K n u (finiteSmoothEquiv n e f) := by
  apply finiteSmoothSlice_injective K n
  funext b
  simp only [finiteSmoothSlice_finiteSmoothEquiv, finiteSmoothSlice_envelopingAction,
    ArchimedeanDifferentialTransport.smoothComap_envelopingAction]

theorem finiteSmoothEquiv_centerAction (n : ℕ) (e : K ≃+* L)
    (z : ArchimedeanGL.EnvelopingCenter K n) (f : FiniteSmoothRationalFunctions L n) :
    finiteSmoothEquiv n e (finiteSmoothCenterAction L n (centerEquiv n e z) f) =
      finiteSmoothCenterAction K n z (finiteSmoothEquiv n e f) := by
  change finiteSmoothEquiv n e
      (finiteSmoothEnvelopingAction L n
        (ArchimedeanGL.centerInclusion L n (centerEquiv n e z)) f) = _
  rw [centerInclusion_centerEquiv]
  exact finiteSmoothEquiv_envelopingAction n e _ f

theorem isCenterFinite_finiteSmoothEquiv_iff (n : ℕ) (e : K ≃+* L)
    (f : FiniteSmoothRationalFunctions L n) :
    IsCenterFinite K n (finiteSmoothInclusion K n (finiteSmoothEquiv n e f)) ↔
      IsCenterFinite L n (finiteSmoothInclusion L n f) := by
  rw [← smoothEquiv_finiteSmoothInclusion]
  exact isCenterFinite_smoothEquiv_iff n e _

private theorem centerFiniteFiniteSmoothFunctions_map (n : ℕ) (e : K ≃+* L) :
    (centerFiniteFiniteSmoothFunctions L n).map (finiteSmoothEquiv n e).toLinearMap =
      centerFiniteFiniteSmoothFunctions K n := by
  ext f
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact (isCenterFinite_finiteSmoothEquiv_iff n e h).mpr hh
  · intro hf
    obtain ⟨h, rfl⟩ := (finiteSmoothEquiv n e).surjective f
    exact ⟨h, (isCenterFinite_finiteSmoothEquiv_iff n e h).mp hf, rfl⟩

/-- Genuine arithmetic equivalence with both a common finite stabilizer and one common center orbit. -/
def centerFiniteFiniteSmoothEquiv (n : ℕ) (e : K ≃+* L) :
    CenterFiniteFiniteSmoothRationalFunctions L n ≃L[ℂ]
      CenterFiniteFiniteSmoothRationalFunctions K n :=
  (finiteSmoothEquiv n e).ofSubmodules _ _ (centerFiniteFiniteSmoothFunctions_map n e)

@[simp] theorem centerFiniteFiniteSmoothEquiv_val (n : ℕ) (e : K ≃+* L)
    (f : CenterFiniteFiniteSmoothRationalFunctions L n) :
    (centerFiniteFiniteSmoothEquiv n e f).val = finiteSmoothEquiv n e f.val := rfl

@[simp] theorem evaluate_centerFiniteFiniteSmoothEquiv (n : ℕ) (e : K ≃+* L)
    (f : CenterFiniteFiniteSmoothRationalFunctions L n) (x : AdelicGL K n) :
    evaluate K n (centerFiniteFiniteSmoothEquiv n e f).val.val x =
      evaluate L n f.val.val (adelicEquiv n e x) := rfl

@[simp] theorem evaluate_centerFiniteFiniteSmoothEquiv_symm (n : ℕ) (e : K ≃+* L)
    (f : CenterFiniteFiniteSmoothRationalFunctions K n) (x : AdelicGL L n) :
    evaluate L n ((centerFiniteFiniteSmoothEquiv n e).symm f).val.val x =
      evaluate K n f.val.val (adelicEquiv n e.symm x) := rfl

@[simp] theorem centerFiniteFiniteSmoothEquiv_refl (n : ℕ)
    (f : CenterFiniteFiniteSmoothRationalFunctions K n) :
    centerFiniteFiniteSmoothEquiv n (RingEquiv.refl K) f = f := by
  apply Subtype.ext
  exact finiteSmoothEquiv_refl n f.val

theorem centerFiniteFiniteSmoothEquiv_trans (n : ℕ) (e : K ≃+* L) (a : L ≃+* M)
    (f : CenterFiniteFiniteSmoothRationalFunctions M n) :
    centerFiniteFiniteSmoothEquiv n (e.trans a) f =
      centerFiniteFiniteSmoothEquiv n e (centerFiniteFiniteSmoothEquiv n a f) := by
  apply Subtype.ext
  exact finiteSmoothEquiv_trans n e a f.val

@[simp] theorem centerFiniteFiniteSmoothEquiv_symm (n : ℕ) (e : K ≃+* L) :
    (centerFiniteFiniteSmoothEquiv n e).symm = centerFiniteFiniteSmoothEquiv n e.symm := by
  apply ContinuousLinearEquiv.ext
  funext f
  apply Subtype.ext
  rfl

/-- Covariance persists for the actual restricted center-finite enveloping action. -/
theorem centerFiniteFiniteSmoothEquiv_envelopingAction (n : ℕ) (e : K ≃+* L)
    (u : ArchimedeanGL.EnvelopingAlgebra K n)
    (f : CenterFiniteFiniteSmoothRationalFunctions L n) :
    centerFiniteFiniteSmoothEquiv n e
        (centerFiniteEnvelopingAction L n (envelopingEquiv n e u) f) =
      centerFiniteEnvelopingAction K n u (centerFiniteFiniteSmoothEquiv n e f) := by
  apply Subtype.ext
  exact finiteSmoothEquiv_envelopingAction n e u f.val

end Langlands.Automorphic.ContinuousRationalFunctions
