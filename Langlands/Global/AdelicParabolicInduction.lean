import Langlands.Global.AdelicBlockDeterminantCharacter
import Langlands.Automorphic.Smooth
import Langlands.Global.ArchimedeanVectorSmooth
import Langlands.Global.AdelicBlockCenter
import Langlands.Representation.Induction.Definitions

/-!
# Half-twisted sections for actual adelic block parabolics

Finite open stabilizers and real-smooth archimedean slices are separate
conditions on actual covariant functions. No whole-group open stabilizer is used.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe uF uV uW uX

namespace Langlands.Global.AdelicParabolicInduction

open NumberField IsDedekindDomain
open Langlands.GeneralLinear AdelicBlockParabolic
open scoped Manifold ContDiff Matrix.Norms.Operator

variable (F : Type uF) [Field F] [NumberField F] {n : ℕ} (B : BlockShape n)
section Algebraic

variable {V : Type uV} {W : Type uW} {X : Type uX}
variable [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
variable [AddCommGroup X] [Module ℂ X]

/-- Inflate the actual Levi representation and twist by the constructed positive half. -/
def inducingRepresentation (σ : Representation ℂ (FullLevi F B) V) :
    Representation ℂ (Full F B) V :=
  twist (AdelicBlockDeterminantCharacter.parabolicHalfCharacter F B).toMonoidHom
    (σ.comp (B.leviProjection (Adeles F)))

/-- The actual module of covariant functions, before regularity conditions. -/
abbrev Sections (σ : Representation ℂ (FullLevi F B) V) : Type (max uF uV) :=
  Induction.EquivariantFunctions (B.parabolic (Adeles F)) (inducingRepresentation F B σ)

/-- Actual right translation on all the covariant functions. -/
abbrev rightAction (σ : Representation ℂ (FullLevi F B) V) :
    Representation ℂ (AdelicGL F n) (Sections F B σ) :=
  Induction.equivariantAction (B.parabolic (Adeles F)) (inducingRepresentation F B σ)

/-- Evaluation of an actual section. -/
def evaluate (σ : Representation ℂ (FullLevi F B) V)
    (f : Sections F B σ) (g : AdelicGL F n) : V :=
  f.val g

theorem covariance (σ : Representation ℂ (FullLevi F B) V)
    (f : Sections F B σ) (p : Full F B) (g : AdelicGL F n) :
    evaluate F B σ f (p.val * g) =
      (AdelicBlockDeterminantCharacter.leviHalfCharacter F B
        (B.leviProjection (Adeles F) p) : ℂ) •
        σ (B.leviProjection (Adeles F) p) (evaluate F B σ f g) :=
  f.property p g

@[simp]
theorem evaluate_rightAction (σ : Representation ℂ (FullLevi F B) V)
    (g x : AdelicGL F n) (f : Sections F B σ) :
    evaluate F B σ (rightAction F B σ g f) x = evaluate F B σ f (x * g) := rfl

/-- The positive half is trivial on common scalars, so it does not change their action. -/
theorem inducingRepresentation_scalar (σ : Representation ℂ (FullLevi F B) V)
    (z : Ideles F) (v : V) :
    inducingRepresentation F B σ (AdelicBlockCenter.scalarParabolic F B z) v =
      σ (AdelicBlockCenter.scalarLevi F B z) v := by
  change (AdelicBlockDeterminantCharacter.leviHalfCharacter F B
    (B.leviProjection (Adeles F) (AdelicBlockCenter.scalarParabolic F B z)) : ℂ) •
      σ (B.leviProjection (Adeles F) (AdelicBlockCenter.scalarParabolic F B z)) v = _
  rw [AdelicBlockCenter.leviProjection_scalar]
  have hh : AdelicBlockDeterminantCharacter.leviHalfCharacter F B
      (AdelicBlockCenter.scalarLevi F B z) = 1 :=
    AdelicBlockDeterminantCharacter.leviHalfCharacter_scalar F B z
  rw [hh, Units.val_one, one_smul]

/-- Actual left scalar covariance, before imposing any scalar character on the coefficients. -/
theorem evaluate_scalar (σ : Representation ℂ (FullLevi F B) V)
    (f : Sections F B σ) (z : Ideles F) (x : AdelicGL F n) :
    evaluate F B σ f (AdelicGL.scalar F n z * x) =
      σ (AdelicBlockCenter.scalarLevi F B z) (evaluate F B σ f x) := by
  have h := f.property (AdelicBlockCenter.scalarParabolic F B z) x
  exact h.trans (inducingRepresentation_scalar F B σ z _)

/-- Right scalar translation is the actual common-scalar Levi action on the values. -/
theorem evaluate_rightAction_scalar (σ : Representation ℂ (FullLevi F B) V)
    (f : Sections F B σ) (z : Ideles F) (x : AdelicGL F n) :
    evaluate F B σ (rightAction F B σ (AdelicGL.scalar F n z) f) x =
      σ (AdelicBlockCenter.scalarLevi F B z) (evaluate F B σ f x) := by
  rw [evaluate_rightAction, ← (AdelicGL.scalar_commute F n z x).eq]
  exact evaluate_scalar F B σ f z x

/-- An actual scalar character of the inducing coefficients is inherited by all sections. -/
theorem rightAction_scalar (σ : Representation ℂ (FullLevi F B) V)
    (c : Ideles F →* ℂˣ)
    (hσ : ∀ (z : Ideles F) (v : V),
      σ (AdelicBlockCenter.scalarLevi F B z) v = (c z : ℂ) • v)
    (z : Ideles F) (f : Sections F B σ) :
    rightAction F B σ (AdelicGL.scalar F n z) f = (c z : ℂ) • f := by
  apply Subtype.ext
  funext x
  exact (evaluate_rightAction_scalar F B σ f z x).trans (hσ z _)

/-- Restriction of right translation to the actual finite factor. -/
def finiteRightAction (σ : Representation ℂ (FullLevi F B) V) :
    Representation ℂ (FiniteAdelicGL F n) (Sections F B σ) :=
  (rightAction F B σ).comp (AdelicGL.ofFinite F n).toMonoidHom

/-- A single open finite stabilizer for the entire section, stable under the full action. -/
def finiteSmoothSubrepresentation (σ : Representation ℂ (FullLevi F B) V) :
    Subrepresentation (rightAction F B σ) where
  toSubmodule := Langlands.smoothVectors (finiteRightAction F B σ)
  apply_mem_toSubmodule g f hf := by
    obtain ⟨K, hK⟩ := hf
    let cg : FiniteAdelicGL F n →* FiniteAdelicGL F n :=
      (MulAut.conj (AdelicGL.finite F n g)⁻¹).toMonoidHom
    have hcg : Continuous cg := IsTopologicalGroup.continuous_conj _
    refine ⟨K.comap cg hcg, ?_⟩
    intro k
    apply ((rightAction F B σ).inv_apply_eq_iff (g := g)).mp
    have hk := hK ⟨cg k.val, k.property⟩
    change rightAction F B σ (AdelicGL.ofFinite F n (cg k.val)) f = f at hk
    change rightAction F B σ g⁻¹
      (rightAction F B σ (AdelicGL.ofFinite F n k.val)
        (rightAction F B σ g f)) = f
    change rightAction F B σ (AdelicGL.ofFinite F n
      ((AdelicGL.finite F n g)⁻¹ * k.val * ((AdelicGL.finite F n g)⁻¹)⁻¹)) f = f at hk
    rw [inv_inv] at hk
    have hfull : rightAction F B σ
        (g⁻¹ * AdelicGL.ofFinite F n k.val * g) f = f := by
      rw [AdelicGL.finite_conjugation]
      exact hk
    simpa only [map_mul, Module.End.mul_apply] using hfull

/-- Covariant functions with a common open finite stabilizer. -/
abbrev FiniteSmoothSections (σ : Representation ℂ (FullLevi F B) V) :=
  (finiteSmoothSubrepresentation F B σ).toSubmodule

/-- The full adelic action on sections with finite smoothness only. -/
def finiteSmoothInduced (σ : Representation ℂ (FullLevi F B) V) :
    Representation ℂ (AdelicGL F n) (FiniteSmoothSections F B σ) :=
  (finiteSmoothSubrepresentation F B σ).toRepresentation

/-- The same scalar character acts on the actual finite-smooth section subspace. -/
theorem finiteSmoothInduced_scalar (σ : Representation ℂ (FullLevi F B) V)
    (c : Ideles F →* ℂˣ)
    (hσ : ∀ (z : Ideles F) (v : V),
      σ (AdelicBlockCenter.scalarLevi F B z) v = (c z : ℂ) • v)
    (z : Ideles F) (f : FiniteSmoothSections F B σ) :
    finiteSmoothInduced F B σ (AdelicGL.scalar F n z) f = (c z : ℂ) • f := by
  apply Subtype.ext
  exact rightAction_scalar F B σ c hσ z f.val

/-- Its restriction to the finite adelic group is smooth. -/
theorem finiteSmoothInduced_isSmooth (σ : Representation ℂ (FullLevi F B) V) :
    Langlands.IsSmooth (R := ℂ) (G := FiniteAdelicGL F n)
      (V := FiniteSmoothSections F B σ)
      ((finiteSmoothInduced F B σ).comp (AdelicGL.ofFinite F n).toMonoidHom) := by
  intro f
  obtain ⟨K, hK⟩ := f.property
  refine ⟨K, ?_⟩
  intro k
  apply Subtype.ext
  exact hK k

/-- Build a section from actual covariance and an explicit common open finite stabilizer. -/
def finiteSmoothSectionOf (σ : Representation ℂ (FullLevi F B) V)
    (f : AdelicGL F n → V)
    (hcov : ∀ (p : Full F B) (g : AdelicGL F n),
      f (p.val * g) = inducingRepresentation F B σ p (f g))
    (K : OpenSubgroup (FiniteAdelicGL F n))
    (hK : ∀ (k : K) (g : AdelicGL F n),
      f (g * AdelicGL.ofFinite F n k.val) = f g) : FiniteSmoothSections F B σ :=
  ⟨⟨f, hcov⟩, K, by
    intro k
    apply Subtype.ext
    exact funext (hK k)⟩

/-- Each finite slice is locally constant, even for purely algebraic coefficients. -/
theorem finiteSmoothSection_finiteLocallyConstant
    (σ : Representation ℂ (FullLevi F B) V) (f : FiniteSmoothSections F B σ)
    (a : InfiniteAdelicGL F n) :
    IsLocallyConstant (fun b => evaluate F B σ f.val (AdelicGL.pair F n a b)) := by
  obtain ⟨K, hK⟩ := f.property
  apply (IsLocallyConstant.iff_exists_open _).mpr
  intro b
  refine ⟨(fun d : FiniteAdelicGL F n => b⁻¹ * d) ⁻¹' (K : Set _),
    K.isOpen.preimage (continuous_const.mul continuous_id), ?_, ?_⟩
  · change b⁻¹ * b ∈ K
    simp
  · intro d hd
    have h := congrArg (fun s => evaluate F B σ s (AdelicGL.pair F n a b))
      (hK ⟨b⁻¹ * d, hd⟩)
    change evaluate F B σ f.val
      (AdelicGL.pair F n a b * AdelicGL.ofFinite F n (b⁻¹ * d)) =
      evaluate F B σ f.val (AdelicGL.pair F n a b) at h
    simpa only [AdelicGL.ofFinite_eq_pair, AdelicGL.pair_mul, mul_one,
      mul_inv_cancel_left] using h

/-- A Levi intertwiner inflates and twists with the same actual positive half. -/
def inducingMap {σ : Representation ℂ (FullLevi F B) V}
    {τ : Representation ℂ (FullLevi F B) W} (T : σ.IntertwiningMap τ) :
    (inducingRepresentation F B σ).IntertwiningMap (inducingRepresentation F B τ) :=
  twistIntertwining _
    { toLinearMap := T.toLinearMap
      isIntertwining' := fun p => T.isIntertwining' (B.leviProjection (Adeles F) p) }

/-- Postcomposition of the actual covariant functions. -/
def sectionMap {σ : Representation ℂ (FullLevi F B) V}
    {τ : Representation ℂ (FullLevi F B) W} (T : σ.IntertwiningMap τ) :
    (rightAction F B σ).IntertwiningMap (rightAction F B τ) :=
  Representation.coindMap _ (inducingMap F B T)

private theorem sectionMap_finiteSmooth {σ : Representation ℂ (FullLevi F B) V}
    {τ : Representation ℂ (FullLevi F B) W} (T : σ.IntertwiningMap τ)
    (f : Sections F B σ) (hf : f ∈ finiteSmoothSubrepresentation F B σ) :
    sectionMap F B T f ∈ finiteSmoothSubrepresentation F B τ := by
  obtain ⟨K, hK⟩ := hf
  refine ⟨K, ?_⟩
  intro k
  have h := Representation.IntertwiningMap.isIntertwining
    (rightAction F B σ) (rightAction F B τ) (sectionMap F B T)
    (AdelicGL.ofFinite F n k.val) f
  change sectionMap F B T
    (finiteRightAction F B σ k.val f) =
      finiteRightAction F B τ k.val (sectionMap F B T f) at h
  have hk : finiteRightAction F B σ k.val f = f := hK k
  rw [hk] at h
  exact h.symm

/-- Postcomposition preserves finite smoothness, with the same stabilizer. -/
def finiteSmoothInducedMap {σ : Representation ℂ (FullLevi F B) V}
    {τ : Representation ℂ (FullLevi F B) W} (T : σ.IntertwiningMap τ) :
    (finiteSmoothInduced F B σ).IntertwiningMap (finiteSmoothInduced F B τ) where
  toLinearMap := (sectionMap F B T).toLinearMap.restrict (sectionMap_finiteSmooth F B T)
  isIntertwining' _ := by ext f x; rfl

@[simp]
theorem finiteSmoothInducedMap_apply {σ : Representation ℂ (FullLevi F B) V}
    {τ : Representation ℂ (FullLevi F B) W} (T : σ.IntertwiningMap τ)
    (f : FiniteSmoothSections F B σ) (x : AdelicGL F n) :
    evaluate F B τ (finiteSmoothInducedMap F B T f).val x =
      T (evaluate F B σ f.val x) := rfl

@[simp]
theorem finiteSmoothInducedMap_id (σ : Representation ℂ (FullLevi F B) V) :
    finiteSmoothInducedMap F B (Representation.IntertwiningMap.id σ) =
      Representation.IntertwiningMap.id (finiteSmoothInduced F B σ) := by
  ext f x
  rfl

@[simp]
theorem finiteSmoothInducedMap_comp {σ : Representation ℂ (FullLevi F B) V}
    {τ : Representation ℂ (FullLevi F B) W} {υ : Representation ℂ (FullLevi F B) X}
    (T : σ.IntertwiningMap τ) (S : τ.IntertwiningMap υ) :
    finiteSmoothInducedMap F B (S.comp T) =
      (finiteSmoothInducedMap F B S).comp (finiteSmoothInducedMap F B T) := by
  ext f x
  rfl

end Algebraic

section Normed

variable {V : Type uV} {W : Type uW} {X : Type uX}
variable [NormedAddCommGroup V] [NormedSpace ℂ V]
variable [NormedAddCommGroup W] [NormedSpace ℂ W]
variable [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- Restrict an actual section to the infinite factor at a fixed finite matrix. -/
def infiniteSlice (σ : Representation ℂ (FullLevi F B) V) (b : FiniteAdelicGL F n) :
    Sections F B σ →ₗ[ℂ] (InfiniteAdelicGL F n → V) where
  toFun f a := evaluate F B σ f (AdelicGL.pair F n a b)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Real smoothness of every infinite slice is invariant under the full adelic action. -/
def infiniteSmoothSubrepresentation (σ : Representation ℂ (FullLevi F B) V) :
    Subrepresentation (rightAction F B σ) where
  toSubmodule := ⨅ b : FiniteAdelicGL F n,
    (ArchimedeanGL.vectorSmoothFunctions F n V).comap (infiniteSlice F B σ b)
  apply_mem_toSubmodule g f hf := by
    simp only [Submodule.mem_iInf, Submodule.mem_comap] at hf ⊢
    intro b
    let s : ArchimedeanGL.VectorSmoothFunctions F n V :=
      ⟨infiniteSlice F B σ (b * AdelicGL.finite F n g) f, hf _⟩
    have h := (ArchimedeanGL.vectorSmoothRightAction F n V
      (AdelicGL.infinite F n g) s).property
    change (fun a => evaluate F B σ f (AdelicGL.pair F n
      (a * AdelicGL.infinite F n g) (b * AdelicGL.finite F n g))) ∈
      ArchimedeanGL.vectorSmoothFunctions F n V at h
    change (fun a => evaluate F B σ f (AdelicGL.pair F n a b * g)) ∈
      ArchimedeanGL.vectorSmoothFunctions F n V
    simpa only [AdelicGL.pair_mul_right] using h

theorem mem_infiniteSmoothSubrepresentation (σ : Representation ℂ (FullLevi F B) V)
    (f : Sections F B σ) :
    f ∈ infiniteSmoothSubrepresentation F B σ ↔
      ∀ b, infiniteSlice F B σ b f ∈ ArchimedeanGL.vectorSmoothFunctions F n V := by
  change f ∈ (⨅ b : FiniteAdelicGL F n,
    (ArchimedeanGL.vectorSmoothFunctions F n V).comap (infiniteSlice F B σ b)) ↔ _
  simp only [Submodule.mem_iInf, Submodule.mem_comap]

/-- Actual covariant functions with real-smooth infinite slices and one open finite stabilizer. -/
def smoothSubrepresentation (σ : Representation ℂ (FullLevi F B) V) :
    Subrepresentation (rightAction F B σ) :=
  infiniteSmoothSubrepresentation F B σ ⊓ finiteSmoothSubrepresentation F B σ

abbrev SmoothSections (σ : Representation ℂ (FullLevi F B) V) :=
  (smoothSubrepresentation F B σ).toSubmodule

/-- The full adelic right action on the actual half-twisted smooth section space. -/
def smoothInduced (σ : Representation ℂ (FullLevi F B) V) :
    Representation ℂ (AdelicGL F n) (SmoothSections F B σ) :=
  (smoothSubrepresentation F B σ).toRepresentation

/-- The same scalar character acts on the actual full smooth section subspace. -/
theorem smoothInduced_scalar (σ : Representation ℂ (FullLevi F B) V)
    (c : Ideles F →* ℂˣ)
    (hσ : ∀ (z : Ideles F) (v : V),
      σ (AdelicBlockCenter.scalarLevi F B z) v = (c z : ℂ) • v)
    (z : Ideles F) (f : SmoothSections F B σ) :
    smoothInduced F B σ (AdelicGL.scalar F n z) f = (c z : ℂ) • f := by
  apply Subtype.ext
  exact rightAction_scalar F B σ c hσ z f.val

/-- Faithful inclusion in the actual covariant function representation. -/
def smoothInclusion (σ : Representation ℂ (FullLevi F B) V) :
    (smoothInduced F B σ).IntertwiningMap (rightAction F B σ) where
  toLinearMap := (smoothSubrepresentation F B σ).toSubmodule.subtype
  isIntertwining' _ := by ext f x; rfl

theorem smoothInclusion_injective (σ : Representation ℂ (FullLevi F B) V) :
    Function.Injective (smoothInclusion F B σ) := Subtype.val_injective

@[simp]
theorem evaluate_smoothInduced (σ : Representation ℂ (FullLevi F B) V)
    (g x : AdelicGL F n) (f : SmoothSections F B σ) :
    evaluate F B σ (smoothInduced F B σ g f).val x =
      evaluate F B σ f.val (x * g) := rfl

/-- The two regularity conditions imply continuity in the actual full adelic topology. -/
theorem smoothSection_continuous (σ : Representation ℂ (FullLevi F B) V)
    (f : SmoothSections F B σ) : Continuous (evaluate F B σ f.val) := by
  obtain ⟨K, hK⟩ := f.property.2
  have hslices := (mem_infiniteSmoothSubrepresentation F B σ f.val).mp f.property.1
  apply continuous_iff_continuousAt.mpr
  intro x
  let b := AdelicGL.finite F n x
  let s : ArchimedeanGL.VectorSmoothFunctions F n V :=
    ⟨infiniteSlice F B σ b f.val, hslices b⟩
  have hc : Continuous (fun y : AdelicGL F n =>
      evaluate F B σ f.val (AdelicGL.pair F n (AdelicGL.infinite F n y) b)) :=
    (ArchimedeanGL.vectorSmooth_continuous F n V s).comp (AdelicGL.infinite F n).continuous
  apply hc.continuousAt.congr_of_eventuallyEq
  have hU : (fun y : AdelicGL F n => b⁻¹ * AdelicGL.finite F n y) ⁻¹'
      (K : Set _) ∈ nhds x :=
    (K.isOpen.preimage (continuous_const.mul (AdelicGL.finite F n).continuous)).mem_nhds
      (by change b⁻¹ * b ∈ K; simp)
  filter_upwards [hU] with y hy
  have h := congrArg (fun t => evaluate F B σ t
      (AdelicGL.pair F n (AdelicGL.infinite F n y) b))
    (hK ⟨b⁻¹ * AdelicGL.finite F n y, hy⟩)
  change evaluate F B σ f.val
      (AdelicGL.pair F n (AdelicGL.infinite F n y) b *
        AdelicGL.ofFinite F n (b⁻¹ * AdelicGL.finite F n y)) =
    evaluate F B σ f.val (AdelicGL.pair F n (AdelicGL.infinite F n y) b) at h
  simpa only [AdelicGL.ofFinite_eq_pair, AdelicGL.pair_mul, mul_one,
    mul_inv_cancel_left, AdelicGL.pair_projections] using h

/-- Faithful realization in actual continuous vector valued functions. -/
def smoothToContinuousMap (σ : Representation ℂ (FullLevi F B) V) :
    SmoothSections F B σ →ₗ[ℂ] C(AdelicGL F n, V) where
  toFun f := ⟨evaluate F B σ f.val, smoothSection_continuous F B σ f⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem smoothToContinuousMap_injective (σ : Representation ℂ (FullLevi F B) V) :
    Function.Injective (smoothToContinuousMap F B σ) := by
  intro f g h
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg ContinuousMap.toFun h

/-- The actual finite factor acts smoothly on the full smooth section space. -/
theorem smoothInduced_isSmooth (σ : Representation ℂ (FullLevi F B) V) :
    Langlands.IsSmooth (R := ℂ) (G := FiniteAdelicGL F n)
      (V := SmoothSections F B σ)
      ((smoothInduced F B σ).comp (AdelicGL.ofFinite F n).toMonoidHom) := by
  intro f
  obtain ⟨K, hK⟩ := f.property.2
  refine ⟨K, ?_⟩
  intro k
  apply Subtype.ext
  exact hK k

/-- Construct a genuine smooth section from explicit covariance and regularity. -/
def smoothSectionOf (σ : Representation ℂ (FullLevi F B) V)
    (f : AdelicGL F n → V)
    (hcov : ∀ (p : Full F B) (g : AdelicGL F n),
      f (p.val * g) = inducingRepresentation F B σ p (f g))
    (K : OpenSubgroup (FiniteAdelicGL F n))
    (hK : ∀ (k : K) (g : AdelicGL F n),
      f (g * AdelicGL.ofFinite F n k.val) = f g)
    (hsmooth : ∀ b : FiniteAdelicGL F n, (fun a => f (AdelicGL.pair F n a b)) ∈
      ArchimedeanGL.vectorSmoothFunctions F n V) : SmoothSections F B σ := by
  let s := finiteSmoothSectionOf F B σ f hcov K hK
  refine ⟨s.val, ?_, s.property⟩
  exact (mem_infiniteSmoothSubrepresentation F B σ s.val).mpr hsmooth

private theorem sectionMap_infiniteSmooth {σ : Representation ℂ (FullLevi F B) V}
    {τ : Representation ℂ (FullLevi F B) W} (T : σ.IntertwiningMap τ)
    (hT : Continuous T) (f : Sections F B σ)
    (hf : f ∈ infiniteSmoothSubrepresentation F B σ) :
    sectionMap F B T f ∈ infiniteSmoothSubrepresentation F B τ := by
  rw [mem_infiniteSmoothSubrepresentation] at hf ⊢
  intro b
  let s : ArchimedeanGL.VectorSmoothFunctions F n V := ⟨infiniteSlice F B σ b f, hf b⟩
  exact (ArchimedeanGL.vectorSmoothMap F n V ⟨T.toLinearMap, hT⟩ s).property

/-- Continuous Levi intertwiners preserve both regularity conditions by postcomposition. -/
def smoothInducedMap {σ : Representation ℂ (FullLevi F B) V}
    {τ : Representation ℂ (FullLevi F B) W} (T : σ.IntertwiningMap τ)
    (hT : Continuous T) :
    (smoothInduced F B σ).IntertwiningMap (smoothInduced F B τ) where
  toLinearMap := (sectionMap F B T).toLinearMap.restrict (by
    intro f hf
    exact ⟨sectionMap_infiniteSmooth F B T hT f hf.1,
      sectionMap_finiteSmooth F B T f hf.2⟩)
  isIntertwining' _ := by ext f x; rfl

@[simp]
theorem smoothInducedMap_apply {σ : Representation ℂ (FullLevi F B) V}
    {τ : Representation ℂ (FullLevi F B) W} (T : σ.IntertwiningMap τ)
    (hT : Continuous T) (f : SmoothSections F B σ) (x : AdelicGL F n) :
    evaluate F B τ (smoothInducedMap F B T hT f).val x =
      T (evaluate F B σ f.val x) := rfl

@[simp]
theorem smoothInducedMap_id (σ : Representation ℂ (FullLevi F B) V) :
    smoothInducedMap F B (Representation.IntertwiningMap.id σ) continuous_id =
      Representation.IntertwiningMap.id (smoothInduced F B σ) := by
  ext f x
  rfl

@[simp]
theorem smoothInducedMap_comp {σ : Representation ℂ (FullLevi F B) V}
    {τ : Representation ℂ (FullLevi F B) W} {υ : Representation ℂ (FullLevi F B) X}
    (T : σ.IntertwiningMap τ) (S : τ.IntertwiningMap υ)
    (hT : Continuous T) (hS : Continuous S) :
    smoothInducedMap F B (S.comp T) (hS.comp hT) =
      (smoothInducedMap F B S hS).comp (smoothInducedMap F B T hT) := by
  ext f x
  rfl

end Normed

end Langlands.Global.AdelicParabolicInduction
