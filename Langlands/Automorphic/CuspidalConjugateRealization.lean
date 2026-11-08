import Langlands.Automorphic.Contragredient
import Langlands.Automorphic.AssociatedFactorStatement
import Langlands.Global.ArchimedeanEnvelopingConjugation

/-!
# The complex conjugate of an actual cuspidal operator realization

Pointwise complex conjugation preserves actual automorphic forms and the stable operator
core. Conjugating an operator by it is a ring automorphism of the concrete operator
algebra fixing the finite and compact translations and acting on differentials through
complex conjugation of the enveloping algebra. The image of an operator realization is
again one, and conjugation is an antilinear bijection commuting with the finite, compact
and real Lie algebra operators. Irreducibility and cuspidality are preserved, and a
central character is replaced by its complex conjugate.
-/

noncomputable section

universe u

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped ComplexConjugate

namespace Langlands

/-- Image and preimage identify invariant subspaces under an antilinear bijection that
intertwines the actions up to an automorphism of the acting monoid. -/
def antilinearConjugatedSubrepresentationOrderIso
    {A V W : Type*} [Monoid A] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ A V) (τ : Representation ℂ A W)
    (α : A ≃* A) (e : V ≃ₛₗ[starRingEnd ℂ] W)
    (hc : ∀ a f, τ a (e f) = e (ρ (α a) f)) :
    Subrepresentation ρ ≃o Subrepresentation τ where
  toFun P :=
    { toSubmodule := P.toSubmodule.map (e : V →ₛₗ[starRingEnd ℂ] W)
      apply_mem_toSubmodule a _ hf := by
        obtain ⟨f, hfP, rfl⟩ := Submodule.mem_map.mp hf
        change τ a (e f) ∈ P.toSubmodule.map (e : V →ₛₗ[starRingEnd ℂ] W)
        rw [hc]
        exact Submodule.mem_map_of_mem (P.apply_mem_toSubmodule (α a) hfP) }
  invFun Q :=
    { toSubmodule := Q.toSubmodule.comap (e : V →ₛₗ[starRingEnd ℂ] W)
      apply_mem_toSubmodule a f hf := by
        change e (ρ a f) ∈ Q
        have hcov := hc (α.symm a) f
        rw [α.apply_symm_apply] at hcov
        rw [← hcov]
        exact Q.apply_mem_toSubmodule (α.symm a) hf }
  left_inv P := Subrepresentation.toSubmodule_injective
    ((Submodule.orderIsoMapComap e).symm_apply_apply P.toSubmodule)
  right_inv Q := Subrepresentation.toSubmodule_injective
    ((Submodule.orderIsoMapComap e).apply_symm_apply Q.toSubmodule)
  map_rel_iff' := (Submodule.orderIsoMapComap e).map_rel_iff

/-- An antilinear map sending each orbit operator applied to `C v` into the image of the
orbit of `v` preserves finiteness of the orbit span. -/
theorem FiniteVectors.IsFiniteVector.antilinear
    {G H V W : Type*} [Monoid G] [Monoid H] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G V} (τ : Representation ℂ H W)
    (C : V →ₛₗ[starRingEnd ℂ] W) {v : V}
    (hC : ∀ h : H, ∃ g : G, τ h (C v) = C (ρ g v))
    (hv : FiniteVectors.IsFiniteVector ρ v) :
    FiniteVectors.IsFiniteVector τ (C v) := by
  have hle : FiniteVectors.orbitSpan τ (C v) ≤ (FiniteVectors.orbitSpan ρ v).map C := by
    apply Submodule.span_le.mpr
    rintro _ ⟨h, rfl⟩
    obtain ⟨g, hg⟩ := hC h
    change τ h (C v) ∈ (FiniteVectors.orbitSpan ρ v).map C
    rw [hg]
    exact Submodule.mem_map_of_mem (FiniteVectors.action_mem_orbitSpan ρ g v)
  have hfg : ((FiniteVectors.orbitSpan ρ v).map C).FG :=
    (Module.Finite.iff_fg.mp hv).map C
  have : Module.Finite ℂ ((FiniteVectors.orbitSpan ρ v).map C) := Module.Finite.iff_fg.mpr hfg
  exact Submodule.finiteDimensional_of_le hle

end Langlands

namespace Langlands.Automorphic

open Langlands.Global NumberField ContinuousRationalFunctions

variable (F : Type u) [Field F] [NumberField F] (n : ℕ)

local instance conjugateRealizationRationalGroup :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance conjugateRealizationContinuousGroup :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance conjugateRealizationFiniteSmoothGroup :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance conjugateRealizationFormGroup :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance conjugateRealizationStableGroup :
    AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _

section Functions

/-- Pointwise complex conjugation of continuous rational-invariant adelic functions. -/
def continuousConj :
    ContinuousRationalFunctions F n →ₛₗ[starRingEnd ℂ] ContinuousRationalFunctions F n where
  toFun f := ⟨⟨fun x => conj (evaluate F n f x), fun γ x => by
      change conj (evaluate F n f (AdelicGL.rational F n γ * x)) = conj (evaluate F n f x)
      rw [evaluate_rational]⟩,
    (Complex.continuous_conj.comp (continuous_evaluate F n f) :
      Continuous fun x => conj (evaluate F n f x))⟩
  map_add' f g := by
    apply Subtype.ext
    apply Subtype.ext
    funext x
    exact map_add (starRingEnd ℂ) (evaluate F n f x) (evaluate F n g x)
  map_smul' c f := by
    apply Subtype.ext
    apply Subtype.ext
    funext x
    exact map_mul (starRingEnd ℂ) c (evaluate F n f x)

@[simp]
theorem evaluate_continuousConj (f : ContinuousRationalFunctions F n) (x : AdelicGL F n) :
    evaluate F n (continuousConj F n f) x = conj (evaluate F n f x) := rfl

@[simp]
theorem continuousConj_continuousConj (f : ContinuousRationalFunctions F n) :
    continuousConj F n (continuousConj F n f) = f := by
  apply Subtype.ext
  apply Subtype.ext
  funext x
  exact Complex.conj_conj (evaluate F n f x)

theorem continuousConj_rightAction (g : AdelicGL F n) (f : ContinuousRationalFunctions F n) :
    continuousConj F n (continuousRightAction F n g f) =
      continuousRightAction F n g (continuousConj F n f) := rfl

theorem continuousConj_mem_infiniteSmooth {f : ContinuousRationalFunctions F n}
    (hf : f ∈ infiniteSmoothSubrepresentation F n) :
    continuousConj F n f ∈ infiniteSmoothSubrepresentation F n := by
  change f ∈ (⨅ b : FiniteAdelicGL F n,
    (ArchimedeanGL.smoothFunctions F n).comap (infiniteSlice F n b)) at hf
  change continuousConj F n f ∈ (⨅ b : FiniteAdelicGL F n,
    (ArchimedeanGL.smoothFunctions F n).comap (infiniteSlice F n b))
  rw [Submodule.mem_iInf] at hf ⊢
  intro b
  exact (ArchimedeanGL.smoothConj F n ⟨infiniteSlice F n b f, hf b⟩).property

theorem continuousConj_mem_finiteSmooth {f : ContinuousRationalFunctions F n}
    (hf : f ∈ finiteSmoothSubrepresentation F n) :
    continuousConj F n f ∈ finiteSmoothSubrepresentation F n := by
  obtain ⟨L, hL⟩ := hf
  refine ⟨L, fun l => ?_⟩
  change continuousRightAction F n (AdelicGL.ofFinite F n l) (continuousConj F n f) =
    continuousConj F n f
  rw [← continuousConj_rightAction]
  exact congrArg (continuousConj F n) (hL l)

/-- Pointwise complex conjugation of the actual finite-smooth functions. -/
def finiteSmoothConj :
    FiniteSmoothRationalFunctions F n →ₛₗ[starRingEnd ℂ] FiniteSmoothRationalFunctions F n where
  toFun f := ⟨continuousConj F n f.val, continuousConj_mem_infiniteSmooth F n f.property.1,
    continuousConj_mem_finiteSmooth F n f.property.2⟩
  map_add' f g := Subtype.ext (map_add (continuousConj F n) f.val g.val)
  map_smul' c f := Subtype.ext (map_smulₛₗ (continuousConj F n) c f.val)

@[simp]
theorem finiteSmoothConj_val (f : FiniteSmoothRationalFunctions F n) :
    (finiteSmoothConj F n f).val = continuousConj F n f.val := rfl

@[simp]
theorem finiteSmoothConj_finiteSmoothConj (f : FiniteSmoothRationalFunctions F n) :
    finiteSmoothConj F n (finiteSmoothConj F n f) = f :=
  Subtype.ext (continuousConj_continuousConj F n f.val)

theorem finiteSmoothConj_rightAction (g : AdelicGL F n) (f : FiniteSmoothRationalFunctions F n) :
    finiteSmoothConj F n (finiteSmoothRightAction F n g f) =
      finiteSmoothRightAction F n g (finiteSmoothConj F n f) := rfl

theorem finiteSmoothSlice_finiteSmoothConj (b : FiniteAdelicGL F n)
    (f : FiniteSmoothRationalFunctions F n) :
    finiteSmoothSlice F n b (finiteSmoothConj F n f) =
      ArchimedeanGL.smoothConj F n (finiteSmoothSlice F n b f) := rfl

/-- Conjugation intertwines the genuine enveloping action with its conjugate. -/
theorem finiteSmoothConj_envelopingAction (u : ArchimedeanGL.EnvelopingAlgebra F n)
    (f : FiniteSmoothRationalFunctions F n) :
    finiteSmoothConj F n (finiteSmoothEnvelopingAction F n u f) =
      finiteSmoothEnvelopingAction F n (ArchimedeanGL.envelopingConj F n u)
        (finiteSmoothConj F n f) := by
  apply finiteSmoothSlice_injective F n
  funext b
  dsimp only
  rw [finiteSmoothSlice_finiteSmoothConj, finiteSmoothSlice_envelopingAction,
    finiteSmoothSlice_envelopingAction, finiteSmoothSlice_finiteSmoothConj,
    ArchimedeanGL.smoothConj_envelopingAction]

theorem finiteSmoothConj_centerAction (z : ArchimedeanGL.EnvelopingCenter F n)
    (f : FiniteSmoothRationalFunctions F n) :
    finiteSmoothConj F n (finiteSmoothCenterAction F n z f) =
      finiteSmoothCenterAction F n (ArchimedeanGL.centerConj F n z)
        (finiteSmoothConj F n f) := by
  change finiteSmoothConj F n
      (finiteSmoothEnvelopingAction F n (ArchimedeanGL.centerInclusion F n z) f) =
    finiteSmoothEnvelopingAction F n
      (ArchimedeanGL.centerInclusion F n (ArchimedeanGL.centerConj F n z))
      (finiteSmoothConj F n f)
  rw [finiteSmoothConj_envelopingAction, ArchimedeanGL.centerInclusion_centerConj]

end Functions

section Operators

/-- Conjugation of an ambient operator by pointwise complex conjugation: `C A C`. -/
def finiteSmoothConjEnd (A : FiniteSmoothEnd F n) : FiniteSmoothEnd F n :=
  ((finiteSmoothConj F n).comp A).comp (finiteSmoothConj F n)

@[simp]
theorem finiteSmoothConjEnd_apply (A : FiniteSmoothEnd F n)
    (f : FiniteSmoothRationalFunctions F n) :
    finiteSmoothConjEnd F n A f = finiteSmoothConj F n (A (finiteSmoothConj F n f)) := rfl

@[simp]
theorem finiteSmoothConjEnd_finiteSmoothConjEnd (A : FiniteSmoothEnd F n) :
    finiteSmoothConjEnd F n (finiteSmoothConjEnd F n A) = A := by
  apply LinearMap.ext
  intro f
  simp only [finiteSmoothConjEnd_apply, finiteSmoothConj_finiteSmoothConj]

theorem finiteSmoothConjEnd_mul (A B : FiniteSmoothEnd F n) :
    finiteSmoothConjEnd F n (A * B) = finiteSmoothConjEnd F n A * finiteSmoothConjEnd F n B := by
  apply LinearMap.ext
  intro f
  simp only [finiteSmoothConjEnd_apply, Module.End.mul_apply, finiteSmoothConj_finiteSmoothConj]

theorem finiteSmoothConjEnd_add (A B : FiniteSmoothEnd F n) :
    finiteSmoothConjEnd F n (A + B) = finiteSmoothConjEnd F n A + finiteSmoothConjEnd F n B := by
  apply LinearMap.ext
  intro f
  simp only [finiteSmoothConjEnd_apply, LinearMap.add_apply, map_add]

theorem finiteSmoothConjEnd_algebraMap (c : ℂ) :
    finiteSmoothConjEnd F n (algebraMap ℂ (FiniteSmoothEnd F n) c) =
      algebraMap ℂ (FiniteSmoothEnd F n) (conj c) := by
  apply LinearMap.ext
  intro f
  simp only [finiteSmoothConjEnd_apply, Module.algebraMap_end_apply, LinearMap.map_smulₛₗ,
    finiteSmoothConj_finiteSmoothConj]

theorem finiteSmoothConjEnd_finite (d : FiniteAdelicGL F n) :
    finiteSmoothConjEnd F n (finiteSmoothFiniteRightAction F n d) =
      finiteSmoothFiniteRightAction F n d := by
  apply LinearMap.ext
  intro f
  rw [finiteSmoothConjEnd_apply]
  change finiteSmoothConj F n (finiteSmoothRightAction F n (AdelicGL.ofFinite F n d)
    (finiteSmoothConj F n f)) = finiteSmoothRightAction F n (AdelicGL.ofFinite F n d) f
  rw [finiteSmoothConj_rightAction, finiteSmoothConj_finiteSmoothConj]

theorem finiteSmoothConjEnd_compact (k : standardInfiniteCompact F n) :
    finiteSmoothConjEnd F n (finiteSmoothCompactRightAction F n k) =
      finiteSmoothCompactRightAction F n k := by
  apply LinearMap.ext
  intro f
  rw [finiteSmoothConjEnd_apply]
  change finiteSmoothConj F n (finiteSmoothRightAction F n (AdelicGL.ofInfinite F n k.val)
    (finiteSmoothConj F n f)) = finiteSmoothRightAction F n (AdelicGL.ofInfinite F n k.val) f
  rw [finiteSmoothConj_rightAction, finiteSmoothConj_finiteSmoothConj]

theorem finiteSmoothConjEnd_envelopingAction (u : ArchimedeanGL.EnvelopingAlgebra F n) :
    finiteSmoothConjEnd F n (finiteSmoothEnvelopingAction F n u) =
      finiteSmoothEnvelopingAction F n (ArchimedeanGL.envelopingConj F n u) := by
  apply LinearMap.ext
  intro f
  rw [finiteSmoothConjEnd_apply, finiteSmoothConj_envelopingAction,
    finiteSmoothConj_finiteSmoothConj]

/-- Conjugation preserves the concrete operator algebra. -/
theorem finiteSmoothConjEnd_mem {A : FiniteSmoothEnd F n}
    (hA : A ∈ automorphicOperatorAlgebra F n) :
    finiteSmoothConjEnd F n A ∈ automorphicOperatorAlgebra F n := by
  refine Algebra.adjoin_induction
    (p := fun A _ => finiteSmoothConjEnd F n A ∈ automorphicOperatorAlgebra F n)
    ?_ ?_ ?_ ?_ hA
  · rintro A ((⟨d, rfl⟩ | ⟨k, rfl⟩) | ⟨u, rfl⟩)
    · rw [finiteSmoothConjEnd_finite]
      exact Algebra.subset_adjoin (Or.inl (Or.inl ⟨d, rfl⟩))
    · rw [finiteSmoothConjEnd_compact]
      exact Algebra.subset_adjoin (Or.inl (Or.inr ⟨k, rfl⟩))
    · rw [finiteSmoothConjEnd_envelopingAction]
      exact Algebra.subset_adjoin (Or.inr ⟨_, rfl⟩)
  · intro c
    rw [finiteSmoothConjEnd_algebraMap]
    exact (automorphicOperatorAlgebra F n).algebraMap_mem (conj c)
  · intro A B _ _ hA hB
    rw [finiteSmoothConjEnd_add]
    exact (automorphicOperatorAlgebra F n).add_mem hA hB
  · intro A B _ _ hA hB
    rw [finiteSmoothConjEnd_mul]
    exact (automorphicOperatorAlgebra F n).mul_mem hA hB

/-- Complex conjugation of the concrete operator algebra, as a multiplicative involution. -/
def operatorConj : automorphicOperatorAlgebra F n ≃* automorphicOperatorAlgebra F n where
  toFun a := ⟨finiteSmoothConjEnd F n a.val, finiteSmoothConjEnd_mem F n a.property⟩
  invFun a := ⟨finiteSmoothConjEnd F n a.val, finiteSmoothConjEnd_mem F n a.property⟩
  left_inv a := Subtype.ext (finiteSmoothConjEnd_finiteSmoothConjEnd F n a.val)
  right_inv a := Subtype.ext (finiteSmoothConjEnd_finiteSmoothConjEnd F n a.val)
  map_mul' a b := Subtype.ext (finiteSmoothConjEnd_mul F n a.val b.val)

@[simp]
theorem operatorConj_val (a : automorphicOperatorAlgebra F n) :
    (operatorConj F n a).val = finiteSmoothConjEnd F n a.val := rfl

@[simp]
theorem operatorConj_operatorConj (a : automorphicOperatorAlgebra F n) :
    operatorConj F n (operatorConj F n a) = a :=
  Subtype.ext (finiteSmoothConjEnd_finiteSmoothConjEnd F n a.val)

theorem operatorConj_finiteOperator (d : FiniteAdelicGL F n) :
    operatorConj F n (finiteOperator F n d) = finiteOperator F n d :=
  Subtype.ext (finiteSmoothConjEnd_finite F n d)

theorem operatorConj_compactOperator (k : standardInfiniteCompact F n) :
    operatorConj F n (compactOperator F n k) = compactOperator F n k :=
  Subtype.ext (finiteSmoothConjEnd_compact F n k)

theorem operatorConj_differentialOperator (u : ArchimedeanGL.EnvelopingAlgebra F n) :
    operatorConj F n (differentialOperator F n u) =
      differentialOperator F n (ArchimedeanGL.envelopingConj F n u) :=
  Subtype.ext (finiteSmoothConjEnd_envelopingAction F n u)

end Operators

section Forms

/-- Conjugation preserves actual automorphic forms. -/
theorem finiteSmoothConj_mem_automorphic {f : FiniteSmoothRationalFunctions F n}
    (hf : f ∈ automorphicSubrepresentation F n) :
    finiteSmoothConj F n f ∈ automorphicSubrepresentation F n := by
  obtain ⟨hc, hk, hg⟩ := hf
  refine ⟨?_, ?_, ?_⟩
  · apply (isCenterFinite_iff_finiteSmoothCenterVector F n _).mpr
    refine FiniteVectors.IsFiniteVector.antilinear (finiteSmoothCenterRepresentation F n)
      (finiteSmoothConj F n) (fun z => ⟨ArchimedeanGL.centerConj F n z, ?_⟩)
      ((isCenterFinite_iff_finiteSmoothCenterVector F n f).mp hc)
    change finiteSmoothCenterAction F n z (finiteSmoothConj F n f) =
      finiteSmoothConj F n (finiteSmoothCenterAction F n (ArchimedeanGL.centerConj F n z) f)
    rw [finiteSmoothConj_centerAction, ArchimedeanGL.centerConj_centerConj]
  · exact FiniteVectors.IsFiniteVector.antilinear
      (infiniteSubgroupRightAction F n (standardInfiniteCompact F n))
      (continuousConj F n) (fun k => ⟨k, rfl⟩) hk
  · change f.val ∈ polynomialGrowthSubrepresentation F n at hg
    change continuousConj F n f.val ∈ polynomialGrowthSubrepresentation F n
    rw [mem_polynomialGrowthSubrepresentation] at hg ⊢
    intro b
    obtain ⟨C, hC, d, h⟩ := hg b
    refine ⟨C, hC, d, fun g => ?_⟩
    change ‖conj (evaluate F n f.val (AdelicGL.pair F n g b))‖ ≤ _
    rw [Complex.norm_conj]
    exact h g

/-- Conjugation preserves the stable operator core of actual forms. -/
theorem finiteSmoothConj_mem_operatorCore {f : FiniteSmoothRationalFunctions F n}
    (hf : f ∈ automorphicOperatorCore F n) :
    finiteSmoothConj F n f ∈ automorphicOperatorCore F n := by
  intro a
  have h := finiteSmoothConj_mem_automorphic F n (hf (operatorConj F n a))
  rw [operatorConj_val, finiteSmoothConjEnd_apply, finiteSmoothConj_finiteSmoothConj] at h
  exact h

/-- Pointwise complex conjugation of the constructed stable form space. -/
def stableConj :
    StableAutomorphicFunctions F n →ₛₗ[starRingEnd ℂ] StableAutomorphicFunctions F n where
  toFun f := ⟨finiteSmoothConj F n f.val, finiteSmoothConj_mem_operatorCore F n f.property⟩
  map_add' f g := Subtype.ext (map_add (finiteSmoothConj F n) f.val g.val)
  map_smul' c f := Subtype.ext (map_smulₛₗ (finiteSmoothConj F n) c f.val)

@[simp]
theorem stableConj_val (f : StableAutomorphicFunctions F n) :
    (stableConj F n f).val = finiteSmoothConj F n f.val := rfl

@[simp]
theorem stableConj_stableConj (f : StableAutomorphicFunctions F n) :
    stableConj F n (stableConj F n f) = f :=
  Subtype.ext (finiteSmoothConj_finiteSmoothConj F n f.val)

/-- Conjugation intertwines each operator with its conjugate. -/
theorem stableConj_operatorAction (a : automorphicOperatorAlgebra F n)
    (f : StableAutomorphicFunctions F n) :
    stableConj F n (stableAutomorphicAction F n a f) =
      stableAutomorphicAction F n (operatorConj F n a) (stableConj F n f) := by
  apply Subtype.ext
  change finiteSmoothConj F n (a.val f.val) =
    finiteSmoothConjEnd F n a.val (finiteSmoothConj F n f.val)
  rw [finiteSmoothConjEnd_apply, finiteSmoothConj_finiteSmoothConj]

/-- Pointwise complex conjugation of the stable form space, as an antilinear involution. -/
def stableConjEquiv :
    StableAutomorphicFunctions F n ≃ₛₗ[starRingEnd ℂ] StableAutomorphicFunctions F n :=
  { stableConj F n with
    invFun := stableConj F n
    left_inv := stableConj_stableConj F n
    right_inv := stableConj_stableConj F n }

@[simp]
theorem stableConjEquiv_apply (f : StableAutomorphicFunctions F n) :
    stableConjEquiv F n f = stableConj F n f := rfl

end Forms

section Cuspidal

variable [CompactSpace (AdeleQuotient F)]

/-- Constant terms of the conjugate function are the conjugate constant terms. -/
theorem constantTerm_continuousConj {a b : ℕ} (h : a + b = n)
    (f : ContinuousRationalFunctions F n) (g : AdelicGL F n) :
    constantTerm F n h (continuousConj F n f) g = conj (constantTerm F n h f g) := by
  let : MeasurableSpace (Matrix (Fin a) (Fin b) (AdeleQuotient F)) := borel _
  exact integral_conj (μ := matrixQuotientHaar F a b) (f := constantTermIntegrand F n h f g)

theorem isCuspidal_continuousConj {f : ContinuousRationalFunctions F n}
    (hf : IsCuspidal F n f) : IsCuspidal F n (continuousConj F n f) := by
  intro a b h ha hb g
  rw [constantTerm_continuousConj, hf a b h ha hb g, map_zero]

end Cuspidal

section Character

/-- Complex conjugation on `ℂˣ`, as a continuous homomorphism. -/
def unitsConj : ℂˣ →ₜ* ℂˣ where
  toMonoidHom := Units.map (starRingEnd ℂ).toMonoidHom
  continuous_toFun := Continuous.units_map _ Complex.continuous_conj

/-- The complex conjugate of an idele class character. -/
def conjCharacter (χ : IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ) : IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ :=
  unitsConj.comp χ

@[simp]
theorem conjCharacter_apply (χ : IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ)
    (x : IdeleClassGroup (𝓞 F) F) :
    ((conjCharacter F χ x : ℂˣ) : ℂ) = conj (χ x : ℂ) := rfl

theorem centralIdeleCharacter_conjCharacter (χ : IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ)
    (z : IdeleGroup (𝓞 F) F) :
    ((centralIdeleCharacter F (conjCharacter F χ) z : ℂˣ) : ℂ) =
      conj (centralIdeleCharacter F χ z : ℂ) := rfl

theorem norm_conjCharacter (χ : IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ)
    (x : IdeleClassGroup (𝓞 F) F) :
    ‖((conjCharacter F χ x : ℂˣ) : ℂ)‖ = ‖(χ x : ℂ)‖ := by
  rw [conjCharacter_apply, Complex.norm_conj]

end Character

namespace OperatorRealization

variable {F n} (S : OperatorRealization F n)

local instance conjugateRealizationSpaceGroup (S : OperatorRealization F n) :
    AddCommGroup S.Space :=
  Submodule.addCommGroup _

/-- The pointwise complex conjugate of an actual operator realization. -/
def conjugate : OperatorRealization F n where
  toSubmodule := S.toSubmodule.map
    (stableConjEquiv F n :
      StableAutomorphicFunctions F n →ₛₗ[starRingEnd ℂ] StableAutomorphicFunctions F n)
  apply_mem_toSubmodule a _ hf := by
    obtain ⟨f, hfS, rfl⟩ := Submodule.mem_map.mp hf
    have h := stableConj_operatorAction F n (operatorConj F n a) f
    rw [operatorConj_operatorConj] at h
    change stableAutomorphicAction F n a (stableConj F n f) ∈ _
    rw [← h]
    exact Submodule.mem_map_of_mem (S.apply_mem_toSubmodule (operatorConj F n a) hfS)

/-- Pointwise conjugation is an antilinear bijection onto the conjugate realization. -/
def conjugateEquiv : S.Space ≃ₛₗ[starRingEnd ℂ] S.conjugate.Space :=
  (stableConjEquiv F n).submoduleMap S.toSubmodule

@[simp]
theorem conjugateEquiv_val (f : S.Space) :
    (S.conjugateEquiv f).val = stableConj F n f.val := rfl

@[simp]
theorem conjugateEquiv_symm_val (f : S.conjugate.Space) :
    (S.conjugateEquiv.symm f).val = stableConj F n f.val := rfl

/-- Conjugation turns each operator into its conjugate operator. -/
theorem conjugateEquiv_operatorAction (a : automorphicOperatorAlgebra F n) (f : S.Space) :
    S.conjugate.representation a (S.conjugateEquiv f) =
      S.conjugateEquiv (S.representation (operatorConj F n a) f) := by
  apply Subtype.ext
  have h := stableConj_operatorAction F n (operatorConj F n a) f.val
  rw [operatorConj_operatorConj] at h
  exact h.symm

theorem conjugateEquiv_finite (d : FiniteAdelicGL F n) (f : S.Space) :
    S.conjugate.finiteRepresentation d (S.conjugateEquiv f) =
      S.conjugateEquiv (S.finiteRepresentation d f) := by
  apply Subtype.ext
  have h := stableConj_operatorAction F n (finiteOperator F n d) f.val
  rw [operatorConj_finiteOperator] at h
  exact h.symm

theorem conjugateEquiv_compact (k : standardInfiniteCompact F n) (f : S.Space) :
    S.conjugate.compactRepresentation k (S.conjugateEquiv f) =
      S.conjugateEquiv (S.compactRepresentation k f) := by
  apply Subtype.ext
  have h := stableConj_operatorAction F n (compactOperator F n k) f.val
  rw [operatorConj_compactOperator] at h
  exact h.symm

theorem conjugateEquiv_envelopingAction (u : ArchimedeanGL.EnvelopingAlgebra F n)
    (f : S.Space) :
    S.conjugate.envelopingAction u (S.conjugateEquiv f) =
      S.conjugateEquiv (S.envelopingAction (ArchimedeanGL.envelopingConj F n u) f) := by
  apply Subtype.ext
  have h := stableConj_operatorAction F n
    (differentialOperator F n (ArchimedeanGL.envelopingConj F n u)) f.val
  rw [operatorConj_differentialOperator, ArchimedeanGL.envelopingConj_envelopingConj] at h
  exact h.symm

/-- Real Lie algebra elements commute with conjugation. -/
theorem conjugateEquiv_lieAction (X : ArchimedeanGL.RealLieAlgebra F n) (f : S.Space) :
    S.conjugate.lieAction X (S.conjugateEquiv f) = S.conjugateEquiv (S.lieAction X f) := by
  have hX : ArchimedeanGL.envelopingConj F n
      (ArchimedeanGL.envelopingGenerator F n (ArchimedeanGL.complexify F n X)) =
      ArchimedeanGL.envelopingGenerator F n (ArchimedeanGL.complexify F n X) := by
    rw [ArchimedeanGL.envelopingConj_generator, ArchimedeanGL.complexConj_complexify]
  apply Subtype.ext
  have h := stableConj_operatorAction F n (differentialOperator F n
    (ArchimedeanGL.envelopingGenerator F n (ArchimedeanGL.complexify F n X))) f.val
  rw [operatorConj_differentialOperator, hX] at h
  exact h.symm

@[simp]
theorem toContinuous_conjugateEquiv (f : S.Space) :
    S.conjugate.toContinuous (S.conjugateEquiv f) = continuousConj F n (S.toContinuous f) :=
  rfl

@[simp]
theorem toContinuous_conjugateEquiv_symm (f : S.conjugate.Space) :
    S.toContinuous (S.conjugateEquiv.symm f) = continuousConj F n (S.conjugate.toContinuous f) :=
  rfl

theorem evaluate_conjugateEquiv (f : S.Space) (x : AdelicGL F n) :
    evaluate F n (S.conjugate.toContinuous (S.conjugateEquiv f)) x =
      conj (evaluate F n (S.toContinuous f) x) := rfl

/-- Invariant subspaces correspond under conjugation. -/
def conjugateSubrepresentationOrderIso :
    Subrepresentation S.representation ≃o Subrepresentation S.conjugate.representation :=
  antilinearConjugatedSubrepresentationOrderIso S.representation S.conjugate.representation
    (operatorConj F n) S.conjugateEquiv S.conjugateEquiv_operatorAction

theorem conjugate_isIrreducible_iff : S.conjugate.IsIrreducible ↔ S.IsIrreducible :=
  S.conjugateSubrepresentationOrderIso.isSimpleOrder_iff.symm

/-- The conjugate realization has the conjugate central character. -/
theorem HasCentralCharacter.conjugate {χ : IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ}
    (hS : S.HasCentralCharacter χ) : S.conjugate.HasCentralCharacter (conjCharacter F χ) := by
  rw [hasCentralCharacter_iff]
  intro f
  obtain ⟨g, rfl⟩ := S.conjugateEquiv.surjective f
  rw [mem_centralCharacterAutomorphicSubrepresentation]
  intro z x
  change conj (evaluate F n (S.toContinuous g) (AdelicGL.scalar F n z * x)) =
    conj (centralIdeleCharacter F χ z : ℂ) * conj (evaluate F n (S.toContinuous g) x)
  rw [S.centralCharacter_evaluate χ hS g z x, map_mul]

section Cuspidal

variable [CompactSpace (AdeleQuotient F)]

theorem conjugate_isCuspidal_iff : S.conjugate.IsCuspidal ↔ S.IsCuspidal := by
  rw [isCuspidal_iff, isCuspidal_iff]
  constructor
  · intro hc f
    have h := isCuspidal_continuousConj F n (hc (S.conjugateEquiv f))
    rw [toContinuous_conjugateEquiv, continuousConj_continuousConj] at h
    exact h
  · intro hs f
    obtain ⟨g, rfl⟩ := S.conjugateEquiv.surjective f
    rw [toContinuous_conjugateEquiv]
    exact isCuspidal_continuousConj F n (hs g)

end Cuspidal

end OperatorRealization

namespace CuspidalOperatorRealization

variable {F} [CompactSpace (AdeleQuotient F)] {r : ℕ} (T : CuspidalOperatorRealization F r)

/-- The pointwise complex conjugate of an actual irreducible cuspidal realization. -/
def conjugate : CuspidalOperatorRealization F r where
  realization := T.realization.conjugate
  irreducible := T.realization.conjugate_isIrreducible_iff.mpr T.irreducible
  cuspidal := T.realization.conjugate_isCuspidal_iff.mpr T.cuspidal

/-- Pointwise conjugation as an antilinear bijection onto the conjugate realization. -/
def conjugateEquiv : T.Space ≃ₛₗ[starRingEnd ℂ] T.conjugate.Space :=
  T.realization.conjugateEquiv

theorem conjugateEquiv_finite (d : FiniteAdelicGL F (r + 1)) (f : T.Space) :
    T.conjugate.realization.finiteRepresentation d (T.conjugateEquiv f) =
      T.conjugateEquiv (T.realization.finiteRepresentation d f) :=
  T.realization.conjugateEquiv_finite d f

theorem conjugateEquiv_compact (k : standardInfiniteCompact F (r + 1)) (f : T.Space) :
    T.conjugate.realization.compactRepresentation k (T.conjugateEquiv f) =
      T.conjugateEquiv (T.realization.compactRepresentation k f) :=
  T.realization.conjugateEquiv_compact k f

theorem conjugateEquiv_lieAction (X : ArchimedeanGL.RealLieAlgebra F (r + 1)) (f : T.Space) :
    T.conjugate.realization.lieAction X (T.conjugateEquiv f) =
      T.conjugateEquiv (T.realization.lieAction X f) :=
  T.realization.conjugateEquiv_lieAction X f

theorem toContinuous_conjugateEquiv (f : T.Space) :
    T.conjugate.realization.toContinuous (T.conjugateEquiv f) =
      continuousConj F (r + 1) (T.realization.toContinuous f) :=
  rfl

theorem HasCentralCharacter.conjugate {χ : IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ}
    (hT : T.HasCentralCharacter χ) : T.conjugate.HasCentralCharacter (conjCharacter F χ) :=
  OperatorRealization.HasCentralCharacter.conjugate T.realization hT

end CuspidalOperatorRealization

end Langlands.Automorphic

namespace Langlands.ClassField.Global.RelativeWeilGroup

open Langlands.Automorphic Langlands.Global NumberField

/-- The conjugate of a realization with unitary central character has unitary central
character. -/
theorem HasUnitaryCentralCharacter.conjugate {F : Type u} [Field F] [NumberField F]
    [CompactSpace (AdeleQuotient F)] {r : ℕ} {T : CuspidalOperatorRealization F r}
    (hT : HasUnitaryCentralCharacter T) : HasUnitaryCentralCharacter T.conjugate := by
  obtain ⟨χ, hχ, hc⟩ := hT
  refine ⟨conjCharacter F χ, fun x => ?_, CuspidalOperatorRealization.HasCentralCharacter.conjugate T hc⟩
  rw [norm_conjCharacter]
  exact hχ x

end Langlands.ClassField.Global.RelativeWeilGroup
