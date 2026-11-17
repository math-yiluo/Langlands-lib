import Langlands.Automorphic.OperatorSubquotientPlaceComponent

/-!
# Place components of irreducible operator subquotients at the complex places

The complex-place half of `Langlands.Automorphic.OperatorSubquotientPlaceComponent`: for an
operator subquotient `Q` of `GL_n` over a number field and a complex place `v`, the place
actions of `Q` at `v` descend from the numerator realization `Q.upper`, and Worker 174's
construction of irreducible admissible place components for cuspidal realizations
(`Langlands.Automorphic.PlaceComponentExistence`) carries over to `Q`.

* `isComplexGKModule_complexPlace`: the place actions at `v` form a `(𝔤𝔩_n(ℂ), U(n))`-structure.
* `representation_mem_of_complexPlaceStable`: a subspace of `Q` stable under the place actions
  at `v` and under every linear map commuting with them is stable under the operator algebra.
* `exists_complexPlace_detection`: for irreducible `Q`, a continuous matrix representation of
  `U(n)` has a nonzero intertwiner into every nonzero place-stable subspace.
* `complexCarrier`, `isAdmissible_complexCarrier`: the carrier of `PlaceComponentCarrierComplex`
  for `Q`, admissible by joint admissibility of `Q`.
* `exists_complexPlaceComponent`: an irreducible admissible place-stable subspace of `Q`.
* `isComplexPlaceIsotypic_restrict`: for irreducible `Q`, every irreducible place-stable
  subspace `W` makes `Q` isotypic at `v` for the restricted `(𝔤, K)`-module of `W`.
-/

noncomputable section

universe u

open scoped TensorProduct Matrix

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic

attribute [local instance 100] LieRing.ofAssociativeRing

open Langlands.Global Langlands.Global.ArchimedeanGL PlaceComponent

local instance subquotientComplexRationalGroup {F : Type u} [Field F] [NumberField F] {n : ℕ} :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance subquotientComplexContinuousGroup {F : Type u} [Field F] [NumberField F]
    {n : ℕ} : AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance subquotientComplexSmoothGroup {F : Type u} [Field F] [NumberField F] {n : ℕ} :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance subquotientComplexFormsGroup {F : Type u} [Field F] [NumberField F] {n : ℕ} :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance subquotientComplexStableGroup {F : Type u} [Field F] [NumberField F] {n : ℕ} :
    AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _
local instance subquotientComplexSpaceGroup {F : Type u} [Field F] [NumberField F] {n : ℕ}
    (S : OperatorRealization F n) : AddCommGroup S.Space := Submodule.addCommGroup _

variable {F : Type u} [Field F] [NumberField F] {n : ℕ}

local notation "RP" =>
  {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsReal v}
local notation "CP" =>
  {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsComplex v}
local notation "CK" => Matrix.unitaryGroup (Fin n) ℂ
local notation "RM" => Matrix (Fin n) (Fin n) ℝ
local notation "CM" => Matrix (Fin n) (Fin n) ℂ

namespace OperatorSubquotient

variable (Q : OperatorSubquotient F n)

/-! ### Descent of the place laws from the numerator -/

/-- The complex-place actions of `Q` form a `(𝔤𝔩_n(ℂ), U(n))`-structure. -/
theorem isComplexGKModule_complexPlace (v : CP) :
    Archimedean.IsComplexGKModule n (Q.complexPlaceCompactRepresentation v)
      (Q.complexPlaceLieAction v) := by
  have hS := Q.upper.isComplexGKModule_complexPlace v
  have hcont := hS.2.1
  have hder := hS.2.2.1
  have hcov := hS.2.2.2
  refine ⟨Q.complexPlaceCompactRepresentation_isFiniteVector v, fun x μ => ?_,
    fun γ X hγ0 hγ x μ => ?_, fun k X x => ?_⟩
  · refine Q.forall_of_projection
      (P := fun x => Continuous fun k : CK => μ (Q.complexPlaceCompactRepresentation v k x))
      (fun g => ?_) x
    exact (hcont g (μ ∘ₗ Q.projection.toLinearMap)).congr fun k =>
      (Q.dual_projection μ _).trans
        (congrArg μ (Q.complexPlaceCompactRepresentation_projection v k g).symm)
  · refine Q.forall_of_projection
      (P := fun x => HasDerivAt (fun t => μ (Q.complexPlaceCompactRepresentation v (γ t) x))
        (μ (Q.complexPlaceLieAction v (1 ⊗ₜ X) x)) 0)
      (fun g => ?_) x
    have h0 := hder γ X hγ0 hγ g (μ ∘ₗ Q.projection.toLinearMap)
    have e1 : (fun t => (μ ∘ₗ Q.projection.toLinearMap)
        (Q.upper.complexPlaceCompactRepresentation v (γ t) g)) =
        fun t => μ (Q.complexPlaceCompactRepresentation v (γ t) (Q.projection g)) :=
      funext fun t => (Q.dual_projection μ _).trans
        (congrArg μ (Q.complexPlaceCompactRepresentation_projection v (γ t) g).symm)
    have e2 : (μ ∘ₗ Q.projection.toLinearMap) (Q.upper.complexPlaceLieAction v (1 ⊗ₜ X) g) =
        μ (Q.complexPlaceLieAction v (1 ⊗ₜ X) (Q.projection g)) :=
      (Q.dual_projection μ _).trans
        (congrArg μ (Q.complexPlaceLieAction_projection v (1 ⊗ₜ X) g).symm)
    exact (h0.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t =>
      (congrFun e1 t).symm)).congr_deriv e2
  · exact Q.comp_eq_of_projection
      (A := Q.complexPlaceCompactRepresentation v k) (B := Q.complexPlaceLieAction v (1 ⊗ₜ X))
      (C := Q.complexPlaceLieAction v (1 ⊗ₜ ((k : CM) * X * (star k : CM))))
      (D := Q.complexPlaceCompactRepresentation v k)
      (Q.complexPlaceCompactRepresentation_projection v k)
      (Q.complexPlaceLieAction_projection v _) (Q.complexPlaceLieAction_projection v _)
      (Q.complexPlaceCompactRepresentation_projection v k) (hcov k X) x

theorem isLocallyFinite_complexPlace (v : CP) :
    IsLocallyFinite (Q.complexPlaceCompactRepresentation v) := fun x =>
  ⟨FiniteVectors.orbitSpan _ x, Q.complexPlaceCompactRepresentation_isFiniteVector v x,
    FiniteVectors.self_mem_orbitSpan _ x,
    fun k _ hy => (FiniteVectors.orbitSubrepresentation _ x).apply_mem_toSubmodule k hy⟩

theorem isWeaklyContinuous_complexPlace (v : CP) :
    IsWeaklyContinuous (Q.complexPlaceCompactRepresentation v) :=
  fun μ x => (Q.isComplexGKModule_complexPlace v).2.1 x μ

/-- Lie actions at distinct complex places commute. -/
theorem complexPlaceLieAction_comm_of_ne {v w : CP} (h : w ≠ v) (X Y : ℂ ⊗[ℝ] CM)
    (f : Q.Space) :
    Q.complexPlaceLieAction v X (Q.complexPlaceLieAction w Y f) =
      Q.complexPlaceLieAction w Y (Q.complexPlaceLieAction v X f) :=
  Q.comp_eq_of_projection
    (A := Q.complexPlaceLieAction v X) (B := Q.complexPlaceLieAction w Y)
    (C := Q.complexPlaceLieAction w Y) (D := Q.complexPlaceLieAction v X)
    (Q.complexPlaceLieAction_projection v X) (Q.complexPlaceLieAction_projection w Y)
    (Q.complexPlaceLieAction_projection w Y) (Q.complexPlaceLieAction_projection v X)
    (Q.upper.complexPlaceLieAction_comm_of_ne h X Y) f

/-- At distinct complex places the compact and Lie operators commute. -/
theorem complexPlaceCompactRepresentation_complexPlaceLieAction_of_ne (v w : CP) (h : w ≠ v)
    (k : CK) (X : ℂ ⊗[ℝ] CM) (f : Q.Space) :
    Q.complexPlaceCompactRepresentation v k (Q.complexPlaceLieAction w X f) =
      Q.complexPlaceLieAction w X (Q.complexPlaceCompactRepresentation v k f) :=
  Q.comp_eq_of_projection
    (A := Q.complexPlaceCompactRepresentation v k) (B := Q.complexPlaceLieAction w X)
    (C := Q.complexPlaceLieAction w X) (D := Q.complexPlaceCompactRepresentation v k)
    (Q.complexPlaceCompactRepresentation_projection v k)
    (Q.complexPlaceLieAction_projection w X) (Q.complexPlaceLieAction_projection w X)
    (Q.complexPlaceCompactRepresentation_projection v k)
    (Q.upper.complexPlaceCompactRepresentation_complexPlaceLieAction_of_ne v w h k X) f

/-- Compact translation at a complex place commutes with every real-place Lie action. -/
theorem complexPlaceCompactRepresentation_realPlaceLieAction (v : CP) (w : RP) (k : CK)
    (X : ℂ ⊗[ℝ] RM) (f : Q.Space) :
    Q.complexPlaceCompactRepresentation v k (Q.realPlaceLieAction w X f) =
      Q.realPlaceLieAction w X (Q.complexPlaceCompactRepresentation v k f) :=
  Q.comp_eq_of_projection
    (A := Q.complexPlaceCompactRepresentation v k) (B := Q.realPlaceLieAction w X)
    (C := Q.realPlaceLieAction w X) (D := Q.complexPlaceCompactRepresentation v k)
    (Q.complexPlaceCompactRepresentation_projection v k)
    (Q.realPlaceLieAction_projection w X) (Q.realPlaceLieAction_projection w X)
    (Q.complexPlaceCompactRepresentation_projection v k)
    (Q.upper.complexPlaceCompactRepresentation_realPlaceLieAction v w k X) f

/-- Compact translation by factors trivial at `v` commutes with the compact action at `v`. -/
theorem compact_comm_complexPlaceCompact (v : CP) {q : ArchimedeanCompactFactors F n}
    (hq : q.2 v = 1) (l : CK) (y : Q.Space) :
    Q.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n q)
        (Q.complexPlaceCompactRepresentation v l y) =
      Q.complexPlaceCompactRepresentation v l
        (Q.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n q) y) :=
  Q.comp_eq_of_projection
    (A := Q.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n q))
    (B := Q.complexPlaceCompactRepresentation v l)
    (C := Q.complexPlaceCompactRepresentation v l)
    (D := Q.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n q))
    (Q.compactRepresentation_projection _) (Q.complexPlaceCompactRepresentation_projection v l)
    (Q.complexPlaceCompactRepresentation_projection v l) (Q.compactRepresentation_projection _)
    (Q.upper.compact_comm_complexPlaceCompact v hq l) y

/-- Compact translation by factors trivial at `v` commutes with the Lie action at `v`. -/
theorem compact_comm_complexPlaceLie (v : CP) {q : ArchimedeanCompactFactors F n}
    (hq : q.2 v = 1) (X : ℂ ⊗[ℝ] CM) (y : Q.Space) :
    Q.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n q)
        (Q.complexPlaceLieAction v X y) =
      Q.complexPlaceLieAction v X
        (Q.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n q) y) :=
  Q.comp_eq_of_projection
    (A := Q.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n q))
    (B := Q.complexPlaceLieAction v X) (C := Q.complexPlaceLieAction v X)
    (D := Q.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n q))
    (Q.compactRepresentation_projection _) (Q.complexPlaceLieAction_projection v X)
    (Q.complexPlaceLieAction_projection v X) (Q.compactRepresentation_projection _)
    (Q.upper.compact_comm_complexPlaceLie v hq X) y

/-- A compact translation splits into its factor at `v` and the rest. -/
theorem compact_eq_complexPlace_mul (v : CP) (k : standardInfiniteCompact F n) (y : Q.Space) :
    Q.compactRepresentation k y =
      Q.complexPlaceCompactRepresentation v ((factorEquiv k).2 v)
        (Q.compactRepresentation
          (ArchimedeanCompactFactors.toStandardCompact F n (awayComplex v (factorEquiv k))) y) :=
  Q.eq_comp_of_projection
    (A := Q.compactRepresentation k)
    (C := Q.complexPlaceCompactRepresentation v ((factorEquiv k).2 v))
    (D := Q.compactRepresentation
      (ArchimedeanCompactFactors.toStandardCompact F n (awayComplex v (factorEquiv k))))
    (Q.compactRepresentation_projection k) (Q.complexPlaceCompactRepresentation_projection v _)
    (Q.compactRepresentation_projection _) (Q.upper.compact_eq_complexPlace_mul v k) y

/-! ### Operator stability at a complex place -/

/-- The complexified Lie algebra preserves a subspace stable under the place actions at the
complex place `v` and under every linear map commuting with them. -/
theorem complexLieAction_mem_of_complexPlaceStable (v : CP) (Z : Submodule ℂ Q.Space)
    (hmap : ∀ A : Q.Space →ₗ[ℂ] Q.Space,
      (∀ k x, A (Q.complexPlaceCompactRepresentation v k x) =
        Q.complexPlaceCompactRepresentation v k (A x)) →
      (∀ X x, A (Q.complexPlaceLieAction v X x) = Q.complexPlaceLieAction v X (A x)) →
      ∀ x ∈ Z, A x ∈ Z)
    (hπ : ∀ (X : ℂ ⊗[ℝ] CM), ∀ x ∈ Z, Q.complexPlaceLieAction v X x ∈ Z)
    (Y : ComplexLieAlgebra F n) : ∀ x ∈ Z, Q.complexLieAction Y x ∈ Z := by
  have hreal : ∀ (w : RP) (X : ℂ ⊗[ℝ] RM), ∀ x ∈ Z, Q.realPlaceLieAction w X x ∈ Z :=
    fun w X x hx => hmap (Q.realPlaceLieAction w X)
      (fun k y => (Q.complexPlaceCompactRepresentation_realPlaceLieAction v w k X y).symm)
      (fun Y y => Q.realPlaceLieAction_comm_complexPlace w v X Y y) x hx
  have hcomplex : ∀ (w : CP) (X : ℂ ⊗[ℝ] CM), ∀ x ∈ Z, Q.complexPlaceLieAction w X x ∈ Z := by
    intro w X x hx
    by_cases hw : w = v
    · subst hw
      exact hπ X x hx
    · exact hmap (Q.complexPlaceLieAction w X)
        (fun k y =>
          (Q.complexPlaceCompactRepresentation_complexPlaceLieAction_of_ne v w hw k X y).symm)
        (fun Y y => (Q.complexPlaceLieAction_comm_of_ne hw Y X y).symm) x hx
  intro x hx
  induction Y using TensorProduct.inductionOn with
  | tmul z X =>
    have hzX : z ⊗ₜ[ℝ] X = z • complexify F n X := by
      rw [complexify_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    have heq : Q.complexLieAction (z ⊗ₜ[ℝ] X) x =
        z • Q.complexLieAction (complexify F n X) x :=
      (congrArg (fun Y => Q.complexLieAction Y x) hzX).trans
        (LinearMap.congr_fun (Q.complexLieAction.map_smul z (complexify F n X)) x)
    have hmem : Q.complexLieAction (complexify F n X) x ∈ Z := by
      refine (congrArg (fun y => y ∈ Z) (Q.complexify_action_eq_sum_place X x)).mpr ?_
      refine Submodule.add_mem _ (Submodule.sum_mem _ fun w _ => ?_)
        (Submodule.sum_mem _ fun w _ => ?_)
      · exact hreal w _ x hx
      · exact hcomplex w _ x hx
    exact (congrArg (fun y => y ∈ Z) heq).mpr (Submodule.smul_mem _ z hmem)
  | add Y₁ Y₂ h₁ h₂ =>
    have heq : Q.complexLieAction (Y₁ + Y₂) x =
        Q.complexLieAction Y₁ x + Q.complexLieAction Y₂ x :=
      LinearMap.congr_fun (Q.complexLieAction.map_add Y₁ Y₂) x
    exact (congrArg (fun y => y ∈ Z) heq).mpr (Submodule.add_mem _ h₁ h₂)

/-- The enveloping algebra preserves such a subspace. -/
theorem envelopingAction_mem_of_complexPlaceStable (v : CP) (Z : Submodule ℂ Q.Space)
    (hmap : ∀ A : Q.Space →ₗ[ℂ] Q.Space,
      (∀ k x, A (Q.complexPlaceCompactRepresentation v k x) =
        Q.complexPlaceCompactRepresentation v k (A x)) →
      (∀ X x, A (Q.complexPlaceLieAction v X x) = Q.complexPlaceLieAction v X (A x)) →
      ∀ x ∈ Z, A x ∈ Z)
    (hπ : ∀ (X : ℂ ⊗[ℝ] CM), ∀ x ∈ Z, Q.complexPlaceLieAction v X x ∈ Z)
    (u : EnvelopingAlgebra F n) : ∀ x ∈ Z, Q.envelopingAction u x ∈ Z := by
  have hu : u ∈ Algebra.adjoin ℂ
      (Set.range (UniversalEnvelopingAlgebra.ι ℂ :
        ComplexLieAlgebra F n → EnvelopingAlgebra F n)) := by
    rw [Langlands.Algebra.LieCasimir.enveloping_adjoin_range]
    trivial
  induction hu using Algebra.adjoin_induction with
  | mem u hu =>
    obtain ⟨Y, rfl⟩ := hu
    intro x hx
    exact Q.complexLieAction_mem_of_complexPlaceStable v Z hmap hπ Y x hx
  | algebraMap c =>
    intro x hx
    have heq : Q.envelopingAction (algebraMap ℂ (EnvelopingAlgebra F n) c) x = c • x :=
      LinearMap.congr_fun (Q.envelopingAction.commutes c) x
    exact (congrArg (fun y => y ∈ Z) heq).mpr (Submodule.smul_mem _ c hx)
  | add a b _ _ ha hb =>
    intro x hx
    have heq : Q.envelopingAction (a + b) x =
        Q.envelopingAction a x + Q.envelopingAction b x :=
      LinearMap.congr_fun (Q.envelopingAction.map_add a b) x
    exact (congrArg (fun y => y ∈ Z) heq).mpr (Submodule.add_mem _ (ha x hx) (hb x hx))
  | mul a b _ _ ha hb =>
    intro x hx
    have heq : Q.envelopingAction (a * b) x =
        Q.envelopingAction a (Q.envelopingAction b x) :=
      LinearMap.congr_fun (Q.envelopingAction.map_mul a b) x
    exact (congrArg (fun y => y ∈ Z) heq).mpr (ha _ (hb x hx))

/-- **Operator stability at a complex place.** A subspace of `Q` stable under the place
actions at `v` and under every linear map commuting with them is stable under the whole
operator algebra. -/
theorem representation_mem_of_complexPlaceStable (v : CP) (Z : Submodule ℂ Q.Space)
    (hmap : ∀ A : Q.Space →ₗ[ℂ] Q.Space,
      (∀ k x, A (Q.complexPlaceCompactRepresentation v k x) =
        Q.complexPlaceCompactRepresentation v k (A x)) →
      (∀ X x, A (Q.complexPlaceLieAction v X x) = Q.complexPlaceLieAction v X (A x)) →
      ∀ x ∈ Z, A x ∈ Z)
    (hκ : ∀ (k : CK), ∀ x ∈ Z, Q.complexPlaceCompactRepresentation v k x ∈ Z)
    (hπ : ∀ (X : ℂ ⊗[ℝ] CM), ∀ x ∈ Z, Q.complexPlaceLieAction v X x ∈ Z)
    (a : automorphicOperatorAlgebra F n) : ∀ x ∈ Z, Q.representation a x ∈ Z := by
  obtain ⟨e, he⟩ := a
  induction he using Algebra.adjoin_induction with
  | mem e he =>
    rcases he with (⟨g, rfl⟩ | ⟨k, rfl⟩) | ⟨u, rfl⟩
    · intro x hx
      exact hmap (Q.finiteRepresentation g)
        (fun k y => Q.finiteRepresentation_complexPlaceCompactRepresentation g v k y)
        (fun X y => Q.finiteRepresentation_complexPlaceLieAction g v X y) x hx
    · intro x hx
      have hsplit := Q.compact_eq_complexPlace_mul v k x
      have hq := awayComplex_snd_self v (factorEquiv k)
      have hy := hmap (Q.compactRepresentation
          (ArchimedeanCompactFactors.toStandardCompact F n (awayComplex v (factorEquiv k))))
        (fun l y => Q.compact_comm_complexPlaceCompact v hq l y)
        (fun X y => Q.compact_comm_complexPlaceLie v hq X y) x hx
      exact (congrArg (fun y => y ∈ Z) hsplit).mpr (hκ _ _ hy)
    · intro x hx
      exact Q.envelopingAction_mem_of_complexPlaceStable v Z hmap hπ u x hx
  | algebraMap c =>
    intro x hx
    have h := Q.representation_algebraMap c x
    exact (congrArg (fun y => y ∈ Z) h).mpr (Submodule.smul_mem _ c hx)
  | add e₁ e₂ he₁ he₂ h₁ h₂ =>
    intro x hx
    have h : Q.representation (⟨e₁, he₁⟩ + ⟨e₂, he₂⟩ : automorphicOperatorAlgebra F n) x =
        Q.representation ⟨e₁, he₁⟩ x + Q.representation ⟨e₂, he₂⟩ x :=
      LinearMap.congr_fun (Q.operatorAction.map_add _ _) x
    exact (congrArg (fun y => y ∈ Z) h).mpr (Submodule.add_mem _ (h₁ x hx) (h₂ x hx))
  | mul e₁ e₂ he₁ he₂ h₁ h₂ =>
    intro x hx
    have h : Q.representation (⟨e₁, he₁⟩ * ⟨e₂, he₂⟩ : automorphicOperatorAlgebra F n) x =
        Q.representation ⟨e₁, he₁⟩ (Q.representation ⟨e₂, he₂⟩ x) :=
      LinearMap.congr_fun (map_mul Q.representation _ _) x
    exact (congrArg (fun y => y ∈ Z) h).mpr (h₁ _ (h₂ x hx))

/-- For irreducible `Q`, such a subspace is `⊥` or `⊤`. -/
theorem eq_bot_or_eq_top_of_complexPlaceStable (hQ : Q.IsIrreducible) (v : CP)
    (Z : Submodule ℂ Q.Space)
    (hmap : ∀ A : Q.Space →ₗ[ℂ] Q.Space,
      (∀ k x, A (Q.complexPlaceCompactRepresentation v k x) =
        Q.complexPlaceCompactRepresentation v k (A x)) →
      (∀ X x, A (Q.complexPlaceLieAction v X x) = Q.complexPlaceLieAction v X (A x)) →
      ∀ x ∈ Z, A x ∈ Z)
    (hκ : ∀ (k : CK), ∀ x ∈ Z, Q.complexPlaceCompactRepresentation v k x ∈ Z)
    (hπ : ∀ (X : ℂ ⊗[ℝ] CM), ∀ x ∈ Z, Q.complexPlaceLieAction v X x ∈ Z) :
    Z = ⊥ ∨ Z = ⊤ := by
  let R : Subrepresentation Q.representation :=
    { toSubmodule := Z
      apply_mem_toSubmodule := fun a x hx =>
        Q.representation_mem_of_complexPlaceStable v Z hmap hκ hπ a x hx }
  rcases hQ.eq_bot_or_eq_top R with h | h
  · exact Or.inl (congrArg Subrepresentation.toSubmodule h)
  · exact Or.inr (congrArg Subrepresentation.toSubmodule h)

/-! ### Detection at a complex place -/

/-- **Detection at a complex place.** For irreducible nonzero `Q`, some continuous matrix
representation of `U(n)` has a nonzero intertwiner into every nonzero stable subspace for the
place actions at the complex place `v`. -/
theorem exists_complexPlace_detection (hQ : Q.IsIrreducible) [Nontrivial Q.Space] (v : CP) :
    ∃ (d : ℕ) (τ : CK →* Matrix (Fin d) (Fin d) ℂ), Continuous τ ∧
      ∀ W : Submodule ℂ Q.Space, IsStable (Q.complexPlaceCompactRepresentation v)
          (Q.complexPlaceLieAction v) W → W ≠ ⊥ →
        intertwiners (Q.complexPlaceCompactRepresentation v) W d τ ≠ ⊥ := by
  refine (exists_ne (0 : Q.Space)).elim fun x₀ hx₀ => ?_
  refine (exists_not_mem_freeSet (π := Q.complexPlaceLieAction v)
    (Q.isLocallyFinite_complexPlace v) (Q.isWeaklyContinuous_complexPlace v) hx₀).elim
    fun d hd => hd.elim fun τ hτn => ?_
  have hτ := hτn.1
  have hnot := hτn.2
  have hZ := Q.eq_bot_or_eq_top_of_complexPlaceStable hQ v
    (freeSet (Q.complexPlaceLieAction v) (Q.isLocallyFinite_complexPlace v)
      (Q.isWeaklyContinuous_complexPlace v) τ)
    (fun A hAκ hAπ x hx => freeSet_map A hAκ hAπ hx)
    (fun k x hx => freeSet_compact k hx) (fun X x hx => freeSet_lie X hx)
  have hbot : freeSet (Q.complexPlaceLieAction v) (Q.isLocallyFinite_complexPlace v)
      (Q.isWeaklyContinuous_complexPlace v) τ = ⊥ := by
    rcases hZ with h | h
    · exact h
    · exfalso
      apply hnot
      rw [h]
      trivial
  refine ⟨d, τ, hτ, ?_⟩
  intro W hWs hW
  exact intertwiners_ne_bot_of_freeSet_eq_bot (hfin := Q.isLocallyFinite_complexPlace v)
    (hweak := Q.isWeaklyContinuous_complexPlace v) hbot hWs hW

/-! ### The carrier at a complex place -/

/-- The carrier at a complex place: linear maps `ℂ^m → Q` with `L`-fixed values intertwining
`R` with the compact action on the factors trivial at `v`. -/
def complexCarrier (v : CP) (L : Subgroup (FiniteAdelicGL F n)) {m : ℕ}
    (R : Representation ℂ (ArchimedeanCompactFactors F n) (Fin m → ℂ)) :
    Submodule ℂ ((Fin m → ℂ) →ₗ[ℂ] Q.Space) where
  carrier := {φ | (∀ x, φ x ∈ fixedVectors Q.finiteRepresentation L) ∧
    ∀ q : ArchimedeanCompactFactors F n, q.2 v = 1 → ∀ x,
      φ (R q x) = Q.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n q)
        (φ x)}
  add_mem' := by
    rintro φ ψ ⟨h1, h2⟩ ⟨h3, h4⟩
    exact ⟨fun x => Submodule.add_mem _ (h1 x) (h3 x), fun q hq x =>
      (congrArg₂ (· + ·) (h2 q hq x) (h4 q hq x)).trans (map_add _ _ _).symm⟩
  zero_mem' := ⟨fun _ => Submodule.zero_mem _, fun q _ x => (map_zero _).symm⟩
  smul_mem' := by
    rintro c φ ⟨h1, h2⟩
    exact ⟨fun x => Submodule.smul_mem _ c (h1 x), fun q hq x =>
      (congrArg (c • ·) (h2 q hq x)).trans (map_smul _ c _).symm⟩

/-- The carrier is stable under post-composition with the place actions at `v`. -/
theorem isStable_complexCarrier (v : CP) (L : Subgroup (FiniteAdelicGL F n)) {m : ℕ}
    (R : Representation ℂ (ArchimedeanCompactFactors F n) (Fin m → ℂ)) :
    IsStable (postRep m (Q.complexPlaceCompactRepresentation v))
      (postLie m (Q.complexPlaceLieAction v)) (Q.complexCarrier v L R) := by
  refine ⟨fun l φ hφ => ⟨fun x => ?_, fun q hq x => ?_⟩,
    fun X φ hφ => ⟨fun x => ?_, fun q hq x => ?_⟩⟩
  · intro d
    exact (Q.finiteRepresentation_complexPlaceCompactRepresentation d v l (φ x)).trans
      (congrArg (Q.complexPlaceCompactRepresentation v l) (hφ.1 x d))
  · exact (congrArg (Q.complexPlaceCompactRepresentation v l) (hφ.2 q hq x)).trans
      (Q.compact_comm_complexPlaceCompact v hq l (φ x)).symm
  · intro d
    exact (Q.finiteRepresentation_complexPlaceLieAction d v X (φ x)).trans
      (congrArg (Q.complexPlaceLieAction v X) (hφ.1 x d))
  · exact (congrArg (Q.complexPlaceLieAction v X) (hφ.2 q hq x)).trans
      (Q.compact_comm_complexPlaceLie v hq X (φ x)).symm

/-- The curried form of an intertwiner into the carrier intertwines `τ ⊗ R`. -/
theorem lift_mem_jointMultiplicity_complex (v : CP) (L : Subgroup (FiniteAdelicGL F n))
    {d m : ℕ} (τ : CK →* Matrix (Fin d) (Fin d) ℂ)
    (R : Representation ℂ (ArchimedeanCompactFactors F n) (Fin m → ℂ))
    {Φ : (Fin d → ℂ) →ₗ[ℂ] ((Fin m → ℂ) →ₗ[ℂ] Q.Space)}
    (hΦ : Φ ∈ intertwiners (postRep m (Q.complexPlaceCompactRepresentation v))
      (Q.complexCarrier v L R) d τ) :
    (∀ t, TensorProduct.lift Φ t ∈ fixedVectors Q.finiteRepresentation L) ∧
      ∀ (k : standardInfiniteCompact F n) t,
        TensorProduct.lift Φ (complexCarrierRep v τ R k t) =
          Q.compactRepresentation k (TensorProduct.lift Φ t) := by
  refine ⟨fun t => ?_, fun k t => ?_⟩
  · induction t using TensorProduct.inductionOn with
    | tmul a b => exact (hΦ.1 a).1 b
    | add t₁ t₂ h₁ h₂ =>
      exact (map_add (TensorProduct.lift Φ) t₁ t₂).symm ▸ Submodule.add_mem _ h₁ h₂
  · induction t using TensorProduct.inductionOn with
    | tmul a b =>
      have hp := awayComplex_snd_self v (factorEquiv k)
      have e1 : Φ (τ ((factorEquiv k).2 v) *ᵥ a) (R (awayComplex v (factorEquiv k)) b) =
          Q.complexPlaceCompactRepresentation v ((factorEquiv k).2 v)
            (Φ a (R (awayComplex v (factorEquiv k)) b)) :=
        LinearMap.congr_fun (hΦ.2 ((factorEquiv k).2 v) a) _
      have e2 : Φ a (R (awayComplex v (factorEquiv k)) b) =
          Q.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n
            (awayComplex v (factorEquiv k))) (Φ a b) := (hΦ.1 a).2 _ hp b
      exact e1.trans ((congrArg (Q.complexPlaceCompactRepresentation v ((factorEquiv k).2 v))
        e2).trans (Q.compact_eq_complexPlace_mul v k (Φ a b)).symm)
    | add t₁ t₂ h₁ h₂ =>
      exact ((congrArg (TensorProduct.lift Φ) (map_add _ t₁ t₂)).trans
        ((map_add _ _ _).trans (congrArg₂ (· + ·) h₁ h₂))).trans
        ((map_add _ _ _).symm.trans (congrArg _ (map_add _ t₁ t₂).symm))

/-- **Admissibility of the carrier.** If `Q` is jointly admissible, the carrier at a complex
place is admissible for the compact action at `v`. -/
theorem isAdmissible_complexCarrier (hJ : Q.IsJointlyAdmissible) (v : CP)
    (L : OpenSubgroup (FiniteAdelicGL F n)) {m : ℕ}
    (R : Representation ℂ (ArchimedeanCompactFactors F n) (Fin m → ℂ)) :
    PlaceComponent.IsAdmissible (postRep m (Q.complexPlaceCompactRepresentation v))
      (Q.complexCarrier v L.toSubgroup R) := by
  intro d τ _
  have : Module.Free ℂ ((Fin d → ℂ) ⊗[ℂ] (Fin m → ℂ)) := Module.Free.of_divisionRing ℂ _
  let ε := (Module.finBasis ℂ ((Fin d → ℂ) ⊗[ℂ] (Fin m → ℂ))).equivFun
  let σ := conjRep ε (complexCarrierRep v τ R)
  have hfin : FiniteDimensional ℂ (jointMultiplicitySpace Q.finiteRepresentation
      Q.compactRepresentation L.toSubgroup σ) := hJ L _ σ
  have hmem : ∀ Φ ∈ intertwiners (postRep m (Q.complexPlaceCompactRepresentation v))
      (Q.complexCarrier v L.toSubgroup R) d τ,
      TensorProduct.lift Φ ∘ₗ ε.symm.toLinearMap ∈ jointMultiplicitySpace
        Q.finiteRepresentation Q.compactRepresentation L.toSubgroup σ := by
    intro Φ hΦ
    have h := Q.lift_mem_jointMultiplicity_complex v L.toSubgroup τ R hΦ
    refine ⟨fun y => h.1 _, fun k y => ?_⟩
    have hσ : ε.symm (σ k y) = complexCarrierRep v τ R k (ε.symm y) :=
      ε.symm_apply_apply (complexCarrierRep v τ R k (ε.symm y))
    exact (congrArg (TensorProduct.lift Φ) hσ).trans (h.2 k (ε.symm y))
  let Ψ : intertwiners (postRep m (Q.complexPlaceCompactRepresentation v))
      (Q.complexCarrier v L.toSubgroup R) d τ →ₗ[ℂ] jointMultiplicitySpace
        Q.finiteRepresentation Q.compactRepresentation L.toSubgroup σ :=
    { toFun := fun Φ => ⟨TensorProduct.lift Φ.1 ∘ₗ ε.symm.toLinearMap, hmem Φ.1 Φ.2⟩
      map_add' := fun Φ₁ Φ₂ => Subtype.ext
        ((congrArg (· ∘ₗ ε.symm.toLinearMap)
          ((TensorProduct.lift.equiv (RingHom.id ℂ) _ _ _).map_add Φ₁.1 Φ₂.1)).trans
          (LinearMap.add_comp _ _ _))
      map_smul' := fun c Φ => Subtype.ext
        ((congrArg (· ∘ₗ ε.symm.toLinearMap)
          ((TensorProduct.lift.equiv (RingHom.id ℂ) _ _ _).map_smul c Φ.1)).trans
          (LinearMap.smul_comp _ _ _)) }
  have hΨ : Function.Injective Ψ := by
    intro Φ₁ Φ₂ h
    have h1 : TensorProduct.lift Φ₁.1 ∘ₗ ε.symm.toLinearMap =
        TensorProduct.lift Φ₂.1 ∘ₗ ε.symm.toLinearMap := congrArg Subtype.val h
    have h2 : TensorProduct.lift Φ₁.1 = TensorProduct.lift Φ₂.1 :=
      LinearMap.ext fun t => by
        have := LinearMap.congr_fun h1 (ε t)
        simpa using this
    exact Subtype.ext ((TensorProduct.lift.equiv (RingHom.id ℂ) _ _ _).injective h2)
  have hN : IsNoetherian ℂ (jointMultiplicitySpace Q.finiteRepresentation
      Q.compactRepresentation L.toSubgroup σ) :=
    isNoetherian_of_isNoetherianRing_of_finite ℂ (jointMultiplicitySpace
      Q.finiteRepresentation Q.compactRepresentation L.toSubgroup σ)
  exact Module.Finite.of_injective Ψ hΨ

/-! ### Components and isotypy at a complex place -/

/-- **Irreducible admissible components at a complex place.** An irreducible jointly admissible
operator subquotient has a subspace irreducible for the place actions at the complex place `v`
and admissible for `U(n)`. -/
theorem exists_complexPlaceComponent (hQ : Q.IsIrreducible) [Nontrivial Q.Space]
    (hJ : Q.IsJointlyAdmissible) (v : CP) :
    ∃ W : Submodule ℂ Q.Space,
      PlaceComponent.IsIrreducible (Q.complexPlaceCompactRepresentation v)
          (Q.complexPlaceLieAction v) W ∧
        PlaceComponent.IsAdmissible (Q.complexPlaceCompactRepresentation v) W := by
  classical
  refine (Q.exists_complexPlace_detection hQ v).elim fun d₀ hd₀ => hd₀.elim fun τ₀ hτ₀ => ?_
  refine (exists_ne (0 : Q.Space)).elim fun f₀ hf₀ => ?_
  refine (Q.finiteRepresentation_isSmooth f₀).elim fun U hU => ?_
  -- the compact orbit span of `f₀`
  let E : Submodule ℂ Q.Space := FiniteVectors.orbitSpan Q.compactRepresentation f₀
  have hEs : ∀ (k : standardInfiniteCompact F n), ∀ y ∈ E,
      Q.compactRepresentation k y ∈ E := fun k _ hy =>
    (FiniteVectors.orbitSubrepresentation Q.compactRepresentation f₀).apply_mem_toSubmodule
      k hy
  have hEfin : FiniteDimensional ℂ E := Q.compactRepresentation_isFiniteVector f₀
  have hEfix : E ≤ fixedVectors Q.finiteRepresentation U.toSubgroup := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨k, rfl⟩
    intro g
    exact (Q.finiteRepresentation_compactRepresentation g k f₀).trans
      (congrArg (Q.compactRepresentation k) (hU g))
  -- the representation of the compact factors on `ℂ^m`
  have : Module.Free ℂ E := Module.Free.of_divisionRing ℂ E
  let b := Module.finBasis ℂ E
  let m := Module.finrank ℂ E
  let ρE := restrictRep Q.compactRepresentation E hEs
  let R : Representation ℂ (ArchimedeanCompactFactors F n) (Fin m → ℂ) :=
    conjRep b.equivFun
      (ρE.comp (ArchimedeanCompactFactors.toStandardCompact F n).toMonoidHom)
  let φ₀ : (Fin m → ℂ) →ₗ[ℂ] Q.Space := E.subtype ∘ₗ b.equivFun.symm.toLinearMap
  have hφ₀ : φ₀ ∈ Q.complexCarrier v U.toSubgroup R :=
    ⟨fun x => hEfix (b.equivFun.symm x).2, fun q _ x =>
      congrArg E.subtype (b.equivFun.symm_apply_apply _)⟩
  have hφ₀0 : φ₀ ≠ 0 := by
    intro h
    apply hf₀
    have h1 : φ₀ (b.equivFun ⟨f₀, FiniteVectors.self_mem_orbitSpan _ f₀⟩) = f₀ :=
      congrArg E.subtype (b.equivFun.symm_apply_apply _)
    rw [h, LinearMap.zero_apply] at h1
    exact h1.symm
  -- the carrier and its irreducible admissible stable subspace
  have hJs := Q.isStable_complexCarrier v U.toSubgroup R
  have hJa := Q.isAdmissible_complexCarrier hJ v U R
  have hJ0 : Q.complexCarrier v U.toSubgroup R ≠ ⊥ := fun h =>
    hφ₀0 ((Submodule.mem_bot ℂ).mp ((congrArg (fun J => φ₀ ∈ J) h).mp hφ₀))
  refine (exists_isIrreducible_isAdmissible
    (postRep m (Q.complexPlaceCompactRepresentation v))
    (postLie m (Q.complexPlaceLieAction v)) hJs hJa hJ0 τ₀ hτ₀.1
    (fun N _ hNs hN0 => intertwiners_ne_bot_postRep m
      (Q.isLocallyFinite_complexPlace v) (Q.isWeaklyContinuous_complexPlace v)
      hτ₀.2 hNs hN0)).elim fun N₀ hN₀ => ?_
  have hirr := hN₀.2.1
  have hadm := hN₀.2.2
  refine (Submodule.exists_mem_ne_zero_of_ne_bot hirr.1).elim fun φ hφ => ?_
  have hex : ∃ j : Fin m, φ (Pi.single j 1) ≠ 0 := by
    by_contra h
    exact hφ.2 (eq_zero_of_single m φ fun j => not_not.mp fun hj => h ⟨j, hj⟩)
  refine hex.elim fun j hj => ?_
  have hW0 : N₀.map (evalAt m (Pi.single j 1)) ≠ ⊥ := by
    intro h
    have hmem : φ (Pi.single j 1) ∈ N₀.map (evalAt m (Pi.single j 1)) := ⟨φ, hφ.1, rfl⟩
    rw [h, Submodule.mem_bot] at hmem
    exact hj hmem
  have hinj := injOn_of_isIrreducible (κ' := Q.complexPlaceCompactRepresentation v)
    (π' := Q.complexPlaceLieAction v) (evalAt m (Pi.single j 1))
    (fun _ _ => rfl) (fun _ _ => rfl) hirr hW0
  exact ⟨N₀.map (evalAt m (Pi.single j 1)),
    isIrreducible_map (evalAt m (Pi.single j 1)) (fun _ _ => rfl) (fun _ _ => rfl) hirr hW0,
    isAdmissible_map (evalAt m (Pi.single j 1)) (fun _ _ => rfl) hirr.2.1.1 hinj hadm⟩

/-- **Isotypy at a complex place.** For irreducible `Q`, every irreducible place-stable
subspace `W` at the complex place `v` makes `Q` isotypic at `v` for the restricted
`(𝔤, K)`-module of `W`: the images of the `(𝔤, K)`-maps from `W` to `Q` span `Q`. -/
theorem isComplexPlaceIsotypic_restrict (hQ : Q.IsIrreducible) (v : CP)
    {W : Submodule ℂ Q.Space}
    (hW : PlaceComponent.IsIrreducible (Q.complexPlaceCompactRepresentation v)
      (Q.complexPlaceLieAction v) W) :
    Q.IsComplexPlaceIsotypic v (restrictCompact hW.2.1) (restrictLie hW.2.1) := by
  have hZ := Q.eq_bot_or_eq_top_of_complexPlaceStable hQ v
    (gkSpan (restrictCompact hW.2.1) (restrictLie hW.2.1)
      (Q.complexPlaceCompactRepresentation v) (Q.complexPlaceLieAction v))
    (fun A hAκ hAπ x hx => comm_mem_gkSpan A hAκ hAπ hx)
    (fun k x hx => compact_mem_gkSpan k hx) (fun X x hx => lie_mem_gkSpan X hx)
  exact hZ.resolve_left (gkSpan_restrict_ne_bot hW.2.1 hW.1)

end OperatorSubquotient

end Langlands.Automorphic
