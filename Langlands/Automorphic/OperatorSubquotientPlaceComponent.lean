import Langlands.Automorphic.PlaceComponentExistence
import Langlands.Automorphic.CuspidalArchimedeanGenericComponentReduction
import Langlands.Automorphic.OperatorSubquotientLocalComponentStatement

/-!
# Place components of irreducible operator subquotients at the real places

Let `Q` be an operator subquotient of `GL_n` over a number field and `v` a real place.
This module carries Worker 174's construction of irreducible admissible place components for
cuspidal realizations (`Langlands.Automorphic.PlaceComponentExistence`) over to `Q`, and adds
the isotypy of `Q` at `v`. The complex-place construction is in the companion module
`Langlands.Automorphic.OperatorSubquotientPlaceComponentComplex`.

* `isRealGKModule_realPlace`: the place actions descend from the numerator `Q.upper` and
  form a `(𝔤, K)`-structure; commutation laws between distinct places descend as well.
* `representation_mem_of_realPlaceStable`: a subspace stable under the place actions and
  every linear map commuting with them is stable under the whole operator algebra.
* `exists_realPlace_detection`: for irreducible `Q`, a continuous matrix representation of
  `O(n)` has a nonzero intertwiner into every nonzero place-stable subspace.
* `realCarrier`: the carrier of `PlaceComponentCarrier` for `Q`, stable and, by joint
  admissibility of `Q`, admissible.
* `exists_realPlaceComponent`: an irreducible admissible place-stable subspace of `Q`.
* `gkSpan`: the general span of images of `(𝔤, K)`-maps, also used at complex places.
* `isRealPlaceIsotypic_restrict`: for irreducible `Q`, every irreducible place-stable
  subspace makes `Q` isotypic for its restricted `(𝔤, K)`-module.
-/

noncomputable section

universe u

open scoped TensorProduct Matrix

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic

attribute [local instance 100] LieRing.ofAssociativeRing

open Langlands.Global Langlands.Global.ArchimedeanGL PlaceComponent

local instance subquotientPlaceRationalGroup {F : Type u} [Field F] [NumberField F] {n : ℕ} :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance subquotientPlaceContinuousGroup {F : Type u} [Field F] [NumberField F] {n : ℕ} :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance subquotientPlaceSmoothGroup {F : Type u} [Field F] [NumberField F] {n : ℕ} :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance subquotientPlaceFormsGroup {F : Type u} [Field F] [NumberField F] {n : ℕ} :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance subquotientPlaceStableGroup {F : Type u} [Field F] [NumberField F] {n : ℕ} :
    AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _
local instance subquotientPlaceSpaceGroup {F : Type u} [Field F] [NumberField F] {n : ℕ}
    (S : OperatorRealization F n) : AddCommGroup S.Space := Submodule.addCommGroup _

variable {F : Type u} [Field F] [NumberField F] {n : ℕ}

local notation "RP" =>
  {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsReal v}
local notation "CP" =>
  {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsComplex v}
local notation "RK" => Matrix.unitaryGroup (Fin n) ℝ
local notation "CK" => Matrix.unitaryGroup (Fin n) ℂ
local notation "RM" => Matrix (Fin n) (Fin n) ℝ
local notation "CM" => Matrix (Fin n) (Fin n) ℂ

namespace OperatorSubquotient

variable (Q : OperatorSubquotient F n)

/-! ### Descent of the place laws from the numerator -/

/-- A property of every vector of `Q` follows from the property of every projection. -/
theorem forall_of_projection {P : Q.Space → Prop} (h : ∀ g, P (Q.projection g))
    (f : Q.Space) : P f := by
  obtain ⟨g, hg⟩ := Q.projection_surjective f
  exact hg ▸ h g

/-- Two composites of maps descended from the numerator agree on `Q` when the composites of
their lifts agree on the numerator. -/
theorem comp_eq_of_projection {A B C D : Q.Space → Q.Space}
    {A' B' C' D' : Q.upper.Space → Q.upper.Space}
    (hA : ∀ g, A (Q.projection g) = Q.projection (A' g))
    (hB : ∀ g, B (Q.projection g) = Q.projection (B' g))
    (hC : ∀ g, C (Q.projection g) = Q.projection (C' g))
    (hD : ∀ g, D (Q.projection g) = Q.projection (D' g))
    (h : ∀ g, A' (B' g) = C' (D' g)) (f : Q.Space) : A (B f) = C (D f) :=
  Q.forall_of_projection (P := fun f => A (B f) = C (D f)) (fun g =>
    ((congrArg A (hB g)).trans (hA (B' g))).trans
      ((congrArg Q.projection (h g)).trans
        ((hC (D' g)).symm.trans (congrArg C (hD g)).symm))) f

/-- A map descended from the numerator equals a composite of two such maps on `Q` when the
same holds for the lifts. -/
theorem eq_comp_of_projection {A C D : Q.Space → Q.Space}
    {A' C' D' : Q.upper.Space → Q.upper.Space}
    (hA : ∀ g, A (Q.projection g) = Q.projection (A' g))
    (hC : ∀ g, C (Q.projection g) = Q.projection (C' g))
    (hD : ∀ g, D (Q.projection g) = Q.projection (D' g))
    (h : ∀ g, A' g = C' (D' g)) (f : Q.Space) : A f = C (D f) :=
  Q.forall_of_projection (P := fun f => A f = C (D f)) (fun g =>
    (hA g).trans ((congrArg Q.projection (h g)).trans
      ((hC (D' g)).symm.trans (congrArg C (hD g)).symm))) f

/-- The value of a functional on a projection is the value of the pulled-back functional. -/
theorem dual_projection (μ : Q.Space →ₗ[ℂ] ℂ) (g : Q.upper.Space) :
    (μ ∘ₗ Q.projection.toLinearMap) g = μ (Q.projection g) :=
  LinearMap.comp_apply μ Q.projection.toLinearMap g

/-- The real-place actions of `Q` form a `(𝔤𝔩_n(ℝ), O(n))`-structure. -/
theorem isRealGKModule_realPlace (v : RP) :
    Archimedean.IsRealGKModule n (Q.realPlaceCompactRepresentation v)
      (Q.realPlaceLieAction v) := by
  have hS := Q.upper.isRealGKModule_realPlace v
  have hcont := hS.2.1
  have hder := hS.2.2.1
  have hcov := hS.2.2.2
  refine ⟨Q.realPlaceCompactRepresentation_isFiniteVector v, fun x μ => ?_,
    fun γ X hγ0 hγ x μ => ?_, fun k X x => ?_⟩
  · refine Q.forall_of_projection
      (P := fun x => Continuous fun k : RK => μ (Q.realPlaceCompactRepresentation v k x))
      (fun g => ?_) x
    exact (hcont g (μ ∘ₗ Q.projection.toLinearMap)).congr fun k =>
      (Q.dual_projection μ _).trans
        (congrArg μ (Q.realPlaceCompactRepresentation_projection v k g).symm)
  · refine Q.forall_of_projection
      (P := fun x => HasDerivAt (fun t => μ (Q.realPlaceCompactRepresentation v (γ t) x))
        (μ (Q.realPlaceLieAction v (1 ⊗ₜ X) x)) 0)
      (fun g => ?_) x
    have h0 := hder γ X hγ0 hγ g (μ ∘ₗ Q.projection.toLinearMap)
    have e1 : (fun t => (μ ∘ₗ Q.projection.toLinearMap)
        (Q.upper.realPlaceCompactRepresentation v (γ t) g)) =
        fun t => μ (Q.realPlaceCompactRepresentation v (γ t) (Q.projection g)) :=
      funext fun t => (Q.dual_projection μ _).trans
        (congrArg μ (Q.realPlaceCompactRepresentation_projection v (γ t) g).symm)
    have e2 : (μ ∘ₗ Q.projection.toLinearMap) (Q.upper.realPlaceLieAction v (1 ⊗ₜ X) g) =
        μ (Q.realPlaceLieAction v (1 ⊗ₜ X) (Q.projection g)) :=
      (Q.dual_projection μ _).trans
        (congrArg μ (Q.realPlaceLieAction_projection v (1 ⊗ₜ X) g).symm)
    exact (h0.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t =>
      (congrFun e1 t).symm)).congr_deriv e2
  · exact Q.comp_eq_of_projection
      (A := Q.realPlaceCompactRepresentation v k) (B := Q.realPlaceLieAction v (1 ⊗ₜ X))
      (C := Q.realPlaceLieAction v (1 ⊗ₜ ((k : RM) * X * (star k : RM))))
      (D := Q.realPlaceCompactRepresentation v k)
      (Q.realPlaceCompactRepresentation_projection v k) (Q.realPlaceLieAction_projection v _)
      (Q.realPlaceLieAction_projection v _) (Q.realPlaceCompactRepresentation_projection v k)
      (hcov k X) x

theorem isLocallyFinite_realPlace (v : RP) :
    IsLocallyFinite (Q.realPlaceCompactRepresentation v) := fun x =>
  ⟨FiniteVectors.orbitSpan _ x, Q.realPlaceCompactRepresentation_isFiniteVector v x,
    FiniteVectors.self_mem_orbitSpan _ x,
    fun k _ hy => (FiniteVectors.orbitSubrepresentation _ x).apply_mem_toSubmodule k hy⟩

theorem isWeaklyContinuous_realPlace (v : RP) :
    IsWeaklyContinuous (Q.realPlaceCompactRepresentation v) :=
  fun μ x => (Q.isRealGKModule_realPlace v).2.1 x μ

/-- Lie actions at distinct real places commute. -/
theorem realPlaceLieAction_comm_of_ne {v w : RP} (h : w ≠ v) (X Y : ℂ ⊗[ℝ] RM)
    (f : Q.Space) :
    Q.realPlaceLieAction v X (Q.realPlaceLieAction w Y f) =
      Q.realPlaceLieAction w Y (Q.realPlaceLieAction v X f) :=
  Q.comp_eq_of_projection
    (A := Q.realPlaceLieAction v X) (B := Q.realPlaceLieAction w Y)
    (C := Q.realPlaceLieAction w Y) (D := Q.realPlaceLieAction v X)
    (Q.realPlaceLieAction_projection v X) (Q.realPlaceLieAction_projection w Y)
    (Q.realPlaceLieAction_projection w Y) (Q.realPlaceLieAction_projection v X)
    (Q.upper.realPlaceLieAction_comm_of_ne h X Y) f

/-- The Lie action at a real place commutes with the Lie actions at complex places. -/
theorem realPlaceLieAction_comm_complexPlace (v : RP) (w : CP) (X : ℂ ⊗[ℝ] RM)
    (Y : ℂ ⊗[ℝ] CM) (f : Q.Space) :
    Q.realPlaceLieAction v X (Q.complexPlaceLieAction w Y f) =
      Q.complexPlaceLieAction w Y (Q.realPlaceLieAction v X f) :=
  Q.comp_eq_of_projection
    (A := Q.realPlaceLieAction v X) (B := Q.complexPlaceLieAction w Y)
    (C := Q.complexPlaceLieAction w Y) (D := Q.realPlaceLieAction v X)
    (Q.realPlaceLieAction_projection v X) (Q.complexPlaceLieAction_projection w Y)
    (Q.complexPlaceLieAction_projection w Y) (Q.realPlaceLieAction_projection v X)
    (Q.upper.realPlaceLieAction_comm_complexPlace v w X Y) f

/-- At distinct real places the compact and Lie operators commute. -/
theorem realPlaceCompactRepresentation_realPlaceLieAction_of_ne (v w : RP) (h : w ≠ v)
    (k : RK) (X : ℂ ⊗[ℝ] RM) (f : Q.Space) :
    Q.realPlaceCompactRepresentation v k (Q.realPlaceLieAction w X f) =
      Q.realPlaceLieAction w X (Q.realPlaceCompactRepresentation v k f) :=
  Q.comp_eq_of_projection
    (A := Q.realPlaceCompactRepresentation v k) (B := Q.realPlaceLieAction w X)
    (C := Q.realPlaceLieAction w X) (D := Q.realPlaceCompactRepresentation v k)
    (Q.realPlaceCompactRepresentation_projection v k) (Q.realPlaceLieAction_projection w X)
    (Q.realPlaceLieAction_projection w X) (Q.realPlaceCompactRepresentation_projection v k)
    (Q.upper.realPlaceCompactRepresentation_realPlaceLieAction_of_ne v w h k X) f

/-- Compact translation at a real place commutes with every complex-place Lie action. -/
theorem realPlaceCompactRepresentation_complexPlaceLieAction (v : RP) (w : CP) (k : RK)
    (X : ℂ ⊗[ℝ] CM) (f : Q.Space) :
    Q.realPlaceCompactRepresentation v k (Q.complexPlaceLieAction w X f) =
      Q.complexPlaceLieAction w X (Q.realPlaceCompactRepresentation v k f) :=
  Q.comp_eq_of_projection
    (A := Q.realPlaceCompactRepresentation v k) (B := Q.complexPlaceLieAction w X)
    (C := Q.complexPlaceLieAction w X) (D := Q.realPlaceCompactRepresentation v k)
    (Q.realPlaceCompactRepresentation_projection v k) (Q.complexPlaceLieAction_projection w X)
    (Q.complexPlaceLieAction_projection w X) (Q.realPlaceCompactRepresentation_projection v k)
    (Q.upper.realPlaceCompactRepresentation_complexPlaceLieAction v w k X) f

/-- Compact translation by factors trivial at `v` commutes with the compact action at `v`. -/
theorem compact_comm_realPlaceCompact (v : RP) {q : ArchimedeanCompactFactors F n}
    (hq : q.1 v = 1) (l : RK) (y : Q.Space) :
    Q.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n q)
        (Q.realPlaceCompactRepresentation v l y) =
      Q.realPlaceCompactRepresentation v l
        (Q.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n q) y) :=
  Q.comp_eq_of_projection
    (A := Q.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n q))
    (B := Q.realPlaceCompactRepresentation v l) (C := Q.realPlaceCompactRepresentation v l)
    (D := Q.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n q))
    (Q.compactRepresentation_projection _) (Q.realPlaceCompactRepresentation_projection v l)
    (Q.realPlaceCompactRepresentation_projection v l) (Q.compactRepresentation_projection _)
    (Q.upper.compact_comm_realPlaceCompact v hq l) y

/-- Compact translation by factors trivial at `v` commutes with the Lie action at `v`. -/
theorem compact_comm_realPlaceLie (v : RP) {q : ArchimedeanCompactFactors F n}
    (hq : q.1 v = 1) (X : ℂ ⊗[ℝ] RM) (y : Q.Space) :
    Q.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n q)
        (Q.realPlaceLieAction v X y) =
      Q.realPlaceLieAction v X
        (Q.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n q) y) :=
  Q.comp_eq_of_projection
    (A := Q.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n q))
    (B := Q.realPlaceLieAction v X) (C := Q.realPlaceLieAction v X)
    (D := Q.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n q))
    (Q.compactRepresentation_projection _) (Q.realPlaceLieAction_projection v X)
    (Q.realPlaceLieAction_projection v X) (Q.compactRepresentation_projection _)
    (Q.upper.compact_comm_realPlaceLie v hq X) y

/-- A compact translation splits into its factor at `v` and the rest. -/
theorem compact_eq_realPlace_mul (v : RP) (k : standardInfiniteCompact F n) (y : Q.Space) :
    Q.compactRepresentation k y = Q.realPlaceCompactRepresentation v ((factorEquiv k).1 v)
      (Q.compactRepresentation
        (ArchimedeanCompactFactors.toStandardCompact F n (awayReal v (factorEquiv k))) y) :=
  Q.eq_comp_of_projection
    (A := Q.compactRepresentation k)
    (C := Q.realPlaceCompactRepresentation v ((factorEquiv k).1 v))
    (D := Q.compactRepresentation
      (ArchimedeanCompactFactors.toStandardCompact F n (awayReal v (factorEquiv k))))
    (Q.compactRepresentation_projection k) (Q.realPlaceCompactRepresentation_projection v _)
    (Q.compactRepresentation_projection _) (Q.upper.compact_eq_realPlace_mul v k) y

/-! ### Operator stability at a real place -/

/-- The action of an element of the operator algebra in the image of the scalars. -/
theorem representation_algebraMap (c : ℂ) (x : Q.Space) :
    Q.representation (algebraMap ℂ (automorphicOperatorAlgebra F n) c) x = c • x :=
  (LinearMap.congr_fun (Q.operatorAction.commutes c) x).trans
    (Module.algebraMap_end_apply ℂ ℂ Q.Space c x)

/-- The complexified Lie algebra preserves a subspace stable under the place actions at the
real place `v` and under every linear map commuting with them. -/
theorem complexLieAction_mem_of_realPlaceStable (v : RP) (Z : Submodule ℂ Q.Space)
    (hmap : ∀ A : Q.Space →ₗ[ℂ] Q.Space,
      (∀ k x, A (Q.realPlaceCompactRepresentation v k x) =
        Q.realPlaceCompactRepresentation v k (A x)) →
      (∀ X x, A (Q.realPlaceLieAction v X x) = Q.realPlaceLieAction v X (A x)) →
      ∀ x ∈ Z, A x ∈ Z)
    (hπ : ∀ (X : ℂ ⊗[ℝ] RM), ∀ x ∈ Z, Q.realPlaceLieAction v X x ∈ Z)
    (Y : ComplexLieAlgebra F n) : ∀ x ∈ Z, Q.complexLieAction Y x ∈ Z := by
  have hreal : ∀ (w : RP) (X : ℂ ⊗[ℝ] RM), ∀ x ∈ Z, Q.realPlaceLieAction w X x ∈ Z := by
    intro w X x hx
    by_cases hw : w = v
    · subst hw
      exact hπ X x hx
    · exact hmap (Q.realPlaceLieAction w X)
        (fun k y => (Q.realPlaceCompactRepresentation_realPlaceLieAction_of_ne v w hw k X y).symm)
        (fun Y y => (Q.realPlaceLieAction_comm_of_ne hw Y X y).symm) x hx
  have hcomplex : ∀ (w : CP) (X : ℂ ⊗[ℝ] CM), ∀ x ∈ Z, Q.complexPlaceLieAction w X x ∈ Z :=
    fun w X x hx => hmap (Q.complexPlaceLieAction w X)
      (fun k y => (Q.realPlaceCompactRepresentation_complexPlaceLieAction v w k X y).symm)
      (fun Y y => (Q.realPlaceLieAction_comm_complexPlace v w Y X y).symm) x hx
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
theorem envelopingAction_mem_of_realPlaceStable (v : RP) (Z : Submodule ℂ Q.Space)
    (hmap : ∀ A : Q.Space →ₗ[ℂ] Q.Space,
      (∀ k x, A (Q.realPlaceCompactRepresentation v k x) =
        Q.realPlaceCompactRepresentation v k (A x)) →
      (∀ X x, A (Q.realPlaceLieAction v X x) = Q.realPlaceLieAction v X (A x)) →
      ∀ x ∈ Z, A x ∈ Z)
    (hπ : ∀ (X : ℂ ⊗[ℝ] RM), ∀ x ∈ Z, Q.realPlaceLieAction v X x ∈ Z)
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
    exact Q.complexLieAction_mem_of_realPlaceStable v Z hmap hπ Y x hx
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

/-- **Operator stability at a real place.** A subspace of `Q` stable under the place actions
at `v` and under every linear map commuting with them is stable under the whole operator
algebra. -/
theorem representation_mem_of_realPlaceStable (v : RP) (Z : Submodule ℂ Q.Space)
    (hmap : ∀ A : Q.Space →ₗ[ℂ] Q.Space,
      (∀ k x, A (Q.realPlaceCompactRepresentation v k x) =
        Q.realPlaceCompactRepresentation v k (A x)) →
      (∀ X x, A (Q.realPlaceLieAction v X x) = Q.realPlaceLieAction v X (A x)) →
      ∀ x ∈ Z, A x ∈ Z)
    (hκ : ∀ (k : RK), ∀ x ∈ Z, Q.realPlaceCompactRepresentation v k x ∈ Z)
    (hπ : ∀ (X : ℂ ⊗[ℝ] RM), ∀ x ∈ Z, Q.realPlaceLieAction v X x ∈ Z)
    (a : automorphicOperatorAlgebra F n) : ∀ x ∈ Z, Q.representation a x ∈ Z := by
  obtain ⟨e, he⟩ := a
  induction he using Algebra.adjoin_induction with
  | mem e he =>
    rcases he with (⟨g, rfl⟩ | ⟨k, rfl⟩) | ⟨u, rfl⟩
    · intro x hx
      exact hmap (Q.finiteRepresentation g)
        (fun k y => Q.finiteRepresentation_realPlaceCompactRepresentation g v k y)
        (fun X y => Q.finiteRepresentation_realPlaceLieAction g v X y) x hx
    · intro x hx
      have hsplit := Q.compact_eq_realPlace_mul v k x
      have hq := awayReal_fst_self v (factorEquiv k)
      have hy := hmap (Q.compactRepresentation
          (ArchimedeanCompactFactors.toStandardCompact F n (awayReal v (factorEquiv k))))
        (fun l y => Q.compact_comm_realPlaceCompact v hq l y)
        (fun X y => Q.compact_comm_realPlaceLie v hq X y) x hx
      exact (congrArg (fun y => y ∈ Z) hsplit).mpr (hκ _ _ hy)
    · intro x hx
      exact Q.envelopingAction_mem_of_realPlaceStable v Z hmap hπ u x hx
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
theorem eq_bot_or_eq_top_of_realPlaceStable (hQ : Q.IsIrreducible) (v : RP)
    (Z : Submodule ℂ Q.Space)
    (hmap : ∀ A : Q.Space →ₗ[ℂ] Q.Space,
      (∀ k x, A (Q.realPlaceCompactRepresentation v k x) =
        Q.realPlaceCompactRepresentation v k (A x)) →
      (∀ X x, A (Q.realPlaceLieAction v X x) = Q.realPlaceLieAction v X (A x)) →
      ∀ x ∈ Z, A x ∈ Z)
    (hκ : ∀ (k : RK), ∀ x ∈ Z, Q.realPlaceCompactRepresentation v k x ∈ Z)
    (hπ : ∀ (X : ℂ ⊗[ℝ] RM), ∀ x ∈ Z, Q.realPlaceLieAction v X x ∈ Z) :
    Z = ⊥ ∨ Z = ⊤ := by
  let R : Subrepresentation Q.representation :=
    { toSubmodule := Z
      apply_mem_toSubmodule := fun a x hx =>
        Q.representation_mem_of_realPlaceStable v Z hmap hκ hπ a x hx }
  rcases hQ.eq_bot_or_eq_top R with h | h
  · exact Or.inl (congrArg Subrepresentation.toSubmodule h)
  · exact Or.inr (congrArg Subrepresentation.toSubmodule h)

/-! ### Detection at a real place -/

/-- **Detection at a real place.** For irreducible nonzero `Q`, some continuous matrix
representation of `O(n)` has a nonzero intertwiner into every nonzero stable subspace for the
place actions at the real place `v`. -/
theorem exists_realPlace_detection (hQ : Q.IsIrreducible) [Nontrivial Q.Space] (v : RP) :
    ∃ (d : ℕ) (τ : RK →* Matrix (Fin d) (Fin d) ℂ), Continuous τ ∧
      ∀ W : Submodule ℂ Q.Space, IsStable (Q.realPlaceCompactRepresentation v)
          (Q.realPlaceLieAction v) W → W ≠ ⊥ →
        intertwiners (Q.realPlaceCompactRepresentation v) W d τ ≠ ⊥ := by
  refine (exists_ne (0 : Q.Space)).elim fun x₀ hx₀ => ?_
  refine (exists_not_mem_freeSet (π := Q.realPlaceLieAction v)
    (Q.isLocallyFinite_realPlace v) (Q.isWeaklyContinuous_realPlace v) hx₀).elim
    fun d hd => hd.elim fun τ hτn => ?_
  have hτ := hτn.1
  have hnot := hτn.2
  have hZ := Q.eq_bot_or_eq_top_of_realPlaceStable hQ v
    (freeSet (Q.realPlaceLieAction v) (Q.isLocallyFinite_realPlace v)
      (Q.isWeaklyContinuous_realPlace v) τ)
    (fun A hAκ hAπ x hx => freeSet_map A hAκ hAπ hx)
    (fun k x hx => freeSet_compact k hx) (fun X x hx => freeSet_lie X hx)
  have hbot : freeSet (Q.realPlaceLieAction v) (Q.isLocallyFinite_realPlace v)
      (Q.isWeaklyContinuous_realPlace v) τ = ⊥ := by
    rcases hZ with h | h
    · exact h
    · exfalso
      apply hnot
      rw [h]
      trivial
  refine ⟨d, τ, hτ, ?_⟩
  intro W hWs hW
  exact intertwiners_ne_bot_of_freeSet_eq_bot (hfin := Q.isLocallyFinite_realPlace v)
    (hweak := Q.isWeaklyContinuous_realPlace v) hbot hWs hW

/-! ### The carrier at a real place -/

/-- The carrier at a real place: linear maps `ℂ^m → Q` with `L`-fixed values intertwining `R`
with the compact action on the factors trivial at `v`. -/
def realCarrier (v : RP) (L : Subgroup (FiniteAdelicGL F n)) {m : ℕ}
    (R : Representation ℂ (ArchimedeanCompactFactors F n) (Fin m → ℂ)) :
    Submodule ℂ ((Fin m → ℂ) →ₗ[ℂ] Q.Space) where
  carrier := {φ | (∀ x, φ x ∈ fixedVectors Q.finiteRepresentation L) ∧
    ∀ q : ArchimedeanCompactFactors F n, q.1 v = 1 → ∀ x,
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
theorem isStable_realCarrier (v : RP) (L : Subgroup (FiniteAdelicGL F n)) {m : ℕ}
    (R : Representation ℂ (ArchimedeanCompactFactors F n) (Fin m → ℂ)) :
    IsStable (postRep m (Q.realPlaceCompactRepresentation v))
      (postLie m (Q.realPlaceLieAction v)) (Q.realCarrier v L R) := by
  refine ⟨fun l φ hφ => ⟨fun x => ?_, fun q hq x => ?_⟩,
    fun X φ hφ => ⟨fun x => ?_, fun q hq x => ?_⟩⟩
  · intro d
    exact (Q.finiteRepresentation_realPlaceCompactRepresentation d v l (φ x)).trans
      (congrArg (Q.realPlaceCompactRepresentation v l) (hφ.1 x d))
  · exact (congrArg (Q.realPlaceCompactRepresentation v l) (hφ.2 q hq x)).trans
      (Q.compact_comm_realPlaceCompact v hq l (φ x)).symm
  · intro d
    exact (Q.finiteRepresentation_realPlaceLieAction d v X (φ x)).trans
      (congrArg (Q.realPlaceLieAction v X) (hφ.1 x d))
  · exact (congrArg (Q.realPlaceLieAction v X) (hφ.2 q hq x)).trans
      (Q.compact_comm_realPlaceLie v hq X (φ x)).symm

/-- The curried form of an intertwiner into the carrier intertwines `τ ⊗ R`. -/
theorem lift_mem_jointMultiplicity (v : RP) (L : Subgroup (FiniteAdelicGL F n)) {d m : ℕ}
    (τ : RK →* Matrix (Fin d) (Fin d) ℂ)
    (R : Representation ℂ (ArchimedeanCompactFactors F n) (Fin m → ℂ))
    {Φ : (Fin d → ℂ) →ₗ[ℂ] ((Fin m → ℂ) →ₗ[ℂ] Q.Space)}
    (hΦ : Φ ∈ intertwiners (postRep m (Q.realPlaceCompactRepresentation v))
      (Q.realCarrier v L R) d τ) :
    (∀ t, TensorProduct.lift Φ t ∈ fixedVectors Q.finiteRepresentation L) ∧
      ∀ (k : standardInfiniteCompact F n) t,
        TensorProduct.lift Φ (realCarrierRep v τ R k t) =
          Q.compactRepresentation k (TensorProduct.lift Φ t) := by
  refine ⟨fun t => ?_, fun k t => ?_⟩
  · induction t using TensorProduct.inductionOn with
    | tmul a b => exact (hΦ.1 a).1 b
    | add t₁ t₂ h₁ h₂ =>
      exact (map_add (TensorProduct.lift Φ) t₁ t₂).symm ▸ Submodule.add_mem _ h₁ h₂
  · induction t using TensorProduct.inductionOn with
    | tmul a b =>
      have hp := awayReal_fst_self v (factorEquiv k)
      have e1 : Φ (τ ((factorEquiv k).1 v) *ᵥ a) (R (awayReal v (factorEquiv k)) b) =
          Q.realPlaceCompactRepresentation v ((factorEquiv k).1 v)
            (Φ a (R (awayReal v (factorEquiv k)) b)) :=
        LinearMap.congr_fun (hΦ.2 ((factorEquiv k).1 v) a) _
      have e2 : Φ a (R (awayReal v (factorEquiv k)) b) =
          Q.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n
            (awayReal v (factorEquiv k))) (Φ a b) := (hΦ.1 a).2 _ hp b
      exact e1.trans ((congrArg (Q.realPlaceCompactRepresentation v ((factorEquiv k).1 v))
        e2).trans (Q.compact_eq_realPlace_mul v k (Φ a b)).symm)
    | add t₁ t₂ h₁ h₂ =>
      exact ((congrArg (TensorProduct.lift Φ) (map_add _ t₁ t₂)).trans
        ((map_add _ _ _).trans (congrArg₂ (· + ·) h₁ h₂))).trans
        ((map_add _ _ _).symm.trans (congrArg _ (map_add _ t₁ t₂).symm))

/-- **Admissibility of the carrier.** If `Q` is jointly admissible, the carrier at a real
place is admissible for the compact action at `v`. -/
theorem isAdmissible_realCarrier (hJ : Q.IsJointlyAdmissible) (v : RP)
    (L : OpenSubgroup (FiniteAdelicGL F n)) {m : ℕ}
    (R : Representation ℂ (ArchimedeanCompactFactors F n) (Fin m → ℂ)) :
    PlaceComponent.IsAdmissible (postRep m (Q.realPlaceCompactRepresentation v))
      (Q.realCarrier v L.toSubgroup R) := by
  intro d τ _
  have : Module.Free ℂ ((Fin d → ℂ) ⊗[ℂ] (Fin m → ℂ)) := Module.Free.of_divisionRing ℂ _
  let ε := (Module.finBasis ℂ ((Fin d → ℂ) ⊗[ℂ] (Fin m → ℂ))).equivFun
  let σ := conjRep ε (realCarrierRep v τ R)
  have hfin : FiniteDimensional ℂ (jointMultiplicitySpace Q.finiteRepresentation
      Q.compactRepresentation L.toSubgroup σ) := hJ L _ σ
  have hmem : ∀ Φ ∈ intertwiners (postRep m (Q.realPlaceCompactRepresentation v))
      (Q.realCarrier v L.toSubgroup R) d τ,
      TensorProduct.lift Φ ∘ₗ ε.symm.toLinearMap ∈ jointMultiplicitySpace
        Q.finiteRepresentation Q.compactRepresentation L.toSubgroup σ := by
    intro Φ hΦ
    have h := Q.lift_mem_jointMultiplicity v L.toSubgroup τ R hΦ
    refine ⟨fun y => h.1 _, fun k y => ?_⟩
    have hσ : ε.symm (σ k y) = realCarrierRep v τ R k (ε.symm y) :=
      ε.symm_apply_apply (realCarrierRep v τ R k (ε.symm y))
    exact (congrArg (TensorProduct.lift Φ) hσ).trans (h.2 k (ε.symm y))
  let Ψ : intertwiners (postRep m (Q.realPlaceCompactRepresentation v))
      (Q.realCarrier v L.toSubgroup R) d τ →ₗ[ℂ] jointMultiplicitySpace
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

/-! ### Components and isotypy at a real place -/

/-- **Irreducible admissible components at a real place.** An irreducible jointly admissible
operator subquotient has a subspace irreducible for the place actions at the real place `v`
and admissible for `O(n)`. -/
theorem exists_realPlaceComponent (hQ : Q.IsIrreducible) [Nontrivial Q.Space]
    (hJ : Q.IsJointlyAdmissible) (v : RP) :
    ∃ W : Submodule ℂ Q.Space,
      PlaceComponent.IsIrreducible (Q.realPlaceCompactRepresentation v)
          (Q.realPlaceLieAction v) W ∧
        PlaceComponent.IsAdmissible (Q.realPlaceCompactRepresentation v) W := by
  classical
  refine (Q.exists_realPlace_detection hQ v).elim fun d₀ hd₀ => hd₀.elim fun τ₀ hτ₀ => ?_
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
  have hφ₀ : φ₀ ∈ Q.realCarrier v U.toSubgroup R :=
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
  have hJs := Q.isStable_realCarrier v U.toSubgroup R
  have hJa := Q.isAdmissible_realCarrier hJ v U R
  have hJ0 : Q.realCarrier v U.toSubgroup R ≠ ⊥ := fun h =>
    hφ₀0 ((Submodule.mem_bot ℂ).mp ((congrArg (fun J => φ₀ ∈ J) h).mp hφ₀))
  refine (exists_isIrreducible_isAdmissible
    (postRep m (Q.realPlaceCompactRepresentation v))
    (postLie m (Q.realPlaceLieAction v)) hJs hJa hJ0 τ₀ hτ₀.1
    (fun N _ hNs hN0 => intertwiners_ne_bot_postRep m
      (Q.isLocallyFinite_realPlace v) (Q.isWeaklyContinuous_realPlace v)
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
  have hinj := injOn_of_isIrreducible (κ' := Q.realPlaceCompactRepresentation v)
    (π' := Q.realPlaceLieAction v) (evalAt m (Pi.single j 1))
    (fun _ _ => rfl) (fun _ _ => rfl) hirr hW0
  exact ⟨N₀.map (evalAt m (Pi.single j 1)),
    isIrreducible_map (evalAt m (Pi.single j 1)) (fun _ _ => rfl) (fun _ _ => rfl) hirr hW0,
    isAdmissible_map (evalAt m (Pi.single j 1)) (fun _ _ => rfl) hirr.2.1.1 hinj hadm⟩

end OperatorSubquotient

/-! ### The span of the images of `(𝔤, K)`-maps -/

section GKSpan

variable {K : Type*} [Group K] {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {W : Type*} [AddCommGroup W] [Module ℂ W]

/-- The span of the images of the `(𝔤, K)`-maps from `(V, ρ, π)` to `(W, ρ', π')`. -/
def gkSpan (ρ : Representation ℂ K V) (π : 𝔤 →ₗ⁅ℂ⁆ Module.End ℂ V)
    (ρ' : Representation ℂ K W) (π' : 𝔤 →ₗ⁅ℂ⁆ Module.End ℂ W) : Submodule ℂ W :=
  ⨆ f ∈ Archimedean.gkHoms ρ π ρ' π', LinearMap.range f

variable {ρ : Representation ℂ K V} {π : 𝔤 →ₗ⁅ℂ⁆ Module.End ℂ V}
  {ρ' : Representation ℂ K W} {π' : 𝔤 →ₗ⁅ℂ⁆ Module.End ℂ W}

theorem apply_mem_gkSpan {f : V →ₗ[ℂ] W} (hf : f ∈ Archimedean.gkHoms ρ π ρ' π') (y : V) :
    f y ∈ gkSpan ρ π ρ' π' :=
  (le_iSup₂ (f := fun (g : V →ₗ[ℂ] W) (_ : g ∈ Archimedean.gkHoms ρ π ρ' π') =>
    LinearMap.range g) f hf) (LinearMap.mem_range_self f y)

/-- A linear map `B` of `W` preserves the span as soon as `B ∘ f` is again a `(𝔤, K)`-map
after precomposition with some linear map of `V`, for every `(𝔤, K)`-map `f`. -/
theorem map_mem_gkSpan (B : W →ₗ[ℂ] W)
    (hB : ∀ f ∈ Archimedean.gkHoms ρ π ρ' π', ∀ y : V,
      ∃ g ∈ Archimedean.gkHoms ρ π ρ' π', ∃ z : V, B (f y) = g z)
    {x : W} (hx : x ∈ gkSpan ρ π ρ' π') : B x ∈ gkSpan ρ π ρ' π' := by
  have hle : gkSpan ρ π ρ' π' ≤ (gkSpan ρ π ρ' π').comap B := by
    refine iSup₂_le fun f hf => ?_
    rintro _ ⟨y, rfl⟩
    obtain ⟨g, hg, z, hz⟩ := hB f hf y
    change B (f y) ∈ gkSpan ρ π ρ' π'
    rw [hz]
    exact apply_mem_gkSpan hg z
  exact hle hx

/-- The span is stable under every linear map commuting with `ρ'` and `π'`. -/
theorem comm_mem_gkSpan (A : W →ₗ[ℂ] W) (hAκ : ∀ k x, A (ρ' k x) = ρ' k (A x))
    (hAπ : ∀ X x, A (π' X x) = π' X (A x)) {x : W} (hx : x ∈ gkSpan ρ π ρ' π') :
    A x ∈ gkSpan ρ π ρ' π' := by
  refine map_mem_gkSpan A (fun f hf y => ⟨A ∘ₗ f, ⟨fun k z => ?_, fun X z => ?_⟩, y, rfl⟩) hx
  · change A (f (ρ k z)) = ρ' k (A (f z))
    rw [hf.1 k z, hAκ]
  · change A (f (π X z)) = π' X (A (f z))
    rw [hf.2 X z, hAπ]

theorem compact_mem_gkSpan (k : K) {x : W} (hx : x ∈ gkSpan ρ π ρ' π') :
    ρ' k x ∈ gkSpan ρ π ρ' π' :=
  map_mem_gkSpan (ρ' k) (fun f hf y => ⟨f, hf, ρ k y, (hf.1 k y).symm⟩) hx

theorem lie_mem_gkSpan (X : 𝔤) {x : W} (hx : x ∈ gkSpan ρ π ρ' π') :
    π' X x ∈ gkSpan ρ π ρ' π' :=
  map_mem_gkSpan (π' X) (fun f hf y => ⟨f, hf, π X y, (hf.2 X y).symm⟩) hx

/-- The inclusion of a stable subspace is a `(𝔤, K)`-map from the restricted module. -/
theorem subtype_mem_gkHoms {κ : Representation ℂ K W} {π : 𝔤 →ₗ⁅ℂ⁆ Module.End ℂ W}
    {Z : Submodule ℂ W} (hZ : IsStable κ π Z) :
    Z.subtype ∈ Archimedean.gkHoms (restrictCompact hZ) (restrictLie hZ) κ π :=
  ⟨fun _ _ => rfl, fun _ _ => rfl⟩

/-- For a nonzero stable subspace `Z`, the span of the images of the `(𝔤, K)`-maps from the
restricted module of `Z` is nonzero. -/
theorem gkSpan_restrict_ne_bot {κ : Representation ℂ K W} {π : 𝔤 →ₗ⁅ℂ⁆ Module.End ℂ W}
    {Z : Submodule ℂ W} (hZ : IsStable κ π Z) (hZ0 : Z ≠ ⊥) :
    gkSpan (restrictCompact hZ) (restrictLie hZ) κ π ≠ ⊥ := by
  intro h
  obtain ⟨x, hxZ, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hZ0
  have hmem := apply_mem_gkSpan (subtype_mem_gkHoms hZ) ⟨x, hxZ⟩
  rw [h, Submodule.mem_bot] at hmem
  exact hx0 hmem

end GKSpan

namespace OperatorSubquotient

variable (Q : OperatorSubquotient F n)

/-- **Isotypy at a real place.** For irreducible `Q`, every irreducible place-stable subspace
`W` at the real place `v` makes `Q` isotypic at `v` for the restricted `(𝔤, K)`-module of
`W`: the images of the `(𝔤, K)`-maps from `W` to `Q` span `Q`. -/
theorem isRealPlaceIsotypic_restrict (hQ : Q.IsIrreducible) (v : RP) {W : Submodule ℂ Q.Space}
    (hW : PlaceComponent.IsIrreducible (Q.realPlaceCompactRepresentation v)
      (Q.realPlaceLieAction v) W) :
    Q.IsRealPlaceIsotypic v (restrictCompact hW.2.1) (restrictLie hW.2.1) := by
  have hZ := Q.eq_bot_or_eq_top_of_realPlaceStable hQ v
    (gkSpan (restrictCompact hW.2.1) (restrictLie hW.2.1)
      (Q.realPlaceCompactRepresentation v) (Q.realPlaceLieAction v))
    (fun A hAκ hAπ x hx => comm_mem_gkSpan A hAκ hAπ hx)
    (fun k x hx => compact_mem_gkSpan k hx) (fun X x hx => lie_mem_gkSpan X hx)
  exact hZ.resolve_left (gkSpan_restrict_ne_bot hW.2.1 hW.1)

end OperatorSubquotient

end Langlands.Automorphic
