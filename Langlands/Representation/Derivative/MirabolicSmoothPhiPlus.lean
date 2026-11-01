import Langlands.Representation.Derivative.MirabolicPlusNormalization
import Langlands.Representation.Induction.Equivalences
import Langlands.Representation.Category.Abelian
import Langlands.Representation.Geometric.CompactSmoothComparison

/-!
# Mirabolic smooth induction `Φ̂⁺`

The Bernstein–Zelevinsky functor `Φ̂⁺ = I_(V,θ) : P_(n+1) → P_(n+2)` (BZ77 §1.8(a), §3.2).
It extends `τ` to the actual plus subgroup `Q = P_(n+1) V_(n+2)` by the positive character
`thetaPlus` and applies the actual smooth induction by right translation, with no support
condition. The normalized functor first twists the input by `|det|^(1/2)`, exactly as the
published compact `Φ⁺`. The compact `Φ⁺` embeds naturally into `Φ̂⁺`, and `Φ̂⁺` preserves
injective intertwiners. No adjunction or exactness is stated here.
-/

noncomputable section

open CategoryTheory

namespace Langlands.Derivative.Mirabolic

open GeneralLinear GeneralLinear.Mirabolic HarmonicAnalysis

universe uV uF

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

/-! ## Unnormalized smooth Phi-plus -/

/-- Unnormalized `Φ̂⁺(τ) = Ind(P_(n+2), Q, τ')`: actual smooth induction from the plus
subgroup `Q`, by right translation and without a support condition. -/
def phiHatPlusUnnormalized (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier) ⥤
      SmoothRep.{0, uF, max uF uV} ℂ (mirabolic (n + 1) F.Carrier) := by
  letI := T.topology
  letI := T.generalLinearTopologicalGroup (n + 1 + 1)
  exact plusTwistFunctor T ψ n ⋙ SmoothRep.toRep ⋙
    Induction.smoothInductionFunctor (plusSubgroup n F.Carrier)

/-- The object carrier is the actual space of smooth covariant functions. -/
theorem phiHatPlusUnnormalized_obj_carrier (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup (n + 1 + 1)
    ∀ τ : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier),
      ((phiHatPlusUnnormalized T ψ n).obj τ : Type (max uF uV)) =
        Induction.SmoothFunctions (plusSubgroup n F.Carrier)
          (plusTwistRepresentation ψ n τ.representation) := by
  intros
  rfl

/-- The object is the bundled actual smooth induction of `τ'`. -/
theorem phiHatPlusUnnormalized_obj (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup (n + 1 + 1)
    ∀ τ : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier),
      (phiHatPlusUnnormalized T ψ n).obj τ =
        SmoothRep.of
          (Induction.smoothInduced (plusSubgroup n F.Carrier)
            (plusTwistRepresentation ψ n τ.representation))
          (Induction.smoothInduced_smooth (plusSubgroup n F.Carrier)
            (plusTwistRepresentation ψ n τ.representation)) := by
  intros
  rfl

/-- Evaluation of a vector of `Φ̂⁺(τ)` at a point of `P_(n+2)`. -/
abbrev phiHatPlusEval (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    (τ : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier)) →
      (phiHatPlusUnnormalized T ψ n).obj τ → mirabolic (n + 1) F.Carrier → τ := by
  letI := T.topology
  letI := T.generalLinearTopologicalGroup (n + 1 + 1)
  exact fun τ φ x => Induction.eval (plusSubgroup n F.Carrier)
    (plusTwistRepresentation ψ n τ.representation)
    (show Induction.SmoothFunctions (plusSubgroup n F.Carrier)
      (plusTwistRepresentation ψ n τ.representation) from φ) x

/-- Vectors of `Φ̂⁺(τ)` are determined by their values. -/
theorem phiHatPlusEval_injective (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    ∀ τ : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier),
      Function.Injective (phiHatPlusEval T ψ n τ) := by
  let := T.topology
  intro τ φ φ' h
  exact Subtype.ext (Subtype.ext h)

/-- Evaluation is additive in the vector. -/
theorem phiHatPlusEval_add (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    ∀ (τ : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier))
      (φ φ' : (phiHatPlusUnnormalized T ψ n).obj τ) (x : mirabolic (n + 1) F.Carrier),
      phiHatPlusEval T ψ n τ (φ + φ') x = phiHatPlusEval T ψ n τ φ x + phiHatPlusEval T ψ n τ φ' x := by
  intros
  rfl

/-- Evaluation is homogeneous in the vector. -/
theorem phiHatPlusEval_smul (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    ∀ (τ : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier)) (c : ℂ)
      (φ : (phiHatPlusUnnormalized T ψ n).obj τ) (x : mirabolic (n + 1) F.Carrier),
      phiHatPlusEval T ψ n τ (c • φ) x = c • phiHatPlusEval T ψ n τ φ x := by
  intros
  rfl

/-- Covariance `φ(q x) = thetaPlus(q) • τ(plusProjection q) φ(x)` for `q ∈ Q`. -/
theorem phiHatPlusEval_covariant (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    ∀ (τ : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier))
      (φ : (phiHatPlusUnnormalized T ψ n).obj τ) (q : plusSubgroup n F.Carrier)
      (x : mirabolic (n + 1) F.Carrier),
      phiHatPlusEval T ψ n τ φ ((q : mirabolic (n + 1) F.Carrier) * x) =
        (thetaPlus ψ n q : ℂ) •
          τ.representation (plusProjection q) (phiHatPlusEval T ψ n τ φ x) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup (n + 1 + 1)
  intro τ φ q x
  exact (show Induction.SmoothFunctions (plusSubgroup n F.Carrier)
    (plusTwistRepresentation ψ n τ.representation) from φ).1.2 q x

/-- The source's covariance `φ(p m x) = Θ(m) τ(p) φ(x)` in Levi-first coordinates. -/
theorem phiHatPlusEval_successor_mul_radical (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    ∀ (τ : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier))
      (φ : (phiHatPlusUnnormalized T ψ n).obj τ) (g : mirabolic n F.Carrier)
      (u : radical (n + 1) F.Carrier) (x : mirabolic (n + 1) F.Carrier),
      phiHatPlusEval T ψ n τ φ (successor g * u.val * x) =
        (theta ψ n u : ℂ) • τ.representation g (phiHatPlusEval T ψ n τ φ x) := by
  let := T.topology
  intro τ φ g u x
  have h := phiHatPlusEval_covariant T ψ n τ φ (plusSuccessor g * plusRadical u) x
  rw [thetaPlus_plusSuccessor_mul_plusRadical, map_mul, plusProjection_plusSuccessor,
    plusProjection_plusRadical, mul_one] at h
  exact h

/-- Radical elements act on values through `Θ`. -/
theorem phiHatPlusEval_radical_mul (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    ∀ (τ : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier))
      (φ : (phiHatPlusUnnormalized T ψ n).obj τ) (u : radical (n + 1) F.Carrier)
      (x : mirabolic (n + 1) F.Carrier),
      phiHatPlusEval T ψ n τ φ (u.val * x) = (theta ψ n u : ℂ) • phiHatPlusEval T ψ n τ φ x := by
  let := T.topology
  intro τ φ u x
  have h := phiHatPlusEval_covariant T ψ n τ φ (plusRadical u) x
  rw [thetaPlus_plusRadical, plusProjection_plusRadical, map_one, Module.End.one_apply] at h
  exact h

/-- Successor elements act on values through `τ`. -/
theorem phiHatPlusEval_successor_mul (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    ∀ (τ : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier))
      (φ : (phiHatPlusUnnormalized T ψ n).obj τ) (g : mirabolic n F.Carrier)
      (x : mirabolic (n + 1) F.Carrier),
      phiHatPlusEval T ψ n τ φ (successor g * x) =
        τ.representation g (phiHatPlusEval T ψ n τ φ x) := by
  let := T.topology
  intro τ φ g x
  have h := phiHatPlusEval_covariant T ψ n τ φ (plusSuccessor g) x
  rw [thetaPlus_plusSuccessor, plusProjection_plusSuccessor, Units.val_one, one_smul] at h
  exact h

/-- Each vector has one open subgroup of right stabilizers. -/
theorem phiHatPlusEval_exists_openSubgroup (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    ∀ (τ : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier))
      (φ : (phiHatPlusUnnormalized T ψ n).obj τ),
      ∃ K : OpenSubgroup (mirabolic (n + 1) F.Carrier),
        ∀ (k : K) (x : mirabolic (n + 1) F.Carrier),
          phiHatPlusEval T ψ n τ φ (x * (k : mirabolic (n + 1) F.Carrier)) =
            phiHatPlusEval T ψ n τ φ x := by
  let := T.topology
  let := T.generalLinearTopologicalGroup (n + 1 + 1)
  intro τ φ
  obtain ⟨K, hK⟩ := (show Induction.SmoothFunctions (plusSubgroup n F.Carrier)
    (plusTwistRepresentation ψ n τ.representation) from φ).2
  exact ⟨K, fun k x => congrArg (fun f => f.1 x) (hK k)⟩

/-- A vector of `Φ̂⁺(τ)` from a covariant function with one open subgroup of right
stabilizers; no support condition is imposed. -/
def phiHatPlusMk (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    (τ : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier)) →
      (f : mirabolic (n + 1) F.Carrier → τ) →
      (∀ (q : plusSubgroup n F.Carrier) (x : mirabolic (n + 1) F.Carrier),
        f ((q : mirabolic (n + 1) F.Carrier) * x) =
          (thetaPlus ψ n q : ℂ) • τ.representation (plusProjection q) (f x)) →
      (K : OpenSubgroup (mirabolic (n + 1) F.Carrier)) →
      (∀ (k : K) (x : mirabolic (n + 1) F.Carrier),
        f (x * (k : mirabolic (n + 1) F.Carrier)) = f x) →
      (phiHatPlusUnnormalized T ψ n).obj τ := by
  letI := T.topology
  letI := T.generalLinearTopologicalGroup (n + 1 + 1)
  exact fun τ f hcov K hK => Induction.smoothFunctionOf (plusSubgroup n F.Carrier)
    (plusTwistRepresentation ψ n τ.representation) f hcov K hK

theorem phiHatPlusEval_mk (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    ∀ (τ : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier))
      (f : mirabolic (n + 1) F.Carrier → τ)
      (hcov : ∀ (q : plusSubgroup n F.Carrier) (x : mirabolic (n + 1) F.Carrier),
        f ((q : mirabolic (n + 1) F.Carrier) * x) =
          (thetaPlus ψ n q : ℂ) • τ.representation (plusProjection q) (f x))
      (K : OpenSubgroup (mirabolic (n + 1) F.Carrier))
      (hK : ∀ (k : K) (x : mirabolic (n + 1) F.Carrier),
        f (x * (k : mirabolic (n + 1) F.Carrier)) = f x),
      phiHatPlusEval T ψ n τ (phiHatPlusMk T ψ n τ f hcov K hK) = f := by
  intros
  rfl

/-- The action is right translation: `(g • φ)(x) = φ(x g)`. -/
theorem phiHatPlusUnnormalized_action (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    ∀ (τ : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier)) (g : mirabolic (n + 1) F.Carrier)
      (φ : (phiHatPlusUnnormalized T ψ n).obj τ) (x : mirabolic (n + 1) F.Carrier),
      phiHatPlusEval T ψ n τ (((phiHatPlusUnnormalized T ψ n).obj τ).representation g φ) x =
        phiHatPlusEval T ψ n τ φ (x * g) := by
  intros
  rfl

theorem phiHatPlusUnnormalized_isSmooth (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    ∀ τ : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier),
      IsSmooth ((phiHatPlusUnnormalized T ψ n).obj τ).representation := by
  let := T.topology
  intro τ
  exact ((phiHatPlusUnnormalized T ψ n).obj τ).isSmooth

/-- The induced map is the actual smooth-induction map of the same intertwiner. -/
theorem phiHatPlusUnnormalized_map_hom (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup (n + 1 + 1)
    ∀ {τ σ : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier)} (f : τ ⟶ σ),
      SmoothRep.hom ((phiHatPlusUnnormalized T ψ n).map f) =
        Induction.smoothInducedMap (plusSubgroup n F.Carrier)
          (SmoothRep.hom ((plusTwistFunctor T ψ n).map f)) := by
  intros
  rfl

/-- On values, the induced map is postcomposition: `(Φ̂⁺ f) φ (x) = f (φ x)`. -/
theorem phiHatPlusUnnormalized_map_eval (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    ∀ {τ σ : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier)} (f : τ ⟶ σ)
      (φ : (phiHatPlusUnnormalized T ψ n).obj τ) (x : mirabolic (n + 1) F.Carrier),
      phiHatPlusEval T ψ n σ (SmoothRep.hom ((phiHatPlusUnnormalized T ψ n).map f) φ) x =
        SmoothRep.hom f (phiHatPlusEval T ψ n τ φ x) := by
  intros
  rfl

/-- Unnormalized `Φ̂⁺` sends injective intertwiners to injective intertwiners. -/
theorem phiHatPlusUnnormalized_map_injective (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    ∀ {τ σ : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier)} (f : τ ⟶ σ),
      Function.Injective (SmoothRep.hom f) →
        Function.Injective (SmoothRep.hom ((phiHatPlusUnnormalized T ψ n).map f)) := by
  let := T.topology
  intro τ σ f hf φ φ' h
  apply phiHatPlusEval_injective T ψ n τ
  funext x
  apply hf
  exact congrArg (fun w => phiHatPlusEval T ψ n σ w x) h

/-! ## Normalized smooth Phi-plus -/

/-- Normalized `Φ̂⁺`: twist by `|det|^(1/2)` on `P_(n+1)`, then apply the actual
unnormalized smooth induction from the plus subgroup `Q = P_(n+1) V_(n+2)`. This is the
normalization of the published compact `Φ⁺`. -/
def phiHatPlus (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier) ⥤
      SmoothRep.{0, uF, max uF uV} ℂ (mirabolic (n + 1) F.Carrier) := by
  letI := T.topology
  exact SmoothRep.twistFunctor (phiPlusCharacter T n) (isOpen_ker_phiPlusCharacter T n) ⋙
    phiHatPlusUnnormalized T ψ n

theorem phiHatPlus_eq (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    phiHatPlus.{uV} T ψ n =
      SmoothRep.twistFunctor (phiPlusCharacter T n) (isOpen_ker_phiPlusCharacter T n) ⋙
        phiHatPlusUnnormalized T ψ n :=
  rfl

/-- Equality of normalized `Φ̂⁺` with normalization by the actual radical Haar positive
half, including maps. -/
theorem phiHatPlus_haarNormalization (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    phiHatPlus.{uV} T ψ n =
      SmoothRep.twistFunctor (phiPlusHaarHalf T n) (isOpen_ker_phiPlusHaarHalf T n) ⋙
        phiHatPlusUnnormalized T ψ n := by
  simp only [phiPlusHaarHalf_eq]
  rfl

/-- The object carrier is the actual space of smooth covariant functions for the
positively normalized inducing representation. -/
theorem phiHatPlus_obj_carrier (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup (n + 1 + 1)
    ∀ τ : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier),
      ((phiHatPlus T ψ n).obj τ : Type (max uF uV)) =
        Induction.SmoothFunctions (plusSubgroup n F.Carrier)
          (plusTwistRepresentation ψ n
            (Langlands.twist (phiPlusCharacter T n) τ.representation)) := by
  intros
  rfl

/-- The object is the bundled actual smooth induction of the normalized `τ'`. -/
theorem phiHatPlus_obj (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup (n + 1 + 1)
    ∀ τ : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier),
      (phiHatPlus T ψ n).obj τ =
        SmoothRep.of
          (Induction.smoothInduced (plusSubgroup n F.Carrier)
            (plusTwistRepresentation ψ n
              (Langlands.twist (phiPlusCharacter T n) τ.representation)))
          (Induction.smoothInduced_smooth (plusSubgroup n F.Carrier)
            (plusTwistRepresentation ψ n
              (Langlands.twist (phiPlusCharacter T n) τ.representation))) := by
  intros
  rfl

/-- Evaluation of a vector of normalized `Φ̂⁺(τ)` at a point of `P_(n+2)`. -/
abbrev phiHatPlusNormalizedEval (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    (τ : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier)) →
      (phiHatPlus T ψ n).obj τ → mirabolic (n + 1) F.Carrier → τ := by
  letI := T.topology
  exact fun τ => phiHatPlusEval T ψ n
    ((SmoothRep.twistFunctor (phiPlusCharacter T n) (isOpen_ker_phiPlusCharacter T n)).obj τ)

/-- Vectors of normalized `Φ̂⁺(τ)` are determined by their values. -/
theorem phiHatPlusNormalizedEval_injective (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    ∀ τ : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier),
      Function.Injective (phiHatPlusNormalizedEval T ψ n τ) := by
  let := T.topology
  intro τ
  exact phiHatPlusEval_injective T ψ n _

/-- Covariance
`φ(q x) = thetaPlus(q) • |det(plusProjection q)|^(1/2) • τ(plusProjection q) φ(x)`
for `q ∈ Q`. -/
theorem phiHatPlusNormalizedEval_covariant (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    ∀ (τ : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier))
      (φ : (phiHatPlus T ψ n).obj τ) (q : plusSubgroup n F.Carrier)
      (x : mirabolic (n + 1) F.Carrier),
      phiHatPlusNormalizedEval T ψ n τ φ ((q : mirabolic (n + 1) F.Carrier) * x) =
        (thetaPlus ψ n q : ℂ) • (phiPlusCharacter T n (plusProjection q) : ℂ) •
          τ.representation (plusProjection q) (phiHatPlusNormalizedEval T ψ n τ φ x) := by
  let := T.topology
  intro τ φ q x
  exact phiHatPlusEval_covariant T ψ n _ φ q x

/-- Radical elements act on values through `Θ`. -/
theorem phiHatPlusNormalizedEval_radical_mul (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    ∀ (τ : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier))
      (φ : (phiHatPlus T ψ n).obj τ) (u : radical (n + 1) F.Carrier)
      (x : mirabolic (n + 1) F.Carrier),
      phiHatPlusNormalizedEval T ψ n τ φ (u.val * x) =
        (theta ψ n u : ℂ) • phiHatPlusNormalizedEval T ψ n τ φ x := by
  let := T.topology
  intro τ φ u x
  exact phiHatPlusEval_radical_mul T ψ n _ φ u x

/-- Successor elements act on values through `|det|^(1/2) τ`. -/
theorem phiHatPlusNormalizedEval_successor_mul (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    ∀ (τ : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier))
      (φ : (phiHatPlus T ψ n).obj τ) (g : mirabolic n F.Carrier)
      (x : mirabolic (n + 1) F.Carrier),
      phiHatPlusNormalizedEval T ψ n τ φ (successor g * x) =
        (phiPlusCharacter T n g : ℂ) •
          τ.representation g (phiHatPlusNormalizedEval T ψ n τ φ x) := by
  let := T.topology
  intro τ φ g x
  exact phiHatPlusEval_successor_mul T ψ n _ φ g x

/-- Each vector has one open subgroup of right stabilizers. -/
theorem phiHatPlusNormalizedEval_exists_openSubgroup (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    ∀ (τ : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier))
      (φ : (phiHatPlus T ψ n).obj τ),
      ∃ K : OpenSubgroup (mirabolic (n + 1) F.Carrier),
        ∀ (k : K) (x : mirabolic (n + 1) F.Carrier),
          phiHatPlusNormalizedEval T ψ n τ φ (x * (k : mirabolic (n + 1) F.Carrier)) =
            phiHatPlusNormalizedEval T ψ n τ φ x := by
  let := T.topology
  intro τ φ
  exact phiHatPlusEval_exists_openSubgroup T ψ n _ φ

/-- A vector of normalized `Φ̂⁺(τ)` from a normalized covariant function with one open
subgroup of right stabilizers. -/
def phiHatPlusNormalizedMk (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    (τ : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier)) →
      (f : mirabolic (n + 1) F.Carrier → τ) →
      (∀ (q : plusSubgroup n F.Carrier) (x : mirabolic (n + 1) F.Carrier),
        f ((q : mirabolic (n + 1) F.Carrier) * x) =
          (thetaPlus ψ n q : ℂ) • (phiPlusCharacter T n (plusProjection q) : ℂ) •
            τ.representation (plusProjection q) (f x)) →
      (K : OpenSubgroup (mirabolic (n + 1) F.Carrier)) →
      (∀ (k : K) (x : mirabolic (n + 1) F.Carrier),
        f (x * (k : mirabolic (n + 1) F.Carrier)) = f x) →
      (phiHatPlus T ψ n).obj τ := by
  letI := T.topology
  exact fun τ f hcov K hK => phiHatPlusMk T ψ n
    ((SmoothRep.twistFunctor (phiPlusCharacter T n) (isOpen_ker_phiPlusCharacter T n)).obj τ)
    f hcov K hK

theorem phiHatPlusNormalizedEval_mk (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    ∀ (τ : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier))
      (f : mirabolic (n + 1) F.Carrier → τ)
      (hcov : ∀ (q : plusSubgroup n F.Carrier) (x : mirabolic (n + 1) F.Carrier),
        f ((q : mirabolic (n + 1) F.Carrier) * x) =
          (thetaPlus ψ n q : ℂ) • (phiPlusCharacter T n (plusProjection q) : ℂ) •
            τ.representation (plusProjection q) (f x))
      (K : OpenSubgroup (mirabolic (n + 1) F.Carrier))
      (hK : ∀ (k : K) (x : mirabolic (n + 1) F.Carrier),
        f (x * (k : mirabolic (n + 1) F.Carrier)) = f x),
      phiHatPlusNormalizedEval T ψ n τ (phiHatPlusNormalizedMk T ψ n τ f hcov K hK) = f := by
  intros
  rfl

/-- The action is right translation: `(g • φ)(x) = φ(x g)`. -/
theorem phiHatPlus_action (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    ∀ (τ : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier)) (g : mirabolic (n + 1) F.Carrier)
      (φ : (phiHatPlus T ψ n).obj τ) (x : mirabolic (n + 1) F.Carrier),
      phiHatPlusNormalizedEval T ψ n τ (((phiHatPlus T ψ n).obj τ).representation g φ) x =
        phiHatPlusNormalizedEval T ψ n τ φ (x * g) := by
  intros
  rfl

/-- On values, the induced map is postcomposition: `(Φ̂⁺ f) φ (x) = f (φ x)`. -/
theorem phiHatPlus_map_eval (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    ∀ {τ σ : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier)} (f : τ ⟶ σ)
      (φ : (phiHatPlus T ψ n).obj τ) (x : mirabolic (n + 1) F.Carrier),
      phiHatPlusNormalizedEval T ψ n σ (SmoothRep.hom ((phiHatPlus T ψ n).map f) φ) x =
        SmoothRep.hom f (phiHatPlusNormalizedEval T ψ n τ φ x) := by
  intros
  rfl

/-- Normalized `Φ̂⁺` sends injective intertwiners to injective intertwiners. -/
theorem phiHatPlus_map_injective (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    ∀ {τ σ : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier)} (f : τ ⟶ σ),
      Function.Injective (SmoothRep.hom f) →
        Function.Injective (SmoothRep.hom ((phiHatPlus T ψ n).map f)) := by
  let := T.topology
  intro τ σ f hf
  exact phiHatPlusUnnormalized_map_injective T ψ n _ hf

/-- Normalized `Φ̂⁺` preserves monomorphisms. -/
theorem phiHatPlus_map_mono (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    ∀ {τ σ : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier)} (f : τ ⟶ σ),
      Mono f → Mono ((phiHatPlus T ψ n).map f) := by
  let := T.topology
  intro τ σ f hf
  rw [SmoothRep.mono_iff_injective] at hf ⊢
  exact phiHatPlus_map_injective T ψ n f hf

/-! ## The compact `Φ⁺` inside the smooth `Φ̂⁺` -/

/-- The inclusion `Φ⁺(τ) ⊆ Φ̂⁺(τ)` of compactly supported smooth covariant functions,
as a natural transformation of the normalized functors (BZ77 §1.8(a)). -/
def phiPlusToPhiHatPlus (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    phiPlus.{uV} T ψ n ⟶ phiHatPlus.{uV} T ψ n := by
  letI := T.topology
  letI := T.generalLinearTopologicalGroup (n + 1 + 1)
  exact Functor.whiskerLeft
    (SmoothRep.twistFunctor (phiPlusCharacter T n) (isOpen_ker_phiPlusCharacter T n) ⋙
      plusTwistFunctor T ψ n ⋙ SmoothRep.toRep)
    (Induction.compactSmoothInclusion (plusSubgroup n F.Carrier))

/-- The inclusion keeps every value. -/
theorem phiPlusToPhiHatPlus_eval (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    ∀ (τ : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier)) (φ : (phiPlus T ψ n).obj τ)
      (x : mirabolic (n + 1) F.Carrier),
      phiHatPlusNormalizedEval T ψ n τ
          (SmoothRep.hom ((phiPlusToPhiHatPlus T ψ n).app τ) φ) x =
        phiPlusNormalizedEval T ψ n τ φ x := by
  intros
  rfl

/-- The inclusion `Φ⁺(τ) → Φ̂⁺(τ)` is injective. -/
theorem phiPlusToPhiHatPlus_injective (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    ∀ τ : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier),
      Function.Injective (SmoothRep.hom ((phiPlusToPhiHatPlus T ψ n).app τ)) := by
  let := T.topology
  intro τ φ φ' h
  apply phiPlusNormalizedEval_injective T ψ n τ
  funext x
  exact congrArg (fun w => phiHatPlusNormalizedEval T ψ n τ w x) h

end Langlands.Derivative.Mirabolic
