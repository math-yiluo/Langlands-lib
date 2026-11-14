import Langlands.AllFieldBZ.Representation.Derivative.Homogeneity
import Langlands.AllFieldBZ.Representation.Derivative.MirabolicSmoothPhiPlusAdjunction
import Langlands.AllFieldBZ.Representation.Mirabolic.MixedProducts
import Langlands.Representation.Derivative.MirabolicSmoothPhiPlusIterate

/-!
# All-field port of `Langlands.Representation.Derivative.MirabolicSmoothPhiPlusIterate`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Derivative.MirabolicSmoothPhiPlusIterate` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
open CategoryTheory
namespace Langlands.AllFieldBZ.Derivative
open Langlands.Derivative hiding HasNonzeroDerivative IsHomogeneous generalLinearDerivative generalLinearDerivativePositive generalLinearDerivativePositive_eq generalLinearDerivativePositive_obj generalLinearDerivative_of_pos generalLinearDerivative_succ generalLinearDerivative_succ_obj generalLinearDerivative_top_succ generalLinearDerivative_zero generalLinearRankCast generalLinearRankCast_refl generalLinearRankCast_symm_comp generalLinearRankCast_trans generalLinearRestriction generalLinearRestriction_map_apply generalLinearRestriction_map_toLinearMap hasNonzeroDerivative_iff isHomogeneous_of_subsingleton le_level_of_hasNonzeroDerivative level level_eq_iff level_eq_zero_iff level_eq_zero_of_subsingleton level_le mirabolicDerivative mirabolicDerivativeAdjunction mirabolicDerivativeAdjunction_comp_left mirabolicDerivativeOfOrder mirabolicDerivativeOfOrderAdjunction mirabolicDerivativeOfOrderAdjunction_comp_left mirabolicDerivativeOfOrderAdjunction_unit mirabolicDerivativeOfOrderAdjunction_unit_comp mirabolicDerivativeOfOrderRightAdjoint mirabolicDerivativeOfOrderUnit mirabolicDerivativeOfOrder_eq mirabolicDerivativeOfOrder_map_eq_zero_of_unit_comp mirabolicDerivativeOfOrder_obj mirabolicDerivativeOfOrder_obj_subsingleton mirabolicDerivativeOfOrder_one mirabolicDerivativeOfOrder_top mirabolicDerivativeRightAdjoint mirabolicDerivative_eq mirabolicDerivative_obj_subsingleton mirabolicDerivative_succ mirabolicDerivative_zero mirabolicRankCast mirabolicRankCastHomEquiv mirabolicRankCastHomEquiv_comp_left mirabolicRankCast_obj_subsingleton mirabolicRankCast_refl phiHatPlusIterate phiHatPlusIterateAdjunction phiHatPlusIterateAdjunction_comp_left phiHatPlusIterateAdjunction_succ phiMinusIterate phiMinusIterate_obj_subsingleton phiMinusIterate_succ phiMinusIterate_zero
open Langlands.GeneralLinear
open Langlands.AllFieldBZ.GeneralLinear
open Langlands.HarmonicAnalysis hiding PadicRectangularHaarScalingStatement padicRectangularHaarScaling padicRectangularHaarScalingStatement padicScalarHaarScaling
open Langlands.AllFieldBZ.HarmonicAnalysis
universe uA uY uG uV uF

/-! ## Intertwiners into a carrier lift -/

section Lift
variable {G : Type uG} [Group G] [TopologicalSpace G]

end Lift
variable {F : LocalFieldPackage.{uF}}

/-! ## Iterated `Φ̂⁺` -/

/-- `(Φ̂⁺)^k : P_(n+1) → P_(n+k+1)` in the carrier universe `max uF uV`, applying `Φ̂⁺` at
the smallest rank first. -/
def phiHatPlusIterate (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    (k : ℕ) →
      letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (mirabolic n F.Carrier) ⥤
        SmoothRep.{0, uF, max uF uV} ℂ (mirabolic (n + k) F.Carrier)
  | 0 => letI := T.topology; 𝟭 _
  | k + 1 => letI := T.topology;
      phiHatPlusIterate T ψ n k ⋙ Mirabolic.phiHatPlus.{max uF uV} T ψ (n + k)

/-- Iterated `Φ⁻ ⊣ Φ̂⁺`: `Hom(A, (Φ̂⁺)^k X) ≃ Hom((Φ⁻)^k A, X)`. -/
def phiHatPlusIterateAdjunction (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    (k : ℕ) →
      letI := T.topology
      (A : SmoothRep.{0, uF, uA} ℂ (mirabolic (n + k) F.Carrier)) →
        (X : SmoothRep.{0, uF, max uF uV} ℂ (mirabolic n F.Carrier)) →
        A.representation.IntertwiningMap
            ((phiHatPlusIterate.{uV} T ψ n k).obj X).representation ≃ₗ[ℂ]
          ((phiMinusIterate T ψ n k).obj A).representation.IntertwiningMap X.representation
  | 0 => fun _ _ => LinearEquiv.refl ℂ _
  | k + 1 => fun A X =>
      (Mirabolic.phiHatPlusAdjunction T ψ (n + k) A
          ((phiHatPlusIterate.{uV} T ψ n k).obj X)).trans
        (phiHatPlusIterateAdjunction T ψ n k ((Mirabolic.phiMinus T ψ (n + k)).obj A) X)

theorem phiHatPlusIterateAdjunction_succ (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n k : ℕ) :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, uA} ℂ (mirabolic (n + k + 1) F.Carrier))
      (X : SmoothRep.{0, uF, max uF uV} ℂ (mirabolic n F.Carrier))
      (Φ : A.representation.IntertwiningMap
        ((phiHatPlusIterate.{uV} T ψ n (k + 1)).obj X).representation),
      phiHatPlusIterateAdjunction T ψ n (k + 1) A X Φ =
        phiHatPlusIterateAdjunction T ψ n k ((Mirabolic.phiMinus T ψ (n + k)).obj A) X
          (Mirabolic.phiHatPlusAdjunction T ψ (n + k) A
            ((phiHatPlusIterate.{uV} T ψ n k).obj X) Φ) := by
  intros
  rfl

/-- Naturality in the left argument. -/
theorem phiHatPlusIterateAdjunction_comp_left (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    ∀ (k : ℕ) {A' A : SmoothRep.{0, uF, uA} ℂ (mirabolic (n + k) F.Carrier)} (f : A' ⟶ A)
      (X : SmoothRep.{0, uF, max uF uV} ℂ (mirabolic n F.Carrier))
      (Φ : A.representation.IntertwiningMap
        ((phiHatPlusIterate.{uV} T ψ n k).obj X).representation),
      phiHatPlusIterateAdjunction T ψ n k A' X (Φ.comp (SmoothRep.hom f)) =
        (phiHatPlusIterateAdjunction T ψ n k A X Φ).comp
          (SmoothRep.hom ((phiMinusIterate T ψ n k).map f)) := by
  let := T.topology
  intro k
  induction k with
  | zero => intros; rfl
  | succ k ih =>
    intro A' A f X Φ
    rw [phiHatPlusIterateAdjunction_succ, phiHatPlusIterateAdjunction_succ]
    have h1 := Mirabolic.phiHatPlusAdjunction_comp_left T ψ (n + k) f
      ((phiHatPlusIterate.{uV} T ψ n k).obj X) Φ
    have h2 := ih ((Mirabolic.phiMinus T ψ (n + k)).map f) X
      (Mirabolic.phiHatPlusAdjunction T ψ (n + k) A ((phiHatPlusIterate.{uV} T ψ n k).obj X) Φ)
    exact (congrArg (fun Ψ => phiHatPlusIterateAdjunction T ψ n k
      ((Mirabolic.phiMinus T ψ (n + k)).obj A') X Ψ) h1).trans h2

/-! ## The right adjoint `Y = (Φ̂⁺)^k ∘ Ψ⁺` -/

/-- `Y_(n,k) = (Φ̂⁺)^k ∘ Ψ⁺ : GL_n → P_(n+k+1)`, with `Ψ⁺ θ` lifted to the carrier universe
`max uF uV` before the iteration. It is right adjoint to the published
`mirabolicDerivative n k = Ψ⁻ ∘ (Φ⁻)^k`. -/
def mirabolicDerivativeRightAdjoint (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n k : ℕ) :
    letI := T.topology
    SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier) ⥤
      SmoothRep.{0, uF, max uF uV} ℂ (mirabolic (n + k) F.Carrier) := by
  letI := T.topology
  exact Mirabolic.psiPlus T n ⋙ MixedProductTensor.liftFunctor.{uF, uV, uF} ⋙
    phiHatPlusIterate.{uV} T ψ n k

/-- BZ77 §3.2(b,c) iterated: `Hom(A, Y θ) ≃ Hom(Ψ⁻ (Φ⁻)^k A, θ)`, the composite of the
iterated `Φ⁻ ⊣ Φ̂⁺`, the carrier lift and `Ψ⁻ ⊣ Ψ⁺`. -/
def mirabolicDerivativeAdjunction (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n k : ℕ) :
    letI := T.topology
    (A : SmoothRep.{0, uF, uA} ℂ (mirabolic (n + k) F.Carrier)) →
      (θ : SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier)) →
      A.representation.IntertwiningMap
          ((mirabolicDerivativeRightAdjoint.{uV} T ψ n k).obj θ).representation ≃ₗ[ℂ]
        ((mirabolicDerivative T ψ n k).obj A).representation.IntertwiningMap θ.representation := by
  letI := T.topology
  exact fun A θ =>
    (phiHatPlusIterateAdjunction T ψ n k A
        ((MixedProductTensor.liftFunctor.{uF, uV, uF}).obj ((Mirabolic.psiPlus T n).obj θ))).trans
      ((liftHomEquiv _ _).trans
        (Mirabolic.psiPlusAdjunction T n ((phiMinusIterate T ψ n k).obj A) θ))

/-- Naturality in the left argument. -/
theorem mirabolicDerivativeAdjunction_comp_left (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n k : ℕ) :
    letI := T.topology
    ∀ {A' A : SmoothRep.{0, uF, uA} ℂ (mirabolic (n + k) F.Carrier)} (f : A' ⟶ A)
      (θ : SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier))
      (Φ : A.representation.IntertwiningMap
        ((mirabolicDerivativeRightAdjoint.{uV} T ψ n k).obj θ).representation),
      mirabolicDerivativeAdjunction T ψ n k A' θ (Φ.comp (SmoothRep.hom f)) =
        (mirabolicDerivativeAdjunction T ψ n k A θ Φ).comp
          (SmoothRep.hom ((mirabolicDerivative T ψ n k).map f)) := by
  let := T.topology
  intro A' A f θ Φ
  have h1 := phiHatPlusIterateAdjunction_comp_left T ψ n k f
    ((MixedProductTensor.liftFunctor.{uF, uV, uF}).obj ((Mirabolic.psiPlus T n).obj θ)) Φ
  have h2 := liftHomEquiv_comp_left ((phiMinusIterate T ψ n k).map f)
    ((Mirabolic.psiPlus T n).obj θ)
    (phiHatPlusIterateAdjunction T ψ n k A _ Φ)
  have h3 := Mirabolic.psiPlusAdjunction_comp_left T n ((phiMinusIterate T ψ n k).map f) θ
    (liftHomEquiv _ _ (phiHatPlusIterateAdjunction T ψ n k A _ Φ))
  exact (congrArg (fun Ψ => Mirabolic.psiPlusAdjunction T n ((phiMinusIterate T ψ n k).obj A') θ
      (liftHomEquiv _ _ Ψ)) h1).trans
    ((congrArg (fun Ψ => Mirabolic.psiPlusAdjunction T n ((phiMinusIterate T ψ n k).obj A') θ Ψ)
      h2).trans h3)

/-! ## Rank transport -/

/-- Intertwiners into a rank transport are intertwiners out of the inverse transport. -/
def mirabolicRankCastHomEquiv (T : F.TopologicalData) {a b : ℕ} (h : a = b) :
    letI := T.topology
    (A : SmoothRep.{0, uF, uA} ℂ (mirabolic b F.Carrier)) →
      (B : SmoothRep.{0, uF, uV} ℂ (mirabolic a F.Carrier)) →
      A.representation.IntertwiningMap ((mirabolicRankCast T h).obj B).representation ≃ₗ[ℂ]
        ((mirabolicRankCast T h.symm).obj A).representation.IntertwiningMap B.representation := by
  subst h
  letI := T.topology
  exact fun _ _ => LinearEquiv.refl ℂ _

theorem mirabolicRankCastHomEquiv_comp_left (T : F.TopologicalData) {a b : ℕ} (h : a = b) :
    letI := T.topology
    ∀ {A' A : SmoothRep.{0, uF, uA} ℂ (mirabolic b F.Carrier)} (f : A' ⟶ A)
      (B : SmoothRep.{0, uF, uV} ℂ (mirabolic a F.Carrier))
      (Φ : A.representation.IntertwiningMap ((mirabolicRankCast T h).obj B).representation),
      mirabolicRankCastHomEquiv T h A' B (Φ.comp (SmoothRep.hom f)) =
        (mirabolicRankCastHomEquiv T h A B Φ).comp
          (SmoothRep.hom ((mirabolicRankCast T h.symm).map f)) := by
  subst h
  intros
  rfl

/-! ## The order-indexed adjunction -/

/-- The right adjoint of `mirabolicDerivativeOfOrder N l`: `Y_(N+1-l, l-1)` transported to
`P_(N+1)` along the published rank equality. -/
def mirabolicDerivativeOfOrderRightAdjoint (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (N l : ℕ) (hl : 0 < l ∧ l ≤ N + 1) :
    letI := T.topology
    SmoothRep.{0, uF, uV} ℂ (GeneralLinear (N + 1 - l) F.Carrier) ⥤
      SmoothRep.{0, uF, max uF uV} ℂ (mirabolic N F.Carrier) := by
  letI := T.topology
  exact mirabolicDerivativeRightAdjoint.{uV} T ψ (N + 1 - l) (l - 1) ⋙
    mirabolicRankCast T (mirabolic_rank_eq_of_order hl).symm

/-- `Hom(A, Y θ) ≃ Hom(A^(l), θ)` for the order-`l` derivative of `A ∈ Rep(P_(N+1))`. -/
def mirabolicDerivativeOfOrderAdjunction (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (N l : ℕ) (hl : 0 < l ∧ l ≤ N + 1) :
    letI := T.topology
    (A : SmoothRep.{0, uF, uA} ℂ (mirabolic N F.Carrier)) →
      (θ : SmoothRep.{0, uF, uV} ℂ (GeneralLinear (N + 1 - l) F.Carrier)) →
      A.representation.IntertwiningMap
          ((mirabolicDerivativeOfOrderRightAdjoint.{uV} T ψ N l hl).obj θ).representation ≃ₗ[ℂ]
        ((mirabolicDerivativeOfOrder T ψ N l hl).obj A).representation.IntertwiningMap
          θ.representation := by
  letI := T.topology
  exact fun A θ =>
    (mirabolicRankCastHomEquiv T (mirabolic_rank_eq_of_order hl).symm A _).trans
      (mirabolicDerivativeAdjunction T ψ (N + 1 - l) (l - 1)
        ((mirabolicRankCast T (mirabolic_rank_eq_of_order hl)).obj A) θ)

/-- Naturality in the left argument. -/
theorem mirabolicDerivativeOfOrderAdjunction_comp_left (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (N l : ℕ) (hl : 0 < l ∧ l ≤ N + 1) :
    letI := T.topology
    ∀ {A' A : SmoothRep.{0, uF, uA} ℂ (mirabolic N F.Carrier)} (f : A' ⟶ A)
      (θ : SmoothRep.{0, uF, uV} ℂ (GeneralLinear (N + 1 - l) F.Carrier))
      (Φ : A.representation.IntertwiningMap
        ((mirabolicDerivativeOfOrderRightAdjoint.{uV} T ψ N l hl).obj θ).representation),
      mirabolicDerivativeOfOrderAdjunction T ψ N l hl A' θ (Φ.comp (SmoothRep.hom f)) =
        (mirabolicDerivativeOfOrderAdjunction T ψ N l hl A θ Φ).comp
          (SmoothRep.hom ((mirabolicDerivativeOfOrder T ψ N l hl).map f)) := by
  let := T.topology
  intro A' A f θ Φ
  have h1 := mirabolicRankCastHomEquiv_comp_left T (mirabolic_rank_eq_of_order hl).symm f
    ((mirabolicDerivativeRightAdjoint.{uV} T ψ (N + 1 - l) (l - 1)).obj θ) Φ
  have h2 := mirabolicDerivativeAdjunction_comp_left T ψ (N + 1 - l) (l - 1)
    ((mirabolicRankCast T (mirabolic_rank_eq_of_order hl)).map f) θ
    (mirabolicRankCastHomEquiv T (mirabolic_rank_eq_of_order hl).symm A _ Φ)
  exact (congrArg (fun Ψ => mirabolicDerivativeAdjunction T ψ (N + 1 - l) (l - 1)
      ((mirabolicRankCast T (mirabolic_rank_eq_of_order hl)).obj A') θ Ψ) h1).trans h2

/-! ## The unit `τ → Y(τ^(l))` -/

/-- The unit `A → Y(A^(l))`: the intertwiner corresponding to the identity of `A^(l)`. -/
def mirabolicDerivativeOfOrderUnit (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (N l : ℕ) (hl : 0 < l ∧ l ≤ N + 1) :
    letI := T.topology
    (A : SmoothRep.{0, uF, uV} ℂ (mirabolic N F.Carrier)) →
      A.representation.IntertwiningMap
        ((mirabolicDerivativeOfOrderRightAdjoint.{uV} T ψ N l hl).obj
          ((mirabolicDerivativeOfOrder T ψ N l hl).obj A)).representation := by
  letI := T.topology
  exact fun A => (mirabolicDerivativeOfOrderAdjunction T ψ N l hl A _).symm
    (Representation.IntertwiningMap.id _)

/-- The unit corresponds to the identity. -/
theorem mirabolicDerivativeOfOrderAdjunction_unit (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (N l : ℕ) (hl : 0 < l ∧ l ≤ N + 1) :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (mirabolic N F.Carrier),
      mirabolicDerivativeOfOrderAdjunction T ψ N l hl A _
          (mirabolicDerivativeOfOrderUnit T ψ N l hl A) =
        Representation.IntertwiningMap.id _ := by
  let := T.topology
  intro A
  exact LinearEquiv.apply_symm_apply _ _

/-- The unit composed with `f : A' ⟶ A` corresponds to the derivative of `f`. -/
theorem mirabolicDerivativeOfOrderAdjunction_unit_comp (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (N l : ℕ) (hl : 0 < l ∧ l ≤ N + 1) :
    letI := T.topology
    ∀ {A' A : SmoothRep.{0, uF, uV} ℂ (mirabolic N F.Carrier)} (f : A' ⟶ A),
      mirabolicDerivativeOfOrderAdjunction T ψ N l hl A' _
          ((mirabolicDerivativeOfOrderUnit T ψ N l hl A).comp (SmoothRep.hom f)) =
        SmoothRep.hom ((mirabolicDerivativeOfOrder T ψ N l hl).map f) := by
  let := T.topology
  intro A' A f
  rw [mirabolicDerivativeOfOrderAdjunction_comp_left, mirabolicDerivativeOfOrderAdjunction_unit]
  rfl

/-- If the unit composed with `f` vanishes, then the derivative of `f` vanishes. -/
theorem mirabolicDerivativeOfOrder_map_eq_zero_of_unit_comp (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (N l : ℕ) (hl : 0 < l ∧ l ≤ N + 1) :
    letI := T.topology
    ∀ {A' A : SmoothRep.{0, uF, uV} ℂ (mirabolic N F.Carrier)} (f : A' ⟶ A),
      (mirabolicDerivativeOfOrderUnit T ψ N l hl A).comp (SmoothRep.hom f) = 0 →
        SmoothRep.hom ((mirabolicDerivativeOfOrder T ψ N l hl).map f) = 0 := by
  let := T.topology
  intro A' A f h
  rw [← mirabolicDerivativeOfOrderAdjunction_unit_comp, h, map_zero]

end Langlands.AllFieldBZ.Derivative
