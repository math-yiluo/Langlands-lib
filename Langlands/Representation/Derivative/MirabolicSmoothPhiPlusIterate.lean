import Langlands.Representation.Derivative.MirabolicSmoothPhiPlusAdjunction
import Langlands.Representation.Derivative.Homogeneity
import Langlands.Representation.Mirabolic.MixedProducts

/-!
# The right adjoint of the mirabolic derivative

Iterating `Φ̂⁺` and composing with `Ψ⁺` gives the right adjoint
`Y = (Φ̂⁺)^k ∘ Ψ⁺ : GL_n → P_(n+k+1)` of the published mirabolic derivative
`Ψ⁻ ∘ (Φ⁻)^k` (Bernstein–Zelevinsky 1977, §3.2(b,c) iterated). For every `σ` and `θ`

* `Hom(σ, Y θ) ≃ Hom(σ^(k+1), θ)`, as an actual complex-linear equivalence of
  intertwiner spaces, natural in `σ` and in `θ`;
* the same for the order-indexed derivative `mirabolicDerivativeOfOrder`, through its
  published rank transport;
* a nonzero intertwiner `σ → Y θ` forces a nonzero derivative `σ^(l)`;
* the unit `τ → Y(τ^(l))` corresponds to the identity of `τ^(l)` and is natural.

`Φ̂⁺` raises the carrier universe to `max uF uV`, so the iteration runs in that universe
and `Ψ⁺ θ` is first lifted to it by the published carrier lift. No exactness and no
injectivity of the unit is stated.
-/

noncomputable section

open CategoryTheory

namespace Langlands.Derivative

open GeneralLinear HarmonicAnalysis

universe uA uY uG uV uF

/-! ## Intertwiners into a carrier lift -/

section Lift

variable {G : Type uG} [Group G] [TopologicalSpace G]

/-- Intertwiners into the carrier lift `ULift B` are intertwiners into `B`:
postcomposition with `ULift.down`. -/
def liftHomEquiv (A : SmoothRep.{0, uG, uA} ℂ G) (B : SmoothRep.{0, uG, uV} ℂ G) :
    A.representation.IntertwiningMap
        ((MixedProductTensor.liftFunctor.{uG, uV, uY}).obj B).representation ≃ₗ[ℂ]
      A.representation.IntertwiningMap B.representation where
  toFun f := (MixedProductTensor.liftEquiv.{uG, uV, uY} B.representation).symm.toIntertwiningMap.comp f
  invFun f := (MixedProductTensor.liftEquiv.{uG, uV, uY} B.representation).toIntertwiningMap.comp f
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem liftHomEquiv_apply (A : SmoothRep.{0, uG, uA} ℂ G) (B : SmoothRep.{0, uG, uV} ℂ G)
    (f : A.representation.IntertwiningMap
      ((MixedProductTensor.liftFunctor.{uG, uV, uY}).obj B).representation) (v : A) :
    liftHomEquiv A B f v = (f v).down :=
  rfl

theorem liftHomEquiv_symm_apply (A : SmoothRep.{0, uG, uA} ℂ G) (B : SmoothRep.{0, uG, uV} ℂ G)
    (f : A.representation.IntertwiningMap B.representation) (v : A) :
    (liftHomEquiv A B).symm f v = ULift.up.{uY} (f v) :=
  rfl

theorem liftHomEquiv_comp_left {A' A : SmoothRep.{0, uG, uA} ℂ G} (f : A' ⟶ A)
    (B : SmoothRep.{0, uG, uV} ℂ G)
    (Φ : A.representation.IntertwiningMap
      ((MixedProductTensor.liftFunctor.{uG, uV, uY}).obj B).representation) :
    liftHomEquiv A' B (Φ.comp (SmoothRep.hom f)) = (liftHomEquiv A B Φ).comp (SmoothRep.hom f) :=
  rfl

theorem liftHomEquiv_comp_right (A : SmoothRep.{0, uG, uA} ℂ G)
    {B B' : SmoothRep.{0, uG, uV} ℂ G} (g : B ⟶ B')
    (Φ : A.representation.IntertwiningMap
      ((MixedProductTensor.liftFunctor.{uG, uV, uY}).obj B).representation) :
    liftHomEquiv A B'
        ((SmoothRep.hom ((MixedProductTensor.liftFunctor.{uG, uV, uY}).map g)).comp Φ) =
      (SmoothRep.hom g).comp (liftHomEquiv A B Φ) :=
  rfl

end Lift

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

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

theorem phiHatPlusIterate_zero (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    phiHatPlusIterate.{uV} T ψ n 0 =
      𝟭 (SmoothRep.{0, uF, max uF uV} ℂ (mirabolic n F.Carrier)) :=
  rfl

theorem phiHatPlusIterate_succ (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n k : ℕ) :
    letI := T.topology
    phiHatPlusIterate.{uV} T ψ n (k + 1) =
      phiHatPlusIterate T ψ n k ⋙ Mirabolic.phiHatPlus.{max uF uV} T ψ (n + k) :=
  rfl

/-- `(Φ̂⁺)^k` sends injective intertwiners to injective intertwiners. -/
theorem phiHatPlusIterate_map_injective (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    ∀ (k : ℕ) {X X' : SmoothRep.{0, uF, max uF uV} ℂ (mirabolic n F.Carrier)} (g : X ⟶ X'),
      Function.Injective (SmoothRep.hom g) →
        Function.Injective (SmoothRep.hom ((phiHatPlusIterate.{uV} T ψ n k).map g)) := by
  let := T.topology
  intro k
  induction k with
  | zero => exact fun _ hg => hg
  | succ k ih =>
    intro X X' g hg
    exact Mirabolic.phiHatPlus_map_injective T ψ (n + k) _ (ih g hg)

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

theorem phiHatPlusIterateAdjunction_zero (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, uA} ℂ (mirabolic n F.Carrier))
      (X : SmoothRep.{0, uF, max uF uV} ℂ (mirabolic n F.Carrier))
      (Φ : A.representation.IntertwiningMap
        ((phiHatPlusIterate.{uV} T ψ n 0).obj X).representation),
      phiHatPlusIterateAdjunction T ψ n 0 A X Φ = Φ := by
  intros
  rfl

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

/-- Naturality in the right argument. -/
theorem phiHatPlusIterateAdjunction_comp_right (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    ∀ (k : ℕ) (A : SmoothRep.{0, uF, uA} ℂ (mirabolic (n + k) F.Carrier))
      {X X' : SmoothRep.{0, uF, max uF uV} ℂ (mirabolic n F.Carrier)} (g : X ⟶ X')
      (Φ : A.representation.IntertwiningMap
        ((phiHatPlusIterate.{uV} T ψ n k).obj X).representation),
      phiHatPlusIterateAdjunction T ψ n k A X'
          ((SmoothRep.hom ((phiHatPlusIterate.{uV} T ψ n k).map g)).comp Φ) =
        (SmoothRep.hom g).comp (phiHatPlusIterateAdjunction T ψ n k A X Φ) := by
  let := T.topology
  intro k
  induction k with
  | zero => intros; rfl
  | succ k ih =>
    intro A X X' g Φ
    rw [phiHatPlusIterateAdjunction_succ, phiHatPlusIterateAdjunction_succ]
    change phiHatPlusIterateAdjunction T ψ n k _ X'
        (Mirabolic.phiHatPlusAdjunction T ψ (n + k) A _
          ((SmoothRep.hom ((Mirabolic.phiHatPlus T ψ (n + k)).map
            ((phiHatPlusIterate.{uV} T ψ n k).map g))).comp Φ)) = _
    have h1 := Mirabolic.phiHatPlusAdjunction_comp_right T ψ (n + k) A
      ((phiHatPlusIterate.{uV} T ψ n k).map g) Φ
    have h2 := ih ((Mirabolic.phiMinus T ψ (n + k)).obj A) g
      (Mirabolic.phiHatPlusAdjunction T ψ (n + k) A ((phiHatPlusIterate.{uV} T ψ n k).obj X) Φ)
    exact (congrArg (fun Ψ => phiHatPlusIterateAdjunction T ψ n k
      ((Mirabolic.phiMinus T ψ (n + k)).obj A) X' Ψ) h1).trans h2

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

theorem mirabolicDerivativeRightAdjoint_eq (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n k : ℕ) :
    letI := T.topology
    mirabolicDerivativeRightAdjoint.{uV} T ψ n k =
      Mirabolic.psiPlus T n ⋙ MixedProductTensor.liftFunctor.{uF, uV, uF} ⋙
        phiHatPlusIterate.{uV} T ψ n k :=
  rfl

/-- `Y` sends injective intertwiners to injective intertwiners. -/
theorem mirabolicDerivativeRightAdjoint_map_injective (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n k : ℕ) :
    letI := T.topology
    ∀ {θ θ' : SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier)} (g : θ ⟶ θ'),
      Function.Injective (SmoothRep.hom g) →
        Function.Injective (SmoothRep.hom ((mirabolicDerivativeRightAdjoint.{uV} T ψ n k).map g)) := by
  let := T.topology
  intro θ θ' g hg
  apply phiHatPlusIterate_map_injective T ψ n k
  intro x y hxy
  exact ULift.ext _ _ (hg (congrArg ULift.down hxy))

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

theorem mirabolicDerivativeAdjunction_apply (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n k : ℕ) :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, uA} ℂ (mirabolic (n + k) F.Carrier))
      (θ : SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier))
      (Φ : A.representation.IntertwiningMap
        ((mirabolicDerivativeRightAdjoint.{uV} T ψ n k).obj θ).representation),
      mirabolicDerivativeAdjunction T ψ n k A θ Φ =
        Mirabolic.psiPlusAdjunction T n ((phiMinusIterate T ψ n k).obj A) θ
          (liftHomEquiv _ _ (phiHatPlusIterateAdjunction T ψ n k A _ Φ)) := by
  intros
  rfl

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

/-- Naturality in the right argument. -/
theorem mirabolicDerivativeAdjunction_comp_right (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n k : ℕ) :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, uA} ℂ (mirabolic (n + k) F.Carrier))
      {θ θ' : SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier)} (g : θ ⟶ θ')
      (Φ : A.representation.IntertwiningMap
        ((mirabolicDerivativeRightAdjoint.{uV} T ψ n k).obj θ).representation),
      mirabolicDerivativeAdjunction T ψ n k A θ'
          ((SmoothRep.hom ((mirabolicDerivativeRightAdjoint.{uV} T ψ n k).map g)).comp Φ) =
        (SmoothRep.hom g).comp (mirabolicDerivativeAdjunction T ψ n k A θ Φ) := by
  let := T.topology
  intro A θ θ' g Φ
  have h1 := phiHatPlusIterateAdjunction_comp_right T ψ n k A
    ((MixedProductTensor.liftFunctor.{uF, uV, uF}).map ((Mirabolic.psiPlus T n).map g)) Φ
  have h2 := liftHomEquiv_comp_right ((phiMinusIterate T ψ n k).obj A)
    ((Mirabolic.psiPlus T n).map g)
    (phiHatPlusIterateAdjunction T ψ n k A _ Φ)
  have h3 := Mirabolic.psiPlusAdjunction_comp_right T n ((phiMinusIterate T ψ n k).obj A) g
    (liftHomEquiv _ _ (phiHatPlusIterateAdjunction T ψ n k A _ Φ))
  exact (congrArg (fun Ψ => Mirabolic.psiPlusAdjunction T n ((phiMinusIterate T ψ n k).obj A) θ'
      (liftHomEquiv _ _ Ψ)) h1).trans
    ((congrArg (fun Ψ => Mirabolic.psiPlusAdjunction T n ((phiMinusIterate T ψ n k).obj A) θ' Ψ)
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

theorem mirabolicRankCastHomEquiv_refl (T : F.TopologicalData) (a : ℕ) (h : a = a) :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, uA} ℂ (mirabolic a F.Carrier))
      (B : SmoothRep.{0, uF, uV} ℂ (mirabolic a F.Carrier))
      (Φ : A.representation.IntertwiningMap ((mirabolicRankCast T h).obj B).representation),
      mirabolicRankCastHomEquiv T h A B Φ = Φ := by
  intros
  rfl

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

theorem mirabolicRankCastHomEquiv_comp_right (T : F.TopologicalData) {a b : ℕ} (h : a = b) :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, uA} ℂ (mirabolic b F.Carrier))
      {B B' : SmoothRep.{0, uF, uV} ℂ (mirabolic a F.Carrier)} (g : B ⟶ B')
      (Φ : A.representation.IntertwiningMap ((mirabolicRankCast T h).obj B).representation),
      mirabolicRankCastHomEquiv T h A B'
          ((SmoothRep.hom ((mirabolicRankCast T h).map g)).comp Φ) =
        (SmoothRep.hom g).comp (mirabolicRankCastHomEquiv T h A B Φ) := by
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

theorem mirabolicDerivativeOfOrderRightAdjoint_eq (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (N l : ℕ) (hl : 0 < l ∧ l ≤ N + 1) :
    letI := T.topology
    mirabolicDerivativeOfOrderRightAdjoint.{uV} T ψ N l hl =
      mirabolicDerivativeRightAdjoint.{uV} T ψ (N + 1 - l) (l - 1) ⋙
        mirabolicRankCast T (mirabolic_rank_eq_of_order hl).symm :=
  rfl

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

theorem mirabolicDerivativeOfOrderAdjunction_apply (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (N l : ℕ) (hl : 0 < l ∧ l ≤ N + 1) :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, uA} ℂ (mirabolic N F.Carrier))
      (θ : SmoothRep.{0, uF, uV} ℂ (GeneralLinear (N + 1 - l) F.Carrier))
      (Φ : A.representation.IntertwiningMap
        ((mirabolicDerivativeOfOrderRightAdjoint.{uV} T ψ N l hl).obj θ).representation),
      mirabolicDerivativeOfOrderAdjunction T ψ N l hl A θ Φ =
        mirabolicDerivativeAdjunction T ψ (N + 1 - l) (l - 1)
          ((mirabolicRankCast T (mirabolic_rank_eq_of_order hl)).obj A) θ
          (mirabolicRankCastHomEquiv T (mirabolic_rank_eq_of_order hl).symm A _ Φ) := by
  intros
  rfl

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

/-- Naturality in the right argument. -/
theorem mirabolicDerivativeOfOrderAdjunction_comp_right (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (N l : ℕ) (hl : 0 < l ∧ l ≤ N + 1) :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, uA} ℂ (mirabolic N F.Carrier))
      {θ θ' : SmoothRep.{0, uF, uV} ℂ (GeneralLinear (N + 1 - l) F.Carrier)} (g : θ ⟶ θ')
      (Φ : A.representation.IntertwiningMap
        ((mirabolicDerivativeOfOrderRightAdjoint.{uV} T ψ N l hl).obj θ).representation),
      mirabolicDerivativeOfOrderAdjunction T ψ N l hl A θ'
          ((SmoothRep.hom ((mirabolicDerivativeOfOrderRightAdjoint.{uV} T ψ N l hl).map g)).comp
            Φ) =
        (SmoothRep.hom g).comp (mirabolicDerivativeOfOrderAdjunction T ψ N l hl A θ Φ) := by
  let := T.topology
  intro A θ θ' g Φ
  have h1 := mirabolicRankCastHomEquiv_comp_right T (mirabolic_rank_eq_of_order hl).symm A
    ((mirabolicDerivativeRightAdjoint.{uV} T ψ (N + 1 - l) (l - 1)).map g) Φ
  have h2 := mirabolicDerivativeAdjunction_comp_right T ψ (N + 1 - l) (l - 1)
    ((mirabolicRankCast T (mirabolic_rank_eq_of_order hl)).obj A) g
    (mirabolicRankCastHomEquiv T (mirabolic_rank_eq_of_order hl).symm A _ Φ)
  exact (congrArg (fun Ψ => mirabolicDerivativeAdjunction T ψ (N + 1 - l) (l - 1)
      ((mirabolicRankCast T (mirabolic_rank_eq_of_order hl)).obj A) θ' Ψ) h1).trans h2

/-- A nonzero intertwiner `A → Y θ` forces a nonzero order-`l` derivative of `A`. -/
theorem nontrivial_mirabolicDerivativeOfOrder_of_ne_zero (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (N l : ℕ) (hl : 0 < l ∧ l ≤ N + 1) :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, uA} ℂ (mirabolic N F.Carrier))
      (θ : SmoothRep.{0, uF, uV} ℂ (GeneralLinear (N + 1 - l) F.Carrier))
      (Φ : A.representation.IntertwiningMap
        ((mirabolicDerivativeOfOrderRightAdjoint.{uV} T ψ N l hl).obj θ).representation),
      Φ ≠ 0 → Nontrivial ((mirabolicDerivativeOfOrder T ψ N l hl).obj A) := by
  let := T.topology
  intro A θ Φ hΦ
  by_contra hn
  rw [not_nontrivial_iff_subsingleton] at hn
  apply hΦ
  apply (mirabolicDerivativeOfOrderAdjunction T ψ N l hl A θ).injective
  rw [map_zero]
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  rw [Subsingleton.elim x 0, map_zero, map_zero]

/-- The same conclusion, as `HasNonzeroDerivative`. -/
theorem hasNonzeroDerivative_of_ne_zero (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (N l : ℕ) (hl : 0 < l ∧ l ≤ N + 1) :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, uA} ℂ (mirabolic N F.Carrier))
      (θ : SmoothRep.{0, uF, uV} ℂ (GeneralLinear (N + 1 - l) F.Carrier))
      (Φ : A.representation.IntertwiningMap
        ((mirabolicDerivativeOfOrderRightAdjoint.{uV} T ψ N l hl).obj θ).representation),
      Φ ≠ 0 → HasNonzeroDerivative T ψ A l := by
  intro A θ Φ hΦ
  exact ⟨hl, nontrivial_mirabolicDerivativeOfOrder_of_ne_zero T ψ N l hl A θ Φ hΦ⟩

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

/-- Naturality of the unit: `Y(f^(l)) ∘ η_(A') = η_A ∘ f`. -/
theorem mirabolicDerivativeOfOrderUnit_naturality (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (N l : ℕ) (hl : 0 < l ∧ l ≤ N + 1) :
    letI := T.topology
    ∀ {A' A : SmoothRep.{0, uF, uV} ℂ (mirabolic N F.Carrier)} (f : A' ⟶ A),
      (SmoothRep.hom ((mirabolicDerivativeOfOrderRightAdjoint.{uV} T ψ N l hl).map
          ((mirabolicDerivativeOfOrder T ψ N l hl).map f))).comp
          (mirabolicDerivativeOfOrderUnit T ψ N l hl A') =
        (mirabolicDerivativeOfOrderUnit T ψ N l hl A).comp (SmoothRep.hom f) := by
  let := T.topology
  intro A' A f
  apply (mirabolicDerivativeOfOrderAdjunction T ψ N l hl A' _).injective
  rw [mirabolicDerivativeOfOrderAdjunction_comp_right, mirabolicDerivativeOfOrderAdjunction_unit,
    mirabolicDerivativeOfOrderAdjunction_unit_comp]
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

end Langlands.Derivative
