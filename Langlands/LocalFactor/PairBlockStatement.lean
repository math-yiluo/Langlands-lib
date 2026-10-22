import Langlands.LocalFactor.CommonClosureGamma
import Langlands.WeilDeligne.SpecialBlocks
import Langlands.WeilDeligne.Twist
import Langlands.VirtualRepresentation.ExactTensor
import Langlands.VirtualRepresentation.ExactTwist

/-!
# Epsilon and gamma laws for sums, pairs and special blocks

Henniart's §§2.1–2.4 factor laws for the conditional common-closure epsilon and
gamma values of a supplied local-constant system, together with the unramified
twist law. Gamma is compared only at points regular for every factor involved.
These are propositions; no system is constructed or chosen.
-/

noncomputable section

universe uF uV

namespace Langlands.LocalFactor.PairBlock

open CommonClosure CommonClosureSpectral CommonClosureWeilDeligne CommonClosureGamma
open VirtualRepresentation

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

section Continuity

/-- The binary direct sum of continuous pairs is continuous. -/
theorem sum_isContinuous (E : Extension F) (A B : Pair.{uF, uV} F E)
    (hA : A.toFiniteRepresentation.IsContinuous) (hB : B.toFiniteRepresentation.IsContinuous) :
    (WeilDeligneRepresentation.sum A B).toFiniteRepresentation.IsContinuous :=
  Weil.OperationClosure.continuous_prod A.representation B.representation hA hB

/-- Twisting a continuous pair by a continuous character keeps it continuous. -/
theorem twist_isContinuous (E : Extension F) (χ : weilSubgroup F E →ₜ* ℂˣ)
    (A : Pair.{uF, uV} F E) (hA : A.toFiniteRepresentation.IsContinuous) :
    (WeilDeligneRepresentation.twist χ.toMonoidHom A).toFiniteRepresentation.IsContinuous :=
  FiniteRepresentation.isContinuous_twist χ hA

/-- The uncentered special block for the actual norm character is continuous. -/
theorem specialBlock_isContinuous (E : Extension F) (m : ℕ) :
    (WeilDeligneRepresentation.specialBlock (normCharacter F E).toMonoidHom m).toFiniteRepresentation.IsContinuous := by
  let _ : TopologicalSpace (Module.End ℂ (Fin m → ℂ)) := moduleTopology ℂ _
  have : IsModuleTopology ℂ (Module.End ℂ (Fin m → ℂ)) := ⟨rfl⟩
  have := IsModuleTopology.toContinuousAdd ℂ (Module.End ℂ (Fin m → ℂ))
  let L : (Fin m → ℂ) →ₗ[ℂ] Module.End ℂ (Fin m → ℂ) :=
    { toFun := fun c => LinearMap.pi fun j => c j • LinearMap.proj j
      map_add' := fun c d => by ext v j; simp [add_mul]
      map_smul' := fun a c => by ext v j; simp [mul_assoc] }
  have hL : Continuous L := IsModuleTopology.continuous_of_linearMap L
  have hc : Continuous fun g : weilSubgroup F E =>
      fun j : Fin m => ((normCharacter F E g : ℂˣ) : ℂ) ^ j.val := by
    apply continuous_pi
    intro j
    exact (Units.continuous_val.comp (normCharacter F E).continuous).pow _
  exact hL.comp hc

/-- A block built from a continuous Weil factor is continuous. -/
theorem block_isContinuous (E : Extension F)
    (ρ : FiniteRepresentation.{0, uF, max uF uV} ℂ (weilSubgroup F E)) (hρ : ρ.IsContinuous)
    (m : ℕ) :
    (WeilDeligneRepresentation.block (normCharacter F E).toMonoidHom ρ m).toFiniteRepresentation.IsContinuous :=
  FiniteRepresentation.isContinuous_tensor hρ (specialBlock_isContinuous F E m)

end Continuity

/-- The zero-monodromy pair `ν^k ⊗ ρ`, for the actual norm character `ν`. -/
def twistedFactor (E : Extension F)
    (ρ : FiniteRepresentation.{0, uF, max uF uV} ℂ (weilSubgroup F E)) (k : ℕ) :
    Pair.{uF, uV} F E :=
  WeilDeligneRepresentation.zeroMonodromy (normCharacter F E).toMonoidHom
    (FiniteRepresentation.twist ((normCharacter F E) ^ k).toMonoidHom ρ)

theorem twistedFactor_isContinuous (E : Extension F)
    (ρ : FiniteRepresentation.{0, uF, max uF uV} ℂ (weilSubgroup F E)) (hρ : ρ.IsContinuous)
    (k : ℕ) : (twistedFactor F E ρ k).toFiniteRepresentation.IsContinuous :=
  FiniteRepresentation.isContinuous_twist _ hρ

/-- Henniart 2.1: epsilon is multiplicative on direct sums of pairs. -/
def EpsilonDirectSum : Prop :=
  ∀ (e : ReciprocityFamily F) (ε : NonabelianSystem.Assignment.{uF, uV} F)
    (hε : NonabelianSystem.IsSystem F e ε) (E : Extension F)
    (ψ : AdditiveCharacter F E) (μ : HaarMeasure F E)
    (A B : Pair.{uF, uV} F E)
    (hA : A.toFiniteRepresentation.IsContinuous) (hB : B.toFiniteRepresentation.IsContinuous)
    (Φ : GeometricFrobenius F E) (s : ℂ),
    conditionalEpsilonValue F e ε hε E ψ μ (WeilDeligneRepresentation.sum A B)
        (sum_isContinuous F E A B hA hB) Φ s =
      conditionalEpsilonValue F e ε hε E ψ μ A hA Φ s *
        conditionalEpsilonValue F e ε hε E ψ μ B hB Φ s

/-- Henniart 2.1: gamma is multiplicative on direct sums, at a common regular point. -/
def GammaDirectSum : Prop :=
  ∀ (e : ReciprocityFamily F) (ε : NonabelianSystem.Assignment.{uF, uV} F)
    (hε : NonabelianSystem.IsSystem F e ε) (E : Extension F)
    (ψ : AdditiveCharacter F E) (μ : HaarMeasure F E)
    (A B : Pair.{uF, uV} F E)
    (hA : A.toFiniteRepresentation.IsContinuous) (hB : B.toFiniteRepresentation.IsContinuous)
    (Φ : GeometricFrobenius F E)
    (s : CommonClosureGamma.RegularPoint F E (WeilDeligneRepresentation.sum A B) Φ)
    (sA : CommonClosureGamma.RegularPoint F E A Φ) (sB : CommonClosureGamma.RegularPoint F E B Φ),
    sA.val = s.val → sB.val = s.val →
    conditionalGammaValue F e ε hε E ψ μ (WeilDeligneRepresentation.sum A B)
        (sum_isContinuous F E A B hA hB) Φ s =
      conditionalGammaValue F e ε hε E ψ μ A hA Φ sA *
        conditionalGammaValue F e ε hε E ψ μ B hB Φ sB

/-- Henniart 2.1: gamma alone is multiplicative on every short exact sequence
`0 → A → C → B → 0` of pairs, whose maps commute with monodromy. -/
def GammaShortExact : Prop :=
  ∀ (e : ReciprocityFamily F) (ε : NonabelianSystem.Assignment.{uF, uV} F)
    (hε : NonabelianSystem.IsSystem F e ε) (E : Extension F)
    (ψ : AdditiveCharacter F E) (μ : HaarMeasure F E)
    (A B C : Pair.{uF, uV} F E)
    (hA : A.toFiniteRepresentation.IsContinuous) (hB : B.toFiniteRepresentation.IsContinuous)
    (hC : C.toFiniteRepresentation.IsContinuous)
    (f : WeilDeligneRepresentation.Hom A C) (g : WeilDeligneRepresentation.Hom C B),
    FiniteRepresentation.IsShortExact f.intertwiner g.intertwiner →
    ∀ (Φ : GeometricFrobenius F E) (s : CommonClosureGamma.RegularPoint F E C Φ)
      (sA : CommonClosureGamma.RegularPoint F E A Φ) (sB : CommonClosureGamma.RegularPoint F E B Φ),
      sA.val = s.val → sB.val = s.val →
      conditionalGammaValue F e ε hε E ψ μ C hC Φ s =
        conditionalGammaValue F e ε hε E ψ μ A hA Φ sA *
          conditionalGammaValue F e ε hε E ψ μ B hB Φ sB

/-- Henniart 2.2: pair epsilon and pair gamma distribute over a direct sum in
either tensor leg. -/
def PairDistributivity : Prop :=
  ∀ (e : ReciprocityFamily F) (ε : NonabelianSystem.Assignment.{uF, uV} F)
    (hε : NonabelianSystem.IsSystem F e ε) (E : Extension F)
    (ψ : AdditiveCharacter F E) (μ : HaarMeasure F E)
    (A A' B : Pair.{uF, uV} F E)
    (hA : A.toFiniteRepresentation.IsContinuous) (hA' : A'.toFiniteRepresentation.IsContinuous)
    (hB : B.toFiniteRepresentation.IsContinuous) (Φ : GeometricFrobenius F E),
    (∀ s : ℂ,
      conditionalPairEpsilonValue F e ε hε E ψ μ (WeilDeligneRepresentation.sum A A') B
          (sum_isContinuous F E A A' hA hA') hB Φ s =
        conditionalPairEpsilonValue F e ε hε E ψ μ A B hA hB Φ s *
          conditionalPairEpsilonValue F e ε hε E ψ μ A' B hA' hB Φ s) ∧
    (∀ s : ℂ,
      conditionalPairEpsilonValue F e ε hε E ψ μ B (WeilDeligneRepresentation.sum A A')
          hB (sum_isContinuous F E A A' hA hA') Φ s =
        conditionalPairEpsilonValue F e ε hε E ψ μ B A hB hA Φ s *
          conditionalPairEpsilonValue F e ε hε E ψ μ B A' hB hA' Φ s) ∧
    (∀ (s : CommonClosureGamma.RegularPoint F E
        (WeilDeligneRepresentation.tensor (WeilDeligneRepresentation.sum A A') B) Φ)
      (s₁ : CommonClosureGamma.RegularPoint F E (WeilDeligneRepresentation.tensor A B) Φ)
      (s₂ : CommonClosureGamma.RegularPoint F E (WeilDeligneRepresentation.tensor A' B) Φ),
      s₁.val = s.val → s₂.val = s.val →
      conditionalPairGammaValue F e ε hε E ψ μ (WeilDeligneRepresentation.sum A A') B
          (sum_isContinuous F E A A' hA hA') hB Φ s =
        conditionalPairGammaValue F e ε hε E ψ μ A B hA hB Φ s₁ *
          conditionalPairGammaValue F e ε hε E ψ μ A' B hA' hB Φ s₂) ∧
    (∀ (s : CommonClosureGamma.RegularPoint F E
        (WeilDeligneRepresentation.tensor B (WeilDeligneRepresentation.sum A A')) Φ)
      (s₁ : CommonClosureGamma.RegularPoint F E (WeilDeligneRepresentation.tensor B A) Φ)
      (s₂ : CommonClosureGamma.RegularPoint F E (WeilDeligneRepresentation.tensor B A') Φ),
      s₁.val = s.val → s₂.val = s.val →
      conditionalPairGammaValue F e ε hε E ψ μ B (WeilDeligneRepresentation.sum A A')
          hB (sum_isContinuous F E A A' hA hA') Φ s =
        conditionalPairGammaValue F e ε hε E ψ μ B A hB hA Φ s₁ *
          conditionalPairGammaValue F e ε hε E ψ μ B A' hB hA' Φ s₂)

/-- Henniart 2.3–2.4 for one block: gamma of `ρ ⊗ S_(n+1)` is the product of
the gamma factors of `ν^i ⊗ ρ`, `0 ≤ i ≤ n`. -/
def BlockGamma : Prop :=
  ∀ (e : ReciprocityFamily F) (ε : NonabelianSystem.Assignment.{uF, uV} F)
    (hε : NonabelianSystem.IsSystem F e ε) (E : Extension F)
    (ψ : AdditiveCharacter F E) (μ : HaarMeasure F E)
    (ρ : FiniteRepresentation.{0, uF, max uF uV} ℂ (weilSubgroup F E)) (hρ : ρ.IsContinuous)
    (n : ℕ) (Φ : GeometricFrobenius F E)
    (s : CommonClosureGamma.RegularPoint F E
      (WeilDeligneRepresentation.block (normCharacter F E).toMonoidHom ρ (n + 1)) Φ)
    (t : (i : Fin (n + 1)) → CommonClosureGamma.RegularPoint F E (twistedFactor F E ρ i.val) Φ),
    (∀ i, (t i).val = s.val) →
    conditionalGammaValue F e ε hε E ψ μ
        (WeilDeligneRepresentation.block (normCharacter F E).toMonoidHom ρ (n + 1))
        (block_isContinuous F E ρ hρ (n + 1)) Φ s =
      ∏ i : Fin (n + 1),
        conditionalGammaValue F e ε hε E ψ μ (twistedFactor F E ρ i.val)
          (twistedFactor_isContinuous F E ρ hρ i.val) Φ (t i)

/-- Henniart 2.4: gamma of the pair `(ρ ⊗ S_(n+1)) ⊗ (ρ' ⊗ S_(m+1))` is the product
of the gamma factors of `ν^(i+j) ⊗ ρ ⊗ ρ'`, `0 ≤ i ≤ n`, `0 ≤ j ≤ m`. -/
def BlockPairGamma : Prop :=
  ∀ (e : ReciprocityFamily F) (ε : NonabelianSystem.Assignment.{uF, uV} F)
    (hε : NonabelianSystem.IsSystem F e ε) (E : Extension F)
    (ψ : AdditiveCharacter F E) (μ : HaarMeasure F E)
    (ρ ρ' : FiniteRepresentation.{0, uF, max uF uV} ℂ (weilSubgroup F E))
    (hρ : ρ.IsContinuous) (hρ' : ρ'.IsContinuous)
    (n m : ℕ) (Φ : GeometricFrobenius F E)
    (s : CommonClosureGamma.RegularPoint F E
      (WeilDeligneRepresentation.tensor
        (WeilDeligneRepresentation.block (normCharacter F E).toMonoidHom ρ (n + 1))
        (WeilDeligneRepresentation.block (normCharacter F E).toMonoidHom ρ' (m + 1))) Φ)
    (t : (i : Fin (n + 1)) → (j : Fin (m + 1)) → CommonClosureGamma.RegularPoint F E
      (twistedFactor F E (FiniteRepresentation.tensor ρ ρ') (i.val + j.val)) Φ),
    (∀ i j, (t i j).val = s.val) →
    conditionalPairGammaValue F e ε hε E ψ μ
        (WeilDeligneRepresentation.block (normCharacter F E).toMonoidHom ρ (n + 1))
        (WeilDeligneRepresentation.block (normCharacter F E).toMonoidHom ρ' (m + 1))
        (block_isContinuous F E ρ hρ (n + 1)) (block_isContinuous F E ρ' hρ' (m + 1)) Φ s =
      ∏ i : Fin (n + 1), ∏ j : Fin (m + 1),
        conditionalGammaValue F e ε hε E ψ μ
          (twistedFactor F E (FiniteRepresentation.tensor ρ ρ') (i.val + j.val))
          (twistedFactor_isContinuous F E (FiniteRepresentation.tensor ρ ρ')
            (FiniteRepresentation.isContinuous_tensor hρ hρ') (i.val + j.val)) Φ (t i j)

/-- An unramified continuous character with value `q_E^(-t)` at the supplied
geometric Frobenius. Every complex value arises for some complex `t`. -/
def IsUnramifiedTwist (E : Extension F) (ω : weilSubgroup F E →ₜ* ℂˣ)
    (Φ : GeometricFrobenius F E) (t : ℂ) : Prop :=
  (∀ w ∈ inertia F E, ω w = 1) ∧
    ω Φ.val = spectralParameter (residueCardinality F E) (residueCardinality_pos F E) t

/-- Unramified twisting shifts the spectral variable (Tate's `V ⊗ ω_s` convention,
3.4.5 and 4.1.6): a twist with value `q_E^(-t)` at Frobenius shifts `s` by `t`, for
classes, class pairs (either leg), pairs, tensor pairs, L-values and gamma values. -/
def UnramifiedTwist : Prop :=
  ∀ (e : ReciprocityFamily F) (ε : NonabelianSystem.Assignment.{uF, uV} F)
    (hε : NonabelianSystem.IsSystem F e ε) (E : Extension F)
    (ψ : AdditiveCharacter F E) (μ : HaarMeasure F E)
    (ω : weilSubgroup F E →ₜ* ℂˣ) (Φ : GeometricFrobenius F E) (t : ℂ),
    IsUnramifiedTwist F E ω Φ t →
    (∀ (x : Virtual.{uF, uV} F E) (s : ℂ),
      conditionalDeligneValue F e ε hε E ψ μ
          (ExactGrothendieckGroup.continuousTwist ω x) s =
        conditionalDeligneValue F e ε hε E ψ μ x (s + t)) ∧
    (∀ (x y : Virtual.{uF, uV} F E) (s : ℂ),
      conditionalDeligneValue F e ε hε E ψ μ
          (ExactGrothendieckGroup.continuousTensorSame
            (ExactGrothendieckGroup.continuousTwist ω x) y) s =
        conditionalDeligneValue F e ε hε E ψ μ
          (ExactGrothendieckGroup.continuousTensorSame x y) (s + t)) ∧
    (∀ (x y : Virtual.{uF, uV} F E) (s : ℂ),
      conditionalDeligneValue F e ε hε E ψ μ
          (ExactGrothendieckGroup.continuousTensorSame x
            (ExactGrothendieckGroup.continuousTwist ω y)) s =
        conditionalDeligneValue F e ε hε E ψ μ
          (ExactGrothendieckGroup.continuousTensorSame x y) (s + t)) ∧
    (∀ (A : Pair.{uF, uV} F E) (hA : A.toFiniteRepresentation.IsContinuous) (s : ℂ),
      conditionalEpsilonValue F e ε hε E ψ μ (WeilDeligneRepresentation.twist ω.toMonoidHom A)
          (twist_isContinuous F E ω A hA) Φ s =
        conditionalEpsilonValue F e ε hε E ψ μ A hA Φ (s + t)) ∧
    (∀ (A B : Pair.{uF, uV} F E) (hA : A.toFiniteRepresentation.IsContinuous)
      (hB : B.toFiniteRepresentation.IsContinuous) (s : ℂ),
      conditionalPairEpsilonValue F e ε hε E ψ μ
          (WeilDeligneRepresentation.twist ω.toMonoidHom A) B
          (twist_isContinuous F E ω A hA) hB Φ s =
        conditionalPairEpsilonValue F e ε hε E ψ μ A B hA hB Φ (s + t)) ∧
    (∀ (A : Pair.{uF, uV} F E)
      (s : CommonClosureWeilDeligne.SpectralRegularPoint F E (WeilDeligneRepresentation.twist ω.toMonoidHom A) Φ)
      (s' : CommonClosureWeilDeligne.SpectralRegularPoint F E A Φ), s'.val = s.val + t →
      CommonClosureWeilDeligne.spectralLValue F E (WeilDeligneRepresentation.twist ω.toMonoidHom A) Φ s =
        CommonClosureWeilDeligne.spectralLValue F E A Φ s') ∧
    (∀ (A : Pair.{uF, uV} F E) (hA : A.toFiniteRepresentation.IsContinuous)
      (s : CommonClosureGamma.RegularPoint F E (WeilDeligneRepresentation.twist ω.toMonoidHom A) Φ)
      (s' : CommonClosureGamma.RegularPoint F E A Φ), s'.val = s.val + t →
      conditionalGammaValue F e ε hε E ψ μ (WeilDeligneRepresentation.twist ω.toMonoidHom A)
          (twist_isContinuous F E ω A hA) Φ s =
        conditionalGammaValue F e ε hε E ψ μ A hA Φ s')

end Langlands.LocalFactor.PairBlock

namespace Langlands.LocalFactor

/-- Henniart 2002 §§2.1–2.4 and the unramified twist law, for every p-adic base
field and every supplied local-constant system on its common closure. -/
def PairBlockFactorStatement : Prop :=
  ∀ {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p),
    PairBlock.EpsilonDirectSum.{uF, uV} F ∧ PairBlock.GammaDirectSum.{uF, uV} F ∧
      PairBlock.GammaShortExact.{uF, uV} F ∧ PairBlock.PairDistributivity.{uF, uV} F ∧
      PairBlock.BlockGamma.{uF, uV} F ∧ PairBlock.BlockPairGamma.{uF, uV} F ∧
      PairBlock.UnramifiedTwist.{uF, uV} F

end Langlands.LocalFactor
