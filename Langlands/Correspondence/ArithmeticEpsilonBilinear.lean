import Langlands.Correspondence.ArithmeticEpsilonMonomial
import Langlands.Global.Factors.RelativeWeilLocalEpsilon

/-!
# The arithmetic pair epsilon factor as a bilinear map on exact K0

For a supplied local-constant system and additive character, the pair
`(c, m)` of the arithmetic epsilon factor `c q^(-ms)` of `A ⊗ B` is an integer-bilinear
function of the exact classes of the continuous Weil representations `A` and `B`. It
is the composite of the exact tensor product, restriction to the bottom field, change
of carrier universe, and the additive map `x ↦ (ε(x), m(x))` on bottom-field virtual
classes.
-/

noncomputable section

set_option autoImplicit false

universe uF uV uP

namespace Langlands.LocalFactor.SpectralConductor

open CommonClosure CommonClosureSpectral CommonClosureSpectralAnalytic ConductorExponent
open VirtualRepresentation NonabelianSystem

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

/-- The exponent of a monomial in `q^(-s)` with a fixed nonzero coefficient is unique. -/
theorem monomial_exponent_unique {a : ℂˣ} {m m' : ℤ}
    (h : ∀ s : ℂ, (a : ℂ) * RankinSelberg.spectralPoint
        F.canonicalTopologicalData.residueCardinality s ^ m =
      (a : ℂ) * RankinSelberg.spectralPoint
        F.canonicalTopologicalData.residueCardinality s ^ m') : m = m' := by
  have hq := F.canonicalTopologicalData.residueCardinality_gt_one
  have hU := Set.infinite_range_of_injective (RankinSelberg.spectralPoint_ofReal_injective hq)
  refine (RankinSelberg.unitMonomial_eq_of_infinite (c := a) (c' := a) hU ?_ ?_).2
  · rintro x ⟨t, rfl⟩
    exact RankinSelberg.spectralPoint_ne_zero hq _
  · rintro x ⟨t, rfl⟩
    exact h t

variable {e : ReciprocityFamily F} {ε : Assignment.{uF, uV} F} (hε : IsSystem F e ε)
  (ψ : AdditiveCharacter F (base F)) (μ : HaarMeasure F (base F))

/-- The integral exponent `m(x)` with `ε(x ω_s) = ε(x) (q^(-s))^m(x)`. -/
def monomialExponent (x : Virtual.{uF, uV} F (base F)) : ℤ :=
  (mem_monomialSubgroup hε ψ μ x).choose

theorem monomialExponent_spec (x : Virtual.{uF, uV} F (base F)) (s : ℂ) :
    (ε (base F) ψ μ (virtualTwist F (base F) s x) : ℂ) =
      ε (base F) ψ μ x *
        RankinSelberg.spectralPoint F.canonicalTopologicalData.residueCardinality s ^
          monomialExponent hε ψ μ x :=
  (mem_monomialSubgroup hε ψ μ x).choose_spec s

theorem monomialExponent_eq (x : Virtual.{uF, uV} F (base F)) {m : ℤ}
    (hm : ∀ s : ℂ, (ε (base F) ψ μ (virtualTwist F (base F) s x) : ℂ) =
      ε (base F) ψ μ x *
        RankinSelberg.spectralPoint F.canonicalTopologicalData.residueCardinality s ^ m) :
    monomialExponent hε ψ μ x = m :=
  monomial_exponent_unique fun s => (monomialExponent_spec hε ψ μ x s).symm.trans (hm s)

/-- The additive map `x ↦ (ε(x), m(x))` on bottom-field virtual classes. -/
def monomialCoefficient : Virtual.{uF, uV} F (base F) →+ Additive ℂˣ × ℤ where
  toFun x := (Additive.ofMul (ε (base F) ψ μ x), monomialExponent hε ψ μ x)
  map_zero' := by
    refine Prod.ext ?_ ?_
    · change Additive.ofMul (ε (base F) ψ μ 0) = 0
      rw [value_zero hε.2.1]
      rfl
    · exact monomialExponent_eq hε ψ μ 0 fun s => by simp [value_zero hε.2.1]
  map_add' x y := by
    refine Prod.ext ?_ ?_
    · change Additive.ofMul (ε (base F) ψ μ (x + y)) =
        Additive.ofMul (ε (base F) ψ μ x) + Additive.ofMul (ε (base F) ψ μ y)
      rw [hε.2.1]
      rfl
    · change monomialExponent hε ψ μ (x + y) =
        monomialExponent hε ψ μ x + monomialExponent hε ψ μ y
      have hq : 0 < F.canonicalTopologicalData.residueCardinality :=
        zero_lt_one.trans F.canonicalTopologicalData.residueCardinality_gt_one
      refine monomialExponent_eq hε ψ μ (x + y) fun s => ?_
      rw [map_add, hε.2.1, hε.2.1, Units.val_mul, Units.val_mul, monomialExponent_spec hε,
        monomialExponent_spec hε, zpow_add₀ (RankinSelberg.spectralPoint_ne_zero_of_pos hq s)]
      ring

end Langlands.LocalFactor.SpectralConductor

namespace Langlands.Correspondence

open LocalFactor LocalFactor.CommonClosure LocalFactor.CommonClosureWeilDeligne
open LocalFactor.CommonClosureSpectral Weil.Local VirtualRepresentation

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance arithmeticEpsilonBilinearTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology

/-- The inclusion of the bottom Weil subgroup, as a continuous homomorphism. -/
def baseSubgroupHom : weilSubgroup F (baseExtension F) →ₜ* localWeilGroup F where
  toMonoidHom := (weilSubgroup F (baseExtension F)).subtype
  continuous_toFun := continuous_subtype_val

variable (eC : ReciprocityFamily F) (ε : NonabelianSystem.Assignment.{uF, uV} F)
  (hε : NonabelianSystem.IsSystem F eC ε) (ψ : NontrivialAdditiveCharacter F)

/-- The arithmetic pair epsilon factor `(c, m)` on the exact Grothendieck group of
continuous Weil representations, as an integer-bilinear map. -/
def pairEpsilonHom :
    LocalWeil.ContinuousExactGroup.{uF, uP} F →ₗ[ℤ]
      LocalWeil.ContinuousExactGroup.{uF, uP} F →ₗ[ℤ] Additive ℂˣ × ℤ :=
  ExactGrothendieckGroup.continuousTensor.compr₂
    ((SpectralConductor.monomialCoefficient hε (baseFieldAdditiveCharacterEquiv F ψ)
        (baseSelfDualMeasure F ψ)).toIntLinearMap ∘ₗ
      (ExactGrothendieckGroup.continuousTransport ∘ₗ
        ExactGrothendieckGroup.continuousRestrict (baseSubgroupHom F)))

/-- On actual representations, the bilinear epsilon map evaluates the bottom-field
class of the tensor product. -/
theorem pairEpsilonHom_ofRepresentation
    (A B : {A : LocalWeilRepresentation.{uF, uP} F // A.IsContinuous}) :
    pairEpsilonHom F eC ε hε ψ (ExactGrothendieckGroup.ofRepresentation _ A)
        (ExactGrothendieckGroup.ofRepresentation _ B) =
      SpectralConductor.monomialCoefficient hε (baseFieldAdditiveCharacterEquiv F ψ)
        (baseSelfDualMeasure F ψ) (baseTensorClass F A.val B.val A.property B.property) := by
  rw [pairEpsilonHom, LinearMap.compr₂_apply]
  erw [ExactGrothendieckGroup.continuousTensor_ofRepresentation]
  simp only [LinearMap.comp_apply, AddMonoidHom.coe_toIntLinearMap]
  congr 1
  unfold ExactGrothendieckGroup.continuousRestrict
  rw [ExactGrothendieckGroup.restrict_ofRepresentation]
  apply ExactGrothendieckGroup.continuousTransport_ofRepresentation_of_equiv
  let A₁ := FiniteRepresentation.restrict (weilSubgroup F (baseExtension F)).subtype A.val
  let B₁ := FiniteRepresentation.restrict (weilSubgroup F (baseExtension F)).subtype B.val
  let r : FiniteRepresentation.Equiv
      (FiniteRepresentation.restrict (weilSubgroup F (baseExtension F)).subtype
        (FiniteRepresentation.tensor A.val B.val))
      (FiniteRepresentation.tensor A₁ B₁) :=
    Representation.Equiv.mk (LinearEquiv.refl ℂ _) fun _ => rfl
  let t : FiniteRepresentation.Equiv (FiniteRepresentation.tensor A₁ B₁)
      (FiniteRepresentation.tensor
        (FiniteRepresentation.transport A₁ : FiniteRepresentation.{0, uF, max uF uV} ℂ _)
        (FiniteRepresentation.transport B₁ : FiniteRepresentation.{0, uF, max uF uV} ℂ _)) :=
    FiniteRepresentation.tensorEquivOfEquiv (FiniteRepresentation.coordinatesEquiv A₁).symm
      (FiniteRepresentation.coordinatesEquiv B₁).symm
  exact r.trans t

/-- The value of the bilinear epsilon map on two continuous representations is an
arithmetic pair epsilon certificate of their zero-monodromy pairs. -/
theorem isArithmeticPairEpsilonFactor_pairEpsilonHom
    (A B : {A : LocalWeilRepresentation.{uF, uP} F // A.IsContinuous}) :
    IsArithmeticPairEpsilonFactor F eC ε hε ψ
      (WeilDeligneRepresentation.classOf
        (WeilDeligneRepresentation.zeroMonodromy (localNormCharacter F).toMonoidHom A.val))
      (WeilDeligneRepresentation.classOf
        (WeilDeligneRepresentation.zeroMonodromy (localNormCharacter F).toMonoidHom B.val))
      (Additive.toMul (pairEpsilonHom F eC ε hε ψ (ExactGrothendieckGroup.ofRepresentation _ A)
        (ExactGrothendieckGroup.ofRepresentation _ B)).1)
      (pairEpsilonHom F eC ε hε ψ (ExactGrothendieckGroup.ofRepresentation _ A)
        (ExactGrothendieckGroup.ofRepresentation _ B)).2 := by
  rw [pairEpsilonHom_ofRepresentation]
  exact isArithmeticPairEpsilonFactor_of_monomial F eC ε hε ψ A.val B.val A.property B.property _
    (SpectralConductor.monomialExponent_spec hε _ _ _)

end Langlands.Correspondence
