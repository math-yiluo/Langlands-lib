import Langlands.Global.Factors.RelativeIsometryFactorStatement
import Langlands.Global.Factors.RelativeWeilLocalEuler

/-!
# Virtual pair L-factors of unitary Weil classes through exact K0

The virtual pair L-factor `unitaryPairLFactor F x y` of two unitary virtual Weil
classes is defined from the basis classes by multiplicative bilinearity. It equals
the L-factor of the tensor product in the exact Grothendieck group of continuous
representations, evaluated at the canonical realizations of `x` and `y`. In
particular, if `x` and `y` expand the classes of actual continuous representations
`A` and `B`, it is the arithmetic pair L-factor of the zero-monodromy pairs of `A`
and `B`.
-/

noncomputable section

set_option autoImplicit false

universe uF uV

namespace Langlands.VirtualRepresentation

/-- The multiplicative form of an integer-bilinear map on integral lattices with
values in the additive group of a commutative group: its value is the
multiplicity-weighted product of its values on pairs of basis classes. -/
theorem toMul_bilinear_eq_prod {ι κ M : Type*} [CommGroup M]
    (Φ : IntegralLattice ι →ₗ[ℤ] IntegralLattice κ →ₗ[ℤ] Additive M)
    (x : IntegralLattice ι) (y : IntegralLattice κ) :
    Additive.toMul (Φ x y) = x.prod fun a m => y.prod fun b n =>
      Additive.toMul (Φ (generator a) (generator b)) ^ (m * n) := by
  have hx : x = x.sum fun a m => m • generator a := by
    simp [generator]
  have hy : y = y.sum fun b n => n • generator b := by
    simp [generator]
  have h1 : Φ x = x.sum fun a m => m • Φ (generator a) := by
    conv_lhs => rw [hx]
    rw [map_finsuppSum]
    simp only [map_zsmul]
  have h2 : ∀ a, Φ (generator a) y = y.sum fun b n => n • Φ (generator a) (generator b) := by
    intro a
    conv_lhs => rw [hy]
    rw [map_finsuppSum]
    simp only [map_zsmul]
  rw [h1, LinearMap.finsupp_sum_apply]
  simp only [LinearMap.smul_apply, h2, Finsupp.prod, Finsupp.sum, toMul_sum, toMul_zsmul]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [← Finset.prod_zpow]
  refine Finset.prod_congr rfl fun b _ => ?_
  rw [← zpow_mul, mul_comm]

end Langlands.VirtualRepresentation

namespace Langlands.VirtualRepresentation.LocalWeil

open Langlands.Weil.Local Langlands.Weil.Local.InertiaEuler
open Langlands.VirtualRepresentation.ExactGrothendieckGroup

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- The pair L-factor on the exact Grothendieck group of continuous representations
of `W_F`: the L-factor of the exact tensor product, as an integer-bilinear map with
values in the additive group of units of `ℂ(X)`. -/
def exactPairLFactorHom :
    ContinuousExactGroup.{uF, uV} F →ₗ[ℤ] ContinuousExactGroup.{uF, uV} F →ₗ[ℤ]
      Additive (RatFunc ℂ)ˣ :=
  continuousTensor.compr₂ (lFactorHom F)

/-- The canonical realization of a unitary virtual Weil class in exact K0. -/
def unitaryRealize : UnitaryLattice.{uF, uV} F →ₗ[ℤ] ContinuousExactGroup.{uF, uV} F :=
  (realizeExact F).comp (includeUnitary F)

/-- On two actual continuous representations, the exact pair L-factor is the
L-factor of their tensor product. -/
theorem exactPairLFactorHom_ofRepresentation
    (A B : {A : LocalWeilRepresentation.{uF, uV} F // A.IsContinuous}) :
    exactPairLFactorHom F (ExactGrothendieckGroup.ofRepresentation _ A) (ExactGrothendieckGroup.ofRepresentation _ B) =
      Additive.ofMul (lFactorUnit F (FiniteRepresentation.tensor A.val B.val)) := by
  rw [exactPairLFactorHom, LinearMap.compr₂_apply]
  erw [continuousTensor_ofRepresentation]
  exact lFactorHom_ofRepresentation F _

/-- On two actual continuous representations, the exact pair L-factor is the
arithmetic pair L-factor of their zero-monodromy pairs. -/
theorem coe_exactPairLFactorHom_ofRepresentation
    (A B : {A : LocalWeilRepresentation.{uF, uV} F // A.IsContinuous}) :
    ((Additive.toMul (exactPairLFactorHom F (ExactGrothendieckGroup.ofRepresentation _ A)
        (ExactGrothendieckGroup.ofRepresentation _ B)) : (RatFunc ℂ)ˣ) : RatFunc ℂ) =
      Correspondence.arithmeticPairLFactor F
        (WeilDeligneRepresentation.classOf
          (WeilDeligneRepresentation.zeroMonodromy (localNormCharacter F).toMonoidHom A.val))
        (WeilDeligneRepresentation.classOf
          (WeilDeligneRepresentation.zeroMonodromy (localNormCharacter F).toMonoidHom B.val)) := by
  rw [exactPairLFactorHom_ofRepresentation, toMul_ofMul,
    arithmeticPairLFactor_zeroMonodromy F A.val B.val _ (Representation.Equiv.refl _)]

/-- A unitary basis class is realized by an actual continuous representation whose
zero-monodromy pair class is the basis pair class. -/
theorem exists_unitaryRealize_generator (b : UnitaryBasis.{uF, uV} F) :
    ∃ A : {A : LocalWeilRepresentation.{uF, uV} F // A.IsContinuous},
      unitaryRealize F (generator b) = ExactGrothendieckGroup.ofRepresentation _ A ∧
        unitaryBasisPairClass F b = WeilDeligneRepresentation.classOf
          (WeilDeligneRepresentation.zeroMonodromy (localNormCharacter F).toMonoidHom A.val) := by
  obtain ⟨⟨n, ⟨c, hc⟩⟩, hu⟩ := b
  induction c using Quotient.inductionOn with
  | h A =>
    refine ⟨⟨A.val, A.property.1⟩, ?_, rfl⟩
    simp only [unitaryRealize, LinearMap.comp_apply, includeUnitary, Weil.includeUnitary,
      includeSubset, map, generator, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
    exact realizeExact_generator F _

/-- The arithmetic pair L-factor of two unitary basis classes is the exact pair
L-factor of their realizations. -/
theorem arithmeticPairLFactor_unitaryBasisPairClass (a b : UnitaryBasis.{uF, uV} F) :
    Correspondence.arithmeticPairLFactor F (unitaryBasisPairClass F a)
        (unitaryBasisPairClass F b) =
      ((Additive.toMul (exactPairLFactorHom F (unitaryRealize F (generator a))
        (unitaryRealize F (generator b))) : (RatFunc ℂ)ˣ) : RatFunc ℂ) := by
  obtain ⟨A, hA, hpA⟩ := exists_unitaryRealize_generator F a
  obtain ⟨B, hB, hpB⟩ := exists_unitaryRealize_generator F b
  rw [hA, hB, hpA, hpB, coe_exactPairLFactorHom_ofRepresentation]

/-- The virtual pair L-factor of unitary Weil classes is the exact pair L-factor of
their canonical realizations. -/
theorem unitaryPairLFactor_eq_exact (x y : UnitaryLattice.{uF, uV} F) :
    unitaryPairLFactor F x y =
      ((Additive.toMul (exactPairLFactorHom F (unitaryRealize F x) (unitaryRealize F y)) :
        (RatFunc ℂ)ˣ) : RatFunc ℂ) := by
  have h := toMul_bilinear_eq_prod
    ((exactPairLFactorHom F).compl₁₂ (unitaryRealize F) (unitaryRealize F)) x y
  simp only [LinearMap.compl₁₂_apply] at h
  rw [h, unitaryPairLFactor]
  simp only [Finsupp.prod, Units.coe_prod, Units.val_zpow_eq_zpow_val,
    arithmeticPairLFactor_unitaryBasisPairClass]

/-- If `x` and `y` expand the exact classes of actual continuous representations
`A` and `B`, the virtual pair L-factor of `x` and `y` is the arithmetic pair
L-factor of the zero-monodromy pairs of `A` and `B`. -/
theorem unitaryPairLFactor_eq_of_expansion (x y : UnitaryLattice.{uF, uV} F)
    (A B : {A : LocalWeilRepresentation.{uF, uV} F // A.IsContinuous})
    (hx : ExactExpansion F (ExactGrothendieckGroup.ofRepresentation _ A) (includeUnitary F x))
    (hy : ExactExpansion F (ExactGrothendieckGroup.ofRepresentation _ B) (includeUnitary F y)) :
    unitaryPairLFactor F x y =
      Correspondence.arithmeticPairLFactor F
        (WeilDeligneRepresentation.classOf
          (WeilDeligneRepresentation.zeroMonodromy (localNormCharacter F).toMonoidHom A.val))
        (WeilDeligneRepresentation.classOf
          (WeilDeligneRepresentation.zeroMonodromy (localNormCharacter F).toMonoidHom B.val)) := by
  rw [unitaryPairLFactor_eq_exact, ← coe_exactPairLFactorHom_ofRepresentation]
  change realizeExact F (includeUnitary F x) = _ at hx
  change realizeExact F (includeUnitary F y) = _ at hy
  change ((Additive.toMul (exactPairLFactorHom F (realizeExact F (includeUnitary F x))
    (realizeExact F (includeUnitary F y))) : (RatFunc ℂ)ˣ) : RatFunc ℂ) = _
  rw [hx, hy]

end Langlands.VirtualRepresentation.LocalWeil
