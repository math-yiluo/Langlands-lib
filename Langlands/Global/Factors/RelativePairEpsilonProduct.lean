import Langlands.Global.Factors.RelativePairEpsilonReduction
import Langlands.Global.Factors.RelativePairLFactorProduct
import Langlands.Representation.RankinSelberg.LanglandsFactors

/-!
# Virtual pair epsilon factors of normalized inductions of unitary supercuspidal blocks

The epsilon factor of a pair through square-integrable Langlands data
(`IsLanglandsPairEpsilonFactor`) is the product of the JPSS epsilon factors of all
block pairs (Henniart 2002, 2.8). A normalized product induction of unitarizable
supercuspidal blocks is such a datum, with all exponents zero. So for irreducible
representations equivalent to these inductions, with unitary lattice supports `x`
and `y`, the classification epsilon factor of the pair is the virtual epsilon factor of
`x` and `y`.
-/

noncomputable section

set_option autoImplicit false

universe uF uV

namespace Langlands.VirtualRepresentation.PadicSupercuspidal

open Langlands.RankinSelberg CategoryTheory

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

private local instance relativePairEpsilonProductTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology

variable {ψ : Correspondence.NontrivialAdditiveCharacter F}
  {ν : Correspondence.LocalAdditiveHaarMeasure F}

/-- A rank-indexed JPSS epsilon certificate of two unitarizable supercuspidal objects is
the basis pair epsilon certificate of their classes. -/
theorem isUnitaryBasisPairEpsilonFactor_blockBasisClass {n t : ℕ} (hn : 0 < n) (ht : 0 < t)
    (A : GeneralLinear.SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := n))
    (B : GeneralLinear.SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := t))
    (hA : IsUnitarizable A.obj.representation) (hB : IsUnitarizable B.obj.representation)
    {e : ℂˣ × ℤ}
    (he : IsPadicRankEpsilonFactor F ψ ν A.obj.representation B.obj.representation e) :
    IsUnitaryBasisPairEpsilonFactor F ψ ν (blockBasisClass F hn A hA)
      (blockBasisClass F ht B hB) e := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero ht.ne'
  exact he

variable (F)

/-- The square-integrable Langlands datum of a normalized product induction of
unitarizable supercuspidal blocks: the blocks themselves, all with exponent zero. -/
def unitarySupercuspidalDatum {n : ℕ} (B : GeneralLinear.BlockShape n)
    (σ : ∀ i, GeneralLinear.SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := B.size i))
    (hσ : ∀ i, IsUnitarizable (σ i).obj.representation) :
    PadicField.TopologicalData.SquareIntegrableLanglandsDatum.{uV, uF}
      F.canonicalTopologicalData n where
  shape := B
  blocks i := (σ i).obj
  irreducible i := (σ i).property.1
  essentiallySquareIntegrable i :=
    (Classification.unitarizableSupercuspidal_isSquareIntegrable F (B.positive i) (σ i)
      (hσ i)).isEssentiallySquareIntegrable
  unitaryExponent i :=
    { exponent := 0
      form := by
        rw [neg_zero, realPowerTwist_zero]
        exact (hσ i).some }
  antitone := fun _ _ _ => le_rfl

variable {F}

/-- An irreducible representation equivalent to the normalized product induction of
the blocks is a Langlands quotient of this datum. -/
theorem isLanglandsQuotient_unitarySupercuspidalDatum {n : ℕ}
    (πL : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier))
    (hπL : πL.IsIrreducible) (B : GeneralLinear.BlockShape n)
    (σ : ∀ i, GeneralLinear.SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := B.size i))
    (hσ : ∀ i, IsUnitarizable (σ i).obj.representation)
    (e : πL.representation.Equiv (F.canonicalTopologicalData.normalizedProductInduced B
      fun i => (σ i).obj.representation)) :
    (unitarySupercuspidalDatum F B σ hσ).IsLanglandsQuotient πL :=
  ⟨hπL, e.symm.toIntertwiningMap, e.symm.toLinearEquiv.surjective⟩

variable (ψ ν)

/-- For irreducible representations equivalent to normalized product inductions of
unitarizable supercuspidal blocks, with unitary lattice supports `x` and `y`, every
classification epsilon factor of the pair is the virtual epsilon factor of `x` and
`y` (self-dual measure). -/
theorem isUnitaryPairEpsilonFactor_of_isLanglandsPairEpsilonFactor
    (hν : Correspondence.IsSelfDualMeasure F ψ ν) {r t : ℕ}
    (πL : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (r + 1) F.Carrier))
    (πL' : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (t + 1) F.Carrier))
    (hπL : πL.IsIrreducible) (hπL' : πL'.IsIrreducible)
    {x y : UnitaryLattice.{uF, uV} F}
    (hx : IsUnitaryLatticeSupport F πL x) (hy : IsUnitaryLatticeSupport F πL' y)
    (B : GeneralLinear.BlockShape (r + 1))
    (σ : ∀ i, GeneralLinear.SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := B.size i))
    (hσ : ∀ i, IsUnitarizable (σ i).obj.representation)
    (e : πL.representation.Equiv (F.canonicalTopologicalData.normalizedProductInduced B
      fun i => (σ i).obj.representation))
    (C : GeneralLinear.BlockShape (t + 1))
    (τ : ∀ j, GeneralLinear.SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := C.size j))
    (hτ : ∀ j, IsUnitarizable (τ j).obj.representation)
    (e' : πL'.representation.Equiv (F.canonicalTopologicalData.normalizedProductInduced C
      fun j => (τ j).obj.representation))
    {ε₀ : ℂˣ × ℤ} (hε₀ : IsLanglandsPairEpsilonFactor.{uF, uV, uV} F ψ ν πL πL' ε₀) :
    IsUnitaryPairEpsilonFactor F ψ ν x y ε₀ := by
  obtain ⟨b, hb, rfl⟩ := hε₀.2.2 _ _
    (isLanglandsQuotient_unitarySupercuspidalDatum πL hπL B σ hσ e)
    (isLanglandsQuotient_unitarySupercuspidalDatum πL' hπL' C τ hτ e')
  rw [eq_sum_blockBasisClass_of_equiv_productInduced πL hπL hx B σ hσ e,
    eq_sum_blockBasisClass_of_equiv_productInduced πL' hπL' hy C τ hτ e',
    isUnitaryPairEpsilonFactor_iff F ψ ν hν]
  have hbb : ∀ i j, unitaryBasisPairEpsilon F ψ ν hν (blockBasisClass F (B.positive i) (σ i) (hσ i))
      (blockBasisClass F (C.positive j) (τ j) (hτ j)) = b i j := fun i j =>
    ((exists_isUnitaryBasisPairEpsilonFactor F ψ ν hν _ _).choose_spec.unique
      (isUnitaryBasisPairEpsilonFactor_blockBasisClass (B.positive i) (C.positive j)
        (σ i) (τ j) (hσ i) (hτ j) (hb i j)))
  simp only [map_sum, LinearMap.sum_apply, epsilonHom_generator]
  refine Prod.ext ?_ ?_
  · simp only [epsilonPair, Prod.fst_sum, toMul_sum, toMul_ofMul, epsilonFactorProduct]
    rw [Finset.prod_comm]
    exact Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ =>
      (congrArg Prod.fst (hbb j i)).symm
  · simp only [epsilonPair, Prod.snd_sum, epsilonFactorProduct]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      (congrArg Prod.snd (hbb j i)).symm

end Langlands.VirtualRepresentation.PadicSupercuspidal
