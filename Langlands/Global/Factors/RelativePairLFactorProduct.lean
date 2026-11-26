import Langlands.Global.Factors.RelativePairLFactorReduction
import Langlands.Representation.RankinSelberg.GroupedLFactorReduction
import Langlands.Representation.RankinSelberg.TemperedLFactorProof
import Langlands.Representation.Classification.UnitarySupercuspidalInductionTempered
import Langlands.Representation.Classification.SupercuspidalSupportUniquenessProof
import Langlands.VirtualRepresentation.Supercuspidal.UnitarySupport
import Langlands.Representation.RankinSelberg.SupercuspidalEqualRankLFactorProof
import Langlands.Representation.RankinSelberg.SupercuspidalUnequalRankLFactorReduction

/-!
# Virtual pair L-factors of normalized inductions of unitary supercuspidal blocks

For normalized product inductions of unitarizable supercuspidal blocks, the JPSS
pair L-polynomial is the product of the pair L-polynomials of the blocks (JPSS
(8.4), the published `temperedLFactor`). In the unitary supercuspidal lattice this
says: the virtual pair L-factor of the sums of the block classes is `1 / P(q^(-s))`
for the L-polynomial `P` of the two inductions.
-/

noncomputable section

set_option autoImplicit false

universe uF uV

open Polynomial

namespace Langlands.VirtualRepresentation.PadicSupercuspidal

open Langlands.RankinSelberg CategoryTheory

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

private local instance relativePairLFactorProductTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology

/-- The unitary basis class of a positive-rank unitarizable supercuspidal object. -/
def blockBasisClass {n : ℕ} (hn : 0 < n)
    (A : GeneralLinear.SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := n))
    (hA : IsUnitarizable A.obj.representation) :
    UnitaryBasis.{uF, uV} F :=
  Supercuspidal.unitaryBasisClass (F := F.Carrier) ⟨n, hn⟩ A hA

variable {F}
variable {ψ : Correspondence.NontrivialAdditiveCharacter F}
  {ν : Correspondence.LocalAdditiveHaarMeasure F}

/-- A rank-indexed JPSS L-polynomial of two unitarizable supercuspidal objects is the
basis pair L-polynomial of their classes. -/
theorem isUnitaryBasisPairLPolynomial_blockBasisClass {n t : ℕ} (hn : 0 < n) (ht : 0 < t)
    (A : GeneralLinear.SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := n))
    (B : GeneralLinear.SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := t))
    (hA : IsUnitarizable A.obj.representation)
    (hB : IsUnitarizable B.obj.representation) {Q : ℂ[X]}
    (hQ : IsPadicRankLPolynomial F ψ ν A.obj.representation B.obj.representation Q) :
    IsUnitaryBasisPairLPolynomial F ψ ν (blockBasisClass F hn A hA) (blockBasisClass F ht B hB) Q := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero ht.ne'
  exact hQ

variable (ψ ν)

/-- JPSS (8.4) in the unitary supercuspidal lattice: for a self-dual measure and
normalized product inductions of unitarizable supercuspidal blocks, the virtual pair
L-factor of the sums of the block classes is `1 / P(q^(-s))`, where `P` is the pair
L-polynomial of the two inductions. -/
theorem isUnitaryPairLFactor_productInduced (hν : Correspondence.IsSelfDualMeasure F ψ ν)
    {r t : ℕ} (B : GeneralLinear.BlockShape (r + 1)) (C : GeneralLinear.BlockShape (t + 1))
    (σ : ∀ i, GeneralLinear.SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := B.size i))
    (τ : ∀ j, GeneralLinear.SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := C.size j))
    (hσ : ∀ i, IsUnitarizable (σ i).obj.representation)
    (hτ : ∀ j, IsUnitarizable (τ j).obj.representation)
    {P : ℂ[X]}
    (hP : IsPadicSymmetricLPolynomial F ψ ν
      (F.canonicalNormalizedProductInduced B fun i => (σ i).obj.representation)
      (F.canonicalNormalizedProductInduced C fun j => (τ j).obj.representation) P) :
    IsUnitaryPairLFactor F ψ ν
      (∑ i, generator (blockBasisClass F (B.positive i) (σ i) (hσ i)))
      (∑ j, generator (blockBasisClass F (C.positive j) (τ j) (hτ j)))
      (algebraMap ℂ[X] (RatFunc ℂ) P)⁻¹ := by
  obtain ⟨P', Q, hP', hQ, hprod⟩ := TemperedLFactorStatement.blockShape F ψ ⟨ν, hν⟩
    temperedLFactor.{uF, uV, uV} B C (fun i => (σ i).obj.representation)
    (fun j => (τ j).obj.representation) (fun i => (σ i).property.1)
    (fun i => Classification.unitarizableSupercuspidal_isSquareIntegrable F
      (B.positive i) (σ i) (hσ i))
    (fun j => (τ j).property.1)
    (fun j => Classification.unitarizableSupercuspidal_isSquareIntegrable F
      (C.positive j) (τ j) (hτ j))
  have hPP : P = P' := hP.unique hP'
  rw [isUnitaryPairLFactor_iff F ψ ν hν]
  simp only [map_sum, LinearMap.sum_apply, unitaryPairLHom_generator,
    toMul_sum, toMul_ofMul, Units.coe_prod]
  rw [hPP, hprod]
  simp only [map_prod, ← Finset.prod_inv_distrib]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun j _ => Finset.prod_congr rfl fun i _ => ?_
  rw [coe_unitaryBasisPairLUnit
    (isUnitaryBasisPairLPolynomial_blockBasisClass (B.positive i) (C.positive j)
      (σ i) (τ j) (hσ i) (hτ j) (hQ i j))]

variable {ψ ν}

/-- The cuspidal datum of a positive-rank supercuspidal object. -/
def blockDatum {n : ℕ} (hn : 0 < n)
    (A : GeneralLinear.SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := n)) :
    PadicField.TopologicalData.CuspidalDatum.{uV, uF} F.canonicalTopologicalData :=
  ⟨n, hn, A.isoClass⟩

/-- An irreducible representation equivalent to the normalized product induction of
supercuspidal blocks has the multiset of the block data as supercuspidal support. -/
theorem isSupercuspidalSupport_of_equiv_productInduced {r : ℕ}
    (πL : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (r + 1) F.Carrier))
    (hπL : πL.IsIrreducible) (B : GeneralLinear.BlockShape (r + 1))
    (σ : ∀ i, GeneralLinear.SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := B.size i))
    (e : πL.representation.Equiv (F.canonicalTopologicalData.normalizedProductInduced B
      fun i => (σ i).obj.representation)) :
    F.canonicalTopologicalData.IsSupercuspidalSupport πL
      (List.ofFn fun i => blockDatum (B.positive i) (σ i)) := by
  refine ⟨B.length, fun i => blockDatum (B.positive i) (σ i), rfl, B.sum_eq, σ,
    fun i => rfl, hπL, ?_⟩
  refine SmoothRep.isSubquotient_iff_exists.mpr ⟨πL, (SmoothRep.mkIso e).hom, 𝟙 πL,
    SmoothRep.hom_hom_injective _, fun y => ⟨y, rfl⟩⟩

/-- If `x` is a unitary lattice support of an irreducible representation equivalent to
the normalized product induction of unitarizable supercuspidal blocks, then `x` is
the sum of the block classes. -/
theorem eq_sum_blockBasisClass_of_equiv_productInduced {r : ℕ}
    (πL : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (r + 1) F.Carrier))
    (hπL : πL.IsIrreducible) {x : UnitaryLattice.{uF, uV} F}
    (hx : IsUnitaryLatticeSupport F πL x) (B : GeneralLinear.BlockShape (r + 1))
    (σ : ∀ i, GeneralLinear.SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := B.size i))
    (hσ : ∀ i, IsUnitarizable (σ i).obj.representation)
    (e : πL.representation.Equiv (F.canonicalTopologicalData.normalizedProductInduced B
      fun i => (σ i).obj.representation)) :
    x = ∑ i, generator (blockBasisClass F (B.positive i) (σ i) (hσ i)) := by
  obtain ⟨s, hs, rfl⟩ := hx
  have hsupp := isSupercuspidalSupport_of_equiv_productInduced πL hπL B σ e
  have heq := glSupercuspidalSupportUniqueness.{uV, uF} p F
    F.canonicalTopologicalData (r + 1) r.succ_pos πL hπL _ _ hs hsupp
  apply Finsupp.mapDomain_injective Subtype.val_injective
  change Supercuspidal.includeUnitary F.Carrier _ = Supercuspidal.includeUnitary F.Carrier _
  rw [F.canonicalTopologicalData.includeUnitary_unitarySupportLattice, heq, map_sum]
  simp only [PadicField.TopologicalData.supportLattice, AddMonoidHom.coe_comp,
    Function.comp_apply, Multiset.mapAddMonoidHom_apply, Multiset.map_coe,
    Multiset.coe_sumAddMonoidHom, Multiset.sum_coe, List.map_ofFn, List.sum_ofFn]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Supercuspidal.includeUnitary, includeSubset, VirtualRepresentation.map, generator,
    blockBasisClass, blockDatum, Supercuspidal.unitaryBasisClass, Supercuspidal.basisClass,
    PadicField.TopologicalData.cuspidalDatumBasisEquiv]

variable (ψ ν)

/-- For irreducible representations equivalent to normalized product inductions of
unitarizable supercuspidal blocks, with unitary lattice supports `x` and `y`, the
virtual pair L-factor of `x` and `y` is `1 / P(q^(-s))` for the pair L-polynomial
`P` of the two representations (self-dual measure). -/
theorem isUnitaryPairLFactor_of_equiv_productInduced
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
    {P : ℂ[X]}
    (hP : IsPadicSymmetricLPolynomial F ψ ν πL.representation πL'.representation P) :
    IsUnitaryPairLFactor F ψ ν x y (algebraMap ℂ[X] (RatFunc ℂ) P)⁻¹ := by
  rw [eq_sum_blockBasisClass_of_equiv_productInduced πL hπL hx B σ hσ e,
    eq_sum_blockBasisClass_of_equiv_productInduced πL' hπL' hy C τ hτ e']
  exact isUnitaryPairLFactor_productInduced ψ ν hν B C σ τ hσ hτ
    ((IsPadicSymmetricLPolynomial.congr_equiv e e').mp hP)

/-- The JPSS pair L-polynomial of two unitary supercuspidal basis classes does not
depend on the additive character or the self-dual measure: by JPSS (8.1) it is `1` in
unequal ranks and `Π_(a ∈ A) (1 - aX)` in equal ranks, for a finite set `A` described
by unramified twists and contragredients only. -/
theorem IsUnitaryBasisPairLPolynomial.change
    {ψ ψ' : Correspondence.NontrivialAdditiveCharacter F}
    {ν ν' : Correspondence.LocalAdditiveHaarMeasure F}
    (hν : Correspondence.IsSelfDualMeasure F ψ ν) (hν' : Correspondence.IsSelfDualMeasure F ψ' ν')
    {a b : UnitaryBasis.{uF, uV} F} {P : ℂ[X]}
    (h : IsUnitaryBasisPairLPolynomial F ψ ν a b P) :
    IsUnitaryBasisPairLPolynomial F ψ' ν' a b P := by
  obtain ⟨P', hP'⟩ := exists_isUnitaryBasisPairLPolynomial F ψ' ν' hν' a b
  suffices hPP : P = P' by rwa [hPP]
  obtain ⟨⟨⟨_ | r, hr⟩, π⟩, ha⟩ := a
  · exact absurd hr (lt_irrefl 0)
  obtain ⟨⟨⟨_ | n, hn⟩, τ⟩, hb⟩ := b
  · exact absurd hn (lt_irrefl 0)
  induction π using Quotient.inductionOn with
  | h A =>
    induction τ using Quotient.inductionOn with
    | h B =>
      change IsPadicSymmetricLPolynomial F ψ ν A.obj.representation B.obj.representation P at h
      change IsPadicSymmetricLPolynomial F ψ' ν' A.obj.representation B.obj.representation P' at hP'
      rcases lt_trichotomy n r with hlt | rfl | hgt
      · have h1 := supercuspidalUnequalRankLFactor.{uF, uV, uV} p F ψ ⟨ν, hν⟩ r n
          A.obj.representation B.obj.representation A.property.1 A.property.2
          (supercuspidalRep_isOfWhittakerType F ψ B) hlt
        have h1' := supercuspidalUnequalRankLFactor.{uF, uV, uV} p F ψ' ⟨ν', hν'⟩ r n
          A.obj.representation B.obj.representation A.property.1 A.property.2
          (supercuspidalRep_isOfWhittakerType F ψ' B) hlt
        simp only [IsPadicSymmetricLPolynomial, hlt.le, ↓reduceIte] at h hP'
        rw [h.unique h1, hP'.unique h1']
      · obtain ⟨S, hS, hSP⟩ := supercuspidalEqualRankLFactor.{uF, uV, uV} p F ψ ⟨ν, hν⟩ n
          A.obj.representation B.obj.representation A.property.1 A.property.2 B.property.1
          (supercuspidalRep_isOfWhittakerType F ψ B)
        obtain ⟨S', hS', hSP'⟩ := supercuspidalEqualRankLFactor.{uF, uV, uV} p F ψ' ⟨ν', hν'⟩ n
          A.obj.representation B.obj.representation A.property.1 A.property.2 B.property.1
          (supercuspidalRep_isOfWhittakerType F ψ' B)
        have hSS : S = S' := Finset.ext fun x => (hS x).trans (hS' x).symm
        simp only [IsPadicSymmetricLPolynomial, le_refl, ↓reduceIte] at h hP'
        rw [h.unique hSP, hP'.unique hSP', hSS]
      · have h1 := supercuspidalUnequalRankLFactor.{uF, uV, uV} p F ψ ⟨ν, hν⟩ n r
          B.obj.representation A.obj.representation B.property.1 B.property.2
          (supercuspidalRep_isOfWhittakerType F ψ A) hgt
        have h1' := supercuspidalUnequalRankLFactor.{uF, uV, uV} p F ψ' ⟨ν', hν'⟩ n r
          B.obj.representation A.obj.representation B.property.1 B.property.2
          (supercuspidalRep_isOfWhittakerType F ψ' A) hgt
        simp only [IsPadicSymmetricLPolynomial, Nat.not_le.mpr hgt, ↓reduceIte] at h hP'
        rw [h.unique h1, hP'.unique h1']

/-- The virtual pair L-factor relation on unitary supercuspidal classes does not depend
on the additive character or the self-dual measure. -/
theorem IsUnitaryPairLFactor.change
    {ψ ψ' : Correspondence.NontrivialAdditiveCharacter F}
    {ν ν' : Correspondence.LocalAdditiveHaarMeasure F}
    (hν : Correspondence.IsSelfDualMeasure F ψ ν) (hν' : Correspondence.IsSelfDualMeasure F ψ' ν')
    {x y : UnitaryLattice.{uF, uV} F} {L : RatFunc ℂ}
    (h : IsUnitaryPairLFactor F ψ ν x y L) : IsUnitaryPairLFactor F ψ' ν' x y L := by
  obtain ⟨P, hP, rfl⟩ := h
  exact ⟨P, fun a ha b hb => (hP a ha b hb).change hν hν', rfl⟩

end Langlands.VirtualRepresentation.PadicSupercuspidal
