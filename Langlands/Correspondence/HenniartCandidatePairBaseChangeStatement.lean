import Langlands.Correspondence.HenniartCandidateBaseChangeFiniteImageReductionStatement

/-!
# Pairs of Henniart candidates compatible with a cyclic base change

For a cyclic prime-degree step `M/L` and a map `Ch` from supercuspidal classes
over `L` to multisets of supercuspidal classes over `M`, the additive extension
`Numerical.cyclicBaseChangeLatticeMap` of `Ch` is a map of supercuspidal
lattices. A candidate `Φ_L` over `L` and a candidate `Φ_M` over `M`
(`StableMap.IsCandidate`, Henniart 2000, §§3.8 and 4.1) are compatible with
`Ch` on the classes factoring through a finite quotient `q` of the absolute
Galois group of `L` when `Ch ∘ Φ_L = Φ_M ∘ Res` there.

Source (b) of §6.5 of the numerical correspondence route note assesses that
(CI1) should follow from Henniart's construction by a global argument; this is
not a published statement. `CertifiedCandidatePairCompatibilityStatement`
isolates the global part, the existence of compatible pairs of candidates for
certified weak cyclic base changes, and `CandidatePairFiniteImageReductionStatement`
states the local deduction of (CI1) on classes of finite image from it.
Definitions and proposition definitions only.
-/

noncomputable section

namespace Langlands.Henniart

universe uK uW uV uQ

open Langlands.Correspondence Langlands.VirtualRepresentation StableMap

namespace Numerical

variable {p : ℕ} [Fact p.Prime]

/-- The additive extension of `Ch` to supercuspidal lattices: a class `π` of rank `n`
over `L` goes to the sum of the classes of the multiset `Ch (n - 1) π`, with their
ranks and multiplicities. -/
def cyclicBaseChangeLatticeMap (S : CyclicPrimeStep.{uK} p)
    (Ch : CyclicBaseChangeMap.{uK, uV} S) :
    PadicSupercuspidal.Lattice.{uK, uV} S.base →ₗ[ℤ]
      PadicSupercuspidal.Lattice.{uK, uV} S.top :=
  extend fun b : PadicSupercuspidal.Basis.{uK, uV} S.base =>
    ((Ch b.1.natPred (Extension.rankCast S.base b (PNat.succPNat_natPred b.1).symm)).map
      fun ρ => generator (⟨ρ.1.succPNat, ρ.2⟩ : PadicSupercuspidal.Basis.{uK, uV} S.top)).sum

/-- `Ch ∘ Φ_L = Φ_M ∘ Res` on the classes factoring through `q`: for every element `x`
of the domain of `Φ_L` in the span of the unitary irreducible classes of `W_L`
factoring through `q`, the restriction of `x` to `W_M`, compared in the exact
Grothendieck group of continuous representations of `W_M`, is an element `x'` of the
domain of `Φ_M`, and the additive extension of `Ch` sends `Φ_L x` to `Φ_M x'`. -/
def IsCandidatePairBaseChangeCompatible (S : CyclicPrimeStep.{uK} p)
    (Ch : CyclicBaseChangeMap.{uK, uV} S) {Q : Type uQ} [Group Q] [Finite Q]
    (q : Field.absoluteGaloisGroup S.base.Carrier →* Q)
    {WL : Submodule ℤ (LocalWeil.UnitaryLattice.{uK, uW} S.base)}
    {AL : Submodule ℤ (PadicSupercuspidal.UnitaryLattice.{uK, uV} S.base)}
    {WM : Submodule ℤ (LocalWeil.UnitaryLattice.{uK, uW} S.top)}
    {AM : Submodule ℤ (PadicSupercuspidal.UnitaryLattice.{uK, uV} S.top)}
    (ΦL : WL ≃ₗ[ℤ] AL) (ΦM : WM ≃ₗ[ℤ] AM) : Prop :=
  ∀ x : WL, (x : LocalWeil.UnitaryLattice.{uK, uW} S.base) ∈
      LocalWeil.unitaryFiniteFactoringSupported.{uK, uW, uQ} S.base q →
    ∃ x' : WM,
      ExactGrothendieckGroup.continuousRestrict
          (Weil.Local.extensionWeilMap S.base S.top S.embedding)
          (LocalWeil.realizeExact S.base (LocalWeil.includeUnitary S.base x)) =
        LocalWeil.realizeExact S.top (LocalWeil.includeUnitary S.top x') ∧
      cyclicBaseChangeLatticeMap S Ch (PadicSupercuspidal.includeUnitary S.base (ΦL x)) =
        PadicSupercuspidal.includeUnitary S.top (ΦM x')

end Numerical

open Numerical

/-- For every weak cyclic base change certified by σ-lifts on supercuspidal classes for
every `σ ≠ 1`, and for every pair of finite quotients `q_L` and `q_M` of the absolute
Galois groups of `L` and `M`, there are a candidate `Φ_L` at `q_L` and a candidate
`Φ_M` at `q_M` with `Ch ∘ Φ_L = Φ_M ∘ Res` on the classes factoring through `q_L`. -/
def CertifiedCandidatePairCompatibilityStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (S : CyclicPrimeStep.{uK} p)
    (Ch : CyclicBaseChangeMap.{uK, uV} S),
    IsWeakCyclicBaseChange S Ch →
    (∀ σ : S.Gal, σ ≠ 1 →
      BaseChange.IsSigmaLiftOnSupercuspidals.{uK, uV} S.embedding Ch σ) →
    ∀ (QL : Type uK) [Group QL] [Finite QL]
      (qL : Field.absoluteGaloisGroup S.base.Carrier →* QL)
      (QM : Type uK) [Group QM] [Finite QM]
      (qM : Field.absoluteGaloisGroup S.top.Carrier →* QM),
      ∃ (WL : Submodule ℤ (LocalWeil.UnitaryLattice.{uK, uW} S.base))
        (AL : Submodule ℤ (PadicSupercuspidal.UnitaryLattice.{uK, uV} S.base))
        (ΦL : WL ≃ₗ[ℤ] AL)
        (WM : Submodule ℤ (LocalWeil.UnitaryLattice.{uK, uW} S.top))
        (AM : Submodule ℤ (PadicSupercuspidal.UnitaryLattice.{uK, uV} S.top))
        (ΦM : WM ≃ₗ[ℤ] AM),
        IsCandidate.{uK, uW, uV, uW, uK} S.base qL ΦL ∧
          IsCandidate.{uK, uW, uV, uW, uK} S.top qM ΦM ∧
          IsCandidatePairBaseChangeCompatible S Ch qL ΦL ΦM

/-- Compatible pairs of candidates for certified weak cyclic base changes give the
reduction of (CI1) on classes of finite image to candidate existence. -/
def CandidatePairFiniteImageReductionStatement : Prop :=
  CertifiedCandidatePairCompatibilityStatement.{uK, uW, uV} →
    CandidateFiniteImageBaseChangeCompatibilityReductionStatement.{uK, uW, uV}

end Langlands.Henniart
