import Langlands.Global.ArthurSiegelSets
import Langlands.Global.ArthurTruncationStatement
import Langlands.Global.AdelicSiegelReductionStatement
import Langlands.Global.AdelicSiegelFiniteVolume
import Langlands.Automorphic.GroupSchemeAdelicUniformGrowth
import Langlands.Automorphic.GroupSchemeActualDifferential

/-! # The partition lemma and the rapid decrease of truncated functions

Arthur 2005, Lemma 8.2 and (8.1) (pp.38–41), and Proposition 13.2(a) (p.71); Arthur 1978,
Lemma 6.4 (p.941), for the objects of `Langlands.Global.ArthurSiegelSets` and
`Langlands.Global.ArthurTruncation`. Each result is a predicate of one compact subgroup `K`;
`ArthurSiegelSetsStatement` asserts that one maximal compact `K` admits Siegel covering data and
satisfies all of them together with Proposition 13.1(a),(b) (`IsTruncationIdempotent`). -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise

namespace Langlands.Global.ArthurTruncation

open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace AdelicGroupPoints
  ArthurParabolicSpaces AdelicSiegelFactors Langlands.Automorphic.GroupSchemeFunctions

section Predicates

variable {F : Type u} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))} {i : T.toGrp ⟶ G} [Mono i.hom.hom.left]
  {ν : cocharacterLattice T}

/-- **The covering property of Siegel sets** (Arthur 1978, §6, p.941: "we can fix `ω` and `T_0`
so that for any `P_1`, `G(𝔸) = P_1(ℚ) S^{P_1}(T_0, ω)`"). For the compact factor data `C`
(`ω = Ω_N Ω_M` and the compact subgroup `C.compactSubgroup`) and `T_1 ∈ 𝔞_0`: for every standard
`P_1` (`Δ_0^{P_1} = S₁`), `G(𝔸) = P_1(F) S^{P_1}(T_1, ω)`. For `P_1 = G` this is the property of
Arthur 2005, Theorem 8.1. -/
def IsSiegelCovering (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    {K : Subgroup (AdelicGroupPoints F G)}
    (hK : IsIwasawaCompact (Standard.parabolicHom i ν ∅) K)
    (hρ : Function.Bijective (restrictToTorus F i ν ∅))
    (C : CompactFactors F G (Standard.unipotentScheme i ν ∅) (Standard.leviScheme i ν ∅))
    (T₁ : V T) : Prop :=
  ∀ S₁ ∈ (simpleFinset ν hG hi).powerset,
    (parabolicRationalImage (Standard.parabolicHom i ν (S₁ : Set (characterLattice T))) :
        Set (AdelicGroupPoints F G)) * siegelSet hi hK hρ C S₁ T₁ = Set.univ

/-- **Arthur 2005, Lemma 8.2, for one compact subgroup `K`.** For every compact factor data `ω`
(with the compact subgroup `K`) and `T_1 ∈ 𝔞_0` with `G(𝔸) = G(F) S^G(T_1, ω)` (Theorem 8.1) there
is `c` such that for every `T ∈ 𝔞_0` with `β(T) > c` for every `β ∈ Δ_0` and every `x ∈ G(𝔸)`:
for each standard `P` only finitely many `δ ∈ P(F)\G(F)` have `F^P(δx, T) τ_P(H_P(δx) − T) ≠ 0`,
and `∑_{P ⊇ P_0} ∑_{δ ∈ P(F)\G(F)} F^P(δx, T) τ_P(H_P(δx) − T) = 1`. -/
def IsSiegelPartition (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (D : RelativeRootReflectionData i) {K : Subgroup (AdelicGroupPoints F G)}
    (hK : IsIwasawaCompact (Standard.parabolicHom i ν ∅) K)
    (hρ : Function.Bijective (restrictToTorus F i ν ∅)) : Prop :=
  ∀ (C : CompactFactors F G (Standard.unipotentScheme i ν ∅) (Standard.leviScheme i ν ∅))
    (T₁ : V T), C.compactSubgroup = K →
    (rationalSubgroup F G : Set (AdelicGroupPoints F G)) *
        siegelSet hi hK hρ C (simpleFinset ν hG hi) T₁ = Set.univ →
    ∃ c : ℝ, ∀ Tp : V T, (∀ β ∈ simpleRelativeRoots i ν, c < eval T β Tp) →
      ∀ x : AdelicGroupPoints F G,
        (∀ S ∈ (simpleFinset ν hG hi).powerset,
          (Function.support fun δ : ParabolicRationalCosets F
              (Standard.parabolicHom i ν (S : Set (characterLattice T))) =>
            siegelIndicator hG hi D hK hρ C S T₁ Tp
                (((Quotient.out δ : rationalSubgroup F G) : AdelicGroupPoints F G) * x) *
              ArthurRelative.tau hG hi ν D (S : Set (characterLattice T))
                (simpleRelativeRoots i ν)
                (height hi hK hρ
                  (((Quotient.out δ : rationalSubgroup F G) : AdelicGroupPoints F G) * x) -
                    Tp)).Finite) ∧
        ∑ S ∈ (simpleFinset ν hG hi).powerset,
          ∑' δ : ParabolicRationalCosets F
              (Standard.parabolicHom i ν (S : Set (characterLattice T))),
            siegelIndicator hG hi D hK hρ C S T₁ Tp
                (((Quotient.out δ : rationalSubgroup F G) : AdelicGroupPoints F G) * x) *
              ArthurRelative.tau hG hi ν D (S : Set (characterLattice T))
                (simpleRelativeRoots i ν)
                (height hi hK hρ
                  (((Quotient.out δ : rationalSubgroup F G) : AdelicGroupPoints F G) * x) - Tp) =
          1

/-- **Arthur 1978, Lemma 6.4; Arthur 2005, (8.1), for one compact subgroup `K`.** For every
compact factor data `ω` (with the compact subgroup `K`) and `T_1 ∈ 𝔞_0` with
`G(𝔸) = P_1(F) S^{P_1}(T_1, ω)` for every standard `P_1` there is `c` such that for every `T` with
`β(T) > c` for every `β ∈ Δ_0`, every standard `P` and every `x ∈ G(𝔸)`: for each
`P_0 ⊆ P_1 ⊆ P` only finitely many `δ ∈ P_1(F)\P(F)` give a nonzero term, and
`∑_{P_0 ⊆ P_1 ⊆ P} ∑_{δ ∈ P_1(F)\P(F)} F^{P_1}(δx, T) τ_{P_1}^P(H_{P_1}(δx) − T) = 1`. -/
def IsRelativeSiegelPartition (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (D : RelativeRootReflectionData i) {K : Subgroup (AdelicGroupPoints F G)}
    (hK : IsIwasawaCompact (Standard.parabolicHom i ν ∅) K)
    (hρ : Function.Bijective (restrictToTorus F i ν ∅)) : Prop :=
  ∀ (C : CompactFactors F G (Standard.unipotentScheme i ν ∅) (Standard.leviScheme i ν ∅))
    (T₁ : V T), C.compactSubgroup = K →
    IsSiegelCovering hG hi hK hρ C T₁ →
    ∃ c : ℝ, ∀ Tp : V T, (∀ β ∈ simpleRelativeRoots i ν, c < eval T β Tp) →
      ∀ SP ∈ (simpleFinset ν hG hi).powerset, ∀ x : AdelicGroupPoints F G,
        (∀ S₁ ∈ SP.powerset,
          (Function.support fun δ : RelativeCosets (F := F) (i := i) (ν := ν)
              (S₁ : Set (characterLattice T)) (SP : Set (characterLattice T)) =>
            siegelIndicator hG hi D hK hρ C S₁ T₁ Tp
                ((((Quotient.out δ : parabolicRationalSubgroup F
                  (Standard.parabolicHom i ν (SP : Set (characterLattice T)))) :
                    rationalSubgroup F G) : AdelicGroupPoints F G) * x) *
              ArthurRelative.tau hG hi ν D (S₁ : Set (characterLattice T))
                (SP : Set (characterLattice T))
                (height hi hK hρ
                  ((((Quotient.out δ : parabolicRationalSubgroup F
                    (Standard.parabolicHom i ν (SP : Set (characterLattice T)))) :
                      rationalSubgroup F G) : AdelicGroupPoints F G) * x) - Tp)).Finite) ∧
        ∑ S₁ ∈ SP.powerset,
          ∑' δ : RelativeCosets (F := F) (i := i) (ν := ν) (S₁ : Set (characterLattice T))
              (SP : Set (characterLattice T)),
            siegelIndicator hG hi D hK hρ C S₁ T₁ Tp
                ((((Quotient.out δ : parabolicRationalSubgroup F
                  (Standard.parabolicHom i ν (SP : Set (characterLattice T)))) :
                    rationalSubgroup F G) : AdelicGroupPoints F G) * x) *
              ArthurRelative.tau hG hi ν D (S₁ : Set (characterLattice T))
                (SP : Set (characterLattice T))
                (height hi hK hρ
                  ((((Quotient.out δ : parabolicRationalSubgroup F
                    (Standard.parabolicHom i ν (SP : Set (characterLattice T)))) :
                      rationalSubgroup F G) : AdelicGroupPoints F G) * x) - Tp) =
          1

/-- **Arthur 2005, Proposition 13.2(a), for one compact subgroup `K`**, for functions on
`G(F) \ G(𝔸)`. For every closed matrix representation `rho` (the height `‖x‖`) and smooth structure
there is `c` such that for every `T` with `β(T) > c` for every `β ∈ Δ_0`: if `φ` is a finite
plot-smooth left `G(F)`-invariant function with uniformly moderate growth (one exponent bounding
every enveloping derivative, `HasAdelicUniformModerateGrowth`), then `Λ^T φ` is rapidly decreasing
on the Siegel sets of `K`: for every Siegel set `S` and every `n`, `|Λ^T φ(x)| ≤ B ‖x‖^{−n}` on
`S ∩ G(𝔸)^1`. -/
def IsTruncationRapidDecay (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (D : RelativeRootReflectionData i) {K : Subgroup (AdelicGroupPoints F G)}
    (hK : IsIwasawaCompact (Standard.parabolicHom i ν ∅) K)
    (hρ : Function.Bijective (restrictToTorus F i ν ∅)) : Prop :=
  ∀ {N d : ℕ} (rho : MatrixRepresentation G (Fin N))
    (hsmooth : SmoothOfRelativeDimension d G.X.hom),
    0 < N → IsClosedSubgroup rho →
    ∃ c : ℝ, ∀ Tp : V T, (∀ β ∈ simpleRelativeRoots i ν, c < eval T β Tp) →
      ∀ f : FinitePlotSmoothRationalFunctions F G,
        HasAdelicUniformModerateGrowth F G rho hsmooth
            (adelicDifferentialCommutator_of_smooth F G hsmooth) f →
          IsRapidlyDecreasing hG hi hK hρ rho
            (truncation hG hi D hK hρ Tp (evaluate F G f.val))

end Predicates

/-- **Arthur 2005, Lemma 8.2, (8.1), Propositions 13.1(a),(b) and 13.2(a), for a chosen suitable
`K`** (Arthur 2005, p.24: "We choose a suitable maximal compact subgroup `K` … with
`G(𝔸) = P_0(𝔸)K`"). There is a compact subgroup `K` of `G(𝔸)` with `P_0(𝔸)K = G(𝔸)`, maximal
compact, whose elements in `P_0(𝔸)` commute with the positive torus of every L1 Siegel setup,
such that for every choice of reflection data `D` (with the bijectivity `hρ`) it admits Siegel
covering data `ω`, `T_1` (`IsSiegelCovering`; Theorem 8.1 and its form in Arthur 1978, §6) and
satisfies `IsTruncationIdempotent`, `IsSiegelPartition`, `IsRelativeSiegelPartition` and
`IsTruncationRapidDecay`. -/
def ArthurSiegelSetsStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G) [Mono i.hom.hom.left]
    (ν : cocharacterLattice T) (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i),
    IsGenericCocharacter i ν →
    ∃ (K : Subgroup (AdelicGroupPoints F G))
      (hK : IsIwasawaCompact (Standard.parabolicHom i ν ∅) K),
      IsMaximalCompactSubgroup F G K ∧
      (∀ (T₀ : CommGroupScheme (Spec (CommRingCat.of F))) (j : T₀ ⟶ T),
        AdelicSiegelFactors.IsSiegelAlgebraicSetup F G T i ν T₀ j →
          AdelicSiegelFactors.IsPositiveTorusCompatible F G T i ν T₀ j K) ∧
      ∀ (D : RelativeRootReflectionData i) (hρ : Function.Bijective (restrictToTorus F i ν ∅)),
        (∃ (C : CompactFactors F G (Standard.unipotentScheme i ν ∅)
            (Standard.leviScheme i ν ∅)) (T₁ : V T),
          C.compactSubgroup = K ∧ IsSiegelCovering hG hi hK hρ C T₁) ∧
        IsTruncationIdempotent hG hi D hK hρ ∧ IsSiegelPartition hG hi D hK hρ ∧
          IsRelativeSiegelPartition hG hi D hK hρ ∧ IsTruncationRapidDecay hG hi D hK hρ

end Langlands.Global.ArthurTruncation
