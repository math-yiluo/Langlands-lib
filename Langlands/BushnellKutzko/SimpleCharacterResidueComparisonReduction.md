# Reduction of the residue comparison of BK94 (5.2)

`SimpleCharacterResidueComparisonReductionStatement` is the implication from
three propositions to `SimpleCharacterResidueComparisonStatement` (BK94 Lemma
(5.2), together with the equality `𝔅₁ + 𝔓 = 𝔅₂ + 𝔓`). The three propositions
are:

- `PureStratumSimpleApproximationStatement`: BK93 (2.4.1)(i). It is used only
  to obtain a defining sequence of a simple stratum
  (`Stratum.exists_exact_definingSequenceChoice`).
- `SimpleCharacterRestrictionStatement`: BK93 (3.2.4)–(3.2.5), (3.3.18),
  (3.3.21). Only its last clause is used: the sets of simple characters are
  nonempty.
- `SimpleCharacterIntertwiningStatement`: BK93 (3.3.2), (3.3.17). Only the
  intertwining clause is used.

The theorem `simpleCharacterResidueComparisonReduction` proves the implication.
It also uses the theorems `simpleStratumGroupProperties` (BK93
(3.1.14)–(3.1.15)), `simpleCharacterIntertwiningFactor_mul_centralizer_zero`
and `tameCorestriction`, which the Library proves.

## Auxiliary results

- `centralizerLattice_eq_inf_fieldCommutant`: for a field `F[β]`,
  `𝔓^t ∩ B_β` is the set of `F[β]`-linear elements of `𝔓^t`. This extends
  `StratumEquivalence.fieldOrder_elementAlgebra` from `t = 0` to all `t`.
- `zero_lt_simpleCriticalDepth_of_isSimple`: a simple stratum `[𝔄,n,0,β]` has
  `0 < −k₀(β,𝔄)` in `WithTop ℤ`.
- `centralizerLattice_sup_eq_of_pairs_eq` (BK94 (5.8)): let `[𝔄,n,0,γ₁]` and
  `[𝔄,n,0,γ₂]` be simple with the same depth-zero character pairs. Then
  `𝔔₁^t + 𝔓^{t+1} = 𝔔₂^t + 𝔓^{t+1}` for every `t ∈ ℤ`, where
  `𝔔_i^t = 𝔓^t ∩ B_{γ_i}` (`centralizerLattice`).

## Proof

1. **A common character.** Choose a defining sequence for `γ₁`. Then choose
   `θ₁ ∈ C(𝔄,0,γ₁)` by nonemptiness. Its pair `(H¹(γ₁,𝔄), θ₁)` lies in the
   pairs of `γ₂`, so it equals `(H¹(γ₂,𝔄), θ₂)` for some defining sequence of
   `γ₂` and some `θ₂ ∈ C(𝔄,0,γ₂)`. Equal pairs have equal self-intertwining.
2. **Intertwining** (BK94 (5.7)). By `SimpleCharacterIntertwiningStatement`,
   the self-intertwining of `θ_i` is `Y_i B_{γ_i}^× Y_i`. By
   `simpleCharacterIntertwiningFactor_mul_centralizer_zero`, this equals
   `J¹_i B_{γ_i}^× J¹_i` with `J¹_i = J¹(γ_i,𝔄) ⊆ U¹(𝔄)`. Hence
   `J¹₁ B_{γ₁}^× J¹₁ = J¹₂ B_{γ₂}^× J¹₂`.
3. **(5.8).** `centralizerLattice_sup_eq_of_doubleCoset_eq` (module
   `CentralizerDoubleCoset`) gives `𝔔₁^t + 𝔓^{t+1} = 𝔔₂^t + 𝔓^{t+1}` for all
   `t`. The case `t = 0` is the first conclusion, `𝔅₁ + 𝔓 = 𝔅₂ + 𝔓`.
4. **(i)–(iii).** Let `F[γ_i]` be fields. They normalize `𝔄` because the strata
   are simple. By `centralizerLattice_eq_inf_fieldCommutant`, step 3 is the
   hypothesis `GradedCentralizer.GradedEq` of the module
   `CentralizerResidueComparison`. Its theorems `exists_integer_sub_mem` (in
   both directions), `exists_primeElement_congr` and
   `exists_tameCorestriction_congr` give (i), (ii) and (iii); in (iii) put
   `t = −(k+1)`.

## Relation to the source

Bushnell and Kutzko, *Simple types in GL(N): computing conjugacy classes*
(1994), Lemma (5.2), (5.7), (5.8) and the proof of (5.2), printed pp. 132–134
(PDF pp. 145–147), literature ID
`bushnell-kutzko-1994-simple-types-conjugacy-classes`, SHA-256
`fd2077476192d9db15188feea9ff73774fe96296a2a31412d612f2081581efaa`. BK94 prove
(5.2) first when `𝔄` is maximal among the orders normalized by `F[γ₁]^×`, from
(5.7) and (5.8). They reduce the general case to that one with BK93 (3.6.1) and
(5.1.16). Here (5.7) and (5.8) are obtained for every `𝔄` from BK93 (3.3.2).
The deduction of (i)–(iii) in `CentralizerResidueComparison` needs no
maximality, so no reduction to the maximal case is needed. The inputs from
Bushnell and Kutzko, *The admissible dual of GL(N) via compact open subgroups*
(1993), are (2.4.1)(i), (3.1.14)–(3.1.15), (3.3.2) and the nonemptiness of
`C(𝔄,0,β)` from (3.3.18)–(3.3.21), printed pp. 65, 95, 105 and 112–114,
literature ID
`bushnell-kutzko-1993-admissible-dual-gln`, SHA-256
`811693b94c03fcbc2cfe33955bc5a00b0fc0b5645ca343f8cc1a3c6511de9c73`. The step
from the double coset to (5.8) is the argument of the proof of BK93 (3.5.1),
printed p. 117.
