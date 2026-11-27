# Reduction of the simple-character class cover

`SimpleCharacterClassCoverReductionStatement` is the implication from seven propositions to
`SimpleCharacterClassCoverStatement`, the Library's form of the upper half of Bushnell and
Kutzko, *Simple types in GL(N): computing conjugacy classes* (1994), (2.3), printed p. 119: it
keeps the choice of a pair from each stratum's set, (2.3)(ii), and the coverage, (2.3)(iii),
and omits the bijectivity of the induced map of classes. Its data are a
nonarchimedean local field `F`, a finite-dimensional `F`-vector space `V`, an additive character
`ψ_F` of `F` trivial on `𝔭_F` and nontrivial on `𝔬_F`, an indexed lattice chain `L` with
hereditary order `𝔄` and unit group `U(𝔄)`, and integers `0 ≤ m < n`. For these data it asserts
one function `Φ` on the simple strata `[𝔄,n,m,β]` on `L` with three properties:

- `Φ` chooses a pair from each stratum's own set: `Φ[𝔄,n,m,β] ∈ Ĉ(𝔄,m,β)`;
- `Φ` respects conjugacy of strata modulo `𝔓^{-m}`: if `β' ≡ u⁻¹ β u (mod 𝔓^{-m})` for some
  `u ∈ U(𝔄)`, then `Φ[𝔄,n,m,β]` and `Φ[𝔄,n,m,β']` are `U(𝔄)`-conjugate;
- `Φ` covers: every pair of `S^m_n(𝔄)`, the union of the sets `Ĉ(𝔄,m,β)` over simple strata
  on `L`, is `U(𝔄)`-conjugate to a value of `Φ`.

The seven propositions are statements of the Library about simple strata and simple
characters, from Bushnell and Kutzko, *The admissible dual of GL(N) via compact open subgroups*
(1993), and BK94:

- `PureStratumSimpleApproximationStatement`, BK93 (2.4.1)(i); it supplies defining sequences;
- `SimpleCharacterConjugationStatement`, transport of simple strata, their groups and their
  simple characters by conjugation (BK93 §3.1–§3.3, BK94 §2, p. 118);
- `SimpleCharacterChoiceStatement`, BK93 (3.3.20);
- `SimpleCharacterRestrictionStatement`, BK93 (3.2.4)–(3.2.5), (3.3.18), (3.3.21);
- `SimpleCharacterCoherenceStatement`, BK93 (3.5.8);
- `SimpleCharacterTranslationStatement`, the Translation Principle, BK94 (2.11);
- `SimpleCharacterCovarianceStatement`, the conjugation formula of BK93 (3.3.9).

The theorem `simpleCharacterClassCoverReduction` proves the implication. It also uses the
Library's `simpleStratumGroupProperties` (BK93 (3.1.14)–(3.1.15)). This module does not prove
the seven propositions.

## Proof

The proof is split over the modules `ClassCoverInduction`, `ClassCoverPremises`,
`ClassCoverFibre`, `ClassCoverTwist`, `ClassCoverSurj`, `ClassCoverDecomposition`,
`ClassCoverAssembly`, `ClassCoverRefine`, `ClassCoverFibreChar`, `ClassCoverDet` and
`ClassCoverFibreScalar`, whose pages give the details. It follows the induction of BK94 §2,
printed pp. 119–123, with the following structure.

1. **Induction on the depth** (`ClassCoverInduction`). It suffices to choose, for each pair `P`
   of `S^m_n(𝔄)`, a simple stratum `κ P` such that `P` is `U(𝔄)`-conjugate to a pair of
   `Ĉ(𝔄,m,κ P)` and such that, whenever the elements `β_P`, `β_Q` of `κ P`, `κ Q` satisfy
   `β_Q ≡ u⁻¹ β_P u (mod 𝔓^{-m})` for some `u ∈ U(𝔄)`, the pairs `P` and `Q` are
   `U(𝔄)`-conjugate. This injection on classes is built by downward induction on `m`. For
   `⌊n/2⌋ ≤ m` it comes from `simpleCharacterHighIndex` (BK93 (3.2.4)). The step from `m + 1` to
   `m` uses restriction to `U^{m+2}(𝔄)` (BK94 (2.2)) and an injection on each fibre of the
   restriction.
2. **Restriction, transport, nonemptiness** (`ClassCoverPremises`). These come from
   approximation, restriction, choice and conjugation. Only an injection from character classes
   into stratum classes is constructed, which is what the upper bound needs. BK94 instead
   constructs bijections on classes.
3. **The fibres** (`ClassCoverFibre`): BK94 (2.10), using coherence and the Translation
   Principle, reduces each fibre to the set `Y(θ₀)` of BK94 p. 120 attached to one simple
   stratum `[𝔄,n,m+1,γ]`. The fibre injection then follows from two statements about
   characters `ϑ ψ_{β-γ}`.
4. **Conjugacy of twisted characters** (`ClassCoverTwist`): BK94 (2.8), (ii) ⇒ (iii), in the
   case of twist coefficients `β_i - γ`. It uses `simpleIntertwining` (BK93 (1.5.8)) and the
   covariance formula (BK93 (3.3.9)).
5. **Every pair of `Y(θ₀)` is a twist by a simple refinement** (`ClassCoverSurj`,
   `ClassCoverDecomposition`, `ClassCoverRefine`, `ClassCoverFibreChar`, `ClassCoverDet`,
   `ClassCoverFibreScalar`): BK94 (2.7) and the surjectivity in (1.8). Here `[𝔄,n,m+1,γ]` is a
   simple stratum on `L` and a simple refinement of it is a simple stratum `[𝔄,n,m,β]` on the
   same indexed chain with `β ≡ γ (mod 𝔓^{-(m+1)})`. The twist formulas BK93 (3.3.18) and
   (3.3.20)(ii) give `Ĉ(𝔄,m,β) = Ĉ(𝔄,m,γ) ψ_{β-γ}` on a common group. Two
   characters of `Ĉ(𝔄,m,γ)` with the same restriction to `U^{m+2}(𝔄)` differ by `ψ_e`, where
   `e ∈ 𝔓^{-(m+1)}` and the tame corestriction of `e` relative to `γ` is a scalar modulo
   `𝔓^{-m}` (`FibreCharacterAt`, the quotient of two
   extensions used in the proof of BK94 (2.7)). The scalar comes from the determinant
   factorization of simple characters and an elementary-matrix lemma
   (`exists_scalar_of_det_invariant`), not from the intertwining argument with BK93 (2.4.11).
   Perturbing a simple refinement by such an element `e`, with both the bound
   `e ∈ 𝔓^{-(m+1)}` and the scalar congruence, gives an element congruent modulo `𝔓^{-m}` to a
   simple refinement (`RefinementSimpleAt`; BK93
   (2.2.8), (2.4.1), BK94 (1.8)). Its proof, `refinementSimpleAt`, shows that the derived
   stratum of `(β - γ) + e` is null or equivalent to a simple stratum, which is the conclusion
   of BK94 (2.7) for that coefficient, before applying BK93 (2.2.8).

`ClassCoverRefine` proves `simpleCharacterClassCover_of_fibreCharacter`, the target from the
seven propositions, the group properties and `SimpleCharacterFibreCharacterStatement`.
`fibreCharacterAt` (module `ClassCoverFibreScalar`) proves the last hypothesis at every depth
from `SimpleCharacterChoiceStatement`, and `simpleCharacterClassCoverReduction` combines the two.
