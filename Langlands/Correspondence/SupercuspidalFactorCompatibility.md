# Pair-factor compatibility of supercuspidal families

Author: Worker 7. This module states the pair L- and epsilon-factor
condition (4) of Henniart 2000, §1.2, for the irreducible-Weil to
supercuspidal family `SupercuspidalMap` of `Domains`: for irreducible Weil
classes `σ`, `τ`, the Rankin–Selberg factors of `π(σ) × π(τ)` defined by
Jacquet, Piatetski-Shapiro and Shalika equal the arithmetic factors of
`σ ⊗ τ`. The conditions are propositions on a given family. No family,
additive character, measure or local-constant system is constructed or
chosen, and no part of the correspondence is asserted.

## Representation side

`F : PadicField p` carries its canonical topological data and `q` is its
residue cardinality. Supercuspidal classes are the published
`PadicField.SupercuspidalClass F n hn`: isomorphism classes of the published
supercuspidal full subcategory of smooth representations of `GL_n(F)`.

- `IsSupercuspidalPairLPolynomial F ψ ν π τ P`, for supercuspidal classes `π`
  of rank `r + 1` and `τ` of rank `n + 1`, is Worker 11's published
  `RankinSelberg.IsPadicSymmetricLPolynomial F ψ ν A B P` on representatives
  `A` of `π` and `B` of `τ`. It says `L(s, π × τ) = 1/P(q^(-s))` in the
  JPSS convention: the representation of larger rank is the candidate, and in
  equal rank `π` is. The relation takes the measure `ν` used by the
  published relation.
- `IsSupercuspidalPairEpsilonFactor F ψ ν π τ e` is likewise the published
  `RankinSelberg.IsPadicSymmetricEpsilonFactor`, with `e = (c, m)` meaning
  `ε(s, π × τ, ψ) = c q^(-ms)`.

Both are defined with `Quotient.lift₂`. Independence of the representatives
is proved from the published `congr_equiv` lemmas of the symmetric relations,
applied to the representation equivalences obtained from isomorphisms in the
supercuspidal subcategory (`SmoothRep.equivOfIso`). That proof is the only
proof in the module.

## Arithmetic side

The arithmetic factors come from this task's `ArithmeticFactors`.
`weilPairClass F σ` is the zero-monodromy pair class of `σ`.
`arithmeticPairLFactor` is the Artin pair L-factor as a rational function of
`X = q^(-s)`. `IsArithmeticPairEpsilonFactor F eC ε hε ψ X Y c m` says that
the epsilon factor computed with the supplied system `ε` (for the
common-closure reciprocity family `eC`, with `hε : IsSystem F eC ε`) is
`c q^(-ms)`.

## Conditions

`SupercuspidalPairFactorCompatibility F eC ε hε c`, for a supercuspidal map
`c`, says: for every nontrivial unitary additive character `ψ` of `F`, all
`r n : ℕ`, and all irreducible Weil classes `σ` of rank `r + 1` and `τ` of
rank `n + 1`:

1. a measure `ν` self-dual for `ψ` exists (`IsSelfDualMeasure` of
   `LocalConventions`); and
2. for every such `ν`:
   - (L) there is a polynomial `P` with
     `IsSupercuspidalPairLPolynomial F ψ ν (c σ) (c τ) P` and
     `arithmeticPairLFactor F (weilPairClass F σ) (weilPairClass F τ) = 1/P`
     in `RatFunc ℂ`;
   - (ε) there is `e = (c₀, m)` with
     `IsSupercuspidalPairEpsilonFactor F ψ ν (c σ) (c τ) e` and
     `IsArithmeticPairEpsilonFactor F eC ε hε ψ (weilPairClass F σ)
     (weilPairClass F τ) c₀ m`.

Ranks are written `r.succPNat` on the Weil side and `r + 1` on the
supercuspidal side, which agree definitionally, so no rank casts occur.

`SupercuspidalFactorCompatibility F e c`, for a rank-one reciprocity
candidate `e`, says that some reciprocity family `eC`, assignment `ε` and
proof `hε : IsSystem F eC ε` exist with `IsBaseReciprocity F e eC` and
`SupercuspidalPairFactorCompatibility F eC ε hε c`. The system takes carrier
universe `uP`, the universe of the Weil classes, so the pair transport of
`ArithmeticFactors` can use their representatives.

## Sources and provenance

- Henniart 2000, §1.2, printed p.440 (PDF p.2), property 4): for
  `σ ∈ G_F^0(n)` and `σ' ∈ G_F^0(n')`, `L(σ ⊗ σ', s) = L(π(σ) × π(σ'), s)`
  and `ε(σ ⊗ σ', s, ψ) = ε(π(σ) × π(σ'), s, ψ)`, the right-hand factors being
  those of JPSS. Section 1.1, printed p.439, fixes one nontrivial additive
  character `ψ`. The remark in §1.3, printed p.441 (PDF p.3), says that,
  given the central-character property 1), (4ε) for one `ψ` implies it for
  every `ψ`.
- Henniart 2002, §1.2, printed pp.588–589 (PDF pp.2–3): the arithmetic
  factors are the Artin L-function and the Langlands–Deligne epsilon factor
  (Tate 1979, §4), the pair factors are those of JPSS, L-factors have the
  form `P(q^(-s))⁻¹` with `P(0) = 1`, and epsilon factors the form
  `α q^(-ms)`. Its §1.3, printed p.589, states the existence of the
  supercuspidal family with the epsilon identity for all `n, n' ≥ 1`.
- JPSS 1983, Theorem 2.7, printed pp.390–391, and (2.12), printed p.403, as
  recorded in Worker 11's published `RankinSelberg/PadicPairFactors`: the
  definition of the pair factors and the convention that the factors of
  `σ × π`, with `σ` of smaller rank, are those of `π × σ`. This module takes
  that convention from the published relations; I did not re-read the JPSS
  scan, which has no text layer.
- Tate 1979, (3.6.4), printed p.17 (PDF p.26): Langlands' `ε(s, V, ψ)` is
  Deligne's constant at the measure self-dual for `ψ`. JPSS also use the
  self-dual measure; the published `RankinSelberg/EpsilonFactor` records this
  (JPSS pp.377–378) and leaves self-duality to its users. Hence both
  measures in the conditions are self-dual.

Source files:

- `henniart-2000-simple-proof`, SHA-256
  `be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de`.
- `henniart-2002-characterization`, SHA-256
  `40c0ed7c7bfb05f1415fd66642d0b1984052f0af7cb5f3061b328216e2d24306`.
- `jpss-1983-rankin-selberg`, SHA-256
  `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
- `tate-1979-number-theoretic-background`, SHA-256
  `c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`.

## Interpretation

- **Every `ψ`.** The conditions quantify over all nontrivial `ψ`, not one
  fixed character. By Henniart's §1.3 remark this is equivalent to the
  one-`ψ` form for families with the central-character property, which the
  full specification requires separately (`OperationCompatibility`). The
  remark is not proved in the Library.
- **Both L and ε.** The L identity and the epsilon identity are stated
  separately, as in Henniart's (4L) and (4ε). A gamma identity is not stated
  separately; Henniart notes after (4) that the gamma identity follows.
- **Totality.** The polynomial `P` and the witness `e` are asserted to exist.
  So the conditions imply that the JPSS factors of every image pair exist in
  the form required by the published relations. They do not assume it. The
  published relations need nonzero Whittaker functionals for both
  representations. Supercuspidal representations are generic, but that is
  not proved in the Library.
- **Measures.** A self-dual measure for `ψ` is asserted to exist, and the
  identities are required for every self-dual measure. The witnesses `P` and
  `e` may a priori depend on `ν`. The published uniqueness lemmas
  (`IsPadicSymmetricLPolynomial.unique`, `IsPadicSymmetricEpsilonFactor.unique`)
  and the measure-independence of the arithmetic side make that dependence
  harmless.
- **Local constants.** The arithmetic epsilon factor is computed from an
  existentially quantified system satisfying the published `IsSystem`, whose
  base reciprocity component is the candidate `e`. Deligne's theorem (Tate
  1979, (3.4.1)) gives existence and uniqueness of such a system; the Library
  states these as `NonabelianSystem.Exists` and `NonabelianSystem.Unique`
  without proof. A universally quantified system would make the condition
  vacuous until existence is proved, so the system is existential. Under
  `Unique` for the family, the existential and universal forms agree.
- **Reciprocity.** The candidate `e` is an input here. The full
  specification must quantify `e` existentially together with
  `IsGeometricReciprocity F e`, as for the other conditions of
  `OperationCompatibility`.
- **Scope.** Only the supercuspidal family is covered. The full family needs
  pair factors of nongeneric representations, which the published JPSS
  relations do not provide; its factor conditions are a separate module of
  this task.

The module imports, and does not copy: Worker 11's
`Langlands.Representation.RankinSelberg.PadicPairFactors`
(`IsPadicSymmetricLPolynomial`, `IsPadicSymmetricEpsilonFactor` and their
`congr_equiv` lemmas), `Langlands.Representation.Classification.Supercuspidal`
(`SupercuspidalRep`, `SupercuspidalClass`, `supercuspidalProperty`),
`LocalConventions` (`NontrivialAdditiveCharacter`, `LocalAdditiveHaarMeasure`,
`IsSelfDualMeasure`) and this task's `Domains` and `ArithmeticFactors`.

## Validation

The module compiles in the project Lean service together with
`ArithmeticFactors`, with no errors or warnings. There is no `sorry` and no
new axiom. Every condition returns `Prop`.
