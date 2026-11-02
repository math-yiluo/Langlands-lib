# Normalized logarithms of norm characters

Author: Worker 200.

Waldspurger, *La formule de Plancherel pour les groupes p-adiques (d’après
Harish-Chandra)*, I.1, printed pp.239–240 (PDF pp.5–6), defines the common
norm kernel and the unramified characters, then fixes the sign of the map
`H_G` by

`q ^ (-⟨χ, H_G(g)⟩) = |χ(g)|_F`.

He explicitly remarks on this minus sign. The registered source is
`waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.
Renard, *Représentations des groupes réductifs p-adiques*, 9 July 2026 edition,
V.2.3, printed p.105 (PDF p.111), instead writes the same coordinate as
`⟨χ, H_G(g)⟩ = v_F(χ(g))` and identifies its kernel with the intersection of
the norm kernels. The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
These conventions agree when `|a|_F = q ^ (-v_F(a))`.

This file constructs the numerical and additive-homomorphism part of these
maps. Its formulation for an arbitrary additive family of positive characters
is derived from those source formulas. It does not introduce a reductive-group
structure or assume any structural theorem.

The inputs are a group `G`, an additive commutative group `L`, and a family

`ν : L →+ Additive (G →* ℝ≥0ˣ)`.

The additive packaging means that `ν (χ + ψ)` evaluates as the product of
`ν χ` and `ν ψ`. The universes of `G` and `L` are independent. No topology,
freeness, finite generation, basis, or nontriviality is required; in particular
the trivial character group is allowed. Values are units in the nonnegative
reals, so every value is strictly positive as a real number.

- `normLog q x` is `-Real.log x / Real.log q`, using the real value of the
  positive unit `x`. `normLog_one` and `normLog_mul` prove the zero and product
  laws. The definition and these laws make sense for every real `q`, using
  Lean’s total division convention.
- The characterizing results require `1 < q`. `normLog_eq_zero_iff` identifies
  zero with the unit value `1`. `rpow_neg_normLog` proves
  `q ^ (-normLog q x) = x` as an equality of real numbers.
  `normLog_eq_of_rpow` proves uniqueness: any real `t` satisfying
  `q ^ (-t) = x` equals `normLog q x`.
- `normLogPairing q ν g : L →+ ℝ` constructs the additive coordinate functional
  for a fixed group element. `normLogarithm q ν` bundles these into the actual
  homomorphism `G →* Multiplicative (L →+ ℝ)`. The multiplicative type tag
  expresses the additive target as the codomain of a homomorphism from `G`;
  its multiplication is addition of functionals.
- `normLogarithm_apply` exposes the coordinate formula. Under `1 < q`,
  `normLogarithm_spec` proves the source’s exponential identity for every
  `g : G` and `χ : L`.
- `normLogarithm_ker` proves, under `1 < q`, equality of the homomorphism’s
  actual kernel with `commonNormKernel (fun χ => (ν χ).toMul)` from
  `Langlands.Representation.Plancherel.UnramifiedCharacters`. Thus the
  construction uses exactly the norm-one subgroup already used to define
  the generic unramified-character group.
- `normLogarithm_eq_intValuation` compares with a given homomorphism
  `v : G →* Multiplicative (L →+ ℤ)`. Its explicit premise is the pointwise
  normalization identity
  `q ^ (-((v g).toAdd χ : ℝ)) = ν χ g` for all `g` and `χ`, with the same
  real coercion of norm values. The conclusion identifies each real logarithm
  coordinate with the cast of the integer coordinate. It constructs neither
  `v` nor a lattice theorem. This is an internal comparison explaining how the
  two cited source formulas agree once the actual valuation is supplied.

The implemented proofs use `Real.log_mul` for additivity, positivity of unit
values and `Real.log_pos` for the kernel calculation, and the real
exponential/logarithm identities for the defining relation and its uniqueness.
Additivity in `L` follows from the given family’s additive law; the
homomorphism law in `G` follows from each norm character’s multiplicativity.
The kernel proof applies the numerical zero criterion at every character and
uses extensionality for additive homomorphisms. The integer comparison is the
numerical uniqueness result applied to the displayed normalization premise.

For the intended specialization, `L` must be the actual group of rational
algebraic characters of the given group scheme, and `ν χ g` must be the actual
normalized absolute value of its evaluation on rational points. The existing
algebraic-group program supplies that character/evaluation interface; this
module does not redefine it. Supplying and comparing that family, and the
integer-valued valuation homomorphism, remain separate obligations.
Waldspurger’s target is the real dual of the real scalar extension of the
split-center character lattice. This file uses the additive real dual of `L`;
comparison with that target requires the actual restriction and scalar-extension
identifications and is not asserted here.

This contribution closes the generic numerical and homomorphism construction
only. It does not prove openness or closedness of the common kernel, containment
of compact or derived subgroups, an integral full-rank image lattice, finite
index of the split-center image, finiteness of the resulting quotient, a complex
or unitary character torus, or any Haar normalization. It supplies no
rational-point topology and makes no claim that the whole retained
Renard V.2.3–V.2.6 obligation has been discharged.
