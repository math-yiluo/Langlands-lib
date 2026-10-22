# Prime-adic Tate twists from actual roots of unity

The namespace `Langlands.TateTwist` constructs the compatible sequences of actual
roots of unity in a commutative ring, their prime-adic scalar action and
rationalization. Ring homomorphisms act coordinatewise. Ring automorphisms, and
in particular field automorphisms over a base field, therefore act on the twist.
No compatible primitive roots or basis of the twist is chosen.

## Source and provenance

The original source is Edixhoven, van der Geer and Moonen, *Abelian Varieties*
(preliminary version), Chapter X, (10.8), printed p.144 (PDF p.148). It defines
`Z_ell(1)` as the inverse limit of `mu_(ell^n)(k_s)` with the power-`ell`
transitions, and identifies the natural Galois action with the cyclotomic
character. The compatible-sequence scalar formula appears in (10.2), and
rationalization in (10.3), both on printed p.142 (PDF p.146).

The registered source is
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, with SHA-256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.
These passages were read in the retained original PDF; there is no
source-specific errata file in the current Library.

This is derived infrastructure: the elementary construction is generalized from
the source's separable-closure field, with `ell` distinct from the
characteristic, to arbitrary commutative rings. Such rings need not have enough
roots, and the resulting module need not have rank one. We construct the actual
roots as Mathlib's subgroup `rootsOfUnity n R` of `R`'s units, rather than
assuming a family of torsion groups. Mathlib's
`NumberTheory/Cyclotomic/CyclotomicCharacter.lean`, in particular
`cyclotomicCharacter.spec`, supplies the proved character formula used below.
The elementary divisibility-transition proof pattern is adapted from Worker
143's published `Langlands.AbelianScheme.Tate.Integral`; the scalar and universal
lift pattern follows Worker 92's prime-adic construction. This file imports only
Mathlib and does not depend on either project's pending candidate.

## Finite levels and transitions

For a commutative ring `R`, `Level R n` is `Additive (rootsOfUnity n R)`.
Thus its elements are actual units `zeta` satisfying `zeta^n = 1`; addition in
this type is multiplication of roots. `toUnit` is the injective underlying-unit
homomorphism, written additively. `level_nsmul_eq_zero` proves annihilation by
`n`, and `levelZModModule` uses it to give the canonical `ZMod n` action.
For positive `n`, `toUnit_zmod_smul` identifies the scalar action by `a` with
the power `a.val` on units. Each level carries the discrete topology.

For `h : n | m`, `transition R h` is the power `m / n` homomorphism.
`transition_self` assumes `0 < n`. `transition_comp` proves the composition
law, and `transition_zmod_smul` proves compatibility with reduction of scalars.
The implementation uses `(m / n) * n = m` to check membership and the natural
number quotient-product identity for composition.

## Integral and rational twists

Here `p` denotes any prime (the source's `ell`), with assumption
`[Fact p.Prime]`. It need not be the residual characteristic of another field.
`levelModule R p n` restricts scalars along
`PadicInt.toZModPow n : Z_p -> ZMod (p^n)`.
`transition_smul` proves that transitions are `Z_p`-linear, using compatibility
of these reduction maps. `toUnit_transition_succ` identifies the transition
from `p^(n+1)` to `p^n` with the power `p` on the underlying units.

`coherent R p` is the submodule of the product of the levels defined by
successive compatibility. Its underlying type is `Integral R p`. In
multiplicative notation an element is a sequence `(zeta_n)` satisfying
`zeta_n^(p^n) = 1` and `zeta_(n+1)^p = zeta_n`. Level zero is the actual
one-element group of first roots of unity. The module law is coordinatewise,
and `evaluation_smul` records the reduction of a `Z_p` scalar at each level.

`evaluation` is the linear coordinate projection and `evaluation_transition`
is its compatibility equation. `lift`, `evaluation_lift` and `lift_unique`
provide the universal linear map from any module equipped with compatible
linear maps to these actual levels. The uniqueness proof is coordinatewise
extensionality. This is a universal property in modules, not a claim about a
scheme-theoretic inverse limit.

The topology on `Integral` is the subspace topology from the product of the
discrete levels. It is a topological additive group. `continuous_evaluation`
and `continuous_lift` give the corresponding coordinatewise continuity facts.
No compactness assertion or joint continuity of scalar multiplication is made.

`Rational R p` is `Q_p tensor_[Z_p] Integral R p`, with its induced
`Q_p`-vector-space structure. This places the coefficient field first in the
tensor product, the usual scalar-extension convention, reversing the displayed
order in source (10.3). No rational topology or rank assertion is included.

## Natural actions and their character

`levelMap` uses Mathlib's `restrictRootsOfUnity` to act on actual units by a
ring homomorphism `f : R -> S`. `levelMap_transition` follows from preservation
of powers, and `levelMapLinear` follows from compatibility of additive maps
with residue scalars. `map` is their universal lift.
`evaluation_map`, `map_id` and `map_comp` establish its coordinate formula,
identity and composition laws. `continuous_map` uses the discrete levels and
the product topology. `rationalMap` is scalar extension, with its pure-tensor,
identity and composition laws proved using Mathlib's base-change lemmas.

`mapEquiv` obtains the inverse from the inverse ring isomorphism.
`automorphismAction R p` is a group homomorphism from ring automorphisms to
`Z_p`-linear automorphisms of the integral twist; its multiplication order is
ordinary composition. `rationalAutomorphismAction` extends these linear
equivalences to `Q_p`. Its formula on pure tensors is
`rationalAutomorphismAction_tmul`. Each fixed integral automorphism is
continuous by `continuous_automorphismAction`; this does not assert a jointly
continuous action of the automorphism group.

With the additional assumptions `[IsDomain R]` and
`[forall n, HasEnoughRootsOfUnity R (p^n)]`, the lemma
`automorphismAction_eq_cyclotomic_smul` proves that `f` acts on every element
by the scalar `(cyclotomicCharacter R p f).val`. The proof applies
`cyclotomicCharacter.spec` to each actual root and uses `toUnit_zmod_smul`.
The enough-roots hypothesis is essential to using this Mathlib character
formula; the natural action is defined without that hypothesis.

For fields `K`, `L` and a `K`-algebra structure on `L`, `galoisAction` and
`rationalGaloisAction` restrict the preceding actions to the actual group
`Gal(L/K)` via its ring automorphism homomorphism. These definitions may in
particular be applied to a separable closure. They do not identify this group
with the fundamental group of a scheme or construct a relative local system.

## Remaining geometric obligations

This unit supplies the actual pointwise twist, not a construction of the
multiplicative group scheme or of the group schemes `mu_n`, nor their
identification with the preceding roots of unity. Rank one, freeness,
finite-level cardinality and profiniteness are not proved here. The source's
rank-one conclusion over a separable closure away from the characteristic
remains separate. Relative geometric monodromy, full and away-from-prime twists,
and Weil pairings from duality of actual torsion kernels remain further units
of the parent task. No arbitrary bilinear pairing is introduced here.
