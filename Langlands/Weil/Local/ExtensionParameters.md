# Restriction and induction along an extension of p-adic fields

Worker 17 authored this construction module. It imports Worker 53's
`Langlands.Weil.Local.ExtensionWeilRange` and `Langlands.Weil.Local.Parameters`, and
`Langlands.WeilDeligne.InductionAlong`.

Fix a prime `p`, p-adic fields `F` and `E` in independent universes, and an
algebra homomorphism `f : F.Carrier →ₐ[Padic p] E.Carrier`, the abstract form
of a finite extension `E/F`. Write `ι = extensionWeilMap F E f : W_E → W_F`
for the actual map of local Weil groups, `I_F`, `I_E` for the actual inertia
subgroups `localInertia`, `‖·‖_F`, `‖·‖_E` for the norm characters
`localNormCharacter`, and `[E : F]` for `extensionDegree F E f`. This module
specializes the generic restriction and induction constructions of the
Library to `ι`. Restriction goes from `W_F` to `W_E`; induction goes from
`W_E` to `W_F`.

## Facts about the Weil map used here

- The imported instance `extensionWeilRange_finiteIndex` registers Worker 53's
  proof `extensionWeilMap_range_finiteIndex` that the range of `ι` has finite
  index in `W_F`; induction uses this shared instance.
- A private lemma proves that `I_F` is open in `W_F`: it is the preimage of
  the identity under the continuous degree map `localDegree F` to the discrete
  group `Degree`.
- `extensionWeilMap_inertia` states `ι(I_E) ⊆ I_F`, the `mpr` direction of
  Worker 53's `extensionWeilMap_mem_localInertia : ι w ∈ I_F ↔ w ∈ I_E`.
- `localDegreeInt_extensionWeilMap_ne_zero` states that if `w ∈ W_E` has
  nonzero integer degree, so has `ι w`. This holds because Worker 53's
  `localDegreeInt_extensionWeilMap` multiplies the degree by the residue
  degree, and `extensionResidueDegree_pos` shows the residue degree is
  positive.
- `localNormCharacter_comp_extensionWeilMap` restates Worker 53's
  `localNormCharacter_extensionWeilMap`, `‖ι w‖_F = ‖w‖_E`, for the composite
  monoid homomorphism.

## Restriction from `W_F` to `W_E`

Weil representations.

- `extensionRestrict A` is `FiniteRepresentation.restrict ι A`: the same space
  with `W_E` acting through `ι`. `extensionRestrictFunctor` is Mathlib's
  restriction functor along `ι`. `rank_extensionRestrict` states that the
  rank does not change.
- `extensionRestrictClass` and `extensionRestrictClassOfRank n` act on genuine
  isomorphism classes, all of them or those of rank `n`.
- `isContinuous_extensionRestrict` proves that restriction keeps continuity for
  the usual topology on `End V`, because `ι` is continuous.
  `extensionContinuousRestrict` acts on continuous objects.
- `extensionOpenInertiaRestrict` and `extensionOpenInertiaRestrictClass` act on
  representations with open inertia kernel, in the separate algebraic
  convention. They apply the published `openInertiaRestrict` with
  `ι(I_E) ⊆ I_F` and the continuity of `ι`.

Weil–Deligne pairs.

- `extensionWDRestrict A` takes the published restriction
  `WeilDeligneRepresentation.restrict ι A`. That pair is covariant for
  `‖·‖_F ∘ ι`; `ofNormEq` restates it for `‖·‖_E` using
  `localNormCharacter_comp_extensionWeilMap`. Carrier, action and monodromy
  do not change (`extensionWDRestrict_monodromy` is `rfl`).
  `extensionWDRestrictFunctor` is the composite of the two published functors;
  `extensionWDRestrictEquiv` transports pair equivalences;
  `rank_extensionWDRestrict` states that the rank does not change.
- `extensionWDRestrictClass` and `extensionWDRestrictClassOfRank n` act on
  genuine pair classes, all of them or those of rank `n`.
- `extensionParameterRestrict`, `extensionParameterRestrictClass` and
  `extensionParameterRestrictClassOfRank n` act on parameters, that is, pairs
  with open inertia kernel. The open-kernel certificate comes from the
  published `parameterRestrict`.
- `isLocalFrobeniusSemisimpleParameter_extensionWDRestrict` proves that
  restriction keeps Frobenius-semisimple parameters. Every `w ∈ W_E` of nonzero
  degree maps to an element of nonzero degree in `W_F`, and on the same space
  its action is the action of `ι w`. So semisimplicity of every nonzero-degree
  operator of `W_F` gives it for `W_E`.
  `extensionFrobeniusSemisimpleRestrict`,
  `extensionFrobeniusSemisimpleRestrictClass` and
  `extensionFrobeniusSemisimpleRestrictClassOfRank n` act on the objects, on
  the genuine classes and on the rank-`n` classes of
  `LocalFrobeniusSemisimpleParameterClassesOfRank`.

## Induction from `W_E` to `W_F`

Induced spaces live in the universe `max u w`, where `u` is the universe of
`F` and `w` the carrier universe, because they consist of functions on `W_F`.

- `extensionInduce A` is the published `FiniteRepresentation.induceAlong ι A`:
  induction from the range `ι(W_E)` of the representation transported along
  the inverse of `W_E ≃* ι(W_E)`. `extensionInduceFunctor`,
  `extensionInduceEquiv` and `extensionInduceClass` give the functor, the
  transport of equivalences and the class map.
- `rank_extensionInduce` proves that the rank of the induced representation is
  `[E : F] * rank A`. It combines `rank_induceAlong` with Worker 53's
  `extensionWeilMap_range_index`, which identifies the index of `ι(W_E)` with
  `[E : F]`. `extensionInduceClassOfRank n` therefore sends rank-`n` classes
  to rank-`[E : F] * n` classes.
- `extensionOpenInertiaInduce` and `extensionOpenInertiaInduceClass` act on
  representations with open inertia kernel. They use that `ι` is an open
  embedding (`extensionWeilMap_isOpenEmbedding`), that `I_F` is open, and that
  `ι w ∈ I_F` implies `w ∈ I_E`.
- `extensionWDInduce A` is the published `WeilDeligneRepresentation.induceAlong`
  with the norm compatibility `‖ι w‖_F = ‖w‖_E`. Its monodromy is
  `N_ind(φ)(g) = ‖g‖_F N(φ(g))`, so nonzero monodromy is kept.
  `extensionWDInduceFunctor`, `extensionWDInduceEquiv`,
  `extensionWDInduceClass` and `extensionWDInduceClassOfRank n` follow;
  `rank_extensionWDInduce` gives rank `[E : F] * rank A`.
- `extensionParameterInduce`, `extensionParameterInduceClass` and
  `extensionParameterInduceClassOfRank n` act on parameters, from rank `n` to
  rank `[E : F] * n`. The open-kernel certificate is the published one for
  `parameterInduceAlong`.

## Source correspondence and provenance

Tate, *Number theoretic background*, Corvallis Part II, source ID
`tate-1979-number-theoretic-background`, retained PDF SHA-256
`c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`:

- §2.1, printed pages 9–10 (PDF pages 18–19): for a finite separable extension
  `E/F` there are restriction `res_{E/F} : R(W_F) → R(W_E)` and induction
  `ind_{E/F} : R(W_E) → R(W_F)`, "for we can identify `W_E` with a closed
  subgroup of finite index in `W_F`". Here the identification is the actual
  map `ι` and the operations are defined on representations and on genuine
  isomorphism classes.
- §1.4.6, printed page 7 (PDF page 16): the norm of `W_F` restricts to the norm
  of `W_E`. This is the norm compatibility used for pairs.
- §4.1.2, printed page 20 (PDF page 29): a representation of the
  Weil–Deligne group is a pair `(ρ, N)` with `ρ(w) N ρ(w)⁻¹ = ‖w‖ N` and
  kernel of `ρ` containing an open subgroup of inertia. §4.1.3 defines
  Frobenius semisimplicity.

Tate does not write out restriction or induction of pairs, nor the
preservation statements above. These are derived constructions and proved
obligations: restriction of pairs keeps `N`; induction of pairs uses the
weighted monodromy of the published generic induction; the inertia, norm,
degree and rank facts come from Worker 53's `ExtensionWeil`.

## Scope

This module defines operations and proves only the certificates their
targets need: continuity, open inertia kernel, Frobenius semisimplicity for
restriction, and ranks. It does not assert Frobenius reciprocity, a Mackey
formula, compatibility of induction with other operations, continuity of
induced representations in the usual topology, or that induction keeps
Frobenius-semisimple parameters. Irreducibility is not claimed to be
preserved in either direction.
