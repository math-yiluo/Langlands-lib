# Arithmetic pair epsilon factors of a local virtual identity

This module is the first part of the finite-place epsilon-factor algebra for the
twisted relative Weil functional equation. Its companion for L-factors is
`RelativeWeilLocalEuler`. Fix a p-adic field `F` and a supplied common-closure
local-constant system: a reciprocity family `eC`, an assignment `ε` and a proof
`hε` of `LocalFactor.NonabelianSystem.IsSystem F eC ε`. Let `V`, `W` be
representations of `W_F`, and let `T` be a continuous representation equivalent to
`V ⊗ W` whose class in the continuous exact virtual group is

`[T] = d [α₀] + Σ_j n_j Ind_{E_j/F}([α_j] - [β_j])`.

Here the `E_j` are standalone p-adic fields with embeddings `g_j : F → E_j`, and
`Ind_{E_j/F}` is induction along `extensionWeilMap F E_j g_j`. The hypothesis is
the same as for `InertiaEuler.arithmeticPairLFactor_eq_of_virtualIdentity`. The
main theorem computes the value that `Correspondence.IsArithmeticPairEpsilonFactor`
tests: the conditional pair epsilon value of every admissible bottom-field datum
`(ψ, μ, A, B, Φ)` for the zero-monodromy pairs of `V` and `W`. It does not assert
that any such datum exists.

## Provenance

The provenance is derived. Tate, *Number theoretic background* (Corvallis 1979),
Theorem (3.4.1), printed pp. 14–15 (PDF pp. 23–24), characterizes the local constants
by their rank-one values and by inductivity in degree zero with the trace characters
`ψ ∘ Tr_{E/F}`. On printed p. 15 he lists the consequences (3.4.2), additivity in `V`,
and (3.4.8),
`ε(V_F, ψ) = ε(V_E, ψ ∘ Tr)` for a degree-zero virtual `V_E` with `V_F` the induced
representation. In the Library these are clauses of `NonabelianSystem.IsSystem`:
`AdditiveRelation`, `InductionRelation` and `RankOneRelation`. The proof applies
these clauses to the supplied identity. The rest is internal bookkeeping. It changes
the carrier universe of virtual classes, it identifies the Weil group of a standalone
extension with the common-closure subgroup of its image, and it commutes restriction
and spectral twists past induction.

## Short exact sequences and carrier universes

- `FiniteRepresentation.isShortExact_of_equiv`: a short exact sequence stays short
  exact after replacing its three terms by equivalent representations, in independent
  carrier universes.
- `FiniteRepresentation.universeModel`, `universeModelEquiv`: a coordinate model of a
  finite-dimensional complex representation in an arbitrary carrier universe. It is
  Library's `VirtualRepresentation.Weil.liftFiniteRepresentation` of the coordinate
  representation `FiniteRep.ofRepresentation`, together with its equivalence to the
  original.
- `ExactGrothendieckGroup.universeClass`, `universeMap`: the ℤ-linear map
  `Continuous.{uG, uA} G → Continuous.{uG, uB} G` of continuous exact virtual groups
  that sends each class to the class of its coordinate model. It is well defined by
  the two previous items.
- `universeMap_ofRepresentation_of_equiv`: `universeMap [A] = [B]` for every
  continuous `B` in the target universe equivalent to `A`.
- `universeMap_characterClass`, `universeMap_continuousRestrict`,
  `universeMap_continuousInduceAlong`: the map preserves character classes and
  commutes with continuous restriction and with induction along an open embedding of
  finite-index range.
- `continuousInduceAlong_ofRepresentation`: the value of induction along an open
  embedding on a genuine class.

The epsilon values of the system live in the carrier universe `max u uE` of
`Assignment.{u, uE}`. The identity is supplied in the carrier universe `max u w` of the
L-factor theorem, and `universeMap` moves it.

## Induction under a change of group

- `FiniteRepresentation.restrictInduceEquiv`: for a group isomorphism `φ : H ≃ G`, a
  finite-index subgroup `S ≤ G` and a finite-index `S' ≤ H` with `φ h ∈ S → h ∈ S'`,
  restricting `Ind_S^G B` along `φ` gives `Ind_{S'}^H` of `B` restricted along `φ`
  on `S'`. The map is `f ↦ f ∘ φ` on equivariant functions.
- `CommonClosure.baseExtension_le`: every finite intermediate field contains the
  bottom field. Using this lemma instead of `bot_le` keeps later rewrites type
  correct.
- `CommonClosure.induce_bot_eq_continuousInduceAlong`: let
  `L = extensionFiniteIntermediate F E g` be the image of a standalone `E`. Then
  common-closure induction from `L` to the bottom field equals the following
  composite: transport to `W_E` by `CommonClosureSpectral.Transport.virtualEquiv`,
  induction along `extensionWeilMap F E g`, and restriction to the bottom-field
  subgroup along `(baseWeilEquiv F).symm`. The proof applies `restrictInduceEquiv`
  and Library's `extensionWeilRange_eq_fixing` on generators.

## Equivalences of tensor products

- `FiniteRepresentation.tensorEquivOfEquiv`: the tensor product of two equivalences
  whose four carriers have independent universes.
- `FiniteRepresentation.restrictTensorIdEquiv`: restriction commutes with tensor
  products, by the identity map.
- `tensorCharacterLineOneEquiv`, `restrictCharacterLineEquiv` and
  `ExactGrothendieckGroup.continuousRestrict_characterClass_comp`: tensoring with the
  trivial character line changes nothing, and restriction of a character line is the
  line of the composite character. The first gives a carrier-universe lift of any
  `V ⊗ W` to which the main theorem applies. The suffix `_comp` keeps the last name
  distinct from a lemma with the same statement in Worker 1795's
  `RelativeWeilBrauer` module, because the final assembly imports both modules.

## Epsilon values (`Langlands.Weil.Local.SystemEpsilon`)

- `imageCharacter F E g χ`: a character `χ` of `W_E`, moved to the common-closure
  subgroup fixing `L` through `extensionImageWeilEquiv`.
- `virtualEquiv_symm_characterClass`: the inverse standalone transport sends the
  class of `χ` to the class of `imageCharacter F E g χ`.
- `continuousRestrict_continuousInduceAlong`: restricting to the bottom field a class
  induced along `W_E → W_F` gives common-closure induction from `L` of its inverse
  transport.
- `virtualTwist_induce`: the spectral twist commutes with common-closure induction,
  by the Library's `CommonClosure.continuousTwist_induce`.
- `twistedValueHom F eC ε hε K ψ μ s`: `x ↦ ε_K(ψ, μ, ω_s x)` as an additive
  homomorphism from the virtual group to `Additive ℂˣ`, where `ω_s x` is the spectral
  twist `virtualTwist F K s x`.
- `twistedValueHom_characterClass`: on a character `χ` its value is the abelian
  epsilon expression of the field character `fieldCharacterEquiv F eC K (ω_s χ)`.
- `twistedValueHom_induce`: on the induction to the bottom field of
  `[a] - [b]` over `L`, its value is the quotient of the two abelian epsilon
  expressions over `L`. They use the trace character `traceCharacter F ⊥ L _ ψ` and an
  arbitrary Haar measure `μL` on `L`. This is `InductionRelation` (Tate (3.4.8)) with
  `RankOneRelation`.
- `conditionalPairEpsilonValue_eq_of_virtualIdentity` (main theorem). Let `A`, `B` be
  bottom-field pairs with `IsBaseRestriction` for the zero-monodromy pairs of `V` and
  `W`, both continuous, and let `Φ` be any geometric Frobenius over the bottom field.
  Let `ψ`, `μ` be any additive character and Haar measure there, and let `μL j` be
  arbitrary Haar measures on the images `L_j` of the `E_j`. Then for every `s`, the
  conditional pair epsilon value is

  `ε_⊥(α₀|_⊥ ω_s, ψ, μ)^d · Π_j (ε_{L_j}(α_j ω_s, ψ ∘ Tr, μL j) /
  ε_{L_j}(β_j ω_s, ψ ∘ Tr, μL j))^{n_j}`.

  Each factor is the abelian epsilon expression of the descended field character.
  The descents are `fieldCharacterEquiv F eC` applied to
  `character F K s * baseRestrictedWeilCharacter F α₀` at the bottom field and to
  `character F L_j s * imageCharacter F E_j g_j α_j` (resp. `β_j`) at `L_j`.
  The proof first shows that `A ⊗ B` has zero monodromy, since `A` and `B` are
  equivalent to restrictions of zero-monodromy pairs, so the value is the system value
  of the spectrally twisted class of `A ⊗ B`. That class is the restriction of
  `universeMap [T]`. The identity, the lemmas above and the additivity of
  `twistedValueHom` then give the formula.

## Scope

The rank-one factors are expressed with the common-closure family `eC` at the
intermediate fields `L_j`. Two further steps remain before they can be compared with
the local components of Hecke characters. They must be moved to the standalone
fields `E_j` and to `PadicAbelian.epsilon`. They must also be compared with geometric
reciprocity candidates. Neither step is in this module.

The continuous character-class restriction identity is reused as
`ExactGrothendieckGroup.continuousRestrict_characterClass` from
`RelativeWeilBrauer`; its group and carrier universes remain independent.
