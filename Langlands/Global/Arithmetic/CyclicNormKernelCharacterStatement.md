# Hecke characters with norm kernel for cyclic extensions

This is a proposition definition, derived from global reciprocity and elementary
character theory of finite cyclic groups. It does not supply a Lean proof.
Its formulation follows the shared draft of Worker 96 for Task 7345.

## Sources and provenance

- J. Neukirch, *Algebraic Number Theory*, Grundlehren 322, Springer (1999),
  Chapter VI, Theorem (5.5), printed p. 391 (PDF p. 403), literature
  `neukirch-1999-algebraic-number-theory`. The reciprocity isomorphism is
  `Gal(E/F)^ab ≅ C_F / N_{E/F} C_E`; its inverse is induced by the global norm
  residue symbol with kernel `N_{E/F} C_E`.
- J. Arthur and L. Clozel, *Simple Algebras, Base Change, and the Advanced
  Theory of the Trace Formula*, Annals of Mathematics Studies 120 (1989),
  Chapter III, §4, printed p. 202 (PDF p. 216), literature
  `arthur-clozel-1989-base-change`. They introduce a character `η` of
  `𝔸_F^×` whose kernel is `F^× N_{E/F}(𝔸_E^×)` before Theorem 4.2
  for prime cyclic degree. Chapter III, Lemma 6.3, printed p. 217
  (PDF p. 231), uses a generating character of the same quotient for
  arbitrary cyclic degree.

Neither source packages the three clauses below as this single proposition.
The extension to every cyclic degree and the universal assertions about every
character with the specified kernel follow from Neukirch's reciprocity law by
the derivation below. Arthur–Clozel supplies the intended automorphic use and
the norm-kernel convention.

## Objects and exact statement

`Langlands.Global.HeckeCharacter F` is the existing continuous character group
`IdeleClasses F →ₜ* ℂˣ`, with multiplication and powers taken pointwise.
The definition uses the existing
`Langlands.Global.AdelicFunctoriality.ideleClassNorm (K := F) (L := E)`,
the actual norm `C_E → C_F`.

The existing predicate `η.HasNormKernel E` in
`Langlands/Automorphic/Unramified/CyclicTransferStatement.lean` means

`∀ x : IdeleClasses F, η x = 1 ↔ x ∈ Set.range ideleClassNorm`.

Thus the kernel is exactly the norm image. Since a Hecke character already
factors through `C_F = F^× \ 𝔸_F^×`, this is Arthur–Clozel's condition on
ideles. Their word “vanishing” means taking the multiplicative value `1`.
The existing predicate `χ.IsTrivialOnNorm E` in
`Langlands/Global/HeckeCharacterFiniteOrder.lean` means

`∀ x : IdeleClasses E, χ (ideleClassNorm x) = 1`.

It asserts containment of the norm image in the kernel.

`Langlands.Global.HeckeCharacter.CyclicNormKernelCharacterStatement.{uF, uE}`
quantifies over number fields `F : Type uF` and `E : Type uE`, with
`[Algebra F E]`, `[IsGalois F E]` and `[IsCyclic (E ≃ₐ[F] E)]`.
Writing `n = Module.finrank F E`, it asserts:

1. There exists `η : HeckeCharacter F` with `η.HasNormKernel E`.
2. Every such `η` satisfies `orderOf η = n`.
3. For every such `η` and every `χ : HeckeCharacter F`,
   `χ.IsTrivialOnNorm E ↔ ∃ i < n, χ = η ^ i`.

Here `i` is a natural number. Clause 3 includes `i = 0`, hence the trivial
character. Clauses 2 and 3 together imply that these `n` powers are distinct.
The trivial extension is included: `n = 1` and only the trivial character
occurs. No local-component compatibility is part of this statement.

## Derivation from reciprocity

Let `H = N_{E/F} C_E` and `Q = C_F / H`.
Neukirch VI (5.5) gives `Q ≅ Gal(E/F)^ab`.
The Galois group is cyclic, hence abelian, and has order `n = [E : F]`.
Consequently `Q` is a cyclic group of order `n`.

The norm image `H` is open: the published theorem
`Langlands.Global.AdelicFunctoriality.isOpenMap_ideleClassNorm`
applied to the whole source gives this. Therefore `Q` has the discrete
quotient topology. A character of `Q` pulls back along `C_F → Q` to a
continuous character of `C_F`.

Choose a generator `q` of `Q` and a primitive complex `n`th root of unity
`ζ`. The character sending `q` to `ζ` is faithful. Its pullback `η`
has kernel precisely `H`, proving the mathematical assertion in clause 1.

For any `η` with this kernel, its induced character on `Q` is faithful.
Its value at `q` has order `n`, so the induced character, and hence `η`
under the surjective pullback, has order `n`. This gives clause 2 for
every such `η`.

A character `χ` trivial on `H` factors through `Q`. Its value at `q` is an
`n`th root of unity, hence is `η(q)^i` for some `0 ≤ i < n`.
The generator determines the character, so `χ = η^i`. Conversely every
power of `η` is trivial on `H`. This proves the equivalence of clause 3.

## Hypotheses and universes

The algebra structure specifies the extension and the norm. The number-field
instances imply that `E/F` is finite dimensional. `IsGalois F E` expresses
normality and separability; together these hypotheses give a finite Galois
extension, the setting of the cited reciprocity theorem, with
`Nat.card (E ≃ₐ[F] E) = Module.finrank F E`.
`IsCyclic (E ≃ₐ[F] E)` makes its abelianization cyclic and allows a faithful
one-dimensional complex character.

The consumers' hypothesis that `σ` generates, expressed by
`∀ τ, τ ∈ Subgroup.zpowers σ`, supplies this cyclicity. In prime degree
the same instance follows from `IsGalois.card_aut_eq_finrank` and
`isCyclic_of_prime_card`. The fields retain the independent universes
`uF` and `uE` of the requested formulation. No changes to the proposed
hypotheses, third clause or universes have been made.

## Library consumers

The following existing declarations in namespace
`Langlands.Automorphic.Unramified` take
`η : HeckeCharacter F` and `η.HasNormKernel E` as premises:

- In `CyclicTransferStatement`: `CyclicPrimeCuspidalLiftStatement`,
  `CyclicPrimeSelfTwistStatement`, `CyclicStableDescentStatement` and
  `CyclicRegularInductionStatement`.
- In `CyclicTransferInputsTCStatement`: `CyclicRegularInductionTCStatement`,
  `CyclicRegularOrbitLiftTCStatement` and `CyclicStableDescentTCStatement`.
- In `IsobaricCyclicTransferStatement`: `CyclicPrimeIsobaricLiftStatement`,
  `CyclicPrimeIsobaricSelfTwistStatement`, `CyclicRegularOrbitLiftStatement`
  and `CyclicStableIsobaricDescentStatement`.

Clause 1 supplies their character premise once proved. Clause 2 specifies
its exact order, while clause 3 identifies all twists by characters trivial
on norms with the powers used in Arthur–Clozel's descent arguments.

## Published ingredients for the future proof

These are possible proof inputs, not additional hypotheses of the proposition.
Besides norm openness, finite norm index is proved by
`Langlands.Global.AdelicFunctoriality.ideleClassNormIndexFinite`.
The global reciprocity quotient can be derived from the published
relative-Weil-group ingredients:

- `Langlands.ClassFieldTheory.Local.localRelativeClassFormation` supplies
  local invariant families with arithmetic normalization;
- `Langlands.ClassField.Global.globalFundamentalClassStatement` supplies
  a compatible global fundamental-class family;
- `Langlands.ClassField.Global.RelativeWeilGroup.relativeWeilTransferReciprocity`
  gives surjective transfer with commutator kernel;
- `Langlands.ClassField.Global.RelativeWeilGroup.transfer_comp_inclusion`
  identifies its restriction to `C_E` with the idele-class norm;
- `Langlands.ClassField.Global.RelativeWeilGroup.projection_surjective`,
  `exact` and `index_range_inclusion` give the extension by `Gal(E/F)`.

The class-formation and relative-Weil results use fields in one universe.
A proof at independent `uF, uE` must also justify universe transport.
This file claims no completed Lean implementation of that composite route.
