# Injectivity of the normalized character of trivial isogeny pullbacks

`Langlands.AbelianScheme.TrivialPullbackCharacterInjectiveStatement.{u}` is the
proposition

```text
∀ (S : Scheme.{u}) (A B : AbelianScheme S) (f : A ⟶ B), IsIsogeny f →
  ∀ (T : Over S),
    Function.Injective
      (trivialHomPullbackClassCharacter f (T := T) (universalGlobalFunctions A)).
```

## Meaning of the terms

All of the following are already published:

- `AbelianScheme S` is the bundled abelian scheme over an arbitrary base scheme
  `S`.
- `IsIsogeny f` says that the underlying scheme morphism `hom f` is finite, flat
  and surjective (`isIsogeny_iff`).
- `T` is an arbitrary scheme over `S`. It may be empty, nonreduced, or have
  inseparable residue field extensions.
- `f_T := (homFamilySpaceMap f).app T` is the actual map
  `T ×_S A ⟶ T ×_S B` of relative families.
- `TrivialHomPullbackClasses f T` is the quotient, by isomorphism, of the full
  subcategory of actual line bundles `L` on `T ×_S B` for which some
  isomorphism `f_T^* L ≅ O_{T ×_S A}` exists (`HasTrivialHomPullback`). No
  trivialization is part of the data.
- `trivialHomPullbackClassCharacter f h` sends such a class to its normalized
  intrinsic character. This is an element of the published Cartier character
  presheaf of the kernel `kernelCommGroupScheme f`, evaluated at `T`.

The character is defined in `KernelCharacterIndependence` and
`IntrinsicKernelCharacter`. On a point `k` of the kernel over a scheme `U`
over `T`, its value is the unit on `U` that descends, via `h`, the scalar
`kernelTranslationScalar f α a k`. That scalar is the comparison scalar
`equalCompositeUnitAut` of the published trivialization `α` along the pair
formed by the ordinary change-of-parameter map and the kernel translation
`kernelShear f a k`. The published lemmas there show that the character does not
depend on `α` or on the representative of the class. The argument `h` is the
published theorem `universalGlobalFunctions A`: global functions on `T ×_S A`
are pulled back from `T`, universally in `T`.

The statement says that two actual line bundles on `T ×_S B` with trivial
`f_T`-pullback and equal normalized characters are isomorphic. It is the
injectivity half of the target `FieldTrivialPullbackCharacterBijectiveStatement`
in `FieldIsogenyKernelDescentStatements`. It is stated over an arbitrary base
`S` rather than only over `Spec k`. The field case is the instance
`S = Spec k`.

## Source and provenance

This is a derived statement. Edixhoven, van der Geer and Moonen, *Abelian
Varieties* (preliminary version), Chapter VII, Proposition (7.4), printed
pp.99–100 (PDF pp.103–104), state the following. Let `G` be a commutative
finite locally free group scheme acting freely on `X`, with quotient
`p : X → Y`, and suppose `f_*(O_{X_T}) = O_T` for all `T`. Then the character
`δ_T`, from isomorphism classes of line bundles `L` on `Y_T` with
`p^* L ≅ O_{X_T}` to `G^D(T)`, is an isomorphism. In particular it is
injective.

Here `X = A`, `Y = B`, `p = f` and `G = ker f`, acting by translation. The
hypothesis on global functions is the published `universalGlobalFunctions A`.
`δ_T` is the published normalized character, defined directly from `f_T` and
kernel translations rather than through a quotient construction. The injectivity
proved in EGM uses only full faithfulness of descent along the faithfully flat
map `f_T` (Proposition (7.2) there). The base-independent form needs only that
`f_T` is affine, flat and surjective. These properties follow from `IsIsogeny f`
by base change, over any `S`.

## Proof obligation

This file supplies a proposition definition, not a proof. The intended proof
factors every pair of maps with equal composite along `f_T` through an ordinary
map and a kernel translation. It then applies
`UnitCocycleDescentUniquenessStatement` in `UnitCocycleDescentStatements` to
`f_T`, once that statement has a proof.
