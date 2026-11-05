# Finite closed equality loci for actual maps into a chosen dual

This is an internal construction from the single-pair closed equality locus in
`Langlands.AlgebraicGeometry.Picard.DualMapEqualityLocus` and the stability of
closed immersions under base change and composition. It makes no new assertion
about the literature.

Let `S : Scheme.{u}`, let `B : Langlands.AbelianScheme S`, and let
`hB : Langlands.AbelianScheme.HasDualScheme B` be the existing geometric
Picard-zero representing datum. For any finite type `I : Type v` and any two
families of actual morphisms
`f g : I → (B.X ⟶ Langlands.AbelianScheme.dualScheme B hB)` in `Over S`, the
definition
`Langlands.AbelianScheme.DualMapEquality.finiteLocus B hB f g` chooses an object
of `Over S`. The choice takes place before a test scheme is supplied. The
instance `finiteLocus_isClosedImmersion` proves that its structure map to `S`
is a closed immersion. For every `T : Over S`, the theorem
`finiteLocus_nonempty_iff` proves precisely

```text
Nonempty (T ⟶ finiteLocus B hB f g) ↔
  ∀ i, (Over.pullback T.hom).map (f i) =
    (Over.pullback T.hom).map (g i).
```

All names below are in `Langlands.AbelianScheme.DualMapEquality`. The
construction includes an empty index type, and the index universe `v` is
independent of the scheme universe `u`. There are no noetherian,
quasi-separatedness, reducedness, projectivity, group-homomorphism or supplied
Hom-representability hypotheses. In particular, every nonreduced scheme over
the base is an allowed test.

The Lean proof constructs finite intersections directly. The definition
`intersection X Y` uses the actual scheme fibre product of the two structure
maps, with its composite map to `S`. Its closed-immersion instance follows
from base-change stability for the first projection and composition with
`X.hom`. The lemma `intersection_nonempty_iff` composes a map with the two
projections in one direction and uses the pullback lift in the other direction.
The required compatibility follows because both input maps are over `S`.

The helper theorem `exists_closed_finiteIntersection` applies finite-set
induction to an arbitrary finite family of closed objects over `S`. For the
empty set it uses `Over.mk (𝟙 S)`, which is terminal over the base and whose
structure morphism is a closed immersion. At an insertion it takes the binary
intersection of the new object and the intersection already constructed, and
uses `intersection_nonempty_iff`. Applying this construction to the whole
finite index type yields a closed object with the simultaneous all-test
factorization property.

The theorem `exists_closed_finiteLocus` applies that helper to the single-pair
objects `locus B hB (f i) (g i)`. The single-pair instance supplies each closed
immersion; `locus_nonempty_iff` identifies each factorization condition with
equality of the actual base-changed morphisms. Finally, `finiteLocus` chooses
the resulting object and the two public results expose its closed immersion
and universal property. Classical choice is used only to select finite
enumeration data and the resulting closed object.

This derivation leaves the chosen-dual datum, all imported Lean/Markdown
pairs, and the Harris representability statement unchanged. It introduces no
polarization inverse or Hom representative and does not address any separate
arithmetic representability or suspended Picard infrastructure obligation.
