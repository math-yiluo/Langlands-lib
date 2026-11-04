# Actual finite Galois descent of a represented unipotent radical

This is an internal construction from the Library's actual finite Galois overlap
components, Galois transport of a represented unipotent radical, and effective
affine group-scheme descent. It supplies a descended affine closed subgroup and
an exact recovery equation. It does not prove existence of a unipotent radical
or maximal-torus conjugacy.

## Inputs and conventions

Let `k` and `L` be fields in an arbitrary common universe `u`, with a `k`-algebra
structure on `L`. Let `G` be a group scheme over `Spec k` whose structural
morphism is affine. Set `p = algebraBaseMap k L`, also named `fieldMap k L` by
the descent API. The input consists of an actual group scheme `U` over `Spec L`,
an actual morphism `i : U ⟶ p*G`, and `hi : IsUnipotentRadical i` with the
Library predicate unchanged. The construction therefore assumes an already
represented radical over `L`; it does not construct that input.

The declarations beginning with `galoisComponentIso` also assume
`FiniteDimensional k L` and `IsGalois k L`. No characteristic, perfection,
infinitude, or splitness restriction is imposed on either field. The overlap is
the actual scheme pullback `Spec L ×[Spec k] Spec L`.

## Component transport and the source datum

The general lemma `Descent.pullIso_canonicalOverlap_eq` identifies the ambient
canonical overlap on any component whose first projection is the identity and
whose second projection is an endomorphism over the base. It is the identity
pullback comparison followed by the inverse canonical transport along that
endomorphism. The proof cancels the canonical transport isomorphism and compares
the two maps into the actual pullback by their original-object and base
projections. `Descent.pullbackComparison_inv_naturality` supplies naturality of
the inverse direct-pullback comparison by cancellation of the forward comparison.

`IsUnipotentRadical.galoisSourceIso_inv_fac` normalizes the previously constructed
radical source transport by the identity pullback. Its equation states that this
normalized inverse source isomorphism commutes with the original inclusion and
the normalized ambient transport.

For each index in `Fin (Module.finrank k L)`, `galoisComponentIso` constructs an
actual isomorphism between the first and second pullbacks of `U` to the
corresponding finite Galois component. It composes direct-pullback comparisons,
the identity comparison, and the inverse `hi.galoisSourceIso` for that component's
field automorphism. `galoisComponentIso_fac` proves that this isomorphism commutes
with `i` and the ambient canonical overlap. The proof uses the preceding
normalized equation and naturality, cancelling the two comparison isomorphisms.

`finiteGaloisOverlap` assembles these isomorphisms over the actual finite
coproduct cover. `finiteGaloisOverlap_fac` proves the assembled inclusion
equation by restriction to every component. `finiteGaloisDatum` is an actual
`Descent.Datum p U`. Its triple-overlap cocycle is proved from that equation by
the Library's closed-subgroup lifting theorem: the third pulled-back inclusion
is monic, so cancellation reduces the source cocycle to the ambient canonical
cocycle. Neither a source cocycle nor a source descent solution is an extra
premise. `compatible_finiteGaloisDatum` expresses compatibility of `i` with this
datum and the ambient canonical datum.

## Effective descent and recovery

The closed inclusion into the affine pullback of `G` proves that `U` is affine.
The field map is flat and surjective. Applying the Library's effective affine
datum and compatible-morphism constructions gives the following actual objects:

- `hi.finiteGaloisSolution` is a solution of the constructed datum. Its object
  `U₀` is a group scheme over `Spec k`, and its isomorphism identifies `p*U₀`
  with the supplied `U` compatibly with the datum.
- `hi.finiteGaloisInclusion : U₀ ⟶ G` is the descended inclusion.
- `baseChange_finiteGaloisInclusion` proves the exact equation
  `(GroupScheme.baseChange p).map hi.finiteGaloisInclusion =
  hi.finiteGaloisSolution.iso.hom ≫ i`.
- `finiteGaloisSolution_isAffine` proves that the underlying scheme of `U₀` is
  affine.
- `finiteGaloisInclusion_isClosedSubgroup` proves that the descended inclusion
  is a closed subgroup. Its pullback is closed by the recovery equation, and
  the Library's affine faithfully flat closed-immersion reflection theorem
  reflects closedness to the base.

These declarations construct an affine closed subgroup with the specified
pullback. This module does not yet assert smoothness, connectedness, unipotence,
normality, or radical greatestness for the descended subgroup. Transport of
those properties, geometric radical existence, splitness results, and the full
rational conjugacy theorem remain separate obligations.
