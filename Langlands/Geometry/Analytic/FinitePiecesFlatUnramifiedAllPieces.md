# Flatness and unramifiedness on finite pieces extend to all pieces

The Library has two formulations of a pointwise condition `Q` on a strong map between
affinoid atlas presentations, at a source point `y`:

- `HasFinitePiecesAt Q y`: there are open neighborhoods `V` of `y` and `U` of its image
  over which the map is finite, and one finite family of recognized affinoid target pieces
  in `U` through the image point, whose union is a neighborhood of it, over each of which
  the induced finite affinoid map has `Q` at `y`;
- `HasAllPiecesAt Q y`: the same open finite neighborhoods, with `Q` over *every* recognized
  affinoid target piece in `U` through the image point.

For flatness at a point these are the Library's recognized-piece forms of Berkovich (1993),
Proposition 3.2.3(a) and (b). Definition 3.2.5 applies that criterion on open
neighborhoods of a quasifinite morphism. The Library's `StrongHom.IsEtale` is its
finite-piece formulation of the unramified-and-flat condition of Definition 3.3.4. It
requires `IsUnramifiedAt` and `IsFlatAt` at every point, each a `HasFinitePiecesAt`
condition with its own neighborhoods and family. For unramifiedness the pointwise test is
the support description of Proposition 3.3.7(b): the point lies outside the support of the
module of differentials of the finite piece. `StrongHom.IsEtaleAllPieces`, used by the
étale site, asks for both conditions over all recognized pieces.

The Library proves `IsEtaleAllPieces.isEtale`. It also proves the finite-to-all upgrade for
the joint condition `IsEtaleAtPoint` (`finitePiecesEtaleAllPieces`), but that upgrade needs
one family carrying both conditions. This module proves the upgrade separately for the two
pointwise conditions:

- for flatness, it is the recognized-piece version of Proposition 3.2.3(a) ⇒ (b);
- for unramifiedness, it is a derived analogue, not a statement of Berkovich. It is proved
  from preservation and reflection of unramifiedness across nested recognized pieces, by
  base change of differentials and faithful flatness.

Consequently `IsEtale` implies `IsEtaleAllPieces`, and the two agree
(`isEtale_iff_isEtaleAllPieces`).

The proofs split the Library's proofs for `IsEtaleAtPoint` into their flat and unramified
halves. The Library proofs split are the two pushout lemmas
`isEtaleAtPoint_of_rightMap_of_tensorComparison` and
`rightMap_isEtaleAtPoint_of_tensorComparison`, `isEtaleAtPoint_comp_boundedEquiv_iff`,
`recognizedNested_isEtaleAtPoint_iff` and `finitePiecesEtaleAllPieces_of_flatness_tensor`.
The prime-level reflections are the Library's `TensorStalkBaseChange.flat_atPrime_reflect`
and `TensorStalkBaseChange.formallyUnramified_atPrime_reflect` (module
`AffineAnalytificationFiniteGermAssembly`).

## Declarations

### Affinoid pushouts (`AffinoidPushout`)

Here `f : A → B` and `g : A → C` are bounded maps, and `rightMap f g` and `leftMap f g` are
the legs of their actual affinoid pushout.

- `isFlatAtPoint_of_rightMap`: if `g` and `leftMap f g` are algebraically flat, then flatness
  of `rightMap f g` at `x` gives flatness of `f` at the image of `x`. This uses
  `flat_atPrime_reflect`.
- `isUnramifiedAtPoint_of_rightMap_of_tensorComparison`: the same for unramifiedness. The
  hypotheses are that the ordinary tensor comparison is bijective, `f` is of finite type and
  `leftMap f g` is flat. This uses `formallyUnramified_atPrime_reflect`. The bijective
  comparison makes the algebraic pushout available, and base change of differentials then
  applies.
- `rightMap_isFlatAtPoint_of_tensorComparison` and
  `rightMap_isUnramifiedAtPoint_of_tensorComparison`: the converse preservation statements.
  Both need a bijective tensor comparison, and the unramified one also needs `f` of finite
  type.

### Bounded equivalences (`BoundedAlgHom`)

- `isFlatAtPoint_comp_boundedEquiv_iff` and `isUnramifiedAtPoint_comp_boundedEquiv_iff`
  (the latter for maps of finite type): composing with a bounded algebra equivalence `e` of
  the target preserves and reflects the pointwise condition, at the point corresponding
  under `e.spectrumHomeomorph`.

### Strong maps (`AffinoidAtlasPresentation.StrongHom`)

- `recognizedNested_isFlatAtPoint_iff` and `recognizedNested_isUnramifiedAtPoint_iff`:
  consider nested recognized inverse-image squares, with `P ⊆ P₀` over `W ⊆ W₀`, `P` the
  inverse image of `W` in `P₀`, and the piece over `W₀` finite. The pointwise condition of
  the small piece at `t` is equivalent to that of the large piece at the restriction of `t`.
  Both lemmas take the Library's `Domain.FlatnessStatement` and
  `FiniteTensorComparisonStatement` as explicit hypotheses.
- `hasAllPiecesAt_of_hasFinitePiecesAt_of_nested`: a general finite-to-all lemma. Its
  hypothesis is that `Q` is invariant across nested recognized pieces, in the form of the two
  lemmas above. Under that hypothesis, `HasFinitePiecesAt Q y` implies `HasAllPiecesAt Q y`.
  The proof follows `finitePiecesEtaleAllPieces_of_flatness_tensor`. Take an arbitrary
  target piece `W` through the image point, and choose a recognized piece `Z` inside both
  `W` and a piece `W₀` of the finite family. Its actual finite inverse image is supplied by
  `IsFiniteOver`. Transport `Q` from `W₀` down to `Z`, then up to `W`. The source points
  are identified by injectivity of the recognized charts.
- `IsFlatAt.isFlatAtAllPieces`: the recognized-piece version of Proposition 3.2.3(a) ⇒ (b)
  for flatness. It is the general lemma with `recognizedNested_isFlatAtPoint_iff`, using the
  published proofs `Domain.flatness` and `AffinoidPushout.finiteTensorComparison`.
- `IsUnramifiedAt.isUnramifiedAtAllPieces`: the derived analogue for unramifiedness, with
  `recognizedNested_isUnramifiedAtPoint_iff` and the same published inputs.
- `IsEtale.isEtaleAllPieces`: `g.IsEtale → g.IsEtaleAllPieces`. The open neighborhood in
  `IsEtaleAtAllPieces` is the whole space.
- `isEtale_iff_isEtaleAllPieces`: `g.IsEtale ↔ g.IsEtaleAllPieces`. The converse direction
  is the Library's `IsEtaleAllPieces.isEtale`.

## Scope

The field is complete, ultrametric and normed; no nontriviality is assumed. Both
presentations share the universe profile `{u, v, w}`, as in the Library's definitions of
`HasFinitePiecesAt` and `HasAllPiecesAt`, and the results hold for every such profile.
