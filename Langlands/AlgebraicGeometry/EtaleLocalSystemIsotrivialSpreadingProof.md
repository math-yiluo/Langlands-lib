# Spreading isotriviality from the spectrum of a stalk

`Langlands.AlgebraicGeometry.etaleLocalSystemIsotrivialSpreading` proves
`EtaleLocalSystemIsotrivialSpreadingStatement.{u}`. For an arbitrary scheme and a
finitely generated étale local system, a finite étale surjective trivializing
cover over the spectrum of the stalk gives a finite étale surjective trivializing
cover over an open neighbourhood of the point. The construction uses the same
finitely generated abelian group for both trivializations.

This is the spreading step from Brian Conrad, *Reductive group schemes* (2014),
proof of Corollary B.3.6, p. 293, registered as
`conrad-2014-reductive-group-schemes`.

Choose an affine open containing the point and express it as `Spec R`. The stalk
map of the open immersion and the affine stalk isomorphism identify the original
stalk spectrum with the spectrum of the prime localization of `R`. The proof
checks that this identification commutes with the maps to the original scheme.
It transports the given cover and its trivialization along this identification.
`LocalEtaleLimit.ofLocalization` presents the localization spectrum as the
cofiltered limit of basic affine opens through the prime.

`exists_localization_model` applies filtered model existence to the cover, which
is finitely presented. It composes the resulting model over a basic open with
that open immersion and retains the pullback square over `Spec R`.
`exists_finite_etale_surjective_level` descends finiteness, étaleness and
surjectivity separately from the localization and chooses a common stage using
stability under base change. The cover at that stage has affine source by
finiteness.

`exists_open_trivializing_cover` pulls the diagram of basic opens back along the
structural map of that affine source. The resulting affine diagram has the
original covering scheme as its limit. The theorem `exists_level_trivialization`
descends the constant-sheaf isomorphism to some stage of this new diagram.
That stage is the source of the finite étale cover pulled back to the
intersection of the two basic opens. The localization spectrum maps into
the intersection, and its closed point maps to the original point. The proof
takes the open image in the original scheme and transports the cover and the
trivialization to its open subscheme.
