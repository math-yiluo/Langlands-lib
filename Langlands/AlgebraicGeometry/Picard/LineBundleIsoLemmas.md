# Elementary isomorphisms of line bundles

Module `Langlands.AlgebraicGeometry.Picard.LineBundleIsoLemmas` is a helper
module for the proof of
`Langlands.AbelianScheme.FieldDualSchemeMapAdditivityStatement`. It packages
standard isomorphisms of the Library's `LineBundle` objects that later
modules use repeatedly. All declarations are in the namespace
`Langlands.AlgebraicGeometry.Picard.LineBundle`.

## Declarations

* `pullbackCompEqIso f g w L`: for `w : f ≫ g = h`, the isomorphism
  `f^* (g^* L) ≅ h^* L`. It is the Library `pullbackComp` followed by the
  `eqToIso` induced by `w`.
* `pullbackEqIso w L`: for equal morphisms `f = f'`, the isomorphism
  `f^* L ≅ f'^* L` (an `eqToIso`).
* `isoOfPullbackIso i e`: if `i` is an isomorphism of schemes and
  `e : i^* L ≅ i^* M`, then `L ≅ M`. It pulls `e` back along `inv i` and
  uses `pullbackCompEqIso` with `inv i ≫ i = 𝟙` and the Library `pullbackId`.
* `tensorTrivialIso preservation L : L ⊗ O ≅ L` is the Library right unitor
  `tensorRightUnitor` as an isomorphism of line bundles.
* `tensorCommIso preservation L M : L ⊗ M ≅ M ⊗ L` is the Library symmetry
  `tensorComm` as an isomorphism of line bundles.
* `tensorIsoTrivialIso preservation L e`: if `e : M ≅ O`, then `L ⊗ M ≅ L`,
  by the Library `tensorIso` and `tensorTrivialIso`.
* `nonempty_iso_trivial_of_restrict_top L U hU e`: if the open `U` is the
  whole space and the restriction of `L` to `U` is trivial, then `L` is
  trivial. The proof turns the restriction into a pullback along the open
  immersion `U.ι` (`restrictFunctorIsoPullback`), uses that `⊤.ι` is an
  isomorphism, and applies `isoOfPullbackIso`.
* `nonempty_iso_trivial_of_unique L`: on a scheme with exactly one point
  every line bundle is trivial. The Library trivializing open
  `L.trivializingOpen` of the unique point contains every point, so it is
  the whole space, and the previous lemma applies to `L.localTrivialization`.

## Provenance

These are internal formalization constructions and elementary lemmas with no
separate literature source. They use the published line-bundle pullback
comparisons, module tensor unitors and symmetry, and the local
trivializations carried by every `LineBundle`. The schemes are arbitrary in
universe `u`; tensor constructions take the explicit parameter
`preservation : pullbackTensorComparisonIsIsoStatement.{u}`.

Worker 270 drafted the Lean constructions and their original descriptions;
Worker 417 extracted and rechecked this pair with the companion
`RigidifiedCarrierIso` module. Neither module proves a geometric Picard
classification or dual-map additivity theorem.
