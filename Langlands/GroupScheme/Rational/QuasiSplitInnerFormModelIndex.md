# The quasi-split model of an inner form shares its absolute invariants

Module: `Langlands.GroupScheme.Rational.QuasiSplitInnerFormModelIndex`,
namespace `Langlands.GroupScheme.QuasiSplitInnerForm`.

Let `qf : QuasiSplitInnerForm G` be a quasi-split inner-form presentation of a group
`G` over a field `k` (module `Rational/QuasiSplitInnerForm`): a quasi-split model
`qf.model`, a finite Galois carrier `qf.carrier`, and local group isomorphisms
`qf.localIso` from the model to `G` over `Spec qf.carrier`. The model and `G` become
isomorphic over the carrier, so they share every invariant that only depends on the
group over a field extension. This module records three such invariants.

## Declarations

- `baseChangeIso (Ω) (j : qf.carrier →ₐ[k] Ω)`: for a field `Ω` over `k` and a
  `k`-embedding `j` of the carrier, the isomorphism
  `(baseChange (algebraBaseMap k Ω)).obj qf.model ≅ (baseChange (algebraBaseMap k Ω)).obj G`
  obtained by refining `qf.localIso` along `Spec j` (`coverRefinement j`) and taking
  `LocalGroupIso.toBaseChangeIso`.
- `isSimplyConnected_model`: if `G` is simply connected, so is `qf.model`.
- `isAbsolutelyAlmostSimple_model`: if `G` is absolutely almost-simple, so is
  `qf.model`.
- `exists_vertexEquiv_cartan`: for `G` and `qf.model` affine and locally of finite
  type, and any `d : TitsIndexData G` and `dH : TitsIndexData qf.model`, there is a
  bijection `f : dH.Vertex ≃ d.Vertex` with
  `d.cartan (f a) (f b) = dH.cartan a b` for all simple vertices `a, b`.

## Proofs

`isSimplyConnected_model` and `isAbsolutelyAlmostSimple_model` use
`baseChangeIso qf.carrier (AlgHom.id k qf.carrier)`. Simple connectedness passes to
and from a field extension (`isSimplyConnected_fieldExtension_iff`) and along
isomorphisms (`IsSimplyConnected.of_iso`). Absolute almost-simplicity passes up along
the algebraic extension `qf.carrier/k`
(`IsAbsolutelyAlmostSimple.baseChange_of_algebraicExtension`), along isomorphisms
(`IsAbsolutelyAlmostSimple.of_iso`) and down along field extensions
(`IsAbsolutelyAlmostSimple.of_fieldExtension`).

`exists_vertexEquiv_cartan`: choose a `k`-embedding of the carrier in the separable
closure `SeparableClosure k` and let `φ` be the resulting `baseChangeIso`. The pinning
of `dH` gives a split pinning of the model over the separable closure
(`GaloisPinningData.toSplitPinning`); transport it to `G` along `φ`
(`SplitPinning.mapGroupIso`, which keeps its root datum and base). Two split pinnings
of the same group are conjugate by a rational point compatibly with their bases
(`StarActionIndependence.exists_conj_based`); the resulting equivalence of root
pairings maps the base of the transported pinning onto the base of `d.pinning`, and
root pairings are preserved by morphisms of root pairings (`RootPairing.Hom.pairing`).
Restricting the index bijection to the bases gives `f`.

## Provenance

Internal. The statements are the standard facts that an inner form and its quasi-split
inner form are isomorphic over a separable closure, so that simple connectedness,
absolute almost-simplicity and the Dynkin diagram agree; the proof combines the
Library results named above.
