# Direct images of line bundles with geometric fibre cohomology in degree zero

This module proves cohomology and base change for a line bundle on a smooth
proper morphism over an arbitrary base scheme, from a hypothesis on the
geometric fibres formed with Mathlib's chosen fibre products. It contains three
theorems in the namespace `Langlands.AlgebraicGeometry.Modules.DerivedSections`.

## `nonempty_relativeCohomology_iso_chosenPullback`

Let `f : X ⟶ S`, `b : Spec R ⟶ S`, and let `h : IsPullback q f' f b` be any
pullback square with top `q : X' ⟶ X` and side `f' : X' ⟶ Spec R`. For a
module `M` on `X` and every degree `n`, the relative cohomology
`(relativeCohomology f' n).obj (q^* M)` is isomorphic to the relative cohomology
of `pullback.fst f b`^* `M` along the chosen projection `pullback.snd f b`.

Proof. `h.isoPullback` is an isomorphism `e : X' ≅ pullback f b` with
`e.hom ≫ pullback.fst f b = q` and `e.hom ≫ pullback.snd f b = f'`. After
substituting these equations, the isomorphism is the composite of
`relativeCohomology` applied to the published composition isomorphism
`Scheme.Modules.pullbackComp e.hom (pullback.fst f b)` and the published
transport `relativeCohomologyPullbackIso e (pullback.snd f b)` from
`SchemeIsoCohomology`.

## `geometricFibreCohomologyDegreeZero_of_isPullback`

Assume `hfib`: for every algebraically closed field `k` (in universe `u`) and
every morphism `b : Spec k ⟶ S`, the pullback of `L` to the chosen fibre
product `pullback f b` has zero `relativeCohomology` along `pullback.snd f b` in
every positive degree, and degree-zero cohomology of `k`-dimension `r`. Then for
every pullback square `hx : IsPullback p fR f x` with `x : Spec R ⟶ S`, the
published predicate `GeometricFibreCohomologyDegreeZero fR (p^* L) r` of
`FibreCohomologyBaseChange` holds.

Proof. That predicate quantifies over a field `k`, a ring map `φ : R ⟶ k`, and
a pullback square `hp'` of `fR` along `Spec.map φ`. Pasting `hp'` with `hx`
gives a pullback square of `f` along `Spec.map φ ≫ x`. The previous theorem,
composed with `Scheme.Modules.pullbackComp p' p`, identifies each cohomology
module of the pulled-back bundle with the corresponding module of the chosen
fibre over `Spec.map φ ≫ x`. Vanishing is transported along these isomorphisms
with `IsZero.of_iso`, and the dimension with `LinearEquiv.finrank_eq`.

## `pushforward_isLocallyFreeOfRank_and_isIso_of_geometricFibres`

Let `f : X ⟶ S` be smooth and proper, with `S` arbitrary, let `L` be a line
bundle on `X`, and let `r : ℕ`. Under the hypothesis `hfib` above, the direct
image `(Scheme.Modules.pushforward f).obj L.obj` is locally free of rank `r`
(`Langlands.Scheme.Modules.IsLocallyFreeOfRank`), and for every pullback square
`h : IsPullback p f' f b` with arbitrary `b : S' ⟶ S`, the published canonical
sheaf comparison `pushforwardBaseChange b f f' p h.w L.obj` is an isomorphism.

Proof. The published sheaf-level endpoint
`pushforward_isLocallyFreeOfRank_and_isIso_pushforwardBaseChange`
(`DirectImageAffineCriterion`) reduces both conclusions to affine charts: for
every pullback square of `f` along `x : Spec R ⟶ S`, the pulled-back sections
must be finite projective of constant rank `r` with invertible canonical scalar
base change. On such a chart, `fR` is smooth and proper by stability of these
properties under base change. The published theorem
`sections_of_geometricFibreCohomologyDegreeZero` (`FibreCohomologyBaseChange`)
gives exactly these four properties from
`GeometricFibreCohomologyDegreeZero fR (p^* L) r`, which the previous theorem
supplies.

## Provenance

These are internal adapters between published Library results. The
mathematical content (cohomology and base change from geometric fibres with
cohomology only in degree zero) is in the published modules
`FibreCohomologyBaseChange` and `DirectImageAffineCriterion`; this module only
transports the fibre hypothesis from Mathlib's chosen fibre products to
arbitrary pullback squares and to arbitrary bases.
