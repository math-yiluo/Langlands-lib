# Full compatible reverse identities after actual refinement

This is an internal derivation from actual compatible strong atlas maps, full
affinoid-domain uniqueness, the constructed reverse chart maps, and the
constructed source refinement. It cites no new external assertion and makes no
identification with a numbered result in the literature.

## Actual objects and hypotheses

Work over a complete ultrametric normed field `K : Type u`. Atlas presentations
have ambient spaces in `Type v` and chart indices in `Type w`, independently.
Their chart algebras are presented affinoid algebras, realized as finite
positive-polyradius Tate quotients. Bounded pullbacks are actual
`BoundedAlgHom` values between these algebras.

`CompatibleStrongHom A B` retains a continuous map and every admissible
original-chart bounded pullback, with its spectrum equation, restriction
naturality and intrinsic local coefficient-test compatibility. The notation
`f.comp g` means first `f`, then `g`. Its bounded pullback on any admissible
chart chain is the composite of the two bounded pullbacks in the opposite
direction.

`s.toStrongHom.IsQuasiIso` says that the ambient map of `s` is a
homeomorphism and every admissible supplied pullback satisfies `Represents`
for its actual chart-image locus. That predicate contains closedness, the
exact spectrum image and unique bounded factorization for every
presented-affinoid coefficient test. The cancellation construction below uses
this full uniqueness, not an assertion that a bounded homomorphism is
determined by its action on spectrum points.

## Cancellation of compatible maps

`CompatibleStrongHom.cancel_comp` has arbitrary compatible maps
`f g : A → B` and `s : B → C`. If `s` is a full quasi-isomorphism, it proves

```text
f.comp s = g.comp s  implies  f = g.
```

There is no directedness, domain-closure or upper-cofinality premise. Ambient
injectivity of `s` first gives equality of the continuous maps of `f` and `g`.
For each original source chart, choose an admissible intermediate chart for
`f`; equality of the continuous maps makes it admissible for `g` too. Choose
any admissible final chart for `s` on that intermediate chart. Equality of the
whole composites gives equality of their full bounded pullbacks to this final
chart. Computing both through the chosen chain produces equality after
composition with the bounded pullback of `s`. Its full affinoid-test
uniqueness, via `Represents.hom_ext`, cancels that structural map.
`CompatibleStrongHom.ext_of_pullback` then recovers equality of the entire
compatible maps from the continuous-map equality and one full admissible
bounded pullback per source chart.

`comp_quasiIso_eq_iff` records the equivalence with equality before
postcomposition. `postcompQuasiIsoEmbedding` is the resulting embedding

```text
CompatibleStrongHom A B ↪ CompatibleStrongHom A C,
f ↦ f.comp s.
```

`postcompQuasiIsoEmbedding_apply` records this defining formula. In the
actual category `CompatibleAtlasPresentation`,
`mono_of_isQuasiIso` packages the same cancellation as `CategoryTheory.Mono`.
This is monicity of the complete compatible morphism, not merely injectivity
of its continuous map.

## Reverse followed by the original forward map

Let `f : CompatibleStrongHom A B`, let `hf` be its full quasi-isomorphism
property, and assume `hb : B.atlas.HasAllLocalDomains`. Target full-domain
closure means that every actual target local domain has the ambient locus of
an original target chart. Intrinsic forward coherence is already part of
the compatible map, through `f.coherent`.

Use the preceding reverse construction:

```text
P(j) := there exists i with range(B.chart j) ⊆ f '' range(A.chart i),
R := hf.reverseSubpresentation hb,
r := hf.reverseCompatibleStrongMap f.coherent hb : R → A,
b := B.compatibleSubatlasInclusion P (proved local refinement) : R → B.
```

The locally refining selection `P`, the original algebras and restrictions of
`R`, and every bounded pullback of `r` are constructed in
`CoherentQuasiIsoReverseSubatlas`. They are not output assumptions of this
unit. `r` has inverse ambient map and full bounded reverse-chart pullbacks.
`reverse_comp` proves the whole-map equality

```text
r.comp f = b.
```

The ambient equation is the original homeomorphism's inverse identity.
For any selected source chart `j`, its selection provides an original `A`
chart `i` containing its inverse image. Choose an original `B` chart `q`
containing the complete forward image of `i`. The supplied full reverse
pullback followed by the original forward pullback is precisely the original
bounded restriction from `q` to `j`, by
`reverseChartPullback_comp_pullback`. Thus both compatible maps agree on one
whole admissible bounded pullback per source chart. Full compatible
extensionality gives the stated equality. No source full-domain closure is
used for this direction.

## Forward lift followed by the reverse map

Also assume `ha : A.atlas.HasAllLocalDomains`. The actual source-refinement
construction of `CompatibleStrongSubatlasRefinement` gives

```text
Q(i) := there exists j with P(j) and
        f '' range(A.chart i) ⊆ range(B.chart j),
S := f.toStrongHom.targetSubatlasSource ha P (proved local refinement),
L := f.targetSubatlasLift ha P (proved local refinement) : S → R,
a := A.compatibleSubatlasInclusion Q (proved local refinement) : S → A.
```

Its hypotheses supply the proved relative local refinement of `Q`; no new
source atlas or lifting map is assumed. The lift keeps the original bounded
pullbacks, and `a` keeps the original bounded restrictions. The existing
complete refinement square is `L.comp b = a.comp f`.

`lift_comp_reverse` proves

```text
L.comp r = a.
```

Postcompose both sides by `f`. Associativity and `reverse_comp` turn the
left side into `L.comp b`; the already proved complete refinement square
identifies it with `a.comp f`. Apply `cancel_comp hf` to conclude. This
argument cancels entire bounded maps using full affinoid-test uniqueness and
does not infer bounded-map equality from the ambient inverse identity.

Both `a` and `b` are the existing full quasi-isomorphism subatlas inclusions;
the preceding constructions also prove that `L` and `r` are full
quasi-isomorphisms. The new equations retain every bounded pullback.
They do not assert an unrefined inverse on all original `B` charts.

## Remaining scope

This unit constructs the hom-set embedding, proves compatible cancellation
and monicity, and proves both reverse composite identities on the actual
refinements. It does not construct a general Ore square for an arbitrary
compatible map and arbitrary quasi-isomorphism, identify the localized
category with an independently defined analytic-space category, construct
etale, quasi-etale or equivariant sites, or specialize to Harris towers.
Those remain obligations of the surrounding analytic geometry and site task.
