# Smooth group actions restrict to reduced orbit-dimension strata

Author: Worker 79.

`OrbitStratumActionRestrictionStatement` states that the action of a smooth group scheme
over a field restricts to a reduced scheme immersed onto an orbit-dimension stratum, and
that every such restricted action has the same orbit dimension at every point. Conrad's
Example 5.5 uses the restricted action on `V_d` without stating it; this statement
supplies it for clauses 2 and 3 of `UnipotentOrbitQuotientStatement`. The module states
the claim and contains no proof.

## The statement

Notation is that of `UnipotentOrbitQuotientStatement.lean`; products are fibre products
over `Spec k` and `G.X ◁ i : G × Z ⟶ G × V` is `𝟙 × i`. Let `k : Type u` be a field and
`G : GroupScheme (Spec k)` a group scheme with `Smooth G.X.hom`. Let `V : Over (Spec k)`
be a scheme locally of finite type over `k`, `a : SchemeAction G V` an action and
`d : ℕ`. Let `Z : Over (Spec k)` be a reduced scheme (`IsReduced Z.left`) and
`i : Z ⟶ V` a morphism over `Spec k` that is an immersion (`IsImmersion i.left`) with
`Set.range i.left.base = {v | HasOrbitDimension a v d}`: its image is the set of points of
`V` whose orbit has dimension `d`. The statement asserts:

1. There is an action `b : SchemeAction G Z` with `b.hom ≫ i = (G.X ◁ i) ≫ a.hom`, that
   is, `i(g.z) = g.i(z)`.
2. Every action `b` with `b.hom ≫ i = (G.X ◁ i) ≫ a.hom` satisfies
   `HasOrbitDimension b z d` for every point `z` of `Z`.

Since `i` is a monomorphism, the action in (1) is unique; (2) is stated for every such
action so that it applies to the action quantified over in clause 3 of the target.

## Source

Brian Conrad, *Weil and Grothendieck approaches to adelic points* (December 31, 2011),
registered source `conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`, Example 5.5, printed
p.16: "For `d ≥ 0` let `V_d ⊂ V` denote the reduced locally closed subscheme of points
whose `G`-orbit has dimension `d`. […] The universal action map `G × V_d → V_d × V_d`
defined by `(g, v) ↦ (g.v, v)` is flat over the diagonal". This map is defined only when
the action of `G` on `V` restricts to `V_d`. In Example 5.5, `G` is a unipotent algebraic
group over a field of characteristic zero, hence smooth (J. S. Milne, *Algebraic Groups*,
2022 corrected reprint, registered source `milne-2022-algebraic-groups`, SHA-256
`f2ddd8fa4d263085f173934664b246007a2c0bd539739b7c82de39bfb5d21f40`, Theorem 3.23,
printed p.71).

## Derivation (provenance: derived)

The statement is not in a source; it is the implicit step of Example 5.5, stated for a
smooth group over any field. The reason it holds:

- *The stratum is stable.* Let `p` be a point of `G × Z` over `z`, with image
  `v' = a(p)` in `V`, and let `L = κ(p)`. Over `L`, the point `p` gives `g ∈ G(L)` with
  `g.i(z)_L = v'_L`, so conjugation by `g` identifies the stabilizers of `i(z)` and `v'`
  after base change to `L`. Dimensions of schemes locally of finite type over a field are
  invariant under field extension, so `v'` has orbit dimension `d`. Hence the composite
  `(G.X ◁ i) ≫ a.hom` maps `G × Z` into the image of `i`.
- *It factors through `i`.* `G × Z` is reduced: `G` is smooth, hence geometrically
  reduced, and `Z` is reduced (The Stacks Project, Section 33.6, Lemma 33.6.7, registered
  source `stacks-geometrically-reduced-schemes-section-035u-2026-10-30`, SHA-256
  `6435a4eaa6664fc49a44d8a086a01e582869c00f2377f660e077709e5df2f888`: "If `X`
  geometrically reduced over `k` and `Y` reduced, then `X ×_k Y` is reduced"). The
  immersion `i` from the reduced scheme `Z` is a closed immersion into an open subscheme
  of `V` with the reduced induced structure. A morphism from a reduced scheme into `V`
  whose image lies in that set factors uniquely through `i`. This gives `b.hom`. The
  action axioms for `b` follow from those of `a` because `i` is a monomorphism.
- *Orbit dimensions are preserved.* For an action `b` making `i` equivariant, `g.z = z`
  if and only if `g.i(z) = i(z)`, since `i` is a monomorphism. So the stabilizer scheme of
  `b` is the base change along `i` of the stabilizer scheme of `a`, and its fibre over `z`
  is the fibre of the latter over `i(z)`, as `κ(z) = κ(i(z))` for an immersion.

Smoothness of `G` is used only for reducedness of `G × Z`; over a field of characteristic
zero, `G × Z` is reduced for every reduced `G`. The hypothesis that `V` is locally of
finite type is that of Example 5.5. The names of the declarations are derived here.
