# Coset copies and translated charts of an induced space

The namespace is `Langlands.TopologicalInduction`. This module constructs
translated charts and a homeomorphism from a coproduct of coset copies to the
balanced quotient already defined in `InducedSpace`.

## Algebraic constructions

Let `G : Type u` be a group, `H` a subgroup, and `X : Type v` a type with an
`H`-action. The universes `u` and `v` are independent. Write `[g,x]` for
`mk H g x` in `Space H X`. Its defining relation identifies
`[g*h,x]` with `[g,h • x]` for `h : H`; the action of `G` is left
multiplication on the first coordinate.

`chart H g` sends `x` to `[g,x]`. The theorem `chart_eq_smul_unit` identifies
it with translation by `g` of the existing unit `x ↦ [1,x]`.
`chart_injective` applies translation by `g⁻¹` to an equality and then
uses the published injectivity of the unit.

`component H` sends `[g,x]` to the left coset `gH` in `G ⧸ H`. It is
constructed by quotient lift: multiplying `g` on the right by an element of
`H` preserves its coset. `component_mk` and `component_chart` give its
values on representatives and charts.

`range_chart_eq_fiber` proves that the image of `chart H g` is exactly
the fiber of `component H` over `gH`. For the reverse inclusion, a
representative `[a,x]` in that fiber has `h = g⁻¹*a` in `H`, and the
balancing relation rewrites it as `[g,h • x]`.
`iUnion_range_chart` proves that all these images cover the quotient by
choosing the first coordinate of a representative. The transition and action
formulas are

```text
chart H (g*h) x = chart H g (h • x),
a • chart H g x = chart H (a*g) x.
```

They are `chart_mul_subgroup` and `smul_chart`, respectively. Together with
the fiber description, they describe the coordinate change within one coset
and the separation of distinct cosets.

`CosetCopies H X` is the dependent sum `Σ c : G ⧸ H, X`.
`ofCosetCopies H` sends `(c,x)` to `[c.out,x]`, using Mathlib's chosen
representative `c.out`. `component_ofCosetCopies` recovers `c`.
Consequently equality of two images first identifies their cosets, after
which chart injectivity identifies their coordinates. This proves
`ofCosetCopies_injective`. For surjectivity, Mathlib supplies
`(aH).out = a*h` with `h : H`, and

```text
[(aH).out, h⁻¹ • x] = [a*h, h⁻¹ • x] = [a,x].
```

This is the proof of `ofCosetCopies_surjective`. These constructions and
identities require no topology.

## Topology and the homeomorphism

Equip `G` and `X` with topologies and the quotient with its existing quotient
topology. `continuous_component` descends the continuous map
`(g,x) ↦ gH`; it requires neither a topological-group assumption nor
continuity of the action. If `G` is a topological group and the `H`-action on
`X` is jointly continuous, `continuous_chart` follows by translating the
continuous unit.

For open `H`, `isOpenEmbedding_chart` composes the existing open unit
embedding with the homeomorphism given by translation by `g`.
`isClopen_range_chart` instead uses the fiber description and the discrete
topology of `G ⧸ H`. This clopen result does not require continuity of the
`H`-action.

Give `CosetCopies H X` its usual topological-sum topology.
`continuous_ofCosetCopies` checks continuity on each summand.
`isOpenMap_ofCosetCopies` checks openness on each summand using the open
chart embeddings. The definition `cosetCopiesHomeomorph H hH`, where
`hH : IsOpen (H : Set G)`, combines these results and the algebraic
bijection into

```text
(Σ c : G ⧸ H, X) ≃ₜ Space H X.
```

`cosetCopiesHomeomorph_apply` records its value `[c.out,x]`.
`smul_cosetCopiesHomeomorph` proves the action formula: if
`a*c.out = d.out*h` for `h : H`, then

```text
a • cosetCopiesHomeomorph H hH (c,x)
  = cosetCopiesHomeomorph H hH (d,h • x).
```

The proof rewrites the representative equation and uses balancing.
The chosen representative of the identity coset need not be `1`; the
unit remains `chart H 1`, and no normalization of `c.out` is asserted.
Empty `X`, infinite index, and non-Hausdorff spaces are allowed.

## Provenance and scope

This is a derived topological comparison with Berkovich's unfinished
1995–1996 manuscript *Étale equivariant sheaves on p-adic analytic spaces*,
Construction 1.1.2, printed/PDF page 2. That passage constructs an analytic
induced space as copies of `X` indexed by left cosets, and describes the
action using `g*g_i = g_j*h`. The present homeomorphism identifies the
published balanced quotient with the underlying topological coproduct, and
the final theorem proves that same action formula for chosen representatives.
The quotient proof route and the component and clopen-fiber results are
derived here.

The retained source has literature ID
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
folder SHA256
`e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`.
The member `Berkovich--Etale equivariant sheaves on p-adic analytic spaces
(unfinished manuscript)--1996.pdf` has SHA256
`91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`.

This module supplies topological chart data for later analytic constructions.
It does not construct an analytic atlas, analytic morphisms, a structure
sheaf, or an equivalence of sites, and does not formalize the manuscript's
retraction remark or induction in stages.
