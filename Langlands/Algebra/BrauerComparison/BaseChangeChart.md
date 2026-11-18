# Scalar extension of a relative Brauer chart

Let `K → L → M` be a tower of fields and let `e` be an `L`-matrix splitting
chart of a central simple `K`-algebra `A`. `enlargedSplittingChart M e` constructs
an `M`-matrix splitting chart of `A` by identifying `M ⊗[K] A` with
`M ⊗[L] (L ⊗[K] A)`, extending `e`, and identifying the extension of the
matrix algebra with matrices over `M`. On `m ⊗ a` it is `m` times the
entrywise image of `e(1 ⊗ a)`.

Given a second compatible tower `K → E → M`, `baseChangeSplittingChart E M e`
first contracts the tensor tower through `E` and applies the enlarged chart.
This gives an `M`-matrix chart of the actual scalar extension `E ⊗[K] A`.
On `m ⊗ (r ⊗ a)` the scalar multiplying the image of `e(1 ⊗ a)` is `r • m`.

When `L/K` is normal, an automorphism `s` of `M/E` restricts to an automorphism
`r(s)` of `L/K` by first restricting scalars to `K` and then restricting to `L`.
The lifted matrix for `s` in the extended chart can be taken to be the
entrywise image of the original lift for `r(s)`. Lean proves the action formula
on pure tensors, using that `e(1 ⊗ a)` is fixed under the old chart action
and that entrywise inclusion intertwines `r(s)` with `s`. It then extends the
formula by additivity. The identity `P_s s(P_t) = c(s,t) P_(st)` for these new
lifts is the image of the corresponding identity for the old lifts. Its
scalar factor is the image of `c(r(s),r(t))` in `Mˣ`.

For nonempty indices the new relative classes are the classes of these
transported factors. `relativeClass_enlargedSplittingChart` gives ordinary
inflation for the enlarged splitting field. `relativeClass_baseChangeSplittingChart`
gives ordinary inflation followed by restriction from `Gal(M/K)` to
`Gal(M/E)` for the mixed chart. Lean uses the naturality of the degree-two
quotient map and the entrywise formula for the transported factors.

This is the chart calculation underlying compatibility with enlargement in
Serre, *Local Fields* (1979), Chapter X, §5, printed p. 159. The version with two
towers follows by the same calculation using the indicated restriction of
automorphisms. The construction works in every characteristic for same-universe
fields and algebras and arbitrary finite matrix index types. The action,
factor and cohomology formulas assume normality of `L/K`. The relative classes
also require nonempty indices.
