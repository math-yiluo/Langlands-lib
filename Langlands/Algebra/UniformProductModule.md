# Uniform finite generation for products of modules

Renard VI.10.5 uses the finiteness of the map from the Bernstein variety of a
Levi to that of its ambient group to obtain a finite module on global functions.
`UniformProductSpanningStatement` supplies the product-module step when the
components are indexed by a map `p : J → I`. Suppose `M j` is an `R (p j)`-module
and the product ring acts on the product of the `M j` through these components.
If every fiber of `p` embeds in a fixed finite type `L` and each `M j` has a
spanning family indexed by a fixed finite type `K`, the product has a spanning
family indexed by `L × K`.

In `exists_spanningFamily_pi_of_boundedFibers`, each embedding assigns a label
in `L` to its fiber elements. The generator at `(l, k)` has the `k`-th local
generator in each coordinate labeled `l` and vanishes in the other coordinates.
Given an element of the product, choose a local expression in the generators
at every coordinate. The coefficient of `(l, k)` in ring coordinate `i` is
the `k`-th coefficient from the unique element labeled `l` in the fiber over
`i`, transported along `p j = i`. It is zero if that label is absent. Evaluating
the finite sum at `j` leaves exactly the terms with the label of `j` and gives
the chosen local expression. `exists_spanningFamily_pi` proves the
coordinatewise case by using the same generator index at every coordinate and
assembling the local coefficients into elements of the product ring.

Source context is Renard, *Représentations des groupes réductifs p-adiques*
(2026), VI.10.5, printed p. 213. The spanning-family argument is elementary
and works for semirings and modules with additive commutative monoids.
