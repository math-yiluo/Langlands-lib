# Full cover descent for an explicit finite tensor decomposition

`SimplyConnectedCoverTensorDescentStatement.{u,v}` is an internal intermediate
target for the arbitrary-field-extension simple-connectedness proof. The
fields `k` and `L` lie in arbitrary universe `u`; the finite indexing type
`J` lies in independent universe `v`. The inputs include an actual
`L`-algebra equivalence
`e : L ⊗[k] L ≃ₐ[L] (J → L)`, specified `k`-algebra automorphisms
`s : J → L ≃ₐ[k] L`, and the formula
`e (a ⊗ b) i = a * s i b` for every `a`, `b`, and `i`.

For an actual group scheme `G` over `k`, an actual group scheme `C` over
`L`, and a supplied full simply connected cover `π : C → G_L`, the
conclusion gives an actual group scheme `D` over `k`, an arrow `a : D → G`,
and a group-scheme isomorphism `j : D_L ≅ C`. The arrow `a` has the full
`IsSimplyConnectedCover` predicate. This includes semisimplicity of `G`,
simple connectedness of `D`, the unchanged central-isogeny predicate with
its scheme-theoretic kernel on all test schemes, and the central-cover
universal property over `k`. The exact recovery equation is
`a_L = j.hom ≫ π`. Every scalar extension uses the actual pullback functor
along `Spec.map (CommRingCat.ofHom (algebraMap k L))`.

The statement's provenance is internal: it isolates the full-cover
conclusion needed after constructing a compatible tensor descent datum,
an effective descended source, and its descended central arrow. Reflection
of semisimplicity, simple connectedness, and the universal property are
separate proof obligations. A private assembly prototype motivates this
interface; that prototype supplies no independent acceptance or
publication evidence. This statement imports only the public cover
definitions and Mathlib tensor-product and product-algebra data.

There is no separate algebraicity, finite-dimensionality, perfection,
separability, nonempty-index, or effective-descent hypothesis. The finite
tensor equivalence and its automorphism formula remain explicit inputs;
the statement asserts neither their existence nor existence of the input
cover. It does not assert that an arbitrary group or isogeny over an
arbitrary extension descends. Publishing this proposition does not prove
it or the unrestricted field-extension theorem.
