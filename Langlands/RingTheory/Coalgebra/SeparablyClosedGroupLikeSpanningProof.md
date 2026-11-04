# Descent of group-like spanning over a separably closed field

`Langlands.CoalgebraDescent.separablyClosedGroupLikeSpanning.{u,v,w}` proves
exactly the published proposition
`Langlands.CoalgebraDescent.SeparablyClosedGroupLikeSpanningStatement.{u,v,w}`,
imported unchanged from
`Langlands.RingTheory.Coalgebra.SeparablyClosedGroupLikeSpanningStatement`.
The universes `u`, `v`, and `w` remain arbitrary and independent.

Throughout, `k` is a field and `C` is an actual Mathlib `k`-coalgebra, with
`AddCommGroup C` and `Module k C`. Field extension `K`, scalar-extension
coalgebra, convolution dual, and bundled subcoalgebra structures retain their
published instances. For any separably closed `k : Type u`, any such
`C : Type v`, and any field `K : Type w` with `[Algebra k K]`, the theorem
proves

```lean
Submodule.span K {x : K ⊗[k] C | IsGroupLikeElem K x} = ⊤ →
  Submodule.span k {x : C | IsGroupLikeElem k x} = ⊤
```

Finite dimensionality is obtained for subcoalgebras inside the proof.
Cocommutativity is derived there from the split scalar-extended dual.
The theorem covers arbitrary-dimensional and zero coalgebras, imperfect
separably closed fields in arbitrary characteristic, and arbitrary extensions
`K/k`, including transcendental and inseparable ones.

## Subcoalgebras of a group-like-spanned coalgebra

`groupLike_subtype_iff` reflects group-like elements through the inclusion of
a `Langlands.Subcoalgebra`. The counit equation is inherited by definition.
The comultiplication equation is reflected by the injective tensor-square
inclusion.

`coordinate_contraction` computes contraction of comultiplication against
a coordinate of a basis of group-like elements: contracting the first factor
by coordinate `i` produces the coefficient of `i` times its basis vector.
It proves the equality of linear maps by checking the basis vectors.
`coordinate_smul_mem_subcoalgebra` shows that this contraction lies in any
subcoalgebra containing the original vector. It lifts comultiplication to
the tensor square of the subcoalgebra and uses tensor induction; the
contraction of each pure tensor is a scalar multiple of its second factor.
`basis_mem_subcoalgebra_of_coord_ne_zero` divides by a nonzero coordinate.

`subcoalgebra_groupLike_spanning_of_basis` expands a subcoalgebra element in
the ambient group-like basis. Every nonzero coordinate contributes a basis
vector in the subcoalgebra, which is group-like there by the reflection
lemma. `subcoalgebra_groupLike_spanning` constructs this basis from Mathlib's
linear independence of group-like elements and the assumed spanning.
No finite-dimensional hypothesis is used in these lemmas.

## The convolution dual and cocommutativity

`isCocomm_of_groupLike_spanning` checks cocommutativity on spanning group-like
elements. `nonempty_convolutionDualEquivPi_of_basis` uses the dual basis
equivalence to identify the convolution dual with functions on a finite
group-like basis. Its unit law is the group-like counit equation, and its
product law is the group-like comultiplication equation together with
Mathlib's convolution formula. `exists_finite_convolutionDualEquivPi` obtains
such a finite basis when the coalgebra is finite dimensional.

`mul_comm_of_tensorProduct_equiv_pi` descends commutativity of an arbitrary
`k`-algebra from a scalar extension isomorphic to a product of copies of `K`.
It applies injectivity of the scalar-extension inclusion and then the
product-algebra equivalence. `isCocomm_of_convolution_comm` recovers
cocommutativity of a finite-dimensional coalgebra from commutativity of its
actual convolution dual: tensor separation from `ConvolutionDualGroupLike`
reduces equality of the two comultiplications to evaluations by pairs of
linear functionals. Swapping the tensor factors swaps their order in the
convolution product. This constructs the canonical cocommutativity proof
needed by Mathlib's convolution `CommRing` instance.

## Transfer and finite-dimensional assembly

`groupLike_spanning_of_surjective` transfers spanning through a surjective
coalgebra homomorphism, since homomorphisms preserve group-like elements.
It expresses the span containment using the comap of the target span.
`baseChange_subcoalgebra_groupLike_spanning` applies this to the inverse of
the published coalgebra equivalence
`Subcoalgebra.baseChangeEquiv K D`, after the subcoalgebra-spanning lemma.
Thus group-like spanning of `K ⊗[k] C` gives spanning of `K ⊗[k] D`.
`mem_groupLike_span_of_mem_subcoalgebra` pushes a subcoalgebra's span into the
ambient coalgebra by its actual inclusion.

`finite_groupLike_spanning_descent` assumes separable closedness and finite
dimensionality. It uses `convolutionDualBaseChangeEquiv k C K`, the canonical
`K`-algebra equivalence between the scalar extension of the convolution dual
and the convolution dual of scalar extension, and composes it with the finite product
equivalence obtained above. Injectivity descends commutativity, tensor
separation yields cocommutativity, and
`span_isGroupLikeElem_eq_top_of_tensorProduct_algEquiv_pi` from
`ConvolutionDualGroupLike` finishes. The latter descends formal
unramifiedness by faithful flatness, splits the finite étale algebra over
the separably closed field, and recovers group-likes by double duality.

`groupLike_spanning_descent_of_local_finiteness` performs the final
local-to-global assembly with local finiteness as an explicit hypothesis.
For each element it chooses a finite-dimensional subcoalgebra containing
it, transfers group-like spanning of the scalar extension to that
subcoalgebra's scalar extension, applies finite-dimensional descent, and
uses the inclusion to put the element in the ambient group-like span.
`separablyClosedGroupLikeSpanning` supplies this hypothesis with
`Langlands.Subcoalgebra.localFiniteness k C`, imported from
`Langlands.RingTheory.Coalgebra.Subcoalgebra.LocalFiniteness`.
This proved theorem applies to every field coalgebra and every element.
The final theorem introduces precisely the quantifiers of the unchanged
published target and applies the local-to-global helper.

## Dependencies and provenance

The target and its paired Markdown are imported unchanged. The
`Subcoalgebra.Basic` and `Subcoalgebra.ScalarExtension` interfaces provide
the induced carrier coalgebra, injective tensor-square inclusion, and the
actual scalar-extension image/equivalence. `ConvolutionDualGroupLike`,
authored by Worker 1248, provides tensor separation, double-dual evaluation,
and étale descent and splitting. `ConvolutionBaseChange` is the separately
authored, independently published construction prerequisite. Its actual
canonical algebra equivalence supplies the finite-dimensional base change.
`Subcoalgebra.LocalFiniteness` supplies the independently proved fundamental
theorem of coalgebras: each element belongs to an actual finite-dimensional
bundled subcoalgebra. These imports supply all constructions and finiteness
arguments used by the final theorem.

These are derived linear algebra arguments implementing the finite-dual
route described in the published statement's Markdown. They generalize the
coetale-to-group-like step of Milne, *Algebraic Groups* (2017), registered
source `milne-2017-algebraic-groups`, Theorem 12.18(c) ⇒ (d), printed
pp. 236–238, from coordinate coalgebras to arbitrary coalgebras. The general
descent statement is not asserted to occur verbatim in that source. The
statement's paired Markdown supplies the original source correspondence and
errata check; this proof implements the derived coalgebra argument. Worker 321
authored the coordinate-closure, commutativity, transfer and assembly proofs;
Worker 1248 authored the companion `ConvolutionDualGroupLike` proof module.
