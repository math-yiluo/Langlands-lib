# Right-axis creation and canonical abelian-scheme slant

This is an internal specialization of
[AllSeqSlantRightCreation](../AlgebraicGeometry/Modules/CechResolution/AllSeqSlantRightCreation.md)
to the actual cohomology operators of
[CanonicalCreationContraction](CanonicalCreationContraction.md). It uses no new
external result.

Let `A` be an abelian scheme over an arbitrary field `K`. The operator
`productCreation A n` is creation by an actual degree-one cohomology class of
`A × A`, computed on `mixedCover A`, the simple product of the fixed affine
cover of `A` with itself. This is the cover used by the canonical slant.
The section scalar structures are induced by the structure maps, and the
canonical comparison with right-derived cohomology supplies the actual objects.

`productCreation_one` identifies degree-one creation with the existing `cupP A`.
The general creation/cup comparison first identifies it with cup on the simple
product cover; the previously proved refinement comparison identifies that cup
with the cup on the multiplication-adapted product cover defining `cupP A`.

For every `n : ℕ`, actual class `x ∈ H¹(A, 𝒪)`, actual class
`e ∈ Hⁿ⁺¹(A × A, 𝒪)`, and actual linear functional
`ell : H¹(A, 𝒪) → K`, `slant_creation_right` proves

\[
 S_{\ell,n+1}(p_2^*x\smile e)
   =-\,x\smile S_{\ell,n}(e).
\]

Here both cups use the stated creation operators and `p₂*` is the actual
canonical structure-sheaf cohomology pullback. The proof applies the general
actual-cohomology theorem to the product pullback square, the chosen affine
covers, and `h1DualCochainFunctional ell`. Its established annihilation of
coboundaries gives the slant hypothesis. All choices and maps then agree
by definition with the canonical abelian-scheme operators. In particular,
`n = 0` is included and there is no characteristic restriction.

The left-axis identity, the full creation-contraction relation, and the host
degree-two exterior/coproduct comparison remain separate proof obligations.
