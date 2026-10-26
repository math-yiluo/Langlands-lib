# Unitarizability from square-integrable coefficients on a central quotient

Author: Worker 580, with interface guidance from Worker 438.

`Langlands.SquareIntegrableUnimodularUnitarityStatement.{uG,uV}` is a closed
proposition definition for an internal extension of the square-integrable
unitarity argument. This pair states an implication; it supplies no proof,
chosen functional, integral construction, or invariant form.

## Exact statement

The group `G : Type uG` has instances
`Group G`, `TopologicalSpace G`, `IsTopologicalGroup G`, `T2Space G`,
`LocallyCompactSpace G`, and `SecondCountableTopology G`. Its compact open
subgroups are cofinal among open subgroups in the explicit sense

```lean
∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G,
  IsCompact (L : Set G) ∧ L ≤ K
```

The carrier `V : Type uV` has only `AddCommGroup V` and `Module ℂ V`.
The universes of `G` and `V` are independent. For each actual action
`ρ : Representation ℂ G V`, the proposition quantifies over any measurable
space on the actual quotient `G ⧸ Subgroup.center G`, an instance of
`BorelSpace` for its inherited quotient topology, and a measure `μ` with
both `MeasureTheory.Measure.IsHaarMeasure μ` and
`MeasureTheory.Measure.IsMulRightInvariant μ`. Its conclusion is precisely

```lean
Representation.IsIrreducible ρ →
  IsSquareIntegrableModCenter ρ μ → IsUnitarizable ρ
```

The existing analytic predicate is used unchanged. It requires admissibility
of `ρ` and a datum `c : UnitaryCentralCharacter ρ` such that
`MemLp (c.coefficientNorm ℓ v) 2 μ` for every `ℓ : SmoothDual ρ` and `v : V`.
On a representative `g`, the descended real function is `‖ℓ (ρ g v)‖`.
The character datum includes the actual scalar action of the center, an open
kernel, and unit norm. Admissibility already includes smoothness. Neither
smoothness nor admissibility is a separate premise of this statement.

The conclusion uses the existing `IsUnitarizable ρ`, namely
`Nonempty (InvariantPositiveForm ρ)`. A witness extends
`InnerProductSpace.Core ℂ V` and preserves its inner product under every
operator `ρ g`. Thus the required form is positive definite and
conjugate-linear in its first argument. The statement imposes no norm,
topology, dimension bound, completeness, prescribed form, or nonzero
functional on `V`.

The quotient topology is the actual group quotient topology. Closedness of
the center of a Hausdorff topological group gives the Hausdorff quotient;
local compactness and second countability pass to this quotient. These
facts are available to a future proof from the group hypotheses. Right
invariance of the specified Haar measure is an explicit additional
hypothesis. The name does not assert or prove unimodularity of an arbitrary
group or quotient.

## Derived provenance and source convention

The statement is an internal, derived extension of the argument in
W. Casselman, *Introduction to the theory of admissible representations of
p-adic reductive groups*, draft of 1 May 1995, §2.5, pp.28–29,
especially Proposition 2.5.4 on p.29. It abstracts the integral argument
while making compact-open cofinality and right invariance explicit.
Casselman's proposition is not cited as a theorem about every group
quantified here. The generic extension remains to be proved.

- Literature ID: `casselman-1995-admissible-representations`.
- Source SHA-256:
  `78b921fc6331ad2b75389f37d15bd5ac3399e6cfc2d7555e1a4d666e0d42612a`.
- Retained original:
  `/home/taskhub/central-library/Casselman--p-adic groups lecture notes/Introduction to representations of p-adic groups/Casselman--Introduction to the theory of admissible representations of p-adic reductive groups--1995.pdf`.
- Reading extent: pp.28–29, with the displayed form on p.29 also checked
  in the rendered page. No source-specific project errata note was present
  when this pair was prepared.

For a nonzero smooth functional `ℓ`, set `c_v(g) = ℓ (ρ g v)`.
Casselman's displayed form conjugates the second factor. To match
Mathlib's conjugate-linear first argument, the proposed form here is

```text
B(u,v) = ∫[G/Z(G)] conjugate(c_u(g)) * c_v(g) dμ(gZ(G)).
```

This convention reverses the arguments of the source form and preserves
its diagonal. The complex coefficients need not individually descend to
the quotient; the paired product does, using the unitary central character.

## Obligations for the subsequent proof

The following is a proposed proof route, not an implemented proof or a list
of extra hypotheses.

1. Extract admissibility, hence smoothness, and the central character from
   `IsSquareIntegrableModCenter ρ μ`. Irreducibility supplies a nonzero
   vector. Use compact-open cofinality and the published
   `smoothBidual_injective_of_compact_cofinal` to show that smooth-dual
   functionals separate vectors and obtain a nonzero `ℓ : SmoothDual ρ`.
   Its compact averaging input is available through
   `smoothDualFixedRestriction_bijective`. Existence of an algebraic dual
   functional alone does not establish smoothness.
2. Construct the complex function on the actual quotient from
   `conjugate(c_u(g)) * c_v(g)`. Under multiplication by a central element,
   its character factors cancel. Prove continuity and measurability of the
   descended product from smooth coefficients and the quotient map.
   The published `MatrixCoefficient.LawsProof` supplies local constancy;
   `MatrixCoefficient.NormRegularityProof` supplies continuity and
   almost-everywhere strong measurability of the descended norms.
3. Identify the integrand's norm as
   `c.coefficientNorm ℓ u * c.coefficientNorm ℓ v`. The two `L²` bounds
   imply actual `L¹` integrability by Cauchy–Schwarz. Use this integrability
   to pass addition, scalar multiplication, and conjugation through the
   integral, proving all Hermitian and sesquilinear laws.
4. Apply `matrixCoefficient_mul` to express the coefficient of `ρ h v`
   as right translation by `h`. The supplied `IsMulRightInvariant μ`
   then proves invariance of the integral under simultaneous action on
   both vectors.
5. The diagonal integrand is the nonnegative real quantity `‖c_v(g)‖²`,
   viewed in `ℂ`. Prove nonnegativity of its integral. A zero diagonal
   integral forces the descended norm to vanish almost everywhere.
   Its continuity and positivity of Haar measure on nonempty open sets
   upgrade this to vanishing everywhere. Vectors whose coefficient
   vanishes everywhere form an invariant subspace. This subspace is proper
   because `ℓ ≠ 0` and `c_v(1) = ℓ(v)`; irreducibility makes it zero.
   This proves definiteness.
6. Assemble these laws into the existing `InvariantPositiveForm ρ` and
   conclude its nonemptiness on the same carrier.

The direct project imports are `MatrixCoefficient.ModuloCenter` and
`Unitary.Basic`; Mathlib supplies `RepresentationTheory.Irreducible`.
The proof dependencies mentioned above are already published, but this
statement does not import them or depend on an unpublished product
construction or proof draft.

In a general linear group application, the parent theorem must supply
compact-open cofinality and right invariance for its actual central quotient
Haar measure, then instantiate this generic implication. This pair does
not prove the generic implication or the final GL theorem. It uses no
tempered, induction, classification, or equal-exponent grouping assumption,
and changes no existing Lean/Markdown pair.
