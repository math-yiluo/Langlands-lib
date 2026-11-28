# Induced inside-Levi cuspidal representations lie in `Alg({K})`: proof

Module `Langlands.Representation.Aubert.General.InducedCuspidalSupportCategoryProof`,
namespace `Langlands.Aubert.General.RationalPointFamily`.

The theorem `rationalInducedCuspidalSupportCategory` proves exactly
`RationalInducedCuspidalSupportCategoryStatement.{u, v}`
([InducedCuspidalSupportCategoryStatement](InducedCuspidalSupportCategoryStatement.md)),
with independent universes `u` (field) and `v` (carrier, the representations
living in `max (u + 1) v`). It has no hypotheses.

The statement says: for every nonarchimedean local field `k`, every connected
reductive group scheme `G` over `Spec k`, the actual maximal split torus `i`
and generic cocharacter `ν`, the point topology on `RationalPoint k G.X` with
its locally compact, nonarchimedean and Hausdorff instances, the displayed
premises `hStandard`, `hInter`, `hRoots`, `hN`, `hZ` and the closedness of
the standard unipotent radicals and Levis, every standard simple-root subset
`K` and every smooth complex representation `τ` of `levi i ν K` satisfying
`IsLeviCuspidal`, the actual normalized induction
`(normalizedInductionFunctor (h K) (hU K)).obj τ` satisfies
`IsInSupportCategory` for `K` with the association `rootAssociation i ν hN hZ`.
The representation `τ` is arbitrary: it may be reducible, zero, not
admissible, not finitely generated or of infinite length. No premise is added.
Development compilation reports only the axioms `propext`, `Classical.choice`
and `Quot.sound`.

## Proof

The Lean term is a composition of four published theorems:

```
rationalInducedCuspidalSupportCategory_of_extractionInputs
  (rationalCuspidalExtractionInputs_of_specialVertexInputs
    (CuspidalSupport.rationalSpecialVertexCompactInputs_of_jointBasis
      BruhatTits.SpecialCompact.jointSpecialCompactBasisExistence))
```

1. `Langlands.BruhatTits.SpecialCompact.jointSpecialCompactBasisExistence`
   (module `Langlands.BruhatTits.SpecialCompact.JointBasisProof`, Renard
   V.5.1–V.5.2) proves `JointSpecialCompactBasisExistenceStatement.{u}`
   without hypotheses: for every nonarchimedean local field, connected
   reductive group, maximal split torus and generic cocharacter there is one
   apartment datum, one special vertex and one represented torus centralizer
   satisfying the special compact properties, the Iwasawa and Cartan
   comparisons and the simultaneous standard basis.
   [Joint basis](../../../BruhatTits/SpecialCompact/JointBasisProof.md)
2. `Langlands.CuspidalSupport.rationalSpecialVertexCompactInputs_of_jointBasis`
   (module `Langlands.Representation.CuspidalSupport.RationalCuspidalInertiaDecompositionReduction`)
   turns this into `RationalSpecialVertexCompactInputsStatement.{u}`: it keeps
   the special vertex, its compact-subgroup properties and the simultaneous
   basis, and adds the finite Cartan covering of the same compact subgroup
   through `rationalPositiveCartanCover`.
   [Special-vertex inputs](../../CuspidalSupport/RationalCuspidalInertiaDecompositionReduction.md)
3. `rationalCuspidalExtractionInputs_of_specialVertexInputs`
   (module `Langlands.Representation.Aubert.General.RationalCuspidalExtractionFromSpecialVertex`)
   proves `RationalCuspidalExtractionInputsStatement.{u, v}`, the conjunction
   of two inputs at every displayed datum.
   - The geometric filtration of `r_J i_K(τ)` (Renard VI.5.1) is the
     unconditional `exists_pointInducedJacquetGeometricFiltration`.
   - The proper-standard exclusion inside every standard Levi (Renard,
     Lemme VI.5.2: an irreducible inside-Levi cuspidal representation of
     `levi i ν J` is not a subquotient of a normalized induction from a proper
     standard parabolic of `levi i ν J`) is
     `pointLeviStandardInductionCuspidalExclusion_of_specialVertexInputs`. It
     applies the special-vertex inputs to the standard Levi scheme, uses the
     compact-restriction characterization of cuspidality (Renard VI.2.1,
     `rationalCuspidalCompactRestriction` and
     `rationalCompactRestrictionCuspidal`) and first adjointness.
   [Extraction inputs](RationalCuspidalExtractionFromSpecialVertex.md)
4. `rationalInducedCuspidalSupportCategory_of_extractionInputs`
   (module `Langlands.Representation.Aubert.General.InducedCuspidalSupportCategoryReduction`)
   proves the target from these inputs. For an irreducible subquotient `π` of
   `i_K(τ)` it takes a minimal cuspidal datum `(I, ρ)` of `π`, with `ρ` an
   irreducible inside-Levi cuspidal quotient of `r_I(π)` and `π ↪ i_I(ρ)` by
   Frobenius reciprocity (`exists_cuspidal_jacquet_quotient_embedding`). Jacquet
   exactness makes `ρ` a subquotient of `r_I i_K(τ)`. The geometric filtration,
   with the exclusion removing the proper target terms and cuspidality of `τ`
   removing the proper source terms, makes `ρ` a subquotient of a grade
   isomorphic to a conjugate `Ad(n) τ` with `rootAssociation K I n`. Pulling `ρ` back by the
   conjugation gives an irreducible inside-Levi cuspidal subquotient `σ` of
   `τ` (`IsLeviCuspidal.of_isSubquotient`), and `π` is a subquotient of
   `i_I(Ad(n) σ)`. None of these steps assumes `τ` irreducible.
   [Reduction](InducedCuspidalSupportCategoryReduction.md)

The composition is plain function application: the conclusion of each theorem
is literally the hypothesis of the next, so no transport is needed. Steps 1
and 2 are at the field universe `u` only; the carrier universe `v` enters in
steps 3 and 4.

## Source

D. Renard, *Représentations des groupes réductifs p-adiques*, version of
9 July 2026, `renard-2026-representations-groupes-reductifs-padiques`
(SHA-256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`),
proof of Théorème VI.7.2, final paragraph of printed p. 183 / PDF p. 189,
with Lemme VI.5.3 (iii) and (V.4.3.3). There a composition factor of
`i^G_P(W_D)` has its Jacquet module along `P` a subquotient of
`r^G_P i^G_P(W_D)` by exactness, and the filtration of that module by the
conjugates `w(W_D)` places its cuspidal support in the component of `D`. The
implemented argument applies the Jacquet functor along the index of a minimal
cuspidal datum of the composition factor instead, and removes the proper
target terms of the geometric filtration with Lemme VI.5.2 inside a standard
Levi; this route is described in the
[reduction's Markdown](InducedCuspidalSupportCategoryReduction.md). Aubert's
*cuspidale* is Renard's *supercuspidale*, given here by `IsLeviCuspidal`, and
`IsInSupportCategory` is the support category `Alg({K})`.
