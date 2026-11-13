# Smoothness, properness and geometric connectedness of the chosen dual over a field

Module `Langlands.AlgebraicGeometry.Picard.FieldDualSchemeGeometryProof`
proves the published proposition
`Langlands.AbelianScheme.FieldDualSchemeGeometryStatement` by the theorem

```text
Langlands.AbelianScheme.fieldDualSchemeGeometry :
  FieldDualSchemeGeometryStatement.{u}
```

whose type is exactly the statement, for an arbitrary universe `u`. For
every field `k : Type u`, every `A : AbelianScheme (Spec k)` and every
`hA : HasDualScheme A`, it proves that the structural morphism
`(dualScheme A hA).hom` of the existing chosen parameter scheme is smooth,
proper and geometrically connected.

The field is arbitrary. No perfectness, algebraic-closedness,
projectivity, ample-bundle, coherence or representability hypothesis is
added, and the theorem has no premise beyond the statement's quantifiers.
The statement's Lean/Markdown pair and its dependency closure are imported
unchanged by Lean module name.

## Implemented proof

The proof applies one published Library theorem to another:

```text
FieldDualSchemeGeometryStatement.of_smooth fieldDualSchemeSmooth
```

1. `Langlands.AbelianScheme.FieldDualSchemeGeometryStatement.of_smooth`, from
   module `Langlands.AlgebraicGeometry.Picard.FieldDualSchemeGeometryReduction`,
   proves the Prop-valued reduction
   `FieldDualSchemeSmoothStatement.{u} → FieldDualSchemeGeometryStatement.{u}`.
   For given `k`, `A` and `hA`, it uses the smoothness hypothesis as follows:
   - **Smoothness:** it is the hypothesis itself.
   - **Properness:** smoothness gives local finite type. Separatedness is the
     published theorem `fieldDualSchemeSeparated`. Universal closedness follows
     from the published surjection `fieldDualSchemeSurjection`, an
     `Over (Spec k)` morphism `A.X ⟶ dualScheme A hA` with surjective
     underlying morphism. Because `A.X.hom` is proper, Mathlib's
     `UniversallyClosed.of_comp_surjective` applies. Mathlib's `isProper_iff`
     then gives properness.
   - **Geometric connectedness:** `A.X` is geometrically connected, and the
     dual is its image under the same surjection. The module's lemma
     `geometricallyConnected_of_surjective` makes this precise. It pastes
     pullback squares and uses that surjectivity is stable under base change.
2. `Langlands.AbelianScheme.fieldDualSchemeSmooth`, from module
   `Langlands.AlgebraicGeometry.Picard.FieldDualSchemeSmoothProof`, proves
   `FieldDualSchemeSmoothStatement.{u}` unconditionally. As described in its
   paired Markdown, it first base-changes to an algebraic closure `Ω` of `k`.
   It identifies the pulled-back chosen dual with the chosen dual of the
   base-changed abelian scheme. That identification is the canonical
   isomorphism obtained from the universal property on all test schemes,
   including nonreduced ones. The published algebraically closed theorem
   `algClosedFieldDualSchemeRelativeDimension` then applies. Finally,
   smoothness descends along the surjective, flat, quasi-compact morphism
   `Spec Ω ⟶ Spec k`.

The development check of this module reported no errors or warnings. The
theorem uses only the axioms `propext`, `Classical.choice` and `Quot.sound`.

## Relation to the source

The statement's source is Edixhoven, van der Geer and Moonen, *Abelian
Varieties*, preliminary draft, registered as
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA-256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`. The
relevant passages are:
- paragraph (6.2), printed p.88/PDF p.92;
- Chapter VI §3, printed p.95/PDF p.99;
- Theorem (6.18) and Definition (6.19), printed p.96/PDF p.100;
- Corollary (7.22), printed p.106/PDF p.110.

The source deduces the geometry of `Pic⁰` from Picard-scheme theory. This
proof does not follow that route literally. The comparison with the Library's
exact geometric-fibre Picard-zero functor, which uses the universal property
on all test schemes, is carried out inside the imported smoothness proof and
the algebraically closed theorem it uses. That comparison yields scheme
isomorphisms, not bijections of geometric points. Properness and geometric
connectedness come from the imported separatedness and surjection proofs, as
described above. The present module adds no mathematics beyond the
composition of the two published theorems.

## Provenance

Worker 858 wrote this assembly for Task 858. The reduction module records
its own authorship, which includes historical Worker 268 and Worker 858.
Worker 1383 wrote the smoothness proof.
