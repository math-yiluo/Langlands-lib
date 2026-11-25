# Scheme representability of the fppf Picard sheaf over a field: proof

Module: `Langlands.AlgebraicGeometry.Picard.FieldPicardSheafRepresentabilityProof`.

The theorem `Langlands.AlgebraicGeometry.Picard.fieldPicardSheafRepresentability`
proves the published proposition
`Langlands.AlgebraicGeometry.Picard.FieldPicardSheafRepresentabilityStatement.{u}`
at every universe `u`. Its type is exactly that proposition. The statement
module `Langlands.AlgebraicGeometry.Picard.FieldPicardSheafRepresentabilityStatement`
and its Markdown are imported unchanged. The module contains only this
theorem and adds no definition, lemma, hypothesis or axiom. The kernel
reports only the standard axioms `propext`, `Classical.choice` and
`Quot.sound`.

## What is proved

Let `k : Type u` be any field, including an imperfect one, and let
`X : Over (Spec (CommRingCat.of k))` satisfy `IsProper X.hom`. Then there is
a scheme `P : Over (Spec (CommRingCat.of k))` such that

- `IsSeparated P.hom`,
- `LocallyOfFiniteType P.hom`, and
- `Nonempty ((RelativePicard.classSheafPresheaf X.hom).RepresentableBy P)`.

The functor `RelativePicard.classSheafPresheaf X.hom` is the underlying
set-valued presheaf of the actual fppf Picard class sheaf on the full slice
over `Spec k`. So `P` naturally represents all sections of the actual relative
Picard sheaf on every scheme over `k`, including sections without a global
line-bundle representative. The only hypothesis is properness. No
projectivity, smoothness, reducedness, connectedness, rational point, section,
condition on global functions, universal bundle or representability is
assumed.

## The implemented proof

The proof is one term:

```text
fieldPicardSheafRepresentability_of_stackAtlas fieldPicardStackAtlas
```

Both names are published Library theorems.

1. `fieldPicardStackAtlas : FieldPicardStackAtlasStatement.{u}` (module
   `Langlands.AlgebraicGeometry.Picard.FieldPicardStackAtlasProof`). For every
   field `k` and proper `X` over `Spec k`, the actual relative line-bundle
   groupoid has a smooth surjective scheme atlas locally of finite type over
   `k`. Its point fibres on the full slice are represented by schemes. That
   module derives the atlas from Artin's criteria for line bundles on a
   noetherian model over a finite-type `ℤ`-algebra. The criteria used are
   formal versality, algebraization via etale completion approximation, and
   openness of versality. The atlas is then base changed to `k`.
2. `fieldPicardSheafRepresentability_of_stackAtlas` (module
   `Langlands.AlgebraicGeometry.Picard.FieldPicardSheafRepresentabilityReduction`)
   proves `FieldPicardSheafRepresentabilityStatement.{u}` from
   `FieldPicardStackAtlasStatement.{u}`. It goes through two steps.
   - `fieldPicardSheafAlgebraicSpace_of_stackAtlas` turns the atlas into
     `FieldPicardSheafAlgebraicSpaceStatement.{u}`. It uses the published
     equalizer immersion `RelativePicard.fieldPicardClassEqualizerImmersion`,
     the automorphism etale atlas `smoothAutomorphismEtaleAtlas`, and the
     etale/fppf class-sheaf comparison. The result is that the actual fppf
     Picard sheaf is an algebraic space with a closed-immersion diagonal and a
     locally finite type etale surjective atlas.
   - `fieldPicardSheafRepresentability_of_algebraicSpace` applies the published
     `AlgebraicSpace.separatedAddCommGroupSheafSchemeRepresentability` to the
     sheaf `RelativePicard.classSheaf X.hom`. Its commutative group structure
     is `RelativePicard.sheafPresheaf X.hom`, linked to the class sheaf by
     `RelativePicard.forgetSheafIso X.hom`. That theorem is the commutative
     case of Stacks Project Lemma 79.10.2 (Tag 0B8D): a separated group
     algebraic space locally of finite type over a field is a scheme. Its
     conclusion is exactly the three conjuncts of the target.

## Relation to the source

The target is the representability assertion of Edixhoven, van der Geer and
Moonen, *Abelian Varieties*, Chapter VI, paragraph (6.3)(iii), as explained in
the statement Markdown. That source cites Murre and Oort and gives no proof.
The Lean route instead uses the algebraicity of the Picard stack (Stacks
Project, Proposition 99.10.2, Tag 0D04, proved in the Library through Artin's
criteria). It then shows that the Picard sheaf is an algebraic space and
applies the theorem that group algebraic spaces over a field are schemes.
This module adds no new mathematics; it only applies the published reduction
to the published atlas theorem.
