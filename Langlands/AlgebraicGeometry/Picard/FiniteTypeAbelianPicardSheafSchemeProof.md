# Scheme representability of the Picard sheaf over finite-type `ℤ`-algebras: proof

Module: `Langlands.AlgebraicGeometry.Picard.FiniteTypeAbelianPicardSheafSchemeProof`.

Author: Worker 5600, for task `de799868-75c2-4835-b620-f024e5969aa8`. The
reductions and the three input theorems it composes were written by other
workers, as listed below.

## Result

The theorem
`Langlands.AlgebraicGeometry.Picard.finiteTypeAbelianPicardSheafScheme`
proves the published proposition
`Langlands.AlgebraicGeometry.Picard.FiniteTypeAbelianPicardSheafSchemeStatement.{u}`
for every universe `u`. Its type is exactly that proposition. The theorem has
no hypotheses, and this module leaves the statement module and its Markdown
unchanged.

Let `R : Type u` be any commutative ring of finite type over `ℤ`, and let `A`
be any Library abelian scheme over `Spec R`. `R` may be nonreduced or not a
domain. No polarization or projectivity of `A` is assumed. Then there is an
object `P` of `Over (Spec R)` with
`Nonempty ((RelativePicard.classSheafPresheaf A.X.hom).RepresentableBy P)`.
The represented functor is the underlying presheaf of the Library's fppf
sheafification `RelativePicard.classSheaf A.X.hom` of isomorphism classes of
line bundles. The representation is natural in every object of the whole
slice over `Spec R`. No finiteness, quasi-compactness or separation property
of `P` is claimed.

## The proof

The proof is one term. It applies two published reductions to three published
unconditional theorems. Each is imported by its Lean name.

The three inputs are:

1. `finiteTypeAbelianPicardSheafAlgebraicSpace` (module
   `Langlands.AlgebraicGeometry.Picard.FiniteTypeAbelianPicardSheafAlgebraicSpaceProof`,
   Task 4828). It proves
   `FiniteTypeAbelianPicardSheafAlgebraicSpaceStatement.{u}`: for the same `R`
   and `A`, the fppf Picard class sheaf is an algebraic space over `Spec R`.
2. `normalFiniteTypeAbelianAmpleExistence` (module
   `Langlands.AlgebraicGeometry.Picard.NormalFiniteTypeAbelianAmpleExistenceProof`,
   Task 5655). It proves `NormalFiniteTypeAbelianAmpleExistenceStatement.{u}`:
   for an integrally closed finite-type `ℤ`-domain `R` and an abelian scheme
   `A` over `Spec R`, the total space `A.X.left` has an ample line bundle.
3. `ampleNormalFiniteTypeAbelianPicardSheafAFScheme` (module
   `Langlands.AlgebraicGeometry.Picard.AmpleNormalFiniteTypeAbelianPicardSheafAFSchemeProof`,
   Task 5656). It proves
   `AmpleNormalFiniteTypeAbelianPicardSheafAFSchemeStatement.{u}`: over such
   an `R`, if `A.X.left` has an ample line bundle, the Picard sheaf is
   represented by a scheme in which every finite set of points lies in an
   affine open.

The two reductions are applied in this order:

- `normalFiniteTypeAbelianPicardSheafAFScheme_of_ample` (module
  `Langlands.AlgebraicGeometry.Picard.NormalFiniteTypeAbelianPicardSheafAFSchemeReduction`)
  combines inputs 2 and 3 into
  `NormalFiniteTypeAbelianPicardSheafAFSchemeStatement.{u}`. This is the AF
  representation over every normal finite-type `ℤ`-domain, with no ampleness
  hypothesis. Input 2 supplies the ample bundle that input 3 needs.
- `finiteTypeAbelianPicardSheafScheme_of_algebraicSpace_of_normal` (module
  `Langlands.AlgebraicGeometry.Picard.FiniteTypeAbelianPicardSheafSchemeReductionProof`)
  derives the target from input 1 and that normal-base statement. Its proof
  takes the normalization cover `g : ∐_p Spec (R ⧸ p)^ν ⟶ Spec R`, one
  component for each minimal prime `p` of `R`. The cover is finite and
  surjective. On each component the base-changed Picard sheaf is represented
  by an AF scheme, by the normal-base statement. These representatives glue
  along the disjoint components to an AF scheme `V'` representing the
  restricted sheaf. The induced chart `V' ⟶ Pic(A/R)` is finite and
  surjective because `g` is. The Picard algebraic space of input 1 is
  quasi-separated (`AbelianScheme.classSheaf_isQuasiSeparated`). The published
  AF descent for finite surjective charts then shows that the Picard space is
  a scheme.

## Scope and dependencies

The theorem proves the target for every finite-type `ℤ`-algebra and every
actual abelian scheme. All test schemes of the slice are kept. Nothing is
assumed beyond the target's own hypotheses.

`lean_check` reports only the axioms `propext`, `Classical.choice` and
`Quot.sound`. No Lean file in this module's import closure names
`Langlands.AbelianScheme.FiniteTypeSmoothFamilyAbelianRepresentabilityStatement`
or `Langlands.AbelianScheme.SmoothFamilyAbelianRepresentabilityStatement`. So
the proof uses neither these statements nor their proofs, and those tasks can
consume this result without a cycle.

The mathematical route is the one recorded in the target statement's
Markdown. The Picard sheaf is an algebraic space by Artin's method. Over a
normal base, an abelian scheme is projective (Faltings–Chai, *Degeneration of
Abelian Varieties*, Chapter I, Theorem 1.9 and Remark 1.10(a)). The
projective case is Grothendieck's existence theorem in Kleiman's form (*The
Picard scheme*, Theorem 4.8). Schemeness then descends from the normalization
along a finite surjective chart. This module adds no mathematical assertion of
its own. Each step is a published Library theorem cited above by Lean name.
