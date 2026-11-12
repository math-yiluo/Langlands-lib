# Exactness of the nondegenerate tensor and Hom functors

Worker 134, Task 5281. This proof targets the published proposition
`Langlands.Algebra.NondegenerateTensorHomExactness.Statements` in
`Langlands.Algebra.NondegenerateTensorHomExactnessStatements`.

The original assertion is the Proposition in David Renard,
*Représentations des groupes réductifs p-adiques*, French version of
9 July 2026, I.2.2, printed p.15 / PDF p.21, registered as
`renard-2026-representations-groupes-reductifs-padiques`. Its sequence
exactness convention is A.VIII.1, printed p.266 / PDF p.272. The published
statement records the passage from complex coefficients to underlying
integer modules. This proof retains its objects, hypotheses and independent
universes `uA`, `uX`, `uY`, `uM`.

## Implemented tensor proof

The proof uses the cokernel universal property directly. This is an
implementation of the standard descent argument for balanced biadditive
maps, using the published quotient tensor and its universal property.

Consider an exact short complex `Y₁ → Y₂ → Y₃` in the category of
nondegenerate right modules, with its second arrow `g` an epimorphism.
The published `NondegenerateModuleExactnessConcrete.exact_iff` and
`epi_iff` give elementwise exactness and surjectivity of `g`.

For any integer-linear map `φ : Y₂ ⊗_A X → N` that kills the map induced
by the first arrow, restrict `φ` to pure tensors. This gives a balanced
biadditive map `b : Y₂ →+ (X →+ N)`. Exactness shows that its kernel
contains the kernel of `g`: a vector killed by `g` is an image from
`Y₁`, so its pairing with every `x` vanishes by the hypothesis on `φ`.
`AddMonoidHom.liftOfSurjective` therefore descends `b` to `Y₃`.
Surjectivity of `g`, its compatibility with the original right action,
and balancing of `b` show that the descended map remains balanced.

The published `NonUnitalModuleTensor.lift` gives the required map
`Y₃ ⊗_A X → N`. Its composite with `g ⊗ id` equals `φ` on pure tensors
by the descent formula, hence everywhere by
`NonUnitalModuleTensor.hom_ext`. Uniqueness follows from surjectivity of
`g` and the same pure-tensor extensionality. Thus `g ⊗ id` is a cokernel.
Mathlib's `exact_and_epi_g_iff_g_is_cokernel` gives both exactness at the
middle tensor and the required epimorphic right boundary. This proves
`tensorRightExact`.

Idempotentedness is used in the source category's abelian structure and
its elementwise criteria. The descent argument needs no nondegeneracy
hypothesis on the fixed left factor, so the published hypothesis on it
can be retained without use. No extra assumption or resizing is introduced.

## Hom clauses and aggregate

For each object of `M(A)`, install the published abelian structure
`NondegenerateModuleCat.abelian A hA`. The two clauses are then exactly
the specializations of the published general theorems
`Langlands.Renard.contravariantHomLeftExact` and
`Langlands.Renard.covariantHomLeftExact`, in
`Langlands.CategoryTheory.Renard.HomExactnessComparison`.

The theorem `Langlands.Algebra.NondegenerateTensorHomExactness.statements`
combines these two specializations with `tensorRightExact`. Its type is
exactly the published conjunction `Statements`, without any change to the
statement module or its imports.
