# Bounded unramified lifts of residue polynomial roots

Author: Worker 32.

The theorem
`Langlands.LocalClassField.residuePolynomialUnramifiedLift.{u}` proves exactly
`Langlands.LocalClassField.ResiduePolynomialUnramifiedLift.{u}`, the published
proposition in [ResiduePolynomialUnramifiedLiftStatement](ResiduePolynomialUnramifiedLiftStatement.md).
It has no extra outer hypotheses. For every prime `p`, every
`F : PadicField.{u} p`, and every polynomial `P` of positive natural degree over
its canonical residue field, it produces a finite Galois intermediate field
`K'` in the specified `AlgebraicClosure F.Carrier`. The canonical absolute
ramification indices agree, `[K' : F] ≤ P.natDegree`, and the image of `P` has
a root in the canonical residue field of `K'.asPadicField`.

The coefficient map is exactly `PadicField.TopologicalData.relativeResidueMap`
induced by the given field inclusion. The proof installs the packaged
`(K'.asPadicField (p := p)).algebra` and its composite scalar tower exactly as
in the target. The residue algebra is `relativeResidueAlgebra`, whose algebra
map is definitionally this residue map. No residue-field isomorphism is
substituted for it. The arbitrary universe `u`, degree-one case, nonmonic
polynomials and polynomials with repeated factors are all retained.

## Implemented proof

The auxiliary theorem `residueFinrank_eq_of_ramificationIndex_eq` works for
p-adic fields in independent universes, with their specified compatible
algebra structure and arbitrary topological data `T` and `S`. It proves that
equality of their absolute ramification indices implies

`finrank T.ResidueField S.ResidueField = finrank F.Carrier E.Carrier`,

where the left side uses `relativeResidueAlgebra T S`. To prove this, let `r`
be the relative residue degree and write `e_F`, `f_F`, `e_E`, `f_E` for the
absolute ramification and residue degrees. Finiteness of the residue fields
and `Module.natCard_eq_pow_finrank` give
`p ^ f_E = (p ^ f_F) ^ r`, so `f_E = f_F * r` by injectivity of powers of
`p > 1`. The two published absolute degree formulas and the field tower
formula give

`e_E * f_E = [E : Q_p] = [F : Q_p] * [E : F] = e_F * f_F * [E : F]`.

Substituting `e_E = e_F` and cancelling the positive integers `e_F` and `f_F`
proves the desired equality. This uses cardinalities of the actual residue
fields and does not require a choice of their identifications with standard
finite fields.

The private lemma `exists_root_of_finrank_eq` treats a field algebra `l/k`
with `l` finite and an irreducible `Q : Polynomial k` such that
`finrank k l = Q.natDegree`. Mathlib's `AdjoinRoot Q` is a field; its power
basis has dimension `Q.natDegree`. Therefore
`FiniteField.nonempty_algHom_of_finrank_dvd` supplies a `k`-algebra
homomorphism `AdjoinRoot Q →ₐ[k] l`. The image of the distinguished root is
a root of `Q.map (algebraMap k l)`, by
`AdjoinRoot.aeval_algHom_eq_zero`. This homomorphism fixes the specified
`k`-algebra structure on `l`.

The closing theorem chooses an irreducible divisor `Q` of `P` using
`WfDvdMonoid.exists_irreducible_factor`. Positive degree makes `P` nonzero
and a nonunit, so this choice applies; irreducibility gives positive degree
for `Q`, and divisibility gives `Q.natDegree ≤ P.natDegree`. The published
`Langlands.ClassFieldTheory.Local.unramifiedExtensionDegreeExistence`
provides an actual finite Galois intermediate extension `K'` of degree
`Q.natDegree` with equal absolute ramification indices. The auxiliary
degree comparison identifies its relative residue degree with
`Q.natDegree`. The private finite-field lemma then gives a root of `Q`
along the actual residue map. Mapping `Q ∣ P` along that map and using
`Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero` makes the same element a
root of the image of `P`.

## Dependencies and provenance

The module imports the unchanged target, the published
[UnramifiedExtensionDegreeProof](UnramifiedExtensionDegreeProof.md), and
Mathlib's `FieldTheory.Finite.GaloisField` and `RingTheory.AdjoinRoot`.
The target imports `Langlands.LocalField.RelativeIntegers`, which supplies
the actual residue map and imports `Langlands.LocalField.Normalization.Proof`.
The arithmetic results used there are `finite_residueField`,
`residueCardinality_eq_pow`, `residueDegree_pos`, `ramificationIndex_pos`,
and `ramificationIndex_mul_residueDegree`. The target pair and all imported
project files are unchanged.

This is a derived finite-residue-polynomial statement. Its source context
is Jean-Pierre Serre, *Local Fields*, Greenberg translation, GTM 67 (1979),
registered as `serre-1979-local-fields`. The retained original is
`/home/taskhub/central-library/Serre--Local Fields--1979.pdf`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
Chapter V, section 4, Proposition 6, printed page 88/PDF page 95, uses a
residue extension of degree at most the degree of a particular critical
norm polynomial to acquire a root. The setup is printed page 87/PDF page 94.
Chapter III, section 5, Theorems 2–3, printed page 54/PDF page 61, and
Corollaries 1–3, printed page 55/PDF page 62, describe unramified extensions
and their residue extensions. These source pages were read; no project
errata note for this source was found.

The present proof uses the Library's existing unramified extension theorem,
whose implemented route is through Galois fixed fields, followed by the
cardinality comparison and Mathlib finite-field embedding argument above.
It does not formalize Serre's norm-polynomial computation or any norm
surjectivity assertion. The generalization from the critical polynomial to
an arbitrary nonconstant polynomial is the published target's derived
formulation, not a verbatim statement from Serre.
