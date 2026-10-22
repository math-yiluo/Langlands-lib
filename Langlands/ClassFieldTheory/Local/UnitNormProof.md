# Norm surjectivity on every unramified unit level

Worker 26 proves `Langlands.LocalClassField.unramifiedUnitNorms.{u,v}` with
exactly the published type `Langlands.LocalClassField.UnramifiedUnitNorms.{u,v}`.
The theorem quantifies every prime, finite p-adic fields in independent
universes, their compatible finite extension, and arbitrary supplied
`TopologicalData T,S`. From equality of their absolute ramification indices,
it proves

\[
N_{E/F}(U_E^n)=U_F^n
\]

for every natural `n`, including zero. Here the norm is the actual determinant
norm `normUnits`, and each filtration is the published image of the
integer-unit reduction kernel. The original statement pair and all imported
pairs are unchanged. No Galois hypothesis or additional proof premise occurs
in the final theorem.

## Arithmetic bridge

All auxiliary lemmas in this module are private.
`map_maximalIdeal_of_ramificationIndex_eq` proves the ideal equality required
by the finite-level arithmetic theorem. The published normalization theorem
gives `(p) = m_T ^ e_T` and `(p) = m_S ^ e_S`. Map the first identity through
the integer-ring homomorphism. Ring homomorphisms preserve the natural-number
element `p`, and the given equality `e_T = e_S` makes the resulting ideal
powers equal. Since `e_T` is positive and ideals in the target DVR are
multiplicatively torsion free, cancellation gives
`Ideal.map f m_T = m_S`. This directly supplies the needed arithmetic
unramifiedness condition without using a relative-degree formula.

`relativeNormData` starts with an integer-ring homomorphism that restricts
the supplied field algebra map. It installs the compatible scalar towers
over the p-adic integer ring. Both local integer rings are already finite
over that ring, so `Module.Finite.of_restrictScalars_finite` makes the extension
of integer rings finite. The restriction formula and field-map injectivity
make the integer map injective, hence give torsion freeness. The base DVR is
a PID, so the module is free.

The published absolute integral-closure instance, together with
`IsIntegralClosure.tower_top`, gives relative integral closure.
`IsIntegralClosure.isLocalization` then identifies the extension field as
the localization of its integer ring at the nonzero base integers.
`Algebra.norm_localization` proves that the field determinant norm of an
integer is the inclusion of its integer-ring determinant norm.

The final theorem uses these helpers with the published
`T.relativeIntegerMap S` and `T.relativeIntegerAlgebra S`. Their restriction
formula and localness supply precisely the remaining structural conditions.
The supplied topological data provide the DVR and finite-residue-field
instances. None of these conditions is left as an added hypothesis.

## Transfer and compact lifting

`congruence_iff` unfolds the actual congruence-unit kernel. Equality after
unit reduction is equality of underlying quotient-ring elements, and
`Ideal.Quotient.eq` identifies this with `x - 1 ∈ m^n`. This calculation
includes `n = 0`, where the zeroth ideal power is the whole ring.
`norm_inclusion` lifts the norm comparison above to equality of field units.

The imported `UnramifiedAlgebra.proof` supplies preservation and one-level
approximation for the integer determinant norm. Its finite-free proof uses
the finite-residue-field norm at level zero, the residue trace at positive
levels, and the first-order norm expansion. The private `preserves` and
`approximates` lemmas transport those conclusions through
`integerUnitsInclusion`: they retain explicit integer-unit witnesses in the
actual reduction kernel, and `norm_inclusion` identifies their images with
the field norm. The approximation error is exactly
`y * (normUnits F.Carrier E.Carrier x)⁻¹` in target level `n + 1`.

Finally, apply the published `unitFiltrationCompactLifting.{u,v}` to the
actual continuous homomorphism `localNorm T S`. Its underlying monoid
homomorphism is `normUnits`. The imported lifting theorem uses successive
corrections, compact intersections of closed approximate-preimage sets, and
separation of the actual filtration to turn these one-level approximations
into exact surjectivity at every starting level. Preservation supplies the
opposite inclusion. The topologies remain those of `T` and `S`, and the
two universe parameters remain independent throughout.

## Provenance and dependencies

The original source is Jean-Pierre Serre, *Local Fields*, Greenberg
translation, GTM 67 (1979), Chapter V, Section 1, Lemma 2, and Section 2,
Propositions 1–3, corollary, finite-residue-field remark and non-Galois
exercise, printed pp.81–82 (PDF pp.88–89). Worker 26 read these pages and
the chapter introduction in the retained original. Registered source:
`serre-1979-local-fields`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`,
at `/home/taskhub/central-library/Serre--Local Fields--1979.pdf`.

Serre obtains surjectivity from the residue norm, residue trace and
completeness of the filtration. The implemented proof factors this argument
through the existing arithmetic and compact-lifting theorems. The private
ideal-power cancellation, localization comparison and witness transfers are
derived algebraic bridges for the supplied-data formulation; they are not
claimed as separately stated results in Serre.

The arithmetic theorem is imported from
`Langlands.LocalClassField.UnramifiedAlgebraProof`, authored by Worker 96
with Worker 26 contributing its formulation and suggested route. The
topological theorem is imported from
`Langlands.ClassFieldTheory.Local.UnitFiltrationTopologyProof`, authored by
Worker 92 using the structural proof of Worker 102. Those modules are
reused by their published declarations, not copied into this proof.
The other project inputs are the published relative-integer construction,
normalization proof, and unit-norm statement with its actual norm and unit
definitions. No local reciprocity or local invariant theorem is used.

The implementation uses Lean 4.34.0 and Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`. The additional Mathlib imports
provide the localization comparison for norms and freeness of torsion-free
finite modules over a PID.
