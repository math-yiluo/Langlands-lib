# Regular-action and left-ideal Noetherian unitization criteria: proof

Worker 709 prepared this proof; Worker 850 checked it against the published
target and dependencies and wrote this explanation. The module imports the
published statement module `Langlands.Algebra.UnitizationIdealNoetherianStatements`
and leaves that pair and its imports unchanged. The closed theorem
`Langlands.Algebra.UnitizationIdealNoetherian.unitizationIdealNoetherian` has
the exact type
`Langlands.Algebra.UnitizationIdealNoetherian.UnitizationIdealNoetherianStatement.{uR,uA}`,
with independent scalar universe `uR` and algebra universe `uA`.

Throughout, `U` denotes `Unitization R A`, `R` is a commutative ring, `A` is
a nonunital ring whose multiplication is `R`-bilinear, and `A` carries a
supplied `U`-module structure satisfying the regular coordinate law
`u • a = u.fst • a + u.snd * a`. No identity or commutativity in `A` and
no field, finite-dimension, countability or nontriviality hypothesis is
used.

## Imported results

- `UnitizationNoetherian.noetherian_iff_kernel` (module
  `Langlands.Algebra.UnitizationNoetherianProof`): `U` is a Noetherian ring
  exactly when `R` is a Noetherian ring and the actual kernel ideal
  `RingHom.ker (Unitization.fstHom R A)` is a Noetherian `U`-module.
- `UnitizationRegularKernel.regularKernelEquiv R A hsmul` (module
  `Langlands.Algebra.UnitizationRegularKernel`): the `U`-linear equivalence
  from the supplied regular module `A` onto that kernel, `a ↦ (0, a)`.
- `UnitizationStableGeneration.noetherian_iff_stable_generators` (module
  `Langlands.Algebra.UnitizationStableGenerationProof`): for a supplied
  ordinary `U`-module `M` with scalar tower, a nonunital `R`-algebra
  representation `ρ : A →ₙₐ[R] Module.End R M` and the coordinate law,
  `IsNoetherian U M` is equivalent to finite stable generation of every
  `ρ`-stable `R`-submodule.
- `AdditiveUnitizationGeneration.noetherian_iff_additive_stable_generators`
  (module `Langlands.Algebra.AdditiveUnitizationGenerationProof`): the
  analogue for `Unitization ℤ A`, a representation
  `ρ : A →ₙ+* AddMonoid.End M` and all `ρ`-stable additive subgroups.

None of these proofs is repeated here.

## Implemented proof

`noetherian_iff_scalar_and_regular` proves the regular criterion. It rewrites
with `noetherian_iff_kernel`, keeps the conjunct `IsNoetherianRing R`, and
replaces the kernel conjunct using Mathlib's `LinearEquiv.isNoetherian_iff`
applied to `regularKernelEquiv R A hsmul`. Noetherianity of `R` is thus part
of the conclusion; it is not assumed.

`noetherian_iff_regular` is the same equivalence when `R` carries an
`IsNoetherianRing` instance: the forward direction keeps the second
conjunct, and the reverse direction supplies the first from the instance.

`noetherian_iff_scalar_stable_ideals` proves the scalar-linear ideal
criterion. It composes `noetherian_iff_regular` with
`noetherian_iff_stable_generators` for `M = A` and
`ρ = NonUnitalAlgHom.lmul R A`, Mathlib's left-multiplication nonunital
algebra homomorphism `A →ₙₐ[R] Module.End R A`. Since `ρ a x = a * x`
definitionally, the supplied coordinate law is the required action law and
the `ρ`-stable `R`-submodules are exactly the `R`-submodules `P` with
`a * x ∈ P` for all `a` and all `x ∈ P`. The supplied tower
`IsScalarTower R U A` is the one this generation result requires. In the
resulting universal property a finite set `S ⊆ P` need only generate `P`
among such stable submodules; it need not generate `P` as an `R`-module.

`noetherian_iff_additive_stable_ideals` proves the additive criterion. Here
the scalar ring is `ℤ`; its `IsNoetherianRing` instance comes from Mathlib's
Euclidean-domain and principal-ideal-domain instances, so
`noetherian_iff_regular ℤ A hsmul` applies, with Mathlib's canonical
`ℤ`-module structure on the additive group `A` and its canonical scalar
tower and commuting-action instances. The proof builds the nonunital
ring homomorphism `ρ : A →ₙ+* AddMonoid.End A` sending `a` to
`AddMonoidHom.mulLeft a`. Its zero, addition and multiplication laws follow
from `zero_mul`, `add_mul` and `mul_assoc`. Then
`noetherian_iff_additive_stable_generators A A ρ hsmul` finishes the proof.
The stable subgroups are all additive subgroups closed under left
multiplication, with no scalar-linearity condition.

`regularCriterion`, `scalarIdealCriterion` and `additiveIdealCriterion` are
these three helpers stated as the published closed propositions.
`unitizationIdealNoetherian` pairs them in the published order. The proof
adds no hypotheses and identifies neither ideal domain with the other.

## Provenance and remaining scope

These are derived internal algebraic equivalences motivated by David Renard,
*Représentations des groupes réductifs p-adiques*, version dated 9 July
2026: the global conventions (printed page 6, PDF page 12), I.2.1 (printed
page 14, PDF page 20), A.I.3 (printed pages 248–249, PDF pages 254–255) and
the final proposition of C.II (printed page 279, PDF page 285). The
registered source is `renard-2026-representations-groupes-reductifs-padiques`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The book does not state these three equivalences as numbered results, and
this proof does not follow a proof in the book.

The proof does not choose a meaning for the book's phrase “Noetherian
algebra” and does not record a correction to the book. The general
nonunital action, Hom, lattice, restriction, quotient and categorical
constructions, the comparisons with the book's finite-type and Noetherian
conventions, actual localization, the stable decomposition and the final
C.II proposition remain obligations of parent task
`f5d1f399-a1f8-4ab5-a981-90b92abd4857`.
