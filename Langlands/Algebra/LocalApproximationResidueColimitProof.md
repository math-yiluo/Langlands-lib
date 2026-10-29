# Preservation of the actual local residue-fibre colimits

`Langlands.Algebra.localApproximationResidueColimit` proves exactly the
published proposition
`Langlands.Algebra.LocalApproximationResidueColimitStatement`, with its seven
independent universe parameters `uI uA uB uN uR uS uM` in the statement's
order. Its three conclusions concern the actual residue-field ring lift,
fibre-ring ring lift, and residue-module additive lift. The statement pair
and all imported Lean/Markdown pairs are unchanged.

The setting is the statement's nonempty directed index preorder, local rings
`R → S`, and local algebra system `D`. The residue-field clause assumes
bijectivity of `D.baseColimitMap`. The fibre-ring clause assumes `D.IsColimit`,
which supplies bijectivity of both original ring comparisons. The module
clause assumes `E.IsColimit` for each module system `E` with the given compatible
target actions. No further hypotheses are imposed.

## Provenance

The unchanged statement's companion records the quotient-colimit observations
in the proofs of Stacks Lemma 10.128.8 (00R7) and Lemma 10.128.4 (046Y), from
the registered original `stacks-algebra-flatness-criteria-2026-10-22`.
Those observations concern the particular approximation systems constructed
in the source. The published proposition is an internal generalization to
any given directed local system satisfying its stated colimit assumptions.
This proof is an internal consequence of the published systems, tensor
comparisons and Mathlib direct limits; its route is not attributed to a
separately stated literature theorem. It works in the statement's tensor
presentations throughout.

The general residue-module clause is supplied by the published theorem
`Langlands.Algebra.localApproximationResidueModuleColimit` from
`Langlands.Algebra.LocalApproximationResidueModuleColimit`. This module adds
the residue-field argument, the regular-module transfer to fibre rings, and
the final conjunction. Its auxiliary declarations are in
`Langlands.Algebra.ResidueColimitProof`.

## Residue fields

`exists_residueι_eq` represents every `a : ResidueField R` at a component:
write `a = residue R r`, then use surjectivity of `D.baseColimitMap` and
`D.exists_baseι_eq` to write `r = D.baseι i r'`. The identity
`D.residueι_residue` gives the required image of `residue (D.base i) r'`.

`residueLift_bijective` proves injectivity of the actual residue-field lift
by `Ring.DirectLimit.lift_injective`, since each `D.residueι i` is a ring
map between fields and is injective. For surjectivity, take the representative
given by `exists_residueι_eq` and apply `Ring.DirectLimit.of` and the lift
formula. Only surjectivity of the original base comparison is needed to
represent elements; the final clause retains the published hypothesis.

## Fibre rings

For the fibre-ring clause, the published `regularModuleSystem` and
`regularModuleSystem_isColimit` from `RingAdditiveColimit` supply the regular
modules with their colimit property from `D.IsColimit`. At each stage these
are `D.alg i` as modules over themselves, and the target is `S` as a module
over itself.

`regularFiberEquiv D i` is an additive equivalence from
`D.FiberRing i = D.alg i ⊗[D.base i] ResidueField (D.base i)` to the raw
residue fibre of `D.regularModuleSystem`. It first inverts the tensor
right-unit equivalence over `D.alg i`, then applies the published
`fiberModuleEquiv`. This respects the raw residue module's specified
restricted base action. The helper `regularTmul` explicitly installs
`D.regularModuleSystem.objBaseModule i` when forming a pure tensor, and
`regularFiberEquiv_tmul` gives the comparison formula `s ⊗ a ↦ a ⊗ s`.
The target comparison `regularTargetEquiv` is tensor commutation from
`S ⊗[R] ResidueField R` to `ResidueField R ⊗[R] S`.

`regularFiberEquiv_map` and `regularTargetEquiv_ι` check these comparisons
against the actual `D.fiberRingMap`, `D.fiberRingι` and the regular module's
`residueFiberMap`, `residueFiberι`. The proofs use their pure-tensor formulas
and extend the equalities by tensor induction and additivity.

`fiberRingLift_bijective_of_regular` transfers bijectivity of the actual
regular-module additive lift to the actual fibre-ring lift. For injectivity,
represent a ring colimit class at a component. A zero target image gives a
zero additive target image after applying the component comparison.
Injectivity of the additive lift makes the corresponding additive class
zero. Mathlib's additive `DirectLimit.of.zero_exact` kills it at a later
stage, and compatibility and injectivity of the component comparison give
the same vanishing in the ring diagram. The ring `of_f` equation then kills
the original class. For surjectivity, take an additive preimage of the
target comparison, represent it at one component, and invert that component
comparison to get the ring preimage.

`fiberRingLift_bijective` discharges this transfer lemma's premise by applying
the published `localApproximationResidueModuleColimit` to
`D.regularModuleSystem`, using `D.regularModuleSystem_isColimit hD`.
That application specializes the general module theorem's component module
universe to the algebra-component universe and its target module universe to
the target algebra universe. The final theorem's unrelated module
universes remain arbitrary. This proves bijectivity of the actual ring lift
without constructing a ring structure on an additive direct limit.

## Assembly

The final theorem introduces the common binders of the exact published
proposition and combines `residueLift_bijective` and
`fiberRingLift_bijective` with the module clause. For that clause it applies
`localApproximationResidueModuleColimit ι R S D M E hE` at the independent
universes of the caller. The imported theorem uses the explicit
`Classical.decEq ι` required by the statement's additive lift. The proof
preserves all seven universes and adds no finiteness, approximation, flatness,
transition-injectivity, localization, Noetherian or residue-colimit
assumption.
