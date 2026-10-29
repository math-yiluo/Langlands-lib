# Lifting injectivity from the residue fibre

`Langlands.Algebra.localFiberInjectivity` proves exactly the published
`Langlands.Algebra.LocalFiberInjectivityStatement`, Stacks Project,
Lemma 10.128.4, tag [046Y](https://stacks.math.columbia.edu/tag/046Y).
For a local homomorphism `R → S` with `S` essentially finitely presented
over `R`, an `S`-linear map `f : M →ₗ[S] N` between finitely presented
`S`-modules is injective and has `R`-flat cokernel whenever `N` is
`R`-flat and the actual residue-field tensor map is injective.
The theorem preserves four independent ambient universes and the caller's
compatible base actions. It adds no hypotheses to the published proposition.

The residue map is `LinearMap.lTensor (IsLocalRing.ResidueField R)
(f.restrictScalars R)`. The concluding cokernel is the actual quotient
`N ⧸ LinearMap.range (f.restrictScalars R)` from the statement.

## Approximation and target flatness

The closing theorem applies the published
`localCompatibleMapApproximationExistence` to obtain one directed local
algebra system `D`, module systems `E` and `F` for `M` and `N`, and a
`CompatibleMap E F f`. Both systems satisfy all six approximation clauses;
the component maps induce the given `f` by their actual cocone equation.
The index and component carriers lie in the maximum of the four ambient
universes, without identifying any of those universes.

The internal helper `flat_compHom_of_isScalarTower` identifies the caller's
`Module R N` with `Module.compHom N (algebraMap R S)` using
`Module.ext'` and `algebraMap_smul`. Equality transport carries the given
flatness hypothesis to the canonical action required by the published
`localApproximationFlatnessDescent`.

`LocalModuleSystem.eventually_flat_of_descent_and_propagation` applies that
descent theorem to the specified target system `F` and obtains a flat
component. It then applies the published
`localApproximationFlatnessPropagation` at every later index. The fifth and
sixth clauses of the same `F.IsApproximation` supply prime localization of
the actual ring base-change map and bijectivity of the actual module
base-change map. Thus the argument retains the common approximation and
its compatible maps. This elementary helper is adapted from Worker 214's
fibrewise-flatness draft, with Worker 214 credited as a coauthor. The
unpublished draft helper is included in the present proof and its review;
only its imported dependencies are used as published results.

## Residue injectivity and the Noetherian component step

`residueFiberι_lTensor` proves a commuting square between the actual
component and ambient residue-tensor maps and the residue cocones.
Tensor induction reduces the square on a pure tensor to the compatible
map's cocone equation. `residue_lTensor_injective_of_cocone` uses this
square: injectivity of the ambient residue map and the source residue
cocone implies injectivity of the component residue map. Target residue
cocone injectivity is unnecessary.

`eventually_injective_and_flat_cokernel_of_noetherian_lifting` obtains
an eventual bound for source residue-cocone injectivity from the published
`localApproximationResidueInjectivity`. This imported theorem supplies
the finite-kernel stabilization step in the source. A common upper bound
with the target flatness bound gives both properties at every later stage.

Each component base ring is essentially of finite type over the integers,
and each component algebra is essentially of finite type over its base.
Mathlib's essential-finite-type Noetherian theorem, applied twice, therefore
makes the component algebra Noetherian. The approximation also supplies a
finite source component, and `D.structure_local` supplies the local ring
map. The published `noetherianLocalFiberInjectivity` (Stacks 00ME) applies
to the component map restricted to its base ring, using the preceding
residue square and target flatness. It gives eventual component injectivity
and base flatness of the component cokernels.

`flat_range_restrictScalars_iff` applies Mathlib's
`Submodule.Quotient.restrictScalarsEquiv` to identify flatness of the
base-linear range quotient with flatness of the algebra-linear range
quotient. This converts the output of 00ME to the quotients used by the
published cokernel diagram.

## Passage to the specified colimits

`injective_of_eventually_injective` represents any source element at a
component using surjectivity of `E.moduleColimitMap` and
`AddCommGroup.DirectLimit.induction_on`. If its ambient image is zero,
injectivity of `F.moduleColimitMap` makes the corresponding target
colimit class zero. `AddCommGroup.DirectLimit.of.zero_exact` then gives a
later stage where its image vanishes. A common upper bound with the
component-injectivity bound makes the source representative zero. Cocone
compatibility gives ambient injectivity. This elementary helper needs no
finiteness or flatness hypotheses.

`injective_and_flat_cokernel_of_noetherian_lifting` combines those results
with the actual `φ.cokernelSystem`. The published
`CompatibleMap.cokernelSystem_moduleColimitMap_bijective` gives its additive
colimit comparison from source-colimit surjectivity and target-colimit
bijectivity. Together with the ring-colimit comparisons in the approximation,
this proves `φ.cokernelSystem.IsColimit`. The published
`LocalModuleSystem.flat_of_eventually_flat` then gives flatness of the
ambient quotient by the `S`-linear range. The quotient equivalence above
returns exactly the restricted-range quotient in the target proposition.

The closing theorem supplies this conditional assembly with the compatible
approximation, the derived target-flatness tail, and the given ambient
residue injectivity. No conditional approximation, descent, Noetherian
lifting, colimit, or flatness premise remains in `localFiberInjectivity`.

## Provenance

The original is registered as `stacks-algebra-flatness-criteria-2026-10-22`,
content SHA256
`4bc1f2db6141508f6dad2132d4abc7963380cd71497ad20620c0e511b972a949`,
in `literature/Stacks Project - Algebra flatness criteria and essentially finite presentation (HTML snapshot 2026-10-22)/`.
The precise source is `046Y.html`, Lemma 10.128.4; the same statement and
complete proof appear in `00R3.html`, immediately after 00R6. The bounded
source check in `Stacks Project - 046Y and 00QX current errata check (HTML snapshot 2026-10-26)/README.md`
reports agreement of the relevant original passages and no comments on those
two pages at its check date.

The scalar-action adapter, residue commuting square, quotient comparison,
and final colimit arguments are internal assembly lemmas derived from the
published system interfaces and Mathlib. Their implementations explain the
explicit tensor and quotient presentations used here. The substantive
approximation, descent, propagation, residue stabilization, Noetherian
lifting and flatness-ascent proofs are imported by their current Lean names.
