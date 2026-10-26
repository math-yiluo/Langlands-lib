# Synchronized local algebra and module tower systems

This module supplies a concrete data interface for the simultaneous approximation
construction in the proof of Stacks Project Lemma 10.128.8, tag **00R7**. It imports
`Langlands.Algebra.LocalApproximationSystem` unchanged. All new names below are
in `Langlands.Algebra`. The structures contain diagram data, and the Prop-valued
predicates specify approximation properties. No existence or flatness result is
asserted.

## Source and provenance

The registered original is `stacks-algebra-flatness-criteria-2026-10-22`, content
SHA256 `4bc1f2db6141508f6dad2132d4abc7963380cd71497ad20620c0e511b972a949`.
The relevant passages are `00R7.html`, Lemma 10.128.8, its construction through the
three ring localization conditions and the module transition isomorphisms;
`00QV.html`, Lemma 10.127.11, its four approximation conditions and proof; and
`00QL.html`, Lemma 10.127.13 (00QX), its six conditions and proof. Online originals:
[00R7](https://stacks.math.columbia.edu/tag/00R7),
[00QV](https://stacks.math.columbia.edu/tag/00QV), and
[00QX](https://stacks.math.columbia.edu/tag/00QX).

The source builds local rings on one common directed tail, first approximating
`R → S`, then adjoining the presentation of the upper ring, and finally a finite
module presentation. Here the upper ring called `S′` in the source is called `T`.
The tensor transition conditions come from this simultaneous construction, with
prime localization understood as in 00QV/00QX. The structure packaging, explicit
cocones, projection names, direct-limit comparisons, and universe choices are
an internal API derived from those passages, not a named source definition.

The source finite-presentation hypotheses belong to the later existence theorem.
They are unnecessary for defining a tower and its approximation specification.
Likewise, nonzeroness and the two flatness hypotheses of 00R7 do not belong in
these data or predicates.

No central errata note for this source was found. The registered 00QV comments
record a corrected polynomial-map typo and leave its essential-finite-type
condition unchanged. The online pages and comments were also checked. There are
three internal cautions about 00R7: a flattened upper polynomial quotient must
retain the lower defining relations; the presentation matrix has coefficients
in the upper stage ring; and the final plain tensor equalities in the proof omit
localization. These are internal observations, not published errata. This module
does not encode any of those three displayed identifications.

## Shared ring data and projections

`LocalAlgebraTowerSystem.{uI,uA,uB,uC,uR,uS,uT} ι R S T` assumes a nonempty directed
preorder `ι`, commutative local rings `R`, `S`, `T`, algebra structures for all
three arrows, and `IsScalarTower R S T`. Only the adjacent ambient algebra maps
are assumed local. `LocalAlgebraTowerSystem.composite_local R S T` proves locality
of `algebraMap R T` by rewriting it as the composite and using Mathlib's locality
of a composite. There is no additional composite-locality hypothesis.

For a tower `D`, its fields are:

| Data | Meaning |
| --- | --- |
| `rs` | The actual published `LocalAlgebraSystem ι R S` for `Rᵢ → Sᵢ`, including its rings, actions, transitions and cocones. |
| `top i` | The upper local ring `Tᵢ`, with `topCommRing` and `topLocalRing`. |
| `upperAlgebra`, `upper_local` | The local algebra map `Sᵢ → Tᵢ` on `rs.alg i` itself. |
| `topMap`, `top_directed`, `topMap_local` | Local upper transition maps, with identity and composition laws. |
| `topMap_comm` | The upper transition square commutes with `rs.algMap`. |
| `topι`, `topι_local`, `topι_compat` | The local cocone `Tᵢ → T`, compatible with upper transitions. |
| `topι_comm` | This cocone intertwines `Sᵢ → Tᵢ` with the actual ambient map `S → T`. |

`D.st` is the canonical `LocalAlgebraSystem ι S T`. Its base rings, base
transitions and base cocone are definitionally `D.rs.alg`, `D.rs.algMap` and
`D.rs.algι`; its upper counterparts are `D.top`, `D.topMap` and `D.topι`.

The instance `D.compositeAlgebra i` defines the action of `Rᵢ` on `Tᵢ` from
`(algebraMap Sᵢ Tᵢ).comp (algebraMap Rᵢ Sᵢ)`. The instance
`D.componentTower i` proves compatibility, and `D.composite_algebraMap i r`
is the pointwise defining equation. Thus there is no independently chosen third
component action requiring identification.

`D.rt` is the canonical `LocalAlgebraSystem ι R T`. It uses `D.rs.base` and
`D.top`, the corresponding stored transitions and cocones, and the composite
component algebra. Its transition square follows by the two adjacent transition
squares; its cocone square follows by the adjacent cocone squares and the ambient
scalar-tower equation. Both `st` and `rt` are abbreviations, so their shared data
reduce directly. `rt` installs the proved ambient composite-locality instance.
When applying generic functions to this projection, a consumer can install
`letI := LocalAlgebraTowerSystem.composite_local R S T` as well.

## Shared module data

`LocalModuleTowerSystem.{uI,uA,uB,uC,uN,uR,uS,uT,uM} D M` assumes only an additive
commutative group `M` with a `T`-module structure and stores
`stModule : LocalModuleSystem D.st M`. Its objects are `Mᵢ`, its actions are the
`Tᵢ`-actions, its transitions are semilinear over `D.topMap`, and its cocone is
semilinear over `D.topι`. No extra ambient `R`- or `S`-module instance on `M` is
chosen. Such actions can be obtained later by restricting scalars.

`E.rtModule` is the `LocalModuleSystem D.rt M` using exactly the same objects,
additive groups, `Tᵢ`-actions, transitions and cocones. The `objModule` instance
exposes the stored action directly on `D.top i`. The three reflexive lemmas
`rtModule_moduleColimitMap`, `rtModule_moduleBaseChangeMap`, and
`rtModule_moduleToLimitMap` state equality of the comparison maps for the two
projections. They do not transport across chosen isomorphisms.

## Colimits and simultaneous approximation

`LocalAlgebraTowerSystem.IsColimit D` is
`D.rs.IsColimit ∧ D.st.IsColimit`. The imported predicates mean bijectivity of
actual `Ring.DirectLimit.lift` maps on the specified cocones. This includes all
three ring diagrams. The middle ring comparison is repeated, since the base
comparison of `st` is definitionally the algebra comparison of `rs`; no extra
choice is made by repeating it.

`LocalModuleTowerSystem.IsColimit E` adds bijectivity of
`E.stModule.moduleColimitMap`. This is the actual underlying additive
`AddCommGroup.DirectLimit.lift`. The stored semilinear maps and cocone retain
compatibility with the varying ring actions, as in the imported API. This module
does not introduce a different abstract module-colimit object.

`LocalAlgebraTowerSystem.IsApproximation D : Prop` is the conjunction of:

1. `D.rs.IsApproximation`: genuine colimits for `Rᵢ` and `Sᵢ`, essential finite
   type of `Rᵢ` over `ℤ` and `Sᵢ` over `Rᵢ`, and prime localization of the canonical
   transition `Sᵢ ⊗[Rᵢ] Rⱼ → Sⱼ`;
2. `D.st.IsColimit`, supplying the upper ring colimit and repeating the same
   middle ring colimit;
3. `Algebra.EssFiniteType (D.rs.alg i) (D.top i)` for every stage;
4. `D.st.IsPrimeLocalization h` for every transition;
5. `D.rt.IsPrimeLocalization h` for every transition.

The last two clauses concern the canonical maps `Tᵢ ⊗[Sᵢ] Sⱼ → Tⱼ` and
`Tᵢ ⊗[Rᵢ] Rⱼ → Tⱼ`. They reuse `LocalAlgebraSystem.ringBaseChangeMap` and
`IsPrimeLocalization`, so localization uses the algebra induced by the exact
canonical map. The source describes the composite localization condition as a
consequence of the adjacent ones. It is retained explicitly as a logically
redundant requirement for later direct use; this unit does not prove that
implication. The specification does not separately require `Sᵢ/ℤ` or `Tᵢ/Rᵢ`
to be essentially finite type: those are transitive consequences of the stated
adjacent conditions.

`LocalModuleTowerSystem.IsApproximation E : Prop` requires `D.IsApproximation`,
bijectivity of the additive module colimit map, `Module.Finite (D.top i)
(E.stModule.obj i)` at every stage, and bijectivity of every
`E.stModule.moduleBaseChangeMap h`. This is the canonical `Tⱼ`-linear map

```
Tⱼ ⊗[Tᵢ] Mᵢ → Mⱼ,       t ⊗ m ↦ t • E.stModule.map i j h m.
```

The imported API uses scalar-first order; tensor commutativity identifies it
with the module-first order in the source. The identical map for `rtModule`
needs no second bijectivity clause. These predicates contain no flatness,
eventual-flatness, nonzeroness, residue-fibre criterion, or existence assertion.

## Canonical maps to the target

The extension `LocalAlgebraSystem.RingToLimit D i` is `Sᵢ ⊗[Rᵢ] R`, using the
algebra on `R` induced by the exact cocone `D.baseι i`.
`LocalAlgebraSystem.ringToLimitMap` is a ring homomorphism built with
`Algebra.TensorProduct.lift` and the cocone commuting square. Its equation is

```
D.ringToLimitMap i (s ⊗ r) = D.algι i s * algebraMap R S r.
```

The tower abbreviations `D.rsToLimitMap i` and `D.stToLimitMap i` give
`Sᵢ ⊗[Rᵢ] R → S` and `Tᵢ ⊗[Sᵢ] S → T`. Their `_tmul` lemmas expose the same
formulas with the stored tower cocones. One may also apply the generic definition
to `D.rt` after installing composite locality.

`LocalModuleSystem.moduleToLimitMap E i` is constructed using
`LinearMap.liftBaseChange`, restriction of scalars along the exact upper cocone,
and semilinearity of `E.ιM i`. On the tower,
`LocalModuleTowerSystem.moduleToLimitMap E i` is the `T`-linear map

```
T ⊗[Tᵢ] Mᵢ → M,       t ⊗ m ↦ t • E.stModule.ιM i m.
```

All `_tmul` lemmas are reflexive computations of these lifts. They require no
approximation hypothesis. There is no localization or bijectivity claim for any
stage-to-target map here; those comparison results would require further proofs.
The imported generic definitions are extended in this new module without editing
the published `LocalApproximationSystem` pair.

## Universes and scope

The index has universe `uI`; the shared component rings have independent
universes `uA,uB,uC`; the component modules have universe `uN`. The ambient
carriers `R,S,T,M` have four further independent universes `uR,uS,uT,uM`.
The component choices do not restrict or identify the ambient universes.
In particular, the ring direct limits have universes `max uI uA`, `max uI uB`,
`max uI uC`, and the additive limit has universe `max uI uN`; their comparison
maps may target different universes. `D.rs.RingToLimit i` and
`D.st.RingToLimit i` have universes `max uB uR` and `max uC uS` respectively.

A later existence theorem must choose sufficiently large index and component
universes, for example a common maximum of its input universes. This interface
does not claim that one fixed small universe suffices for every ambient tower.
It also does not assemble independently obtained systems by unproved
identifications. Directed-tail restrictions, generic 00QV/00QX existence, 00R6
descent, residue-fibre systems, and the regular-module adapter are separate work.
