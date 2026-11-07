# Characters in the assembly of the relative Weil functional equation

## Contents

This module supports the proof of
`Langlands.Global.FunctionalEquationComparison.RelativeWeilTwistFunctionalEquationStatement`.
It collects the facts about characters that the final assembly needs. These are reciprocity
characters of relative Weil groups, Hecke characters composed with the idele-class norm, and
the local components of the additive character `ψ ∘ Tr`. Two published propositions enter
as explicit hypotheses and are not proved here: `TransferCharacterFactorization` (module
`Langlands.ClassField.Global.RelativeWeilCharacterFactorizationStatement`) and
`TransferNormCompatibility` (module `Langlands.ClassField.Global.RelativeWeilTransferNormStatement`).
`Gal(E/F)` carries the discrete topology `relativeGaloisTopology` in the
`RelativeWeilGroup` namespace, as in the published relative Weil modules.

### Reciprocity characters

Namespace `Langlands.ClassField.Global.RelativeWeilGroup`. `continuousReciprocityCharacter c F E χ`
is the published continuous form of `χ ∘ τ_F = (χ ∘ transfer)⁻¹`
(`Langlands.Global.Factors.RelativeWeilBrauer`).

- `continuousReciprocityCharacter_apply`: its value at `t` is `(χ (transfer c F E t))⁻¹`.
- `continuousReciprocityCharacter_mul`, `continuousReciprocityCharacter_inv`: it is
  multiplicative in `χ`.
- `exists_eq_continuousReciprocityCharacter` (hypothesis `TransferCharacterFactorization c F E`):
  every continuous character `θ` of `W_{E/F}` equals `continuousReciprocityCharacter c F E l` for
  some Hecke character `l` of `F`.
- `continuousReciprocityCharacter_apply_of_transfer_eq`: let `φ : G → W_{E/F}` and
  `f : G → (F_v)ˣ` satisfy `transfer (φ y) = (ofAdicCompletion v (f y))⁻¹` for all `y`, at a
  finite place `v`. Then `continuousReciprocityCharacter c F E l (φ y)` is the component
  `l.finiteComponent v (f y)`. This applies to the local maps of the published N2 and N3
  statements, whose transfers are inverse local reciprocity.
- `continuousReciprocityCharacter_comp_restrictionInclusion` (hypothesis
  `TransferNormCompatibility c F K E h`): the restriction of `χ ∘ τ_F` to `W_{E/K}` along
  `restrictionInclusion` is `(χ ∘ N_{K/F}) ∘ τ_K`.

### Idele norms of ideles supported at one place

Namespace `Langlands.Global.AdelicFunctoriality`, for a finite extension `L / K` of number
fields.

- `ideleNorm_ofAdicCompletion`, `ideleClassNorm_ofAdicCompletion`: the (class) norm of the
  idele supported at a finite place `q` above `p` with value `x` is supported at `p`, with value
  the local unit norm `FiniteExtension.localUnitNorm p q x`.
- `ideleNorm_ofCompletion`, `ideleClassNorm_ofCompletion`: the same at an infinite place
  `w` above `v`, with `InfiniteExtension.localUnitNorm v w`.

### The local components of `ψ ∘ Tr`

- `localTraceCharacter p q ψp`: the additive character `ψp ∘ Tr_{L_q/K_p}` of the completion
  `L_q`, for an additive character `ψp` of `K_p`. Here `Tr` is the published
  `FiniteExtension.localTrace` (`Langlands.Global.AdelicFunctoriality.Trace`).
  `localTraceCharacter_apply` gives its values.
- `isFiniteAdditiveComponent_traceAdditiveCharacter`: if `ψp` is the component at `p` of a
  character `ψ` of `A_K` trivial on `K`, in the sense of the published
  `HeckeFunctionalEquation.IsFiniteAdditiveComponent`, then `localTraceCharacter p q ψp` is the
  component at `q` of the published `traceAdditiveCharacter ψ hψ = ψ ∘ Tr_{A_L/A_K}`.

### Hecke characters composed with the norm

Namespace `Langlands.Global.HeckeCharacter`.

- `normComp χ`, the main definition: the Hecke character `χ ∘ N_{L/K}` of `L`, for a Hecke
  character `χ` of `K`.
- `normComp_finiteComponent`: its component at a finite place `q` above `p` is
  `χ.finiteComponent p ∘ localUnitNorm p q`.
- `normComp_isUnramifiedAt`: it is unramified at every place above a place where `χ` is
  unramified.
- `infiniteComponent_eq_one_of_hasPrescribedInfinityComponent_one`: a Hecke character
  trivial on the archimedean ideles (`HasPrescribedInfinityComponent 1`) has trivial
  archimedean components.
- `normComp_infiniteComponent_eq_one`: for such `χ`, every archimedean component of
  `normComp χ` is trivial.

## Source and provenance

John Tate, *Number theoretic background*, Proc. Sympos. Pure Math. 33, Part II (1979),
3–26 (registered `tate-1979-number-theoretic-background`). Printed page `p` is PDF page `p + 9`.

- §1.1, printed p.3, and (1.2.2), printed p.4: reciprocity maps of Weil groups and their
  compatibility with the norm. The reciprocity-character lemmas restate the published
  statements `TransferCharacterFactorization` and `TransferNormCompatibility` in the form the
  assembly uses.
- Theorem (3.4.1) and (3.4.8), printed pp.14–15: the additive character `ψ ∘ Tr` of a finite
  extension of local fields.

The idele-norm computations, the norm-composed Hecke characters and the component lemmas are
internal bookkeeping on published definitions (`ideleNorm`, `ideleClassNorm`,
`HeckeCharacter.finiteComponent`, `HeckeCharacter.infiniteComponent`,
`traceAdditiveCharacter`).

## Proof

- The reciprocity-character lemmas unfold `continuousReciprocityCharacter` pointwise
  (`DFunLike.ext`). `exists_eq_continuousReciprocityCharacter` takes `l = χ⁻¹` for the
  character `χ` supplied by the factorization. `continuousReciprocityCharacter_apply_of_transfer_eq`
  rewrites with the transfer identity and `map_inv`. The restriction lemma rewrites with the
  norm compatibility.
- `ideleNorm_ofAdicCompletion` compares the two units coordinatewise. The infinite part is
  `infiniteAdeleNorm 1 = 1`. At a finite place `p'` the coordinate is a product of local norms
  over the places above `p'`. If `p' = p`, only the factor at `q` differs from `1`
  (`Finset.prod_eq_single`). Otherwise no place above `p'` equals `q`, by
  `finitePlacesAbove_under`. `ideleNorm_ofCompletion` is the same argument at infinite places,
  with `InfinitePlace.LiesOver.comap_eq`. The class versions follow from `ideleClassNorm_mk`.
- `normComp_finiteComponent` is `ideleClassNorm_ofAdicCompletion`. `normComp_isUnramifiedAt`
  uses `localUnitNorm_integral`, since local norms of valuation units are valuation units.
- `infiniteComponent_eq_one_of_hasPrescribedInfinityComponent_one`: the inclusion of an
  archimedean completion into the ideles factors through the archimedean ideles, on which
  `χ` is trivial. `normComp_infiniteComponent_eq_one` combines this with
  `ideleClassNorm_ofCompletion` at the place `w.comap (algebraMap K L)` below `w`.
- `localTraceCharacter` is `UnitaryAdditiveCharacter.comapSurjective` along the local trace.
  The trace is continuous (`continuous_localTrace`) and surjective
  (`Algebra.trace_surjective`; the completion has characteristic zero, so the extension is
  separable). `isFiniteAdditiveComponent_traceAdditiveCharacter` is the published
  `traceAdditiveCharacter_single` combined with the component hypothesis for `ψp`.
