# Independence of finite idele invariants from the upper place

Worker 21 proves the supporting target
`Langlands.ClassField.Global.FiniteIdeleInvariantPlaceIndependenceStatement.{u}`.
The complete unapplied type of the exported theorem is

```lean
Langlands.ClassField.Global.finiteIdeleInvariantPlaceIndependenceStatement.{u} :
  Langlands.ClassField.Global.FiniteIdeleInvariantPlaceIndependenceStatement.{u}
```

There are no additional parameters or hypotheses outside this proposition.
It quantifies every family
`I : ∀ (p : ℕ) [Fact p.Prime], InvariantFamily.{u, u} p` and requires only
`hInf : ∀ (p : ℕ) [Fact p.Prime], (I p).InflationCompatibility`.
The conclusion is the existing `FiniteIdeleInvariantPlaceIndependent I`.
Thus, for number fields `E/F` in the arbitrary common universe `u`, with
`E/F` Galois, the actual finite idele invariant of every degree-two class
is equal at any two upper places over a fixed base finite place.

## Implemented proof

The helper
`finiteIdeleInvariantPlaceIndependent_of_inflationCompatibility I hInf`
proves the existing predicate directly. Given a base place `v`, upper
places `w,z`, and a class `c`, it uses `exists_finitePlaceEquiv_eq v w z`
to find `g : E ≃ₐ[F] E` with
`finitePlaceEquiv g.toRingEquiv w = z`, then substitutes that equality.
The pullback convention for `finitePlaceEquiv` means that the published
`finiteCompletionAlgEquiv v w g` goes from the completion at `z` to the
completion at `w`, as an algebra equivalence over `v.adicCompletion F`.

The proof installs the published lying-over, local finite-dimensionality,
and local Galois instances for the two completions. It applies
`InvariantFamily.relative_relativeConjugacy_refl_of_inflationCompatibility`
to the family `I (residuePrime v)`, the p-adic base `padicField v`, this
completion equivalence, its compatibility certificate
`finiteCompletionCompatible v w g`, and the localization of `c` at `z`.
This says that applying the actual cohomology transport leaves the local
invariant unchanged. The theorem
`ideleLocalMap_finiteCompletionConjugacy_apply` identifies that transported
class with the localization of the same `c` at `w`. Rewriting gives the
required equality of `finiteIdeleInvariant` values, whose definitions are
exactly these local invariants after localization.

The target theorem introduces `I` and `hInf` and applies the helper.
The proof assumes neither `RelativeConjugacy` nor an invariant law between
different p-adic bases. It uses neither `RelativeImages` nor arithmetic
normalization to prove finite-place independence.

## Consequences for the total family

Both corollaries additionally take
`hI : ∀ (p : ℕ) [Fact p.Prime], (I p).RelativeImages`, as required to
construct the finite-support sum. They retain `I` and `hInf` above.

- `totalIdeleInvariantMaps_eq_of_inflationCompatibility I hInf hI`:
  for all number fields `F E : Type u` with `Algebra F E` and
  `IsGalois F E`, and all choices
  `wf : ∀ v : HeightOneSpectrum (𝓞 F), FinitePlacesAbove E v` and
  `wi : ∀ v : InfinitePlace F, InfinitePlacesAbove E v`, the additive
  homomorphism `totalIdeleInvariantMaps I hI F E` equals
  `totalIdeleInvariant I hI wf wi`.
- `totalIdeleInvariantMaps_inflation_of_inflationCompatibility I hInf hI`:
  the family `totalIdeleInvariantMaps I hI` satisfies the existing
  `IdeleInvariantMaps.InflationCompatible` predicate. In every finite
  number-field tower `F → E → L`, with both `E/F` and `L/F` Galois,
  this means its value after the actual `relativeIdeleInflation F E L 2`
  equals its value before inflation.

These proofs supply the newly proved finite-place independence to the
corresponding theorems in `IdeleFiniteInvariantTransfer`. In particular,
place independence is discharged; it is not an additional assumption of
either corollary. No global idele-class invariant maps are constructed in
this unit, and `GlobalInvariantStatement` is not its target.

## Provenance and checks

This is an internal derivation from the published transitivity and
completion-localization conjugacy results, the published same-base local
invariant naturality theorem, and the published conditional total-family
consequences. The proof route is described above and makes no new claim
about original literature. All original statement and imported pairs are
preserved.

The full entry module passed a development Lake build with zero errors and
warnings. Inspection of the unapplied target theorem reported exactly the
universe parameter `u` and the axioms `propext`, `Classical.choice`, and
`Quot.sound`. Its type is the target proposition displayed above, with no
extra field or family parameter. These checks establish development
compilation and the allowed-axiom boundary; independent semantic review,
exact-target validation, and publication remain separate requirements.
