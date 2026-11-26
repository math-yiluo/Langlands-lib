# Finite-character correction in Harris's Lemma 1.6: proof

`Langlands.Global.Harris.finiteCharacterConjugateDualCorrection` proves the
[Library statement](HarrisCyclicDescentCorrectionStatement.md#actual-determinant-twist)
`FiniteCharacterConjugateDualCorrectionStatement`. This is the determinant and local
step of Harris 1998, Lemma 1.6, printed p. 189.

The data are an actual rank `r + 1` cuspidal realization `S` over a CM field `E`, an
actual contragredient `Sdual` of `S` and a finite place `v`. There is also a
finite-order Hecke character `α` with `Sᶜ∨ ≃ S ⊗ ((α · αᶜ) ∘ det)` on classes. Write
`T = S.determinantTwist α hα`. Each of the three conclusions is proved by a lemma of
this module about the actual realizations and presentations involved.

## Conjugate self-duality

`OperatorRealization.determinantTwist_isConjugateSelfDual` takes operator
realizations `S` and `D` of `GL_n` over `E` with `D.IsContragredientOf S` and
`IsFiniteOrderDeterminantTwist (α * α.complexConj) S D.complexConj`. It proves that
`S.determinantTwist α hα` is conjugate self-dual. The final theorem applies it to
`S.realization` and `Sdual.realization`. The class hypothesis is this relation on
these representatives, since `isFiniteOrderDeterminantTwist_isoClass_iff` is
`Iff.rfl`. Also, `Sdual.complexConj.realization` is `Sdual.realization.complexConj`
by definition. `CuspidalOperatorRealization.isoClass_isConjugateSelfDual_iff`
returns the conclusion to the class.

The proof starts from four pieces of data:

- the contragredient pairing `B₀` between `S` and `D`;
- the linear equivalence `e : S → Dᶜ` of the twist relation, with its finite,
  compact and enveloping equations;
- the multiplication `u : S → T` by `α ∘ det` (`determinantTwistEquiv`);
- the CM image map `w : D → Dᶜ` (`complexConjEquiv`).

The pairing on `T` is `correctedPairing B₀ u e w`, that is
`B(y, x) = B₀(u⁻¹ y, w⁻¹(e(u⁻¹ x)))`. Its properties come from generic lemmas about
linear equivalences of complex vector spaces.

- **Finite and compact invariance** (`correctedPairing_invariant`). Fix a finite
  adelic matrix `d` with conjugate `d̄ = finiteConj d`. Put `a = α(det d)` and
  `b = αᶜ(det d)`. By `determinantTwistScalar_mul`, the scalar of `e` at `d` is
  `(α · αᶜ)(det d) = a b`. The operator `T(d̄)` multiplies by `α(det d̄)`, and
  `adelicDeterminant_ofFinite_finiteConj_eq` shows that this equals `b`. That lemma
  follows from `HeckeCharacter.adelicDeterminant_complexConj` and
  `RankOneHecke.adelicConj_pair`. The map `w` intertwines `D(d̄)` with `Dᶜ(d)`
  (`complexConjEquiv_finite`). Hence `u⁻¹(T(d̄) y) = b · S(d̄)(u⁻¹ y)`, and
  `w⁻¹(e(u⁻¹(T(d) x)))` is `a (a b)⁻¹` times `D(d̄)` applied to `w⁻¹(e(u⁻¹ x))`.
  The total scalar `b · a · (a b)⁻¹` is `1`, so the equation for `B` reduces to the
  invariance of `B₀` under `d̄`. The compact case is the same argument, with
  `compactConj`, `adelicDeterminant_ofInfinite_compactConj_eq` and
  `complexConjEquiv_compact`.
- **Lie invariance** (`correctedPairing_lie`). The map `u` intertwines the enveloping
  actions (`determinantTwistEquiv_differential`). So does `e`, by the third equation
  of the twist relation. `OperatorRealization.complexConjEquiv_lieAction` shows that
  `w` intertwines `D.lieAction (lieConj X)` with `Dᶜ.lieAction X`. It identifies the
  real Lie transport of the field conjugation with `lieConj` entry by entry. The same
  computation is a private lemma of `Langlands/Galois/HarrisParityBaseChangeProof.lean`.
  The Lie equation for `B` at `X` thus becomes the Lie equation for `B₀` at
  `lieConj X`.
- **The partial pairing.** By `correctedPairing_flip`,
  `B(·, x) = B₀(·, w⁻¹(e(u⁻¹ x))) ∘ u⁻¹`. The lemma
  `isContragredientFunctional_comp_of_twisted` makes this a contragredient functional
  on `T`. It applies to `u⁻¹` with the scalars `α(det)⁻¹`, which equal `1` on the open
  subgroup `heckeDeterminantKernel α`. Injectivity of the partial map follows from
  `pairing_flip_injective`. For surjectivity, take a contragredient functional `l` on
  `T`. The same lemma, applied to `u`, makes `l ∘ u` a contragredient functional on
  `S`. So `l ∘ u = B₀(·, z)` for some `z`, and `pairing_flip_surjective` gives
  `B(·, x) = l` for `x = (w⁻¹ ∘ e ∘ u⁻¹)⁻¹ z`. This is surjectivity onto all
  contragredient functionals, as `IsConjugateContragredientPairing` requires.

## Regular algebraic type

`OperatorRealization.determinantTwist_isRegularAlgebraic` holds over every number
field and for every finite-order Hecke character `χ`. Its proof uses only
`determinantTwistEquiv_differential`. That equation, stated for finite-order
characters, says that multiplication by `χ ∘ det` intertwines the actions of the
whole enveloping algebra. So a central element that acts on `S` by the scalar `c(z)`
acts on the twist by the same scalar. The twist therefore has the same regular
algebraic infinitesimal character `c`. The final theorem passes between classes and
representatives with `CuspidalOperatorRealization.isoClass_isRegularAlgebraic_iff`.

## Square-integrable component

1. `IsoClass.hasSupercuspidalComponent_iff` gives a presentation `P` of `S` whose
   local component at `v` is supercuspidal.
2. `CuspidalOperatorRealization.isUnitarizable_of_hasUnitaryCentralCharacter` turns
   the unitary central character of `S` into an invariant positive form.
   `OperatorRealization.IsUnitarizable.determinantTwist` carries that form to `T`.
   It uses that a finite-order character has modulus one.
3. `CuspidalSpectralPresentation.determinantTwist_localComponent_isSupercuspidal`
   shows that the local component of `P.determinantTwist α hα` at `v` is
   supercuspidal. That component is equivalent to the multiplied component
   `(P.localComponent v).determinantTwist α hα`
   (`determinantTwistLocalComponentEquiv`). The multiplied component is the twist by
   `α_v ∘ det` (`determinantTwistRepresentationEquiv`). Irreducibility and
   admissibility pass through (`determinantTwist_isIrreducible_iff`,
   `determinantTwist_isAdmissible_iff`).

   On canonical `p`-adic classes, `determinantQuasiCharacter_quasicharacterBase`
   makes this the character twist by `quasicharacterBase v (α.finiteComponent v)`.
   Then `isCharacterTwist_iff_eq_twist` and
   `GeneralLinear.SupercuspidalClass.toSmoothDualClass_twist` identify the new class
   with the image of `supercuspidalTwist` of the old supercuspidal class. The
   argument is that of `heckeDeterminantTwistSupercuspidal`, applied here to the
   finite-order twist of the presentation.
4. `CuspidalSpectralPresentation.localComponent_isUnitarizable` makes every local
   component of a presentation of a unitarizable cuspidal realization unitarizable.
   The component embeds by `localSubspaceInclusion` into the local restriction of the
   global form (`IsUnitarizable.localRestriction`).
5. `LocalRealization.isSquareIntegrable_of_isSupercuspidal` proves that a
   supercuspidal local realization with a unitarizable action is square-integrable
   modulo the center.

   A representative `C` of its supercuspidal class is equivalent to its canonical
   `p`-adic object (`automorphicClassOf_eq_iff`), so `C` is unitarizable too.
   `Classification.unitarizableSupercuspidal_isSquareIntegrable` then makes `C`
   square-integrable. Inside that theorem, unitarizability gives a unitary central
   character (`unitarizableCentralCharacter`), and supercuspidal representations are
   essentially square-integrable. `PadicField.TopologicalData.isSquareIntegrable_iff_of_equiv`
   carries the conclusion back to the local realization.
6. `IsoClass.hasSquareIntegrableComponent_iff` concludes with the presentation
   `P.determinantTwist α hα`. This is the presentation on which supercuspidality was
   transported.

The statement's Markdown follows the source: a unitary twist keeps the unitary
central character. The Lean proof carries the stronger unitarizability of `S`
through the twist and down to the local component, and it recovers the local unitary
central character there.
