# The closed locus of the actual finite Harris Rosati equations

This internal construction specializes the published all-test finite equality
locus for maps into a chosen dual to the actual Harris Rosati equations. It
uses `HarrisIntegralRosatiBaseChange` and
`Langlands.AlgebraicGeometry.Picard.DualMapFiniteEqualityLocus`. Its provenance
is this deduction from existing constructions; it makes no new assertion
about the literature.

All public names below are in
`Langlands.Shimura.PEL.HarrisPolarizedWeilLevel`. The arithmetic data are the
existing universe-zero number fields, central simple unitary datum `D`, and
normalized signature charts `C`. Write `O` for
`D.harrisHodgePELIntegralOrder C`, `b_k` for its finite integer basis
`D.harrisHodgePELIntegralBasis C`, and `tau` for
`D.harrisHodgePELIntegralInvolution C`. These are the existing order and
positive auxiliary left involution.

The input family is an actual abelian scheme `B` over an arbitrary
`S : Scheme.{s}`, together with `hB : HasDualScheme B`, an evaluation line
bundle `MB`, its evaluation isomorphism, and `DualSchemeGeometry B hB`.
The named tensor comparison, composition, unit, associativity, left-unitor,
symmetry, and Picard-zero pullback prerequisites are supplied explicitly.
They define the existing actual dual abelian scheme `DB` and contravariant
dual homomorphism `dualInt`. The further inputs are an actual ring action
`a : O →+* End B` and an arbitrary actual homomorphism `lam : B ⟶ DB`.
In particular, this construction does not require a polarization or Rosati
condition on `lam`.

For each basis index form the actual abelian-scheme homomorphisms

```text
p_k = a(b_k) ≫ lam,
q_k = lam ≫ dualInt(a(tau(b_k))).
```

Their underlying morphisms in `Over S` are
`(groupHom p_k).hom.hom` and `(groupHom q_k).hom.hom`.
The underlying object of `DB` is definitionally `dualScheme B hB`, so both
families have the exact target required by `DualMapEquality.finiteLocus`.
The abbreviation `integralRosatiClosedLocus` is that chosen finite equality
locus. It chooses one object `Z` of `Over S` before a test is supplied.
The instance `integralRosatiClosedLocus_isClosedImmersion` obtains the closed
immersion `Z.hom` directly from the published finite-locus instance.
Construction and closedness require neither local noetherianity of `S`
nor a supplied relative Hom representative or its separatedness. If `S` is
locally noetherian, the additional instance
`integralRosatiClosedLocus_isLocallyNoetherian` proves that `Z.left` is locally
noetherian: a closed immersion is locally of finite type, and this property
transfers local noetherianity from the base.

For every `T : Over S`, without any noetherian, reducedness, or connectedness
restriction, `integralRosatiClosedLocus_nonempty_iff_pullback` proves

```text
Nonempty (T ⟶ Z) ↔
  ∀ k, (baseChange T.hom).map p_k = (baseChange T.hom).map q_k.
```

The published all-test finite-locus property first gives equality of the
underlying `Over T.left` morphisms. The proof lifts this equality to actual
abelian-scheme homomorphisms using `Grp.hom_ext` and
`Additive.toMul.injective`. In the reverse direction it applies the
underlying-morphism map to an equality. The actual abelian-scheme base-change
functor uses `Over.pullback` on these underlying maps, so the resulting
criterion is the displayed equality of actual pulled-back homomorphisms.

The remaining criteria also take the explicitly named Picard-zero universal
base-change and dual abelian base-change statements. On this particular test
`T`, supply the chosen dual datum, evaluation bundle and isomorphism, and
dual geometry for `B_T`. Let `beta` be the published canonical dual
base-change isomorphism, and set

```text
lam_T = (baseChange T.hom).map lam ≫ beta.hom,
a_T = baseChangeOrderAction T.hom B a.
```

This `lam_T` is exactly the published `dualAbelianBaseChangeMap`. The private
lemma `integralRosatiClosedPullbackEquation_iff` composes both pulled-back
sides with `beta.hom`. Functoriality identifies the left side with
`a_T(b_k) ≫ lam_T`. The published
`dualAbelianBaseChangeNaturality` identifies the right side with
`lam_T ≫ dualIntT(a_T(tau(b_k)))`. Cancellation of the isomorphism
`beta.hom` proves the equivalence in both directions; the argument assumes
no faithfulness of arbitrary base change.

Combining this calculation with the preceding all-test property,
`integralRosatiClosedLocus_nonempty_iff_basis` proves that `T` maps to `Z`
if and only if the existing `IntegralRosatiBasisEquations` hold for `a_T`
and `lam_T`. This criterion needs no dual-additivity assumption.
With the additional explicit
`DualSchemeMapAdditivity` for the actual dual maps at `T`,
`integralRosatiClosedLocus_nonempty_iff` applies the published
`integralRosatiEquations_iff_basis` and obtains exactly
`IntegralRosatiEquations`, quantified over every element of `O`.
The factorization conditions are stated as `Nonempty` of the actual Hom
types in `Over S`; the locus is a closed subobject of the base.

This removes the supplied relative Hom-representability input from this
closed-locus construction. It retains the fixed abelian family, action,
map to the chosen dual, and every displayed duality prerequisite. It does
not produce that family or action, prove a polarization condition, or
construct a space parametrizing all PEL families. The determinant and Lie
conditions, integral realization of rational data, normalized
rational-isogeny and adelic-level comparisons, admissibility, smoothness,
and division-case projectivity in the full normalized CM representability
target remain separate obligations. The imported Lean/Markdown pairs and
the target proposition are unchanged.
