# Proof: Murre's condition (F3) for the two-axis class presheaf

Author: Worker 385.

This module proves the published proposition
`Langlands.AlgebraicGeometry.Picard.NoetherianTwoAxisClassAdicLimitsStatement`:

```lean
theorem Langlands.AlgebraicGeometry.Picard.noetherianTwoAxisClassAdicLimits :
    NoetherianTwoAxisClassAdicLimitsStatement.{u}
```

The proof is unconditional. Its only axioms are `propext`, `Classical.choice` and `Quot.sound`.

## The statement

Let `R` be a noetherian ring and `A` an abelian scheme over `Spec R`. Let `B` be a complete
local noetherian ring with maximal ideal `m`, and let `f : Spec B ⟶ Spec R`. Write `T = Spec B`
and `T_n = Spec (B/mⁿ)` as objects of `Over (Spec R)`. A class over `T` is an isomorphism class
of line bundles `L` on the self-product `P = A_T ×_T A_T`, with compatible trivializations along
the two unit axes. The condition `UnramifiedFunctor.AdicLimits` has two parts:

1. (injectivity) two classes over `T` with equal restrictions to every `T_n` are equal;
2. (existence) every family of classes `s n` over `T_n` that is compatible under the transition
   maps `T_n ⟶ T_{n+1}` is the family of restrictions of one class over `T`.

The proof uses two facts throughout (both in the helper module
`TwoAxisClassProductBaseChange`):

- a class is determined by the isomorphism class of its underlying line bundle
  (`mk_eq_mk_of_carrierIso`, `nonempty_carrierIso_of_mk_eq_mk`, `classesPullback_mk_eq_iff`),
  because on an abelian scheme any isomorphism of carriers can be corrected to respect the
  rigidifications;
- restricting a class along a test map `h` pulls back its carrier along `productMap A h`, and
  `productMap A h` is a base change of `h` (`productMap_isPullback`).

So the rigidifications never need to be carried through limits: they are discarded and
reconstructed at the end.

## Injectivity: `nonempty_carrierIso_of_forall_adic`

Let `L`, `M` be line bundles on `P` whose pullbacks along every `productMap A (T_n ⟶ T)` are
isomorphic. Apply the published seesaw theorem `noetherianLineBundleSeesaw` to the structure map
`c : P ⟶ Spec B`, with test scheme `Spec B` itself and the identity map. Its hypotheses hold:
`c` is proper, flat and geometrically integral, and global functions on every affine base
change of `P` are the functions on the base (helper module). The theorem gives a closed
immersion `ι : Z ⟶ Spec B`. A map `ψ : T' ⟶ Spec B` factors through `ι` exactly when the pullbacks
of `L` and `M` to `P ×_B T'` are locally isomorphic over `T'`.

- Each `ψ_n : Spec (B/mⁿ) ⟶ Spec B` factors through `ι`. Indeed, `P ×_B T'` maps to the
  self-product over `T_n` via the cartesian square `productMap_isPullback`. Pulling the given
  isomorphism back along that map gives a global, hence local, isomorphism
  (`LocallyIsoOver.of_iso`).
- Hence every `b` in the kernel of `ι` on global sections maps to zero in each `B/mⁿ`, that is,
  `b ∈ ⋂ mⁿ`. By Krull's intersection theorem (`Ideal.iInf_pow_eq_bot_of_isLocalRing`) `b = 0`.
  So `ι` is injective on global sections, and Mathlib's
  `IsClosedImmersion.isIso_of_injective_of_isAffine` makes `ι` an isomorphism.
- Then the identity of `Spec B` factors through `ι`. So `L` and `M` are isomorphic over an open
  neighbourhood `V` of the closed point. The preimage of `V` contains all of `P`, because every
  point of `Spec B` specializes to the closed point
  (`IsLocalRing.specializes_closedPoint`). The published `nonempty_pullback_iso_of_restrict_iso`
  turns this into an isomorphism along the section `P ⟶ P ×_B Spec B`, and so `L ≅ M`.

The injectivity half of `noetherianTwoAxisClassAdicLimits` takes two classes `⟦L⟧`, `⟦M⟧` with
equal restrictions. It converts each equality into an isomorphism of pulled-back carriers
(`nonempty_carrierIso_of_mk_eq_mk`), applies `nonempty_carrierIso_of_forall_adic`, and concludes
with `mk_eq_mk_of_carrierIso`. Completeness of `B` is not used in this half.

## Existence: `exists_classesPullback_eq`

Notation (all in namespace `TwoAxisClassAdicLimits`):

- `adicTest B f n` is `T_n`, `adicTestBase B f n : T_n ⟶ T` its structure map, and
  `adicTestTransition B f n : T_n ⟶ T_{n+1}` the transition map of the statement.
  `algHomOver_comp_algebraOverBase` and `adicTestTransition_comp` show that the transition
  followed by the structure map is the structure map.
- The published `FormalLineBundleSystem` lives on the thickenings
  `adicSpace c m n = P ×_{Spec B} Spec (B/m^(n+1))`. Note the index shift `n+1`.
  `adicBaseProjection_eq` and `adicBaseTransition_eq` identify the base maps used there with
  `adicTestBase B f (n+1)` and `adicTestTransition B f (n+1)`.
- `adicComparison A B f n` is the map from `adicSpace c m n` to the self-product over `T_{n+1}`,
  obtained from the cartesian square `productMap_isPullback`. `adicComparisonInv` and
  `adicComparisonIso` show that it is an isomorphism. `adicComparison_productMap` and
  `adicComparison_hom` record its two projections. `adicTransition_comparison` shows that it
  intertwines the published `adicTransition` with `productMap A (adicTestTransition B f (n+1))`.

Given a compatible family `s`, choose representatives `(s n).out`. `repBundle A B f s n` is the
underlying actual line bundle of `(s n).out`.

1. `formalSystem A B f s hs` is the formal line-bundle system whose `n`-th member is the pullback
   of `repBundle (n+1)` along `adicComparison n`. Its transition isomorphisms come from
   `adicTransition_comparison`, the pullback-composition isomorphism `pullbackCompIso`, and the
   carrier isomorphism `pullback (productMap A (adicTestTransition (n+1))) (repBundle (n+2)) ≅
   repBundle (n+1)`. That last isomorphism exists by `classesPullback_mk_eq_iff` and the
   compatibility `hs (n+1)`; it is chosen with `Classical.choice`. The published system has no
   cocycle condition, so nothing further is needed.
2. The published `properFormalLineBundleEffectivity`, applied over the complete local noetherian
   ring `B` to the proper map `c`, gives a line bundle `E` on `P` and a comparison `φ` of its
   restriction system with `formalSystem`.
3. For each `n`, the map `productMap A (T_{n+1} ⟶ T)` equals the inverse of `adicComparison n`
   followed by `adicProjection n`. So `φ.component n` gives an isomorphism
   `e : pullback (productMap A (T_{n+1} ⟶ T)) E ≅ repBundle (n+1)`.
4. `E` need not be trivial along the two unit axes of `P`. Replace it by the Library's normalized
   bundle `E' = LineBundle.twoAxisNormalizedBundle pullbackTensorComparisonIsIso A_T E`. `E'` has
   the canonical compatible rigidification `twoAxisNormalizedBundleRigidification`. The candidate
   class is `x = ⟦ofLineBundle E' ρ⟧`.
5. The representative `(s (n+1)).out` is rigidified, so `repBundle (n+1)` is trivial along both
   axes. The published `twoAxisNormalizedBundleRestrictionIso` then turns `e` into an isomorphism
   between the pullback of `E'` along `productMap A (T_{n+1} ⟶ T)` and `repBundle (n+1)`. Its
   axis-square inputs are `productMap_fst`, `productMap_snd`, `first_naturality` and
   `second_naturality`, and its axis trivializations are the inverses of the two rigidification
   isomorphisms of the representative. `mk_eq_mk_of_carrierIso` gives that the restriction of `x`
   to `T_{n+1}` is `s (n+1)`.
6. For an arbitrary `n`, `s n` is the restriction of `s (n+1)` along the transition. By
   `classesPullback_comp` and `adicTestTransition_comp` this is the restriction of `x` to `T_n`.

The existence half of `noetherianTwoAxisClassAdicLimits` is `exists_classesPullback_eq`. The
presheaf's restriction maps are definitionally `classesPullback`, so no conversion is needed.

## Provenance

Condition (F3) is from Murre's representability criterion, as encoded in
`UnramifiedFunctor.AdicLimits`. The mathematical route is the standard one: separation via the
seesaw locus and Krull's intersection theorem, and existence via Grothendieck's existence
theorem for line bundles on proper schemes over a complete local noetherian ring (the published
`properFormalLineBundleEffectivity`), followed by renormalization along the unit axes. The Lean
proof and its helper declarations are original to this project.
