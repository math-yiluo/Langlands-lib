# Conjugation invariance of the scalar `j` (target)

Worker 5. The module
`Langlands.Representation.Plancherel.DynamicOppositeConjugationScalar`
states one Prop-valued target,
`ConditionalDynamicOppositeConjugationScalarStatement`. It is Waldspurger's
IV.3 (3) `j(wπ) = j(π)` for the Library's canonical scalar
`conditionalCanonicalRationalScalar` (the scalar `j_P` of
`J_{P|P̄} J_{P̄|P}`, module `DynamicOppositeCanonicalScalar`), in transport
form for an arbitrary rational point `g`.

The target is not proved here. The module defines and proves what is
needed to state it:

- transport of regular and rational functions on unramified characters
  along an isomorphism of affine group schemes;
- the data of the conjugate cocharacter `gχg⁻¹`: Levi conjugation, the
  conjugate representation, the isomorphism of the actual centralizer
  schemes, and the Iwasawa decompositions for `gKg⁻¹`.

It also proves the form of the target in which the conjugate data use any
compact open subgroup equal to `gKg⁻¹`, for example `K` itself when `g ∈ K`.

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques
(d'après Harish-Chandra)*, J. Inst. Math. Jussieu 2 (2003), 235–333, DOI
10.1017/S1474748003000082, registered as `waldspurger-2003-plancherel`, PDF
SHA256 `4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.

- Start of IV.3, printed p.285 / PDF p.51: for `π'` in the nonempty Zariski
  open subset of `O_ℂ` where `I_P^G V'` is irreducible,
  `J_{P|P̄}(π') J_{P̄|P}(π')` is multiplication by `j_P(π')`, and `j_P` is a
  rational function on `O_ℂ`.
- IV.3 (1), printed p.285–286 / PDF p.51–52: `j_P(π)` does not depend on
  `P ∈ P(M)`; it is written `j(π)`.
- IV.3 (3), printed p.286 / PDF p.52: "Si `w ∈ W^G`, `j(wπ) = j(π)` (`wπ`
  est une représentation de `w·M`)." The proof: for every `P ∈ P(M)`, left
  translation by `w` is an isomorphism `λ(w) : I_P^G V → I_{w·P}^G wV`, and
  for `P, P' ∈ P(M)` it carries `J_{P'|P}(π)` to `J_{w·P'|w·P}(wπ)`.
- Lemma V.2.1, printed p.292 / PDF p.58, third item: `μ(sω) = μ(ω)` for
  `s ∈ W^G`, where `μ(ω) = j(ω)⁻¹ ∏_α γ(M_α|M)²`. The proof (printed p.293 /
  PDF p.59) cites IV.3 (2), (3), (5) and (6).
- `W^G` is the Weyl group of the maximal split torus `A_0` fixed in I.1
  (printed p.238 / PDF p.4), whose centralizer is `M_0`. Waldspurger's `K`
  (I.1, printed p.240 / PDF p.6) is the stabilizer of a special point of the
  apartment of `A_0`; by a standard property of special points, every
  element of `W^G` has a representative in `K`.

## Provenance

The target is a derived statement adapted to the Library's data.

**Transport form.** Waldspurger's argument does not use that `w`
normalizes anything: it compares the integrals for `(P, P', π)` with those
for `(w·P, w·P', wπ)`. The target states this comparison for every
rational point `g` of `G` and the canonical scalar: the scalar `j_{gPg⁻¹}`
of the conjugate data equals the scalar `j_P` transported along
conjugation. Waldspurger's IV.3 (3) is the case of a Weyl representative
`g = w`, combined with IV.3 (1) to pass from `w·P` to another parabolic of
`P(w·M)`. IV.3 (1) for the Library's scalars is treated separately in the
module `StandardInductionCanonicalScalarComposition` (Worker 200); this
module does not use it.

**Cocharacters.** The Library's parabolic data are dynamic: `P = P_G(χ)`,
`P̄ = P_G(χ⁻¹)`, `M = Z_G(χ)` for a cocharacter `χ`. Conjugation by `g` is
the composite `χ ≫ (G.innerIso g).hom` with the scheme inner automorphism
`Int(g)`; its parabolic, opposite parabolic and Levi are `gPg⁻¹`, `gP̄g⁻¹`
and `gMg⁻¹` on rational points.

**Compact subgroup.** The measures in the Library's integrals are
normalized by `K`: the Haar measures `radicalHaar χ K hK` and
`oppositeRadicalHaar χ K hK` on the unipotent radicals and the quotient
measures `forwardQuotientMeasure χ K hK` and `reverseQuotientMeasure χ K hK`.
Conjugation by `g` carries these normalizations to those formed with
`gKg⁻¹`.
The conjugate data are therefore formed with
`RationalDynamicSource.conjugateCompact g K` (the existing Library
construction, with rational points `{gkg⁻¹ : k ∈ K}`). When `g ∈ K`, as can be arranged
for representatives of `W^G`, this is `K` itself
(`RationalDynamicSource.conjugateCompact_eq_self`);
`conditionalDynamicOppositeConjugationScalar_of_eq` gives the target in
that form. Unlike `ConditionalDynamicOppositeContragredientScalarStatement`,
the target has no hypotheses on `K ∩ P` and `K ∩ P̄`: transport needs none.

**Parameters.** The Library parametrizes the twists `A ⊗ z` by unramified
characters `z` of the actual centralizer scheme `parameterScheme χ`, and
its scalar is an element of the field of rational functions on these
characters. Under the isomorphism
`e = parameterConjugationIso χ g : parameterScheme χ ≅ parameterScheme (gχg⁻¹)`
induced by `Int(g)`, the twist `A ⊗ z` corresponds to `gA ⊗ (z ∘ e⁻¹)`
(`parameterHomeomorph_parameterConjugationIso`). The target therefore
reads `j_{gPg⁻¹}(gA ⊗ (z ∘ e⁻¹)) = j_P(A ⊗ z)`, that is, the scalar for
`gA` is the image of the scalar for `A` under the field isomorphism
`f ↦ (z' ↦ f(z' ∘ e))`.

## Transport of functions

Section `Transport` works with affine group schemes `H`, `G` over `F` and
the regular functions `unramifiedRegularFunctions` on their unramified
characters (the subalgebra generated by the evaluations at rational
points).

- `rationalUnramifiedRegularFunctionsMap f` for `f : H ⟶ G` sends `b` to
  `z ↦ b(rationalUnramifiedCharacterRestrict f z)`. It sends the evaluation
  at `h ∈ H(F)` to the evaluation at `f(h)`
  (`rationalUnramifiedRegularFunctionsMap_evaluation`), which shows that
  the image is regular. Lemmas `_apply`, `_id`, `_comp`.
- `rationalUnramifiedRegularFunctionsEquiv e` for `e : H ≅ G` is the
  algebra isomorphism with forward map along `e.hom` and inverse along
  `e.inv`.
- `rationalUnramifiedCharacterTransport e`, the restriction along `e.inv`,
  sends a character `z` of `H(F)` to `z ∘ e⁻¹`.
  `rationalUnramifiedCharacterRestrict_transport` says that restricting it
  back along `e.hom` gives `z`.
  `rationalUnramifiedRegularFunctionsEquiv_val_transport` says that the
  transported function takes the value `b(z)` at the transported
  character; `rationalUnramifiedRegularFunctionsEquiv_symm_val` evaluates
  the inverse.

Section `FunctionField` assumes continuity of the valuation-image
projections and connected reductivity of `H` and `G`, which are the
hypotheses of `rationalUnramifiedFunctionField`.

- `rationalUnramifiedFunctionFieldEquiv … e` is the field isomorphism
  `IsFractionRing.ringEquivOfRingEquiv` of the regular-function
  isomorphism. Lemmas `_algebraMap`, `_symm_algebraMap`, `_constant`
  (complex constants are fixed).
- `rationalFunctionRegularAt_equiv_iff`: the transported rational function
  is regular (`RationalFunctionRegularAt`) at the transported character iff
  the original function is regular at the original character.
- `rationalFunctionNonnegAt_equiv_iff`: the same for
  `RationalFunctionNonnegAt` (regular with a nonnegative real value).

## Conjugate data

Section `Conjugation` fixes `χ` and `g : RationalPoint F G.X`.

- `inverseCocharacter_conjugate`: `(gχg⁻¹)⁻¹ = g χ⁻¹ g⁻¹` as cocharacters.
- `conjugateLevi_mem_iff`, `conjugateParabolic_mem_iff`,
  `conjugateOppositeParabolic_mem_iff`: `gxg⁻¹` lies in the Levi,
  parabolic, opposite parabolic of `gχg⁻¹` iff `x` lies in that of `χ`. The
  Levi case is `Dynamic.mem_centralizer_conj`; the parabolic case is the
  Library's `RationalDynamicSource.parabolic_conjugation_mem_iff`; the
  opposite case applies it to `χ⁻¹`.
- `leviConjugation χ g : levi χ ≃ₜ* levi (gχg⁻¹)`, `m ↦ gmg⁻¹`, built with
  `QuotientIntegration.subgroupContinuousMulEquiv` from the conjugation
  homeomorphism `GroupScheme.rationalPointsConjHomeomorph G g`.
- `conjugateRepresentation χ g A`: the pullback of `A` along the inverse of
  `leviConjugation χ g` (`SmoothRep.pullback`), so `(gA)(gmg⁻¹) = A(m)` on
  the same space.
- `parameterConjugationIso χ g : parameterScheme χ ≅ parameterScheme (gχg⁻¹)`:
  the isomorphism of the actual centralizer schemes over `Int(g)`
  (`SubgroupFunctor.IsRepresentedBy.isoOfComap` with
  `Dynamic.centralizer_eq_comap_of_iso`).
  `parameterConjugationIso_hom_points` computes it on rational points.
- `parameterHomeomorph_apply_coe` unfolds the Library identification
  `parameterHomeomorph` of parameter points with the Levi.
  `parameterHomeomorph_parameterConjugationIso` proves the compatibility
  `parameterHomeomorph (gχg⁻¹) ∘ e = leviConjugation χ g ∘ parameterHomeomorph χ`.
- `conjugate_parabolic_mul_compact`, `conjugate_oppositeParabolic_mul_compact`:
  from `G = P K` and `G = P̄ K`, the decompositions
  `G = gPg⁻¹ · gKg⁻¹` and `G = gP̄g⁻¹ · gKg⁻¹`.

## The target

In the target the local notations stand for the conjugate data:
`χg = χ ≫ (G.innerIso g).hom`, `Kg = RationalDynamicSource.conjugateCompact g K`,
`hKg = RationalDynamicSource.conjugateCompact_isCompact g K hK`,
`hPKg = conjugate_parabolic_mul_compact χ g K hPK`,
`hOppKg = conjugate_oppositeParabolic_mul_compact χ g K hOppK` and
`Ag = conjugateRepresentation χ g A`.

`ConditionalDynamicOppositeConjugationScalarStatement` quantifies over a
nonarchimedean local field `F`, an affine group scheme `G` of locally
finite type, a cocharacter `χ`, the premises `hRefl`, `hCST`,
`hG : IsConnectedReductive G`, a rational point `g`, a compact open
subgroup `K` with `hPK : G = P K` and `hOppK : G = P̄ K`, and a smooth
representation `A` of `M(F)`. It takes:

- conditional data of the canonical scalar for `(χ, K, A)`, exactly as
  taken by `conditionalCanonicalRationalScalar`: continuations `p`, `q`,
  open nonempty `DForward ⊆ forwardFullDomainRegion χ K hK A` and
  `DReverse ⊆ reverseFullDomainRegion χ K hK A`, and an open nonempty `D`
  on which the unramified induction of `A ⊗ z` is irreducible (`hi`);
- independent conditional data `p'`, `q'`, `DForward'`, `DReverse'`, `D'`,
  `hi'` of the same kind for `(χg, Kg, Ag)`.

Its conclusion is

```
conditionalCanonicalRationalScalar χg … Kg hKg hPKg hOppKg Ag p' q' … hi'
  = rationalUnramifiedFunctionFieldEquiv … (parameterConjugationIso χ g)
      (conditionalCanonicalRationalScalar χ … K hK hPK hOppK A p q … hi).
```

`conditionalDynamicOppositeConjugationScalar_of_eq` assumes the target and
gives the same conclusion when the conjugate data are formed with any
compact open subgroup `K₁` with `hK₁ : Kg = K₁`, any proofs of its
compactness and of `G = gPg⁻¹ K₁ = gP̄g⁻¹ K₁`, and conditional data for
`(χg, K₁, Ag)`. The proof substitutes `hK₁` and applies the target; the
proofs of the Prop-valued hypotheses agree by proof irrelevance. With
`hK₁ = RationalDynamicSource.conjugateCompact_eq_self g K hg` for `g ∈ K`,
both scalars are formed with `K`.

## Intended use

The target is meant to be proved as Waldspurger proves IV.3 (3). Left
translation by `g` maps compact-picture sections for `(χ, K, A ⊗ z)` to
those for `(χg, Kg, Ag ⊗ (z ∘ e⁻¹))`. On the convergence domains it
intertwines the forward and reverse integrals, because the normalized Haar
measures on the unipotent radicals and the quotient measures correspond
under conjugation (`RationalSourceHaarConjugation`). It maps the
convergence domains and the irreducibility loci for `A` onto those for
`Ag`. Then the composites `J_{P|P̄} J_{P̄|P}` on the two sides are the same
scalar on a nonempty open set, and the rational functions agree.

Together with IV.3 (1) for the Library's scalar and an identification of
the Levis `w·M = M` for Weyl representatives `w` normalizing `M`, the
target gives the third item of Lemma V.2.1, `μ(sω) = μ(ω)`. That item
also needs the invariance of the product of the `γ(M_α|M)` under `s`.

## Not proved here

The target. The compatibility of the Library's integrals, measures and
convergence domains with conjugation. The combination with IV.3 (1) for a
Weyl representative normalizing `M`. The invariance of the Plancherel
density `plancherelDensity` under `W^G`.

## Axioms

The proved results use only `propext`, `Classical.choice` and `Quot.sound`.
The target is a `def … : Prop` and introduces no axioms.
