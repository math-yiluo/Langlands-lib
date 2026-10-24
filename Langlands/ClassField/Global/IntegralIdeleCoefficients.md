# The integral-idele coefficient diagram

Let `F : Type u` and `E : Type v` be fields with `[NumberField E]` and
`[Algebra F E]`, and put `G = E ≃ₐ[F] E`. The universes are independent.
Write `J_E = NumberField.IdeleGroup (𝓞 E) E` for Mathlib's idele group,
`C_E = NumberField.IdeleClassGroup (𝓞 E) E` for its quotient by the
principal ideles `IdeleGroup.principalSubgroup (𝓞 E) E`, and
`U = (𝓞 E)ˣ` for the units of the ring of integers. This module defines the
actual subgroups, quotient and maps

\[
U \longrightarrow J_\infty \longrightarrow C_\infty \longrightarrow C_E
\longrightarrow C_E/C_\infty,
\qquad
J_\infty \longrightarrow J_E \longrightarrow C_E,
\]

with the actions of `G` restricted from or induced by the published
arithmetic actions `relativeIdeleAut F E` on `J_E` and
`relativeIdeleClassAut F E` on `C_E`. It packages them as additive
coefficient representations over the published lifted integer scalars
`k = NormalizedTwoCocycle.CoefficientScalars.{v}`, as morphisms of these
representations, and exposes their ordinary `groupCohomology`. All
declarations are in `Langlands.ClassField.Global`.

The multiplicative actions on `J∞`, `C∞` and `C_E/C∞` are explicitly named
definitions marked `@[instance_reducible]` and installed only as local
instances in this module, following the published `relativeIdeleAction` and
`relativeIdeleClassAction`. Downstream users obtain the actions through the
representations, whose `_apply` lemmas give their values.

## A generic coefficient morphism

For groups `G`, `A`, `B` in the universe `v`, with `A` and `B` commutative
and carrying multiplicative actions of `G`, `equivariantCoefficientHom f hf`
turns a homomorphism `f : A →* B` satisfying `f (g • a) = g • f a` into a
morphism

\[
\operatorname{coefficientRepresentation}(G,A)\longrightarrow
\operatorname{coefficientRepresentation}(G,B)
\]

of the published additive coefficient representations. On the additive
type tags it is `ofMul a ↦ ofMul (f a)` (`equivariantCoefficientHom_apply`).
Additivity is `map_mul f`, integer linearity is `map_zpow f` applied to the
underlying integer of a lifted scalar, and intertwining is the hypothesis
`hf`. All morphisms of representations below are instances of this one
construction.

## Integral ideles and integral idele classes

- `integralIdeles E` is the subgroup `J∞` of `J_E` consisting of the ideles
  `x` with `Valued.v (ideleCoordinate w x) = 1` at every finite place
  `w : HeightOneSpectrum (𝓞 E)`. Here `ideleCoordinate w` is the published
  finite coordinate `J_E →* E_wˣ`. No condition is imposed at the infinite
  places. Closure under products, the identity and inverses follows from
  multiplicativity of the valuation. `mem_integralIdeles_iff` restates
  membership, and `mem_integralIdeles_iff_localUnits` says that `x ∈ J∞`
  exactly when every finite coordinate lies in the published valuation-unit
  subgroup `localUnits w` of `E_wˣ`.
- `integralIdeleClasses E` is the subgroup `C∞` of `C_E`: the image of `J∞`
  under the actual quotient map `QuotientGroup.mk' (principalSubgroup)`.
  `mem_integralIdeleClasses_iff` restates membership as the existence of an
  integral idele with the given class, and `mk_mem_integralIdeleClasses`
  says that the class of an integral idele lies in `C∞`.
- `integralIdeleClasses_normal` records that `C∞` is normal, which holds
  because `C_E` is commutative.
- `IntegralIdeleClassQuotient E` is the actual quotient group
  `C_E ⧸ C∞`. The instance `integralIdeleClassQuotientCommGroup` gives its
  commutative group structure directly. It uses the quotient group
  structure and proves commutativity on representatives. This explicit
  instance is used because elaborating Mathlib's generic
  `QuotientGroup.Quotient.commGroup` on this double quotient times out.

## Global units and the quotient map

- `valued_algebraMap_ringIntegerUnit u w`: the image of a unit
  `u ∈ (𝓞 E)ˣ` in the completion `E_w` at a finite place `w` has valuation
  one. The proof reduces, through Mathlib's comparison of the valuation on
  `E_w` with the `w`-adic valuation on `E`, to the fact that a unit does not
  lie in the prime ideal of `w`.
- `ringIntegerUnitsToIntegralIdeles E : (𝓞 E)ˣ →* J∞` is the published
  principal embedding `IdeleGroup.unitEmbedding (𝓞 E) E` composed with the
  units map induced by `algebraMap (𝓞 E) E`, with values restricted to
  `J∞` by the previous lemma. `coe_ringIntegerUnitsToIntegralIdeles` states
  that the underlying idele of `u` is the principal idele of `u` viewed in
  `Eˣ`.
- `integralIdelesToClasses E : J∞ →* C∞` is the restriction of the quotient
  map `J_E → C_E`, given by Mathlib's `MonoidHom.subgroupMap`.
  `coe_integralIdelesToClasses` states that the underlying idele class of
  `x ∈ J∞` is the quotient class of `x` in `C_E`, and
  `integralIdelesToClasses_surjective` that the map is onto `C∞`.
- `integralIdelesToClasses_ker`: the kernel of `J∞ → C∞` is the preimage of
  the principal subgroup under the inclusion `J∞ → J_E`. That is, it
  consists of the integral ideles that are principal.
- `integralIdelesToClasses_ringIntegerUnitsToIntegralIdeles`: the class of
  the image of a global unit is trivial, since its idele is principal.

This module does not identify the kernel of `J∞ → C∞` with the image of
`(𝓞 E)ˣ`. Doing so needs a principal idele with unit finite coordinates
to come from an element of `𝓞 E`, an integral-element recognition result. It
is left to a separate statement and proof.

## Arithmetic actions

The published `relativeIdeleAut F E σ` is the idele isomorphism
`ideleEquiv σ.toRingEquiv`. Its coordinate at a finite place `w` is the
transport, by the published `finiteCompletionEquiv`, of the coordinate at
the place `finitePlaceEquiv σ.toRingEquiv w`, whose ideal is the preimage of
the ideal of `w` under `σ`.

- `valued_ideleCoordinate_relativeIdeleAut`: the valuation of the
  `w`-coordinate of `relativeIdeleAut F E σ x` equals the valuation of the
  coordinate of `x` at `finitePlaceEquiv σ.toRingEquiv w`. It is the
  published valuation compatibility `finiteCompletionEquiv_valuation`.
- `relativeIdeleAut_mem_integralIdeles`: hence each `relativeIdeleAut F E σ`
  maps `J∞` into `J∞`.
- `relativeIdeleClassAut_mem_integralIdeleClasses`: each
  `relativeIdeleClassAut F E σ` maps `C∞` into `C∞`. The published class
  automorphism sends the class of `x` to the class of
  `relativeIdeleAut F E σ x`, so this follows from the previous item.
- `integralIdeleClasses_map_relativeIdeleClassAut`: the image of `C∞` under
  `relativeIdeleClassAut F E σ` is exactly `C∞`. The reverse inclusion uses
  `σ⁻¹`.
- `integralIdeleAut F E : G →* MulAut J∞` and
  `integralIdeleClassAut F E : G →* MulAut C∞` restrict
  `relativeIdeleAut F E` and `relativeIdeleClassAut F E`. The inverse of
  each restricted automorphism is the restriction of the automorphism of
  `σ⁻¹`. The identity and composition laws are those of the published
  actions. `coe_integralIdeleAut` and `coe_integralIdeleClassAut` say that
  the underlying idele or idele class is the published translate.
- `integralIdeleClassQuotientAut F E : G →* MulAut (C_E/C∞)` sends `σ` to
  the automorphism of `C_E/C∞` that Mathlib's `QuotientGroup.congr` induces
  from `relativeIdeleClassAut F E σ`, using the previous image equality.
  `integralIdeleClassQuotientAut_mk` says that it sends the class of `c` to
  the class of `relativeIdeleClassAut F E σ c`.
- `integralIdeleAction`, `integralIdeleClassAction` and
  `integralIdeleClassQuotientAction` are the corresponding multiplicative
  actions of `G`. `coe_integralIdele_smul`, `coe_integralIdeleClass_smul`
  and `integralIdeleClassQuotient_smul_mk` give their values.

The action on `(𝓞 E)ˣ` is not redefined here. The published
`ringIntegerUnitsRepresentation F E` of `UnitTorsionSequence` uses the
action of `G` on the ring of integers, through Mathlib's
`Units.mulDistribMulActionRight`, and this module reuses it.

## Representations and morphisms

- `integralIdeleRepresentation F E`, `integralIdeleClassRepresentation F E`
  and `integralIdeleClassQuotientRepresentation F E` are the published
  `NormalizedTwoCocycle.coefficientRepresentation` applied to `J∞`, `C∞`
  and `C_E/C∞` with the actions above. They are representations of `G` over
  `k` on `Additive J∞`, `Additive C∞` and `Additive (C_E/C∞)`. Their
  `_apply` lemmas state that `σ` acts by `integralIdeleAut F E σ`,
  `integralIdeleClassAut F E σ` and `integralIdeleClassQuotientAut F E σ`.
- `ringIntegerUnitsToIntegralIdeles_smul`: the map `(𝓞 E)ˣ → J∞` commutes
  with the actions. The proof applies the published `ideleEquiv_diagonal`,
  which says that `ideleEquiv` sends the principal idele of `a` to the
  principal idele of the transported element.

The morphisms of representations are the following.

| Lean name | Morphism | Underlying map |
| --- | --- | --- |
| `ringIntegerUnitsToIntegralIdelesHom F E` | `ringIntegerUnitsRepresentation F E ⟶ integralIdeleRepresentation F E` | `ringIntegerUnitsToIntegralIdeles E` |
| `integralIdeleInclusion F E` | `integralIdeleRepresentation F E ⟶ relativeIdeleRepresentation F E` | subgroup inclusion `J∞ → J_E` |
| `relativeIdeleClassProjection F E` | `relativeIdeleRepresentation F E ⟶ relativeIdeleClassRepresentation F E` | quotient map `J_E → C_E` |
| `integralIdelesToClassesHom F E` | `integralIdeleRepresentation F E ⟶ integralIdeleClassRepresentation F E` | `integralIdelesToClasses E` |
| `integralIdeleClassInclusion F E` | `integralIdeleClassRepresentation F E ⟶ relativeIdeleClassRepresentation F E` | subgroup inclusion `C∞ → C_E` |
| `integralIdeleClassQuotientProjection F E` | `relativeIdeleClassRepresentation F E ⟶ integralIdeleClassQuotientRepresentation F E` | quotient map `C_E → C_E/C∞` |

Each is `equivariantCoefficientHom` applied to the underlying homomorphism.
Apart from the first, equivariance holds by definition of the restricted or
induced action. Each has an `_apply` lemma giving its value on
`ofMul` elements. `relativeIdeleClassProjection F E` is needed because the
published `ideleQuotientCoefficients` requires `F` and `E` to share a
universe. See the last section.

The element-level and composite facts are:

- `ringIntegerUnitsToIntegralIdelesHom_comp_integralIdeleInclusion_apply`:
  the composite `(𝓞 E)ˣ → J∞ → J_E` sends `ofMul u` to the `ofMul` of the
  principal idele `IdeleGroup.unitEmbedding (𝓞 E) E u`, with `u` viewed in
  `Eˣ`.
- `integralIdelesToClassesHom_comp_integralIdeleClassInclusion_apply`: the
  composite `J∞ → C∞ → C_E` sends `ofMul x` to the `ofMul` of the quotient
  class of the underlying idele of `x`.
- `integralIdelesToClassesHom_comp_integralIdeleClassInclusion`: the square
  `J∞ → C∞ → C_E` equals `J∞ → J_E → C_E` as morphisms of
  representations. A `@[reassoc]` variant is generated.
- `ringIntegerUnitsToIntegralIdelesHom_comp_integralIdelesToClassesHom`: the
  composite `(𝓞 E)ˣ → J∞ → C∞` is zero.
- `integralIdeleClassInclusion_comp_integralIdeleClassQuotientProjection`:
  the composite `C∞ → C_E → C_E/C∞` is zero.
- `integralIdeleInclusion_injective`: the underlying map of
  `integralIdeleInclusion F E` is injective.
- `integralIdelesToClassesHom_surjective`: the underlying map of
  `integralIdelesToClassesHom F E` is surjective.

`integralIdeleClassSequence F E` is the short complex
`C∞ → C_E → C_E/C∞` of representations, made of
`integralIdeleClassInclusion F E` and
`integralIdeleClassQuotientProjection F E`. The theorem
`integralIdeleClassSequence_shortExact` proves that it is short exact:

\[
0\longrightarrow \operatorname{Additive}(C_\infty)
\longrightarrow \operatorname{Additive}(C_E)
\longrightarrow \operatorname{Additive}(C_E/C_\infty)\longrightarrow 0.
\]

The proof applies the published `repShortExact_of_values`. Injectivity is
subtype extensionality. A class with trivial image in `C_E/C∞` lies in
`C∞`, by `QuotientGroup.eq_one_iff`, which gives the kernel preimage.
Surjectivity is surjectivity of the quotient map.

## Group cohomology

The following abbreviations are Mathlib's `groupCohomology` of the
representations above, in every degree `n`, with values in
`ModuleCat.{v} k`:

- `integralIdeleCohomology F E n` for `J∞`,
- `integralIdeleClassCohomology F E n` for `C∞`,
- `integralIdeleClassQuotientCohomology F E n` for `C_E/C∞`,
- `ringIntegerUnitsCohomology F E n` for `(𝓞 E)ˣ`, using the published
  `ringIntegerUnitsRepresentation F E`.

The induced maps are `groupCohomology.map (MonoidHom.id G) f n` for the
morphisms `f` above:

- `ringIntegerUnitsToIntegralIdeleCohomologyMap F E n : Hⁿ((𝓞 E)ˣ) ⟶ Hⁿ(J∞)`,
- `integralIdeleInclusionCohomologyMap F E n : Hⁿ(J∞) ⟶ Hⁿ(J_E)`, with
  target the published `relativeIdeleCohomology F E n`,
- `integralIdelesToClassesCohomologyMap F E n : Hⁿ(J∞) ⟶ Hⁿ(C∞)`,
- `integralIdeleClassInclusionCohomologyMap F E n : Hⁿ(C∞) ⟶ Hⁿ(C_E)`, with
  target the published `relativeIdeleClassCohomology F E n`,
- `integralIdeleClassQuotientCohomologyMap F E n : Hⁿ(C_E) ⟶ Hⁿ(C_E/C∞)`.

They are new names for ordinary group cohomology. No published cohomology
declaration is redefined.

## Same-universe comparison

When `F` and `E` lie in one universe,
`relativeIdeleClassProjection_eq_ideleQuotientCoefficients` states that
`relativeIdeleClassProjection F E` is the published
`ideleQuotientCoefficients F E` of `IdeleCoefficientSequence`. The two
morphisms are definitionally equal.

## Scope

This is a definition unit. It does not prove:

- exactness of `(𝓞 E)ˣ → J∞ → C∞` at `J∞`, that is, that every integral
  principal idele comes from a global unit. Only the kernel
  (`integralIdelesToClasses_ker`) and the vanishing of the composite are
  established;
- injectivity of `(𝓞 E)ˣ → J∞`;
- finiteness of `C_E/C∞`, which is the finiteness of the ideal class group;
- any Herbrand quotient, vanishing or order statement for these
  cohomology groups.

These are the subjects of separate statement and proof tasks.

## Sources and provenance

The groups follow Artin–Tate, *Class Field Theory* (AMS Chelsea, 2009),
Chapter V §3, printed p.13 (PDF p.22). For a finite non-empty set `S` of
primes containing the archimedean primes, that section notes that the
subgroups `K*`, `J_S` and `K* J_S` of the idele group are invariant under
the Galois group. It uses
`J_S = (∏_{P∉S} U_P) × (∏_{P∈S} K_P*)`, the finite quotient `J/J_S K*`, and
the isomorphism `J_S K*/K* ≅ J_S/K_S*` with `K_S* = J_S ∩ K*`. For a number
field the set `S` of all archimedean primes is finite and non-empty. With
this `S`:

- `J_S` is `J∞`, since `U_P` is the group of valuation units at `P`;
- the image `J_S K*/K*` of `J_S` in the idele class group is `C∞`;
- `J/J_S K*` is `C_E/C∞`;
- `K_S* = J_S ∩ K*` is the group of `S`-units, which for this `S` is
  `(𝓞 E)ˣ`. In Lean, `(𝓞 E)ˣ` and the kernel `J∞ ∩ (principal ideles)` of
  `J∞ → C∞` appear separately. Their identification is not proved here.

Milne, *Class Field Theory*, v4.03 (2020), Chapter VII §2, proofs of
Propositions 2.5 and 2.7, printed pp.205–206 (PDF pp.214–215), uses the same
groups `I_{L,S}`. Milne gives the action of the Galois group on ideles: if
`α` has `a_w` in the `w`-position, then `σα` has `σa_w` in the
`σw`-position. The coordinate description of `relativeIdeleAut` above is
this convention, since `finitePlaceEquiv σ.toRingEquiv w` is `σ⁻¹w`.
Chapter VII §3, printed p.207 (PDF p.216), defines the `T`-units `U(T)`;
for `T` the infinite places they are `(𝓞 E)ˣ`.

The Lean constructions are actual subgroups, quotients and restrictions of
the published arithmetic actions, with no model substituted for any
group. The helper `equivariantCoefficientHom`, the explicit commutative
group instance on `C_E/C∞`, the independent-universe projection
`relativeIdeleClassProjection` and the cohomology abbreviations are
internal adapters, not constructions from the sources.
