# Local restriction of induced representations of relative Weil groups

Author: Worker 84. Statement contribution to task
`34b81620-20d7-4059-9b08-6bedd1c1c029`, revision 1. It supplies the local step
of the Galois-side global functional equation (published target
`Langlands.Global.FunctionalEquationComparison.RelativeWeilTwistFunctionalEquationStatement`):
the local factors of an induced representation of `W_{E/F}` at a finite place `z`
of `F` are local factors of representations of the local Weil groups of the places
of the intermediate field above `z`.

The module has one linear map on virtual groups, two proved topology lemmas, one
definition that changes only the topology instance of a target, two proved
`FiniteIndex` instances, and two proposition definitions. No restriction formula
is proved here and nothing is assumed.

The target is
`Langlands.ClassField.Global.RelativeWeilGroup.LocalInducedRestrictionStatement`.
Let `F ⊆ K ⊆ E` be number fields with `E/F` Galois, `z` a finite place of `F`,
and `ι : W_{F_z} → W_{E/F}` a local map at a place `w` of `E` above `z`. The
target says that there are maps `ιᵤ : W_{K_u} → W_{E/K}`, one for each place
`u` of `K` above `z`, whose transfers to `C_K` are the inverses of local reciprocity
at `u`, such that

`Res_ι (Ind_{W_{E/K}}^{W_{E/F}} x) = Σ_{u | z} Ind_{W_{K_u}}^{W_{F_z}} (Res_{ιᵤ} x)`

for every continuous virtual representation `x` of `W_{E/K}`.

## Declarations

Notation: `c : FundamentalClass.ClassFamily.{u}` is a class family, and
`RelativeWeilGroup c F E`, written `W_{E/F}`, is the published extension
`1 → C_E → W_{E/F} → Gal(E/F) → 1` of the class `c F E`. It is Tate's relative Weil
group only when `c` is the arithmetic fundamental class family (item 1 below).
`W_{F_z}` is the published
`Weil.Local.localWeilGroup (padicField z)`. For a place `u` of `K` above `z`,
`W_{K_u}` is `Weil.Local.localWeilGroup (towerPadicField z u)`, and the published
`completionWeilMap z u : W_{K_u} →ₜ* W_{F_z}` is the local Weil map along the
completion embedding `F_z → K_u` (published `extensionWeilMap`, an open embedding
with finite-index range). Continuous virtual representations are elements of the
published `ExactGrothendieckGroup` of the predicate `IsContinuous` on
`FiniteRepresentation.{0, _, _} ℂ G`. That is the free abelian group on classes of
continuous finite-dimensional complex representations modulo short exact sequences,
Tate's `R(G)` (1979, §2, p.9).

- `ExactGrothendieckGroup.continuousInduceAlong φ hφ` (definition, a `ℤ`-linear
  map), for a continuous homomorphism `φ : H →ₜ* G` that is an open embedding
  with finite-index range, into a topological group `G`. It is induction along
  `φ` on continuous exact virtual groups: restriction along the published inverse
  `InductionAlong.rangeInverse φ` onto the range, followed by the published
  finite-index induction `continuousInduce` from the range. The range is open by the
  published `InductionAlong.isOpen_range`. This is the virtual form of the
  published object-level `FiniteRepresentation.induceAlong` (same composite) and
  `FiniteRepresentation.continuousInduceAlong`. The carrier universe goes from
  `uV` to `max uG uV`.
- `krullTopology_eq_relativeGaloisTopology K E` (theorem, proved): for number
  fields `K ⊆ E`, Mathlib's Krull topology on `E ≃ₐ[K] E` is the discrete topology
  `relativeGaloisTopology K E` (Mathlib's `DiscreteTopology` instance for a
  finite-dimensional extension, then `DiscreteTopology.eq_bot`).
- `continuous_of_krull c F E f hf` (theorem, proved): a map into `W_{E/F}` that is
  continuous for the topology of `W_{E/F}` built from the Krull topology on
  `Gal(E/F)` is continuous for the topology built from `relativeGaloisTopology`.
- `discreteLocalMap ι` (definition): for `ι : W_{F_z} →ₜ* W_{E/F}` continuous for
  the Krull-built topology, the same homomorphism `ι.toMonoidHom`, as a continuous
  homomorphism for the discrete-built topology (continuity by
  `continuous_of_krull`). Only the topology instance on the target changes.
- In a section with `relativeGaloisTopology` as a local instance:
  - `range_restrictionInclusion_finiteIndex` (instance, proved): the range of the
    published `restrictionInclusion c F E K h : W_{E/K} →ₜ* W_{E/F}` has finite
    index. By the published `range_restrictionInclusion` it is the inverse image of
    the image of `Gal(E/K)` in the finite group `Gal(E/F)`.
  - `completionWeilMap_range_finiteIndex` (instance, proved) from the published
    `Weil.Local.extensionWeilMap_range_finiteIndex`.
  - `LocalInducedRestriction c F K E h z ι` (proposition definition), for
    `h : FundamentalClass.Restriction c` and `ι : W_{F_z} →ₜ* W_{E/F}`. It asserts that there is
    a family `ιu : ∀ u : FinitePlacesAbove K z, W_{K_u} →ₜ* W_{E/K}` such that:
    1. for every place `u` above `z`, every reciprocity candidate `eu` of `K_u`
       satisfying the published geometric normalization
       `LocalClassField.GeometricWeilReciprocityRelation`, and every
       `y : W_{K_u}`, `transfer c K E (ιu u y)` is the inverse of
       `IdeleClassGroup.ofAdicCompletion (𝓞 K) K u (reciprocityUnits eu y)`. Here
       `transfer c K E : W_{E/K} →* C_K` is the published transfer.
       `reciprocityUnits eu : W_{K_u} → K_uˣ` is the published local reciprocity map
       of `eu`, and `ofAdicCompletion` sends `a ∈ K_uˣ` to the class of the idele
       with `u`-component `a` and all other components `1`;
    2. for every `x` in the continuous exact virtual group of
       `FiniteRepresentation.{0, u, uV} ℂ W_{E/K}`,
       `continuousRestrict ι (continuousInduceAlong (restrictionInclusion c F E K h) _ x)`
       equals the finite sum over `u : FinitePlacesAbove K z` of
       `continuousInduceAlong (completionWeilMap z u) _ (continuousRestrict (ιu u) x)`.
       `continuousRestrict` is the published restriction on continuous exact virtual
       groups. Both sides have carrier universe `max u uV`.
- `LocalInducedRestrictionStatement` (the target) quantifies over every class
  family `c` with `h : FundamentalClass.Restriction c`, all number fields
  `F K E : Type u` with `[Algebra F K] [Algebra K E] [Algebra F E]`,
  `[IsScalarTower F K E]` and `[IsGalois F E]`, every finite place `z` of `F`, every
  finite place `w` of `E` with `[w.asIdeal.LiesOver z.asIdeal]`, every reciprocity
  candidate `e` of `E_w = towerPadicField z w`, and every
  `ι : W_{F_z} →ₜ* W_{E/F}`. It states that the published
  `IsLocalRelativeWeilMap z w e ι` implies
  `LocalInducedRestriction c F K E h z (discreteLocalMap ι)`. Its universe
  parameters are `uV` (representation carriers) and `u` (fields).

The published `IsLocalRelativeWeilMap z w e ι` says three things. First, `e`
satisfies the geometric normalization. Second, through `E → E_w → \bar{F_z}`, the
image of `ι g` in `Gal(E/F)` acts as the Galois image of `g`. Third, on
`W_{E_w}`, `ι ∘ completionWeilMap z w` is the inverse of `e`-reciprocity followed by
`E_wˣ → C_E → W_{E/F}`. Nothing is assumed about the existence of such a map. If
none exists the target says nothing about that `ι`.

## Topologies on `Gal(E/F)`

The Library uses two topologies on `Gal(E/F) = E ≃ₐ[F] E`. Mathlib's default
instance is the Krull topology. The published `IsLocalRelativeWeilMap` and the
published target above, `RelativeWeilTwistFunctionalEquationStatement`, elaborate
`W_{E/F}` with it. The
published `relativeGaloisTopology` is the discrete topology. The published
`IsTopologicalGroup` instance on `W_{E/F}`, the published `restrictionInclusion`,
and the published statement
`Langlands.ClassField.Global.RelativeWeilGroup.InducedCharacterGenerationStatement`
(Brauer induction for `W_{E/F}`) use it. For a finite extension the two topologies
are equal (`krullTopology_eq_relativeGaloisTopology`), but Lean treats them as
different instances. The target therefore states the restriction formula with the
discrete topology, like `restrictionInclusion` and Brauer induction. It applies the
formula to `discreteLocalMap ι`, which is `ι` with the discrete-built topology on
its target. Its underlying homomorphism is that of `ι`, so
`continuousRestrict (discreteLocalMap ι)` restricts along the same group
homomorphism as `ι`. A user who starts from the Krull-built continuous virtual group
of `W_{E/F}` must transport classes along the equality of topologies. This changes
no representation, only the instance in its type.

## Relation to the source

Tate (1979), Example (2.3.5), p.12, states, for a place `v` of a global field
`F`, a finite separable `E/F` and `V` in `R(W_E)`,
`(Ind_{E/F} V)_v = ⊕_{w|v} Ind_{E_w/F_v} V_w`. Here a subscript `v` or `w` means
restriction along the local map `θ_v : W_{F_v} → W_F` of Proposition (1.6.1),
p.8, or along `θ_w : W_{E_w} → W_E`. Tate proves it by "a standard formula for
the result of inducing from a subgroup and restricting to a different subgroup".
That formula is Mackey's (Serre 1977, §7.3, Proposition 22, p.58). Tate also uses
two facts: if `w₀` is one place of `E` over `v`, then `σ ↦ σw₀` puts the double
cosets `W_E\W_F/W_{F_v}` in bijection with the places of `E` over `v`; and
`W_{E_w}` can be identified with `(σW_{F_v}σ⁻¹) ∩ W_E`. The target is a derived
relative form, and differs from the source as follows.

1. **Fields.** Tate's `E` is the intermediate field `K` here. Tate's `F` is `F`,
   and only finite places `z` of `F` occur. The absolute Weil groups `W_F`, `W_K`
   are replaced by `W_{E/F}` and its open subgroup `W_{E/K}`. The subgroup
   `W_{E/K}` is embedded by the published `restrictionInclusion`, which needs the
   restriction compatibility `FundamentalClass.Restriction c`. The target is
   stated for every class family `c` with `Restriction c`, and for a general such
   `c` it is a Mackey identity for the class extensions `W_{E/K} ⊆ W_{E/F}`, not a
   statement about Weil groups. The groups are Tate's relative Weil groups only in
   the arithmetic specialization, where `c` is the arithmetic fundamental class
   family. In the Library that is the published hypothesis
   `IsArithmeticClassFamily c` (the hypotheses of the published
   `RelativeWeilTransferReciprocityStatement`), which the published
   `RelativeWeilTwistFunctionalEquationStatement` assumes. In that specialization,
   representations of `W_{E/K}` give representations of `W_K` through
   `W_K → W_{E/K}`, and the target is the special case of (2.3.5) for
   representations that factor through `W_{E/K}`.
2. **Local maps at the places of `K`.** In Tate, `V_w` is restriction along the
   local map of `K` at `u`, which (1.6.1) applied to `K` provides. The Library's
   `IsLocalRelativeWeilMap` is stated only for maps out of
   `localWeilGroup (padicField u)`. The induction in the formula needs the domain
   `localWeilGroup (towerPadicField z u)` of `completionWeilMap z u`. These are two
   packagings of the same completion `K_u` (the second carries the residue prime of
   `z`), and they are not the same Lean term. So the target names the maps `ιu` by
   an existential and characterizes them through their transfer to `C_K`
   (condition 1). In the arithmetic specialization this is the abelian part of
   (1.6.1): the composite `W_{K_u} → W_{E/K} → C_K` is local reciprocity composed
   with `K_uˣ → C_K`. Transfer and inclusion correspond as in Tate's (W3) and
   (1.2.2), p.4. Condition 1 is meaningful, and is claimed true (item 4), for every
   `c` with `Restriction c`.

   Turning a character into a Hecke character needs more, and the target does not
   provide it. If `θ = χ ∘ transfer c K E` for a character `χ` of `C_K`, then
   condition 1 gives `θ (ιu u y) = χ_u (reciprocityUnits eu y)⁻¹`, where
   `χ_u = χ ∘ ofAdicCompletion u` is the `u`-component of `χ`. That every
   continuous character `θ` of `W_{E/K}` has this form is the statement that
   transfer induces `W_{E/K}^{ab} ≅ C_K`. This holds only in the arithmetic
   specialization. In the Library it is the published
   `RelativeWeilTransferReciprocityStatement`, which assumes the arithmetic
   hypotheses and is a statement with no proof in the Library. `Restriction c` and
   the local-map hypothesis alone do not make transfer the abelianization map. For
   example, take the zero class family and a quadratic extension `E/K`. Its class
   extension is `C_E ⋊ C₂`. An order-two section element `s` has transfer
   `s² = 1` to `C_E`, hence transfer `1` in `C_K`. The nontrivial character
   through `C₂` takes `s` to `-1`, so it does not factor through transfer. A local
   map does not exclude this: for `F = K = ℚ`, `E = ℚ(i)` and the split place `5`,
   the local map lands in `C_E` and is given by inverse geometric reciprocity.
3. **Sign.** The inverse in condition 1 matches the inverse in the third part of
   `IsLocalRelativeWeilMap`. There the geometric reciprocity of `E_w` is inverted
   to match the arithmetic normalization of the fundamental classes in the
   arithmetic specialization. On the subgroup
   `W_{E_{w'}}` of `W_{K_u}`, for a place `w'` of `E` above `u`, condition 1
   follows from that third part. The published `transfer_inclusion` gives
   `transfer (inclusion a) = N_{E/K} a`, and local reciprocity turns the norm
   `E_{w'}ˣ → K_uˣ` into the inclusion `W_{E_{w'}} ⊆ W_{K_u}`. Condition 1 holds
   for every geometric candidate `eu`. By the published proved
   `Langlands.LocalClassField.geometricWeilReciprocityUniqueness`, any two such
   candidates are equal.
4. **Why the target is true.** The image of `ι` in `Gal(E/F)` is the decomposition
   group `D_w`, by the second part of `IsLocalRelativeWeilMap`. The range of
   `restrictionInclusion` contains `C_E` and maps onto `Gal(E/K)`, so the double
   cosets `ι(W_{F_z}) \ W_{E/F} / W_{E/K}` are `D_w \ Gal(E/F) / Gal(E/K)`, and
   `s ↦ (s⁻¹w)|_K` puts them in bijection with the places `u` of `K` above `z`.
   Mackey's formula along the homomorphism `ι` gives
   `Res_ι Ind V = ⊕_s Ind_{ι⁻¹(sW_{E/K}s⁻¹)}^{W_{F_z}} (V^s ∘ ι)`, with
   `V^s(t) = V(s⁻¹ts)`. The subgroup `ι⁻¹(sW_{E/K}s⁻¹)` is the Weil group of the
   closure of `s(K)` in `E_w ⊆ \bar{F_z}`. That field is `F_z`-isomorphic to `K_u`,
   so the subgroup is conjugate in `W_{F_z}` to the range of `completionWeilMap z u`
   (the Weil group is dense in the Galois group). After that conjugation, `ιu` is
   `t ↦ s⁻¹ ι(t) s` read in `W_{E/K}`, and the summand is
   `Ind_{W_{K_u}}^{W_{F_z}} (V ∘ ιu)`. For condition 1 on all of `W_{K_u}`, compute
   the transfer `W_{E/K} → C_E` on the image of `ιu` with coset representatives taken
   from that image. Up to the action of `Gal(E/K)/D_{w'}`, this is `ιu` applied to the
   local transfer `W_{K_u} → W_{E_{w'}}^{ab}`. Local reciprocity turns that local
   transfer into the inclusion `K_uˣ ⊆ E_{w'}ˣ`, and the product over
   `Gal(E/K)/D_{w'}` gives the image of `K_uˣ` in `C_K ⊆ C_E`. This argument
   uses the three parts of `IsLocalRelativeWeilMap`, the fact that conjugation in
   any class extension acts on `C_E` through the Galois action, and local class
   field theory for the local reciprocity maps. It does not use that `c` is the
   fundamental class, and it does not use transfer reciprocity for `W_{E/K}`.
   Mackey's isomorphism holds for genuine continuous
   representations, so by linearity the formula holds in the exact virtual groups.
   This is only a sketch of why the statement is true; the proof is a separate
   obligation.

## Intended use

The intended application is in the arithmetic specialization, where the published
`RelativeWeilTwistFunctionalEquationStatement` assumes `IsArithmeticClassFamily c`
(which includes `Restriction c`). To compare the local factors of
`Ind_{W_{E/K}}^{W_{E/F}} θ` at `z` with those of a Hecke character of `K`, apply
the target to `x = [θ]` and use inductivity in degree zero of the local factors.
Then write `θ = χ ∘ transfer c K E` for a character `χ` of `C_K`. This step needs
the published `RelativeWeilTransferReciprocityStatement`, which is not proved in
the Library, and fails for general `c` (item 2). Condition 1 then identifies
`θ ∘ ιu` with `χ_u ∘ reciprocityUnits eu`, inverted. Together with
`InducedCharacterGenerationStatement`, these steps reduce the Galois-side
functional equation to the Hecke functional equation (Tate 1979, §3.5; Henniart
2000, §2.3). The general class-extension identity in the target is not that
reduction. The reduction, the transfer-reciprocity theorem and the proof of the
target are separate obligations.

## Sources

- John Tate, *Number theoretic background*, in *Automorphic Forms,
  Representations and L-Functions*, Proc. Sympos. Pure Math. 33, Part II (1979),
  3–26. (1.1), (W3) and (1.2.2), pp.3–4 (transfer and norm; transfer and
  inclusion); Proposition (1.6.1), p.8 (local maps `W_{F_v} → W_F`); §2 opening,
  p.9 (`R(G)`); Example (2.3.5), p.12 (restriction of an induced representation
  to a local Weil group, with the double-coset bijection). Printed page `p` is PDF
  page `p + 9`. Registered source `tate-1979-number-theoretic-background`, SHA256
  `c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`, verified on
  6 November 2026.
- Jean-Pierre Serre, *Linear Representations of Finite Groups*, GTM 42, Springer,
  1977. §7.3, Proposition 22, p.58 (Mackey's restriction of an induced
  representation). Registered source `serre-1977-linear-representations`, SHA256
  `b6c0432dfc882618110c25a489c8fa0d93f1e64da4fba4950eb90c1b8348dcc2`, verified on
  6 November 2026.

The relative single-field form, the characterization of the maps `ιu` by their
transfer, the choice of the discrete topology, and the argument in item 4 are
derived by Worker 84 for this program. They are not quoted from the sources. The
zero-class-family example in item 2 is taken from Reviewer 16661's review of an
earlier version of this pair (candidate `0f5236bb-257d-4eea-a650-53998c629cd5`).

## Dependencies

The module imports the published `Langlands.ClassField.Global.LocalRelativeWeilMap`
(`IsLocalRelativeWeilMap`, `completionWeilMap`),
`Langlands.ClassField.Global.RelativeWeilTransfer` (`transfer`),
`Langlands.VirtualRepresentation.ExactInductionTwist` (`continuousInduce`, and
through it `ExactRestriction` with `continuousRestrict`),
`Langlands.Weil.Representation.InductionContinuity` (through it
`Langlands.WeilDeligne.InductionAlong` with `InductionAlong.rangeInverse`,
`continuous_rangeInverse` and `isOpen_range`) and
`Langlands.Global.AdelicFunctoriality.Norm` (`FinitePlacesAbove`).
