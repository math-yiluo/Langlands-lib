# Extension of scalars of representations and of Harris's inverse-limit complex

Author: Worker 61. Built on
`Langlands.Cohomology.DivisibleSystem.InverseLimit`
(`quotientInvariantsInverseLimit`), Worker 13's
`Langlands.Representation.Category.SmoothPartAdjunction`
(`SmoothRep.smoothPartFunctor`, `SmoothRep.toRepSmoothPartAdjunction`) and
the coefficient rings `CoefficientIntegers` of
`Langlands.Shimura.Coefficients.Lattice` and `FiniteCompletion` of
`Langlands.Global.Adelic`. From Mathlib it uses `Representation`, `Rep`,
`Rep.of`, `Rep.ofHom`, `LinearMap.baseChange`, `LinearMap.liftBaseChange`,
`RestrictScalars` (with `RestrictScalars.addEquiv` and
`RestrictScalars.module`), `Adjunction.mkOfUnitCounit` and
`Functor.mapHomologicalComplex`.

Everything is in the namespace `Langlands.Cohomology`. The declarations of
the sections "Harris's complex" and "Coefficients at a finite place" are in
`Langlands.Cohomology.DivisibleSystem`. At the pinned commit, Mathlib's
`Rep k G` is a structure (a module with a representation, morphisms the
intertwining maps), not `Action (ModuleCat k) G`. Mathlib has no extension or
restriction of scalars for `Rep`. The Library's étale modules change scalars
on `Action (ModuleCat R) G` and on equivariant sheaves, which do not apply to
`Rep`. This module supplies both operations for `Rep`, directly on
representations rather than through `ModuleCat.extendScalars`.

## Extension and restriction of scalars of representations

`R` and `S` are commutative rings (universes `uR`, `uS`) with an algebra
structure `algebraMap R S`, and `G` is a monoid. A representation of `G` over
`R` on `V` is a monoid homomorphism `ρ : G →* (V →ₗ[R] V)`.

- `baseChangeRepresentation S ρ`: for `ρ : Representation R G V`, the
  representation of `G` over `S` on `S ⊗[R] V` in which `g` acts by
  `(ρ g).baseChange S`, that is `s ⊗ v ↦ s ⊗ ρ g v`
  (`baseChangeRepresentation_apply_tmul`).
- `restrictScalarsLinearMap R S f`: an `S`-linear map `f : W →ₗ[S] W'`,
  viewed as an `R`-linear map `RestrictScalars R S W →ₗ[R]
  RestrictScalars R S W'`. Mathlib's `RestrictScalars R S W` is a copy of
  `W` on which `r` acts as `algebraMap R S r`; the map is `f` transported
  along the identifications `RestrictScalars.addEquiv`
  (`restrictScalarsLinearMap_apply`).
- `restrictScalarsModule R S M`: Mathlib's `RestrictScalars.module R S M`,
  stated for the additive monoid structure that comes from the additive group
  structure on `RestrictScalars R S M`. `Rep.of` requires the module
  structure in that form. The two additive monoid structures agree only after
  unfolding the definition `RestrictScalars`, which instance search does not
  do. This abbreviation is a local instance of the module, not a new
  structure.
- `restrictScalarsRepresentation R S σ`: for `σ : Representation S G W`, the
  representation of `G` over `R` on `RestrictScalars R S W` in which `g` acts
  by `restrictScalarsLinearMap R S (σ g)`.
- `baseChangeUnitLinearMap R S V`: the `R`-linear map
  `v ↦ 1 ⊗ v` from `V` to `RestrictScalars R S (S ⊗[R] V)`.
- `baseChangeCounitLinearMap R S W`: the `S`-linear map
  `S ⊗[R] RestrictScalars R S W → W`, `s ⊗ w ↦ s • w`
  (`baseChangeCounitLinearMap_tmul`). It is Mathlib's
  `LinearMap.liftBaseChange S` of the identity.
- `repExtendScalars R S G : Rep.{w} R G ⥤ Rep.{max uS w} S G`: extension of
  scalars, `V ↦ S ⊗[R] V` with `baseChangeRepresentation`, and
  `f ↦ f.baseChange S` on intertwining maps
  (`repExtendScalars_map_tmul`). The carrier `S ⊗[R] V` lies in universe
  `max uS w`.
- `repRestrictScalars R S G : Rep.{w} S G ⥤ Rep.{w} R G`: restriction of
  scalars, `W ↦ RestrictScalars R S W` with
  `restrictScalarsRepresentation`, and `f ↦ restrictScalarsLinearMap R S f`
  on intertwining maps.
- `repExtendScalars_additive`, `repRestrictScalars_additive`: both functors
  are additive.
- `repExtendScalarsUnit R S G`: the natural transformation from the identity
  of `Rep.{max uS w} R G` to `repExtendScalars ⋙ repRestrictScalars`, with
  components `v ↦ 1 ⊗ v` (`repExtendScalarsUnit_app_apply`). The carrier
  universe is `max uS w`, so that the composite maps `Rep.{max uS w} R G` to
  itself.
- `repExtendScalarsCounit R S G`: the natural transformation from
  `repRestrictScalars ⋙ repExtendScalars` to the identity of
  `Rep.{max uS w} S G`, with components `s ⊗ w ↦ s • w`
  (`repExtendScalarsCounit_app_tmul`). Its components are `G`-equivariant
  and natural because the action and every intertwining map are `S`-linear;
  both are checked on pure tensors.
- `repExtendScalarsAdjunction R S G`: `repExtendScalars ⊣
  repRestrictScalars` between `Rep.{max uS w} R G` and `Rep.{max uS w} S G`,
  built from this unit and counit. The triangle identities are
  `s • (1 ⊗ v) = s ⊗ v`, checked on pure tensors, and `1 • w = w`.

## Complexes

`c` is a complex shape on an index type `ι`.

- `repExtendScalarsComplex R S G c` and `repRestrictScalarsComplex R S G c`:
  extension and restriction of scalars applied degreewise to complexes of
  representations of shape `c` (`Functor.mapHomologicalComplex`; this uses
  additivity).
- `repExtendScalarsComplexUnit R S G c`: the natural chain map from a complex
  `K` in `Rep.{max uS w} R G` to the restriction of scalars of its extension
  of scalars, with degree-`i` component the unit at `K.X i`, `v ↦ 1 ⊗ v`.
  It commutes with the differentials by naturality of the unit.

## Smooth parts of complexes

Here `G` is a topological group and `R` a commutative ring.

- `smoothPartFunctor_additive`: the published smooth-part functor
  `SmoothRep.smoothPartFunctor R G : Rep R G ⥤ SmoothRep R G`, which takes
  the vectors fixed by some open subgroup, is additive. The sum of two
  intertwining maps restricts to the sum of their restrictions, by
  definition.
- `smoothPartComplex R G c`: the smooth part applied degreewise to complexes
  of representations of shape `c`, giving complexes in `SmoothRep R G`.
- `smoothPartComplexInclusion R G c`: the natural chain map from the image in
  `Rep R G` of `smoothPartComplex` of `K` to `K`, whose degree-`i` component
  is the counit of `SmoothRep.toRepSmoothPartAdjunction` at `K.X i`, the
  inclusion of smooth vectors.

## Harris's complex

The variables are those of the InverseLimit module's section "Harris's Lemma
2.8": `K` is an `ℓ`-divisible system of `ℕ`-graded complexes of smooth
representations of `G` (`SmoothRep.{uR, uG, max w uR uG} R G`), `N : ℕ`, `ι`
a filtered preorder with an antitone family `H` of normal subgroups of finite
index (`hH`), and the hypotheses `hK` (surjectivity on invariants) and `hk`
(kernel orders are units in `R`). In addition `S` is a commutative
`R`-algebra in the universe `uR` of `R`. Then extension of scalars takes the
complexes over `R` (carriers in universe `max w uR uG`) to complexes over `S`
with carriers in the same universe, and the smooth parts lie in
`SmoothRep.{uR, uG, max w uR uG} S G`, the universe pattern of `K`.

- `quotientInvariantsInverseLimitBaseChange S N K H hH hK hk`: the
  `ℤ`-graded cochain complex in `Rep S G` obtained by applying
  `repExtendScalarsComplex` to `quotientInvariantsInverseLimit N K H hH hK
  hk`, Harris's `lim C_m^•`. Its degree-`q` term is `S ⊗[R]` the degree-`q`
  term of the inverse limit.
- `quotientInvariantsInverseLimitToBaseChange S N K H hH hK hk`: the chain
  map `v ↦ 1 ⊗ v` from `quotientInvariantsInverseLimit` to the restriction
  of scalars of `quotientInvariantsInverseLimitBaseChange`, the component of
  `repExtendScalarsComplexUnit`.

Assume moreover that `G` is a topological group.

- `quotientInvariantsInverseLimitBaseChangeSmooth S N K H hH hK hk`: the
  degreewise smooth part of `quotientInvariantsInverseLimitBaseChange`, a
  `ℤ`-graded cochain complex in `SmoothRep S G`.
- `quotientInvariantsInverseLimitBaseChangeSmoothInclusion S N K H hH hK hk`:
  its degreewise inclusion into `quotientInvariantsInverseLimitBaseChange`,
  the component of `smoothPartComplexInclusion`.

## Coefficients at a finite place

`L` is a number field in universe `uR`, `l` a finite place of `L`, and
`R = CoefficientIntegers l`, the valuation ring `l.adicCompletionIntegers L`
of the completion `FiniteCompletion L l = l.adicCompletion L`. The algebra
structure is Mathlib's inclusion of the valuation subring into the
completion. The other variables are as in the previous section, with
`R = CoefficientIntegers l`. `ℓ` is an arbitrary natural number, not tied to
the residue characteristic of `l`.

- `quotientInvariantsInverseLimitCompletion l N K H hH hK hk`:
  `quotientInvariantsInverseLimitBaseChange` with
  `S = FiniteCompletion L l`, a `ℤ`-graded cochain complex in
  `Rep (FiniteCompletion L l) G`.
- `quotientInvariantsInverseLimitToCompletion l N K H hH hK hk`: the
  corresponding chain map `v ↦ 1 ⊗ v`.
- `quotientInvariantsInverseLimitCompletionSmooth l N K H hH hK hk` and
  `quotientInvariantsInverseLimitCompletionSmoothInclusion l N K H hH hK hk`
  (for `G` a topological group): the degreewise smooth part, a complex in
  `SmoothRep (FiniteCompletion L l) G`, and its inclusion.

All declarations of the last two sections are abbreviations for the generic
constructions applied to `quotientInvariantsInverseLimit`.

## Provenance and interpretation

Harris, *Supercuspidal representations in the cohomology of Drinfel'd upper
half spaces; elaboration of Carayol's program*, Invent. Math. 129 (1997),
printed p.92 (one-based PDF page 18): "Berkovich shows that the discrete
complexes calculating cohomology with coefficients in Z/ℓ^nZ, as n varies,
satisfy an appropriate Mittag-Leffler condition, and give rise in the inverse
limit over n to a complex of smooth Z_ℓ[S(e,d)]-modules, whose cohomology
equals H_c^•(U(e,N), Z_ℓ). [...] Tensoring with Q_ℓ, we obtain our complex
C(e,d)."

Harris, *Galois properties of cohomological automorphic forms on GL(n)*, J.
Math. Kyoto Univ. 39-2 (1999), printed p.311 (one-based PDF page 13): for
the coefficient ring 𝒪 of `L_ℓ`, "the inverse system {𝓛̃_m} defines a lisse
ℓ-adic sheaf W̃ = lim 𝓛̃_m ⊗_𝒪 L_ℓ", and in Proposition 4.10 "Ext^i denotes
the i-th derived functor of Hom in the category of smooth L_ℓ[GJ]-modules".
The proof of Proposition 4.10 (pp.311-312) checks a Mittag-Leffler condition
for the complexes as `m` varies and ends with "This and the arguments of [H1]
suffice to complete the proof", where [H1] is the 1997 paper. Worker 61 read
both passages, the second in the rendered scanned page.

Our rendering:

1. The construction `quotientInvariantsInverseLimitBaseChange` is the step
   "Tensoring with `ℚ_ℓ`" applied to our inverse limit
   `quotientInvariantsInverseLimit` (the rendering of `lim C_m^•` in the
   InverseLimit module). It is defined for any commutative `R`-algebra `S`.
   `quotientInvariantsInverseLimitCompletion` specializes it to the actual
   coefficient rings of the published Lattice module,
   `CoefficientIntegers l → FiniteCompletion L l`, which play the roles of
   Harris's `𝒪 → L_ℓ` in 1999 and, for `L = ℚ`, of `ℤ_ℓ → ℚ_ℓ` in 1997. No
   identification with Mathlib's `ℤ_[p]` or `ℚ_[p]` is made.
2. Harris's inverse limit is a complex of smooth modules, by Berkovich's
   results. We do not prove that `quotientInvariantsInverseLimit` or its
   extension of scalars has smooth terms; an inverse limit of smooth
   representations need not be smooth. To obtain a complex in the published
   category `SmoothRep`, where Harris's Ext groups of Proposition 4.10 live,
   we take the smooth part degreewise. This is our device, not a step of
   Harris. We do not prove that the inclusion
   `quotientInvariantsInverseLimitBaseChangeSmoothInclusion` is an
   isomorphism or a quasi-isomorphism.
3. No comparisons are proved. In particular we do not prove that extension
   of scalars commutes with the inverse limit or with cohomology (Harris
   tensors the complex and then takes cohomology; the module does not show
   that this gives `S ⊗[R]` the cohomology). We do not identify the
   cohomology with `H_c^•(U(e,N), ℚ_ℓ)` or with the cohomology of Harris's
   `W̃`.
4. The generic constructions (base change and restriction of
   representations, the functors, unit, counit and adjunction, their
   degreewise versions, the additivity of the smooth-part functor and the
   degreewise smooth part with its inclusion) are ours. They are the
   standard extension and restriction of scalars of modules, with the group
   acting on the second tensor factor.
5. The hypotheses of the Harris sections are exactly those needed to form
   `quotientInvariantsInverseLimit`. Harris's specific family of subgroups
   and the topology on `G` are not constructed (see the InvariantLimit
   module).

## Scope

The module defines extension and restriction of scalars of representations
and of complexes of representations, their adjunction, the degreewise smooth
part with its inclusion, and their application to
`quotientInvariantsInverseLimit` for a general coefficient algebra and for
`CoefficientIntegers l → FiniteCompletion L l`. All maps are `G`-equivariant.
It proves no statement about cohomology, flatness, limits or smoothness of
these complexes.

Source registration: Harris 1997, `harris-1997-drinfeld-cohomology`,
SHA-256 `aea284b917442459028b710dbfd9ae537631490504f3bc6d54a1e76ee697e0d9`;
Harris 1999,
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

Dependencies are the modules named above, pinned to Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
