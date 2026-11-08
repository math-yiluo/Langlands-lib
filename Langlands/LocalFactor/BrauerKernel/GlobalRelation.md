# The global relation of a Galois type decomposition

Author: Worker 1838. This is a supporting unit for task
`92a3d086-a5ad-476f-9fd9-aa9d4eaa3778`, which must prove
`Langlands.LocalFactor.NonabelianBrauer.KernelCompatibilityStatement`. In Deligne's global
argument (1973, §4.12) the local finite Galois group is realized as a global Galois group,
and the local relation becomes a global one. This unit performs that step on relative Weil
groups `W_{K'/k}`. The input is a `GaloisTypeDecomposition` (`BrauerKernel.GaloisType`) of an
actual relation `z` over the bottom field of `F`, and a group isomorphism
`θ : Gal(K'/k) ≃ Gal(K/F)` for a Galois extension of number fields. It does not construct
`θ` or any global field; the published `totallyRealGaloisRealization` will supply them. No
epsilon or L-factor identity and no local map is involved.

Everything is in `Langlands.LocalFactor.NonabelianBrauer`. Fix `D : GaloisTypeDecomposition F e z`,
a class family `c : FundamentalClass.ClassFamily.{u}`, number fields `k`, `K'` in universe
`u` with `K'/k` Galois, and `θ`. `Gal(K'/k)` has the discrete topology
(`relativeGaloisTopology`), as in the published relative Weil modules.

## Definitions

- `globalSubgroup D k K' θ g`: the subgroup of `Gal(K'/k)` corresponding under `θ` to
  `galoisImage F D.K L_g`.
- `globalField D k K' θ g`: its fixed field `𝕃_g`, an intermediate field of `K'/k`.
- `globalQuotient D c k K' θ`: the map `θ ∘ projection : W_{K'/k} → Gal(K/F)`.
  `isOpen_ker_globalQuotient` and `globalQuotient_surjective` record that it has open kernel
  (the kernel is the inverse image of the trivial subgroup, open by the published
  `isOpen_galoisPreimage`) and is surjective (the published `projection_surjective`).
- `globalSubgroupCharacter D k K' θ g χ`: a character `χ` of `galoisImage F D.K L_g`, read on
  `globalSubgroup` through `θ`.
- `globalCharacter D c k K' θ h g χ`: the published inflation
  `RelativeWeilGroup.galoisCharacter` of that character to `W_{H'}`, composed with the
  corestriction of `restrictionInclusion c k K' 𝕃_g h : W_{K'/𝕃_g} → W_{K'/k}` onto its range
  `W_{H'}` (published `range_restrictionInclusion_fixedField`). Here
  `h : FundamentalClass.Restriction c` is required by `restrictionInclusion`.

## Results

- `inflate_induce_globalSubgroup`: inflating along `globalQuotient` the class of
  `Ind_{galoisImage L_g}^{Gal(K/F)} χ` gives the induction from `W_{H'}` of the line of the
  inflated character. This is the published `ExactGrothendieckGroup.inflate_ofClass_induce`.
  Its matching condition holds by definition, as in the published
  `RelativeWeilGroup.inflate_induce_oneDimensional`.
- `continuousTwist_inflate_induce`: twisting that class by a continuous character `Ω` of
  `W_{K'/k}` gives `IndAlong_ι [(Ω ∘ ι) · globalCharacter χ]` along `ι = restrictionInclusion`.
  The proof uses the published projection formula `continuousInduce_continuousTwist`,
  `continuousTwist_characterClass` and `continuousInduce_characterClass_eq_along`.
- `globalRelation`: for every family `Ω : ℂ → (W_{K'/k} →ₜ* ℂˣ)`,

  `Σ_{g ∈ supp z} z(g) · IndAlong_{ι_g} ([(Ω (t₁ g) ∘ ι_g) · Y₁ g] - [(Ω (t₂ g) ∘ ι_g) · Y₂ g]) = 0`

  in `ContinuousVirtual c k K'`, with `Y_i g = globalCharacter … (D.θ_i g)`. For each type `τ`,
  inflate the identity `D.identity τ` along `globalQuotient` and twist it by `Ω τ`. By the
  previous item this gives
  `Σ_g z(g) ([t₁ g = τ] X₁(τ, g) - [t₂ g = τ] X₂(τ, g)) = 0`. Sum over the finite set of types
  used on the support and exchange the two sums; `Finset.sum_ite_eq` collapses the sum over
  `τ`.

In the intended application, which is not part of this unit, `Ω τ` is the reciprocity
character of `|·|^τ` times an isolating twist. The characters `(Ω τ ∘ ι_g) · Y_i g` are then
the global characters attached to the generators.

The field universe `uF`, the global universe `u` and the representation universe `uV` are
independent.

## Provenance

Deligne, *Les constantes des équations fonctionnelles des fonctions L* (1973),
registered as `deligne-1973-local-constants`, SHA256
`b03f483c4eeca79b75e34b88f41406fe4c9e16ba621480ce859697c93e8d5844`, Lemma 4.12 and its proof
(printed page 544, PDF page 44). There a subgroup `H ⊆ Gal(K'/K) = Gal(K'_v/K_v)` defines both a
local extension `L_v` and a global extension `L`, and a representation of `H` is read on both
sides. The twisting by a type character follows §4.11 (printed page 543). This unit is the
relative-Weil-group counterpart. It is internal bookkeeping with the published inflation,
induction and twist lemmas of `VirtualRepresentation.FiniteInflation`,
`ExactInductionTwist` and `Global.Factors.RelativeWeilBrauer`.
