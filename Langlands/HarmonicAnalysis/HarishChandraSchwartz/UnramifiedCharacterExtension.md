# Extension of unitary characters to unramified characters: the extension step of Waldspurger VIII.5

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.UnramifiedCharacterExtension`,
namespace `Langlands.HarishChandraSchwartz`. It imports:

- `Langlands.HarmonicAnalysis.HarishChandraSchwartz.DiscreteSeriesOrbitFiniteness`:
  `discreteSeriesCentralFixed` (Waldspurger's `E₂(G)^H_χ`), `discreteSeriesFixedOrbits`
  (Waldspurger's `Θ^H_G`), `finite_discreteSeriesFixedOrbits` and
  `finite_discreteSeriesFixedOrbits_of_coefficient_mem`; through it
  `Langlands.Representation.Plancherel.UnramifiedCharacters` (`commonNormKernel`,
  `mem_commonNormKernel`, `unitaryUnramifiedCharacters`), `coefficientFunctionSpace` and
  `IsBiInvariant` from `CoefficientIndependence` and `Basic`, and
  `Langlands.Weil.continuous_of_open_kernel` from `Langlands.Weil.Representation.ContinuityProof`;
- `Mathlib.Algebra.Category.Grp.Injective`: `Module.Baer.of_divisible` (a divisible abelian
  group is an injective `ℤ`-module, in Baer's form);
- `Mathlib.Analysis.SpecialFunctions.Complex.Circle`: `Circle.exp_surjective`.

The Library names from `UnramifiedCharacters` are read in the namespace
`Langlands.Plancherel`. From Mathlib it also uses `Module.Baer.extension_property_addMonoidHom`,
`Function.Surjective.divisibleBy`, `Circle.expHom`, `Circle.toUnits`, `MonoidHom.pi`,
`QuotientGroup.lift`, `QuotientGroup.quotientKerEquivRange` and `Subgroup.isOpen_mono`.

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333, DOI
10.1017/S1474748003000082. Printed page numbers; the PDF page is the printed page minus 234.

- I.1, printed p. 239 (PDF p. 5): "On note `Hom(G, ℂ*)` le groupe des homomorphismes continus de
  `G` dans `ℂ*`. Pour tout `χ ∈ Rat(G)`, on note `|χ|_F ∈ Hom(G, ℂ*)` le caractère défini par
  [...]. On pose `G¹ = ⋂_{χ ∈ Rat(G)} Ker |χ|_F`, `X(G) = Hom(G/G¹, ℂ*)`." and "On pose
  `Im X(G) = {χ ∈ X(G); Re(χ) = 0}`. C'est le sous-ensemble des éléments unitaires de `X(G)`.
  L'application de restriction `Im X(G) → Im X(A_G)` est surjective de noyau fini."
- VIII.4, printed p. 327 (PDF p. 93): "Notons `Â_G` l'ensemble des caractères unitaires de
  `A_G`".
- VIII.5, printed pp. 331–332 (PDF pp. 97–98): "Notons `Â^H_G` l'ensemble des `χ ∈ Â_G` dont la
  restriction à `A_G ∩ H` est triviale. Le groupe `Im X(G)` agit sur `Â^H_G` par
  multiplication. Le quotient `Â^H_G / Im X(G)` est fini."

In the published module `DiscreteSeriesOrbitFiniteness` the passage from `Θ^H_G` to the sets
`E₂(G)^H_χ` takes as the hypothesis `hsurj` the statement that every continuous unitary
character of `A` trivial on `A ∩ G¹` is the restriction of an element of `Im X(G)`. There the
finiteness of `Â^H_G / Im X(G)` is proved for classes modulo the characters trivial on
`A ∩ G¹`, and `hsurj` identifies these classes with the `Im X(G)`-orbits. Waldspurger asserts
the finiteness of the quotient without comment; `hsurj` is a variant of the surjectivity of
`Im X(G) → Im X(A_G)` quoted from I.1, in which `Im X(A_G)` is formed with the norm kernel of
`A_G` itself rather than with `A_G ∩ G¹`. This module proves `hsurj` for abstract data
whenever `G¹` is open. The proof uses the existing circle-character extension lemma, derived from
divisibility of the circle group rather than taken from Waldspurger.

## Scope: abstract data and explicit hypotheses

The module does not construct `A_G` or `G¹`. As in `DiscreteSeriesOrbitFiniteness`,
`ν : I → (G →* ℝ≥0ˣ)` is any family of positive characters, `commonNormKernel ν` plays the role
of `G¹` and `unitaryUnramifiedCharacters ν` (continuous characters `G →ₜ* ℂˣ` trivial on
`commonNormKernel ν` with absolute value one) the role of `Im X(G)`. A "unitary character" of
a subgroup `A` is a homomorphism `χ : A →* ℂˣ` with `‖(χ a : ℂ)‖ = 1` for all `a`.

- `Langlands.Plancherel.exists_circle_character_extension f hf χ`: `A`, `B` commutative groups, `f : A →* B`,
  `hf : Function.Injective f`, `χ : A →* Circle`. No topology.

**Section `NormMap`.** `G` is a group and `ν : I → (G →* ℝ≥0ˣ)`.

- `commonNormMap ν` (definition), `commonNormMap_apply ν g i` and `ker_commonNormMap ν`.

Then `G` is a topological group.

- `exists_unitaryUnramifiedCharacter_restrict_eq ν hG1 A χ hχn hχ1`:
  `hG1 : IsOpen (commonNormKernel ν : Set G)`, `A : Subgroup G` (any subgroup; neither
  normality, centrality nor closedness is assumed), `χ : A →* ℂˣ`,
  `hχn : ∀ a, ‖(χ a : ℂ)‖ = 1`, and `hχ1 : ∀ a : A, (a : G) ∈ commonNormKernel ν → χ a = 1`.
  Continuity of `χ` is not assumed.

**Section `Orbits`.** `G` is a nonarchimedean topological group (`[NonarchimedeanGroup G]`),
`A` a normal subgroup with `hA : A ≤ Subgroup.center G`, `G ⧸ A` carries a measurable structure,
`μ` is a Haar measure on `G ⧸ A`, and `ν : I → (G →* ℝ≥0ˣ)` (the data of
`DiscreteSeriesOrbitFiniteness`).

- `finite_discreteSeriesFixedOrbits_of_finite_central A hA μ ν H hHo hH1 hA1 hfin`:
  `H : Subgroup G` with `hHo : IsOpen (H : Set G)` and `hH1 : H ≤ commonNormKernel ν`;
  `hA1 : IsCompact ((A ⊓ commonNormKernel ν : Subgroup G) : Set G)`; `hfin`: for every
  continuous unitary character `χ` of `A` with `χ a = 1` for all `a ∈ A ∩ H`, the set
  `discreteSeriesCentralFixed A hA μ χ H` is finite.
- `finite_discreteSeriesFixedOrbits_of_finiteDimensional A hA μ ν H hH hH1 hA1 hF`:
  `H : OpenSubgroup G` with `hH : IsCompact (H : Set G)` and `hH1 : H ≤ commonNormKernel ν`;
  `hA1` as above; `hF`: for every continuous unitary character `χ` of `A` with `χ a = 1` for all
  `a ∈ A ∩ H` there is a finite-dimensional `F : Submodule ℂ (G → ℂ)` containing every
  `H`-bi-invariant element of `coefficientFunctionSpace ω.val.out.obj`, for all
  `ω ∈ discreteSeriesCentralFixed A hA μ χ H`.

These two theorems are `finite_discreteSeriesFixedOrbits` and
`finite_discreteSeriesFixedOrbits_of_coefficient_mem` of `DiscreteSeriesOrbitFiniteness` with
the hypothesis `hsurj` removed. In Waldspurger's situation `A = A_G`, `H` is compact open and
`F = p_χ(°C_H)`; Proposition VIII.4.1 and Theorem VIII.4.2, which give `hF`, are not assembled
here.

## Definitions

- `commonNormMap ν : G →* (I → ℝ≥0ˣ)`: the joint norm map `g ↦ (ν i g)ᵢ`
  (`MonoidHom.pi ν`). By `ker_commonNormMap` its kernel is `commonNormKernel ν`. This map is
  derived for this module; Waldspurger defines `G¹` as the intersection of the kernels of the
  `|χ|_F` (I.1), which is the kernel of the joint map.

## Results

- `Langlands.Plancherel.exists_circle_character_extension`: every character `χ : A →* Circle` of a commutative
  group extends along an injective homomorphism `f : A →* B` of commutative groups to a
  character `ψ : B →* Circle` with `ψ.comp f = χ`. This is the existing lemma imported from
  `RationalRestrictionSurjectivity`, now exposed for reuse.
- `commonNormMap_apply`: `commonNormMap ν g i = ν i g`.
- `ker_commonNormMap`: `(commonNormMap ν).ker = commonNormKernel ν`.
- `exists_unitaryUnramifiedCharacter_restrict_eq` (**extension to `Im X(G)`**): if `G¹` is
  open, every unitary character of a subgroup `A` trivial on `A ∩ G¹` is the restriction to
  `A` of some `η ∈ unitaryUnramifiedCharacters ν`, that is, `η a = χ a` for all `a ∈ A`. Since
  continuous unitary characters are a special case, this gives the hypothesis `hsurj` of
  `DiscreteSeriesOrbitFiniteness`.
- `finite_discreteSeriesFixedOrbits_of_finite_central` (**Theorem VIII.1.2 from the
  finiteness of the `E₂(G)^H_χ`**): under `hHo`, `hH1`, `hA1`, `hfin`, `Θ^H_G` is finite.
- `finite_discreteSeriesFixedOrbits_of_finiteDimensional` (**Theorem VIII.1.2 from
  Proposition VIII.4.1 and Theorem VIII.4.2**, abstract form): under `hH`, `hH1`, `hA1`, `hF`,
  `Θ^H_G` is finite.

## Proof notes

1. `Langlands.Plancherel.exists_circle_character_extension`: `Circle` is divisible as an additive group, because
   `Circle.expHom : ℝ →+ Additive Circle` is surjective (`Circle.exp_surjective`) and `ℝ` is
   divisible (`Function.Surjective.divisibleBy`). Hence `Additive Circle` satisfies Baer's
   criterion over `ℤ` (`Module.Baer.of_divisible`), and
   `Module.Baer.extension_property_addMonoidHom` extends `χ.toAdditive` along the injective
   `f.toAdditive`; pass back to multiplicative notation.
2. `ker_commonNormMap`: `g` lies in the kernel iff `ν i g = 1` for all `i`
   (`mem_commonNormKernel`, function extensionality).
3. `exists_unitaryUnramifiedCharacter_restrict_eq`: regard `χ` as a circle-valued character
   `χc` (by `hχn`). Let `φ = commonNormMap ν ∘ A.subtype : A →* (I → ℝ≥0ˣ)`. By
   `ker_commonNormMap` and `hχ1`, `ker φ ≤ ker χc`, so `χc` factors through
   `A ⧸ ker φ ≅ φ.range` (`QuotientGroup.lift`, `QuotientGroup.quotientKerEquivRange`), giving
   `χr : φ.range →* Circle` with `χr (φ a) = χc a`. The group `I → ℝ≥0ˣ` is commutative, so step
   1 extends `χr` along the inclusion `φ.range → (I → ℝ≥0ˣ)` to some `ψ`. Put
   `η₀ = Circle.toUnits ∘ ψ ∘ commonNormMap ν : G →* ℂˣ`. Its kernel contains
   `ker (commonNormMap ν) = G¹`, which is open by `hG1`; so the kernel of `η₀` is open
   (`Subgroup.isOpen_mono`) and `η₀` is continuous (`Langlands.Weil.continuous_of_open_kernel`).
   The resulting `η : G →ₜ* ℂˣ` is trivial on `G¹` and has absolute value one, so
   `η ∈ unitaryUnramifiedCharacters ν`, and `η a = ψ (φ a) = χr (φ a) = χ a` for `a ∈ A`.
4. The two finiteness theorems apply `finite_discreteSeriesFixedOrbits` and
   `finite_discreteSeriesFixedOrbits_of_coefficient_mem` with `hsurj` supplied by step 3. The
   openness of `G¹` follows from `hH1` and the openness of `H` (`Subgroup.isOpen_mono`).

## Relation to the Library

- `DiscreteSeriesOrbitFiniteness` states the reduction of Theorem VIII.1.2 with the explicit
  hypothesis `hsurj`; this module discharges it in the same abstract setting.
- `RationalRestrictionSurjectivity` proves, for an actual connected reductive group `G` and a
  split component `s : T → G`,
  `rationalUnitaryUnramifiedCharacterRestrict_surjective`: restriction of rational unitary
  unramified characters of `G` to those of the split component (characters trivial on the split
  component's own rational norm kernel) is surjective. This is Waldspurger's surjectivity of
  `Im X(G) → Im X(A_G)` in I.1. The present module instead treats an arbitrary subgroup `A`, the
  condition "trivial on `A ∩ G¹`" (with `G¹` the norm kernel of `G`), and abstract `ν`, under
  the hypothesis that `G¹` is open.
- In the Library's rational specialization, `isOpen_rationalCommonNormKernel`
  (`RationalNormKernelTopology`) proves that `rationalCommonNormKernel G` is open for an affine
  group scheme `G` locally of finite type over a nonarchimedean local field, so `hG1` holds
  there; this deduction is not made in this module.

## Open obligations

- `hF` for `F = p_χ(°C_H)` (Proposition VIII.4.1 and Theorem VIII.4.2 for Waldspurger's data)
  remains open, as recorded in `DiscreteSeriesOrbitFiniteness`.
- The specialization `A = A_G` with `ν` the absolute values of the rational characters is
  made in `RationalDiscreteSeriesOrbitFiniteness`, which imports this module and discharges
  `hH1` and `hA1` for the actual group `G(F)`; there `hfin` or `hF` remains.
