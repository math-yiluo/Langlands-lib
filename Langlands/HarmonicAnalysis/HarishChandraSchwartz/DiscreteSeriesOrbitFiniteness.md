# Finiteness of the discrete-series orbits with fixed vectors: Waldspurger VIII.5, proof of Theorem VIII.1.2

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.DiscreteSeriesOrbitFiniteness`,
namespace `Langlands.HarishChandraSchwartz`. It imports:

- `Langlands.HarmonicAnalysis.HarishChandraSchwartz.CoefficientIndependence`:
  `coefficientFunctionSpace` (Waldspurger's coefficient space `A(π)`) and
  `finite_of_isBiInvariant_coefficient_mem` (the finiteness step of VIII.5); through it
  `IsBiInvariant` from `Basic`;
- `Langlands.Representation.Plancherel.DiscreteSeriesOrbits`: `DiscreteSeriesClass A hA μ`
  (Waldspurger's `E₂(G)` with a central subgroup `A` in place of `A_G`), the action
  `unitaryUnramifiedTwistAction` of `unitaryUnramifiedCharacters ν` on it,
  `DiscreteSeriesOrbitClass A hA μ ν` (the orbit quotient); through it
  `Langlands.Representation.Plancherel.UnramifiedCharacters` (`commonNormKernel`,
  `unitaryUnramifiedCharacters`, `unramifiedCharacter_isOpen_ker`),
  `Langlands.Representation.Category.Twist` (`SmoothDualClass.twist`, and through it the
  representation-level twist `Langlands.twist` of `Langlands.Representation.Twist.Definitions`)
  and
  `Langlands.Representation.MatrixCoefficient.ModuloCenter` (`UnitaryCentralCharacter`);
- `Langlands.Representation.Category.ClassInvariants`: `SmoothDualClass.HasFixedVector`;
- `Langlands.Weil.Representation.ContinuityProof`: `Langlands.Weil.continuous_of_open_kernel`.

These Library names are read in the namespaces `Langlands.Plancherel` and `Langlands`
(for example `Langlands.Plancherel.DiscreteSeriesClass`,
`Langlands.Plancherel.commonNormKernel`, `Langlands.fixedVectors`).

From Mathlib it uses `Subgroup.subgroupOf_isOpen`, `Subgroup.quotient_finite_of_isOpen`,
`Subgroup.index_ne_zero_of_finite`, `Subgroup.pow_relIndex_mem`, `rootsOfUnity`,
`mem_rootsOfUnity`, `QuotientGroup.mk_out_eq_mul`, `QuotientGroup.eq`, `Finite.of_injective`,
`Set.finite_iUnion`, `MulAction.orbitRel`, `isCompact_iff_compactSpace` and
`Subtype.isCompact_iff`.

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333, DOI
10.1017/S1474748003000082. Printed page numbers; the PDF page is the printed page minus 234.

- VIII.1, printed p. 321 (PDF p. 87): "Notons `Θ_G` l'ensemble des orbites dans `E₂(G)` pour
  l'action de `Im X(G)`. [...] Soit `H` un sous-groupe ouvert compact de `G`. Pour
  `(O, P) ∈ Θ` et `(ω, E) ∈ O`, la propriété '`I_P^G E` possède des éléments non nuls
  invariants par `H`' ne dépend pas du choix de `(ω, E) ∈ O`. On note `Θ^H` l'ensemble des
  `(O, P)` tels que cette propriété soit vérifiée pour un (ou pour tout) `(ω, E) ∈ O`. On pose
  `Θ^H_G = Θ_G ∩ Θ^H`." Then "Théorème VIII.1.2. Pour tout sous-groupe ouvert compact `H` de
  `G`, `Θ^H_G` est fini."
- VIII.4, printed p. 327 (PDF p. 93): "Notons `Â_G` l'ensemble des caractères unitaires de
  `A_G`".
- VIII.4, printed p. 330 (PDF p. 96): "Pour `χ ∈ Â_G`, notons `E₂(G)_χ` l'ensemble des
  `ω ∈ E₂(G)` tels que la restriction `χ_ω` à `A_G` de leur caractère central soit égale à
  `χ`."
- VIII.5, printed pp. 331–332 (PDF pp. 97–98): "Démontrons le Théorème VIII.1.2. Soit `H` un
  sous-groupe ouvert compact de `G`. Notons `Â^H_G` l'ensemble des `χ ∈ Â_G` dont la
  restriction à `A_G ∩ H` est triviale. Le groupe `Im X(G)` agit sur `Â^H_G` par
  multiplication. Le quotient `Â^H_G / Im X(G)` est fini. Fixons un ensemble de représentants
  `X` de ce quotient. D'autre part pour tout `χ ∈ Â^H_G`, notons `E₂(G)^H_χ` l'ensemble des
  `(ω, E) ∈ E₂(G)_χ` tels que l'espace des invariants `E^H` soit non nul. On définit une
  application `⋃_{χ ∈ X} E₂(G)^H_χ → Θ^H_G` qui à `ω` associe son orbite pour l'action de
  `Im X(G)`. Cette application est surjective. Il suffit donc de fixer `χ ∈ X` et de prouver
  que `E₂(G)^H_χ` est fini. Mais, d'après le Théorème VIII.4.2, et puisque `p_χ` est
  `G × G`-invariante, on a `⨁_{ω ∈ E₂(G)^H_χ} A(ω)^{H×H} ⊂ p_χ(°C_H)` [...]. Pour tout
  `ω ∈ E₂(G)^H_χ`, `A(ω)^{H×H} ≠ {0}`. Comme `p_χ(°C_H)` est de dimension finie
  (Proposition VIII.4.1), `E₂(G)^H_χ` est fini. Cela démontre le Théorème VIII.1.2."
- I.1, printed p. 239 (PDF p. 5): `Hom(G, ℂ*)` denotes the continuous homomorphisms; so
  `Â_G` consists of continuous characters of `A_G` of absolute value one.

This module proves the first part of VIII.5 (the finiteness of `Â^H_G / Im X(G)` and the
surjectivity argument) and combines it with the published finiteness step
`finite_of_isBiInvariant_coefficient_mem`. Waldspurger states the finiteness of
`Â^H_G / Im X(G)` without proof; the argument given here (restrictions to the compact group
`A_G ∩ G¹` take values in roots of unity) is derived for this module.

## Scope: abstract data and explicit hypotheses

The module does not construct `A_G`, `G¹`, `Im X(G)` or the space `p_χ(°C_H)`, and it does not
prove Proposition VIII.4.1 or Theorem VIII.4.2. The group `A` is any normal subgroup contained
in the center (Waldspurger's `A_G`), `ν : I → (G →* ℝ≥0ˣ)` is any family of positive
characters, `commonNormKernel ν` plays the role of `G¹` and `unitaryUnramifiedCharacters ν` the
role of `Im X(G)` (as in the Library's `DiscreteSeriesOrbits`). Characters of `A` are
homomorphisms `χ : A →* ℂˣ`; "continuous unitary character of `A`" means `Continuous χ` and
`‖(χ a : ℂ)‖ = 1` for all `a`, which is Waldspurger's `χ ∈ Â_G`.

**Section `Characters`.** `A` is a group.

- `characterAnnihilator K` (definition) and `mem_characterAnnihilator`: `K : Subgroup A`.
- `finite_image_mk_of_finite_image_restrict K hS`: `K : Subgroup A`, `S` a set of characters
  `A →* ℂˣ`, `hS`: the restrictions to `K` of the elements of `S` form a finite set.

Then `A` is a topological group.

- `finite_restrict_of_isCompact K U hK hU` and `finite_image_mk_characterAnnihilator K U hK hU`:
  `K U : Subgroup A`, `[U.Normal]`, `hK : IsCompact (K : Set A)`, `hU : IsOpen (U : Set A)`.

**Section `Counting`.** `finite_image_orbitRel_of_finite R P rel c hP hadj himage hfib`: a group
`X` acting on a type `E`, a commutative group `C` with a subgroup `R`, a predicate `P` on `E`, a
relation `rel : E → C → Prop` and a map `c : E → C`, with
`hP : ∀ x e, P e → P (x • e)`,
`hadj : ∀ e e', P e → P e' → (c e)⁻¹ * c e' ∈ R → ∃ x, rel (x • e) (c e')`,
`himage`: the image of `c '' {e | P e}` in `C ⧸ R` is finite, and
`hfib : ∀ e, P e → {e' | P e' ∧ rel e' (c e)}.Finite`.

**Section `Classes`.** `G` is a group with a topology.

- `actsByCharacter_of_equiv e A χ h`: no topology is used; `e : ρ.Equiv σ` between complex
  representations of `G`, `A : Subgroup G`, `χ : A →* ℂˣ` and
  `h : ∀ a v, ρ a v = χ a • v`.
- `classActsByCharacter A χ` (definition) and `classActsByCharacter_mk`: `A : Subgroup G`,
  `χ : A →* ℂˣ`.
- `classActsByCharacter_eq_one hχ hH a ha`: `hχ : classActsByCharacter A χ ω`,
  `hH : SmoothDualClass.HasFixedVector H ω` for `H : Subgroup G`, `a : A` with `(a : G) ∈ H`.
- `classActsByCharacter_twist η hη hχ`: `η : G →* ℂˣ`, `hη : IsOpen (η.ker : Set G)`,
  `hχ : classActsByCharacter A χ ω`.
- `hasFixedVector_twist η hη hηH hω`: `η`, `hη` as above, `hηH : ∀ h ∈ H, η h = 1`,
  `hω : SmoothDualClass.HasFixedVector H ω`.

Then `G` is a topological group, `A` a normal subgroup with `hA : A ≤ Subgroup.center G`,
`G ⧸ A` carries a measurable structure and `μ` is a Haar measure on `G ⧸ A` (the data of
`DiscreteSeriesClass A hA μ`).

- `discreteSeriesCentralFixed A hA μ χ H` (definition): `χ : A →* ℂˣ`, `H : Subgroup G`.
- `exists_classActsByCharacter A hA μ ω`: `ω : DiscreteSeriesClass A hA μ`.
- `finite_discreteSeriesCentralFixed_of_coefficient_mem A hA μ χ H hH F hF`:
  `χ : A →* ℂˣ`, `H : OpenSubgroup G`, `hH : IsCompact (H : Set G)`,
  `F : Submodule ℂ (G → ℂ)` with `[FiniteDimensional ℂ F]`, and
  `hF : ∀ ω ∈ discreteSeriesCentralFixed A hA μ χ H, ∀ f ∈ coefficientFunctionSpace
  ω.val.out.obj, IsBiInvariant H f → f ∈ F`.

**Section `Orbits`.** `G` is a nonarchimedean topological group (`[NonarchimedeanGroup G]`, as
in the `Actions` section of `DiscreteSeriesOrbits`), with `A`, `hA`, `μ` as above and a family
`ν : I → (G →* ℝ≥0ˣ)`.

- `discreteSeriesFixedOrbits A hA μ ν H` (definition): `H : Subgroup G`.
- `finite_discreteSeriesFixedOrbits A hA μ ν H hHo hH1 hA1 hsurj hfin`: `H : Subgroup G` with
  `hHo : IsOpen (H : Set G)` and `hH1 : H ≤ commonNormKernel ν`;
  `hA1 : IsCompact ((A ⊓ commonNormKernel ν : Subgroup G) : Set G)`;
  `hsurj`: every continuous unitary character `χ` of `A` with `χ a = 1` for all
  `a ∈ A ∩ commonNormKernel ν` is the restriction to `A` of some
  `η ∈ unitaryUnramifiedCharacters ν`;
  `hfin`: for every continuous unitary character `χ` of `A` with `χ a = 1` for all
  `a ∈ A ∩ H`, the set `discreteSeriesCentralFixed A hA μ χ H` is finite.
- `finite_discreteSeriesFixedOrbits_of_coefficient_mem A hA μ ν H hH hH1 hA1 hsurj hF`:
  `H : OpenSubgroup G` with `hH : IsCompact (H : Set G)` and `hH1 : H ≤ commonNormKernel ν`;
  `hA1` and `hsurj` as above; `hF`: for every continuous unitary character `χ` of `A` with
  `χ a = 1` for all `a ∈ A ∩ H` there is a finite-dimensional `F : Submodule ℂ (G → ℂ)`
  containing every `H`-bi-invariant element of `coefficientFunctionSpace ω.val.out.obj`, for
  all `ω ∈ discreteSeriesCentralFixed A hA μ χ H`.

In Waldspurger's situation `A = A_G`, `ν` is the family of absolute values of the rational
characters, `H` is compact open, `μ` is a Haar measure on `G / A_G`, and `F = p_χ(°C_H)`.

## Definitions

- `characterAnnihilator K : Subgroup (A →* ℂˣ)`: the characters `χ` with `χ k = 1` for all
  `k ∈ K`. (Unrelated to `Langlands.GroupScheme.RealTorusSpace.characterAnnihilator`, which is
  a subspace of real characters of a torus.)
- `classActsByCharacter A χ : SmoothDualClass → Prop`: for the class of an irreducible
  admissible complex representation `π`, every `a ∈ A` acts on `π` by the scalar `χ a`. The
  predicate is well defined on classes by `actsByCharacter_of_equiv`. For `A = A_G` and `ω` a
  discrete-series class this is "the restriction `χ_ω` to `A_G` of the central character of `ω`
  equals `χ`", i.e. `ω ∈ E₂(G)_χ`. (The Library's `SmoothDualClass.HasCentralCharacter`
  prescribes the character on the whole center; here only its restriction to `A` is
  prescribed.)
- `discreteSeriesCentralFixed A hA μ χ H : Set (DiscreteSeriesClass A hA μ)`: the classes `ω`
  with `classActsByCharacter A χ ω` and `SmoothDualClass.HasFixedVector H ω` (a nonzero
  `H`-fixed vector). This is Waldspurger's `E₂(G)^H_χ`.
- `discreteSeriesFixedOrbits A hA μ ν H : Set (DiscreteSeriesOrbitClass A hA μ ν)`: the image
  in the orbit quotient of the discrete-series classes with a nonzero `H`-fixed vector. This
  is Waldspurger's `Θ^H_G` (orbits for which the property holds "pour un `(ω, E) ∈ O`"); when
  `H ≤ commonNormKernel ν`, `hasFixedVector_twist` shows that the property then holds for every
  member of the orbit.

## Results

- `finite_image_mk_of_finite_image_restrict`: if the restrictions to `K` of the characters in
  `S` form a finite set, then `S` has finitely many classes modulo `characterAnnihilator K`.
- `finite_restrict_of_isCompact`: for `K` compact and `U` open normal, the restrictions to `K`
  of the characters trivial on `U` form a finite set.
- `finite_image_mk_characterAnnihilator` (**finiteness of `Â^H_G / Im X(G)`**, in the form
  used): the characters trivial on `U` have finitely many classes modulo
  `characterAnnihilator K`. With `K = A ∩ G¹` and `U = A ∩ H`, and `hsurj` identifying
  `characterAnnihilator K` (on continuous unitary characters) with the restrictions of
  `Im X(G)`, this is the finiteness of `Â^H_G / Im X(G)`.
- `finite_image_orbitRel_of_finite` (counting lemma): under `hP`, `hadj`, `himage`, `hfib`,
  finitely many `X`-orbits meet `{e | P e}`.
- `actsByCharacter_of_equiv`: the property "`A` acts by `χ`" transfers along an equivalence.
- `classActsByCharacter_mk`: unfolding on a representative.
- `classActsByCharacter_eq_one`: if `A` acts on `ω` by `χ` and `ω` has a nonzero `H`-fixed
  vector, then `χ` is trivial on `A ∩ H`.
- `classActsByCharacter_twist`: if `A` acts on `ω` by `χ`, then `A` acts on the twist of `ω`
  by `η` through `η|_A · χ`.
- `hasFixedVector_twist`: twisting by `η` trivial on `H` preserves the existence of a nonzero
  `H`-fixed vector.
- `exists_classActsByCharacter`: every `ω ∈ DiscreteSeriesClass A hA μ` has a character
  `χ : A →* ℂˣ` with open kernel and `‖χ a‖ = 1` by which `A` acts (the restriction of its
  unitary central character).
- `finite_discreteSeriesCentralFixed_of_coefficient_mem` (**finiteness of `E₂(G)^H_χ`**): under
  `hF`, `E₂(G)^H_χ` is finite.
- `finite_discreteSeriesFixedOrbits` (**Theorem VIII.1.2 from the finiteness of the
  `E₂(G)^H_χ`**): under `hHo`, `hH1`, `hA1`, `hsurj`, `hfin`, `Θ^H_G` is finite.
- `finite_discreteSeriesFixedOrbits_of_coefficient_mem` (**Theorem VIII.1.2 from Proposition
  VIII.4.1 and Theorem VIII.4.2**, abstract form): under `hH`, `hH1`, `hA1`, `hsurj`, `hF`,
  `Θ^H_G` is finite.

## Proof notes

1. `finite_image_mk_of_finite_image_restrict`: choose, for each restriction `ψ` that occurs, one
   character of `S` with restriction `ψ`; two characters with the same restriction to `K` differ
   by an element of `characterAnnihilator K` (`QuotientGroup.eq`), so the image in the quotient
   is the image of a finite set.
2. `finite_restrict_of_isCompact`: `U ∩ K` is open in the compact group `K`, so it has finite
   index `n = [K : U ∩ K]` (`Subgroup.quotient_finite_of_isOpen`). A character `ψ` of `K`
   trivial on `U ∩ K` satisfies `ψ(k)ⁿ = ψ(kⁿ) = 1` (`Subgroup.pow_relIndex_mem`), and `ψ` is
   determined by its values on the representatives `q.out` of `K ⧸ (U ∩ K)`
   (`QuotientGroup.mk_out_eq_mul`). This gives an injective map into the finite set of maps
   `K ⧸ (U ∩ K) → rootsOfUnity n ℂ`.
3. `finite_image_orbitRel_of_finite`: choose for each class `s` in the finite image an element
   `g s` with `P (g s)` and class `s`. For `e` with `P e` and class `s`, `hadj e (g s)` gives
   `x` with `rel (x • e) (c (g s))`, so `x • e` lies in the finite fibre of `g s` and the orbit
   of `e` is the orbit of `x • e`. The set of orbits is contained in a finite union of images of
   finite fibres.
4. `classActsByCharacter_eq_one`: for a nonzero `H`-fixed `v` and `a ∈ A ∩ H`,
   `(χ a - 1) • v = π(a) v - v = 0`.
5. `exists_classActsByCharacter`: the definition of square integrability modulo `A`
   (`IsSquareIntegrableModCentralSubgroup`) contains a `UnitaryCentralCharacter`; its character
   composed with `Subgroup.inclusion hA` has open kernel and absolute value one and gives the
   action of `A`.
6. `finite_discreteSeriesCentralFixed_of_coefficient_mem`: apply
   `finite_of_isBiInvariant_coefficient_mem` to the family `ω ↦ ω.val.out.obj` indexed by
   `E₂(G)^H_χ`. The representatives are irreducible; equivalent representatives have equal
   classes (`Quotient.sound`), so the family is pairwise inequivalent; and the fixed-vector
   condition transfers to the representative (`Quotient.out_eq`).
7. `finite_discreteSeriesFixedOrbits`: choose the character `c ω` of step 5 for every `ω`; it is
   continuous (`Langlands.Weil.continuous_of_open_kernel`). Apply step 3 with
   `X = unitaryUnramifiedCharacters ν`, `C = (A →* ℂˣ)`,
   `R = characterAnnihilator (A ∩ G¹)`, `P ω = HasFixedVector H ω`,
   `rel ω χ = classActsByCharacter A χ ω`:
   - `hP`: elements of `unitaryUnramifiedCharacters ν` are trivial on `G¹ ⊇ H`, so
     `hasFixedVector_twist` applies;
   - `hadj`: if `(c ω)⁻¹ c ω'` is trivial on `A ∩ G¹`, it is a continuous unitary character
     trivial on `A ∩ G¹`, so by `hsurj` it is the restriction of some `η ∈ Im X(G)`; by
     `classActsByCharacter_twist`, `A` acts on `η • ω` by `η|_A · c ω = c ω'`;
   - `himage`: by `classActsByCharacter_eq_one` every `c ω` with `ω` having an `H`-fixed vector
     is trivial on `U = A ∩ H`, which is open in `A` and normal (as `A` is central); conclude by
     step 2 with `K = A ∩ G¹` (compact by `hA1`);
   - `hfib`: the fibre of `ω` is contained in `E₂(G)^H_{c ω}`, finite by `hfin` (`c ω` is
     continuous, unitary and trivial on `A ∩ H`).
8. `finite_discreteSeriesFixedOrbits_of_coefficient_mem`: step 7 with `hfin` from step 6.

## Relation to the Library

- `CoefficientIndependence` proves the finiteness step for an abstract family of pairwise
  inequivalent irreducible representations; this module supplies the family `E₂(G)^H_χ` of
  discrete-series classes, and the reduction from `Θ^H_G` to the `E₂(G)^H_χ`.
- `DiscreteSeriesOrbits` defines `E₂(G)`, the twist action of `Im X(G)` and the orbit quotient
  `Θ_G`; it contains no subset `Θ^H_G` and no finiteness statement.
- In the Library's rational specialization (`ν` the absolute values of the rational
  characters, `commonNormKernel ν = rationalCommonNormKernel G`):
  `compactSubgroup_le_rationalCommonNormKernel` gives `hH1` for compact `H`, and more generally
  `commonNormKernelTopology` gives it when every `ν i` is continuous (and `G` is weakly locally
  compact); `isCompact_rationalCommonNormKernel_inf_center` proves that `Z(G) ∩ G¹` is compact,
  so `hA1` holds for every closed `A ≤ Z(G)`. These deductions are not made in this module.

## Open obligations

- The general subgroup-form `hsurj` remains an input here. For an actual split
  component of a connected reductive group, the Library theorem
  `Langlands.Plancherel.rationalUnitaryUnramifiedCharacterRestrict_surjective`
  in `RationalRestrictionSurjectivity` proves the corresponding character
  extension. Applying it here still requires transport between the split
  component's rational points and its central subgroup image. Waldspurger uses
  this extension when letting `Im X(G)` act on `Â^H_G`.
- `hF` for `F = p_χ(°C_H)`: the finite dimensionality is Proposition VIII.4.1 (the Library's
  `KernelFiniteness` proves it under explicit kernel hypotheses), and the inclusion of the
  `H`-bi-invariant coefficients is Theorem VIII.4.2 (the Library's `DiscreteCoefficientSpace`
  and `CentralCoefficientFormula` give parts of it); their assembly for Waldspurger's data is
  not done here.
