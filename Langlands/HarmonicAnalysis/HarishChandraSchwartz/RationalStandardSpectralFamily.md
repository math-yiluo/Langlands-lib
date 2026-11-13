# The spectral family `ψ_f` over the standard part of `Θ` on actual points

Author: Worker 3642, task `1ef6854b-f0e9-4d96-bbe5-cb8c4b52f927` (revision 1).

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalStandardSpectralFamily`,
namespace `Langlands.HarishChandraSchwartz`. It imports:

- `Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalThetaFixedFiniteness` (Library, this
  author's Unit 31): `exists_finite_sigma_rationalFourierOrbitSection_ne_zero_of_statement`
  (Remarque VIII.1.3 (ii) for the standard parabolics, given the published statement of Theorem
  VIII.1.2). Through its imports come `rationalLeviSplitCenter`,
  `rationalLeviSplitCenter_le_center` (`A_{M_I}(F)`), `rationalFourierOrbitSection`
  (`ψ_f[O, P_I]`), `RationalSchwartzSpace` (`C(G)`), `IsRationalLeviTempered`,
  `RationalDiscreteSeriesOrbitFinitenessStatement`, and from
  `Langlands.Representation.Plancherel.DiscreteSeriesOrbits` and
  `Langlands.Representation.Plancherel.ProductInducedOrbitSections` (Library):
  `DiscreteSeriesOrbitClass` (orbits of `Im X(M)` in `E₂(M)`), `discreteSeriesClass`,
  `UnitaryOrbitRepresentative` (the representatives of the twist orbit of `π`),
  `ProductInducedOrbitSections` (sections over that orbit). `SmoothDualClass.twist_one` comes from
  `Langlands.Representation.Category.Twist`.
- `Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalFourierOrbitSmoothness` (Library,
  this author's Unit 24): `rationalFourierOrbitSmoothSectionLinear` (`f ↦ ψ_f[O, P_I] ∈
  C^∞(O, P_I)`, Proposition VII.1.3 without continuity) and
  `rationalFourierOrbitSmoothSectionLinear_val`. Through its imports comes
  `rationalInducedSmoothOrbitSections` (`C^∞(O, P_I)`).
- `Langlands.Representation.Plancherel.ProductInducedOrbitBaseChange` (Library):
  `unitaryOrbitRepresentativeBaseEquiv`, `productInducedOrbitBaseEquiv` and
  `productInducedSmoothOrbitBaseEquiv` (independence of the base representative for the section
  spaces and for the smooth sections).

From Mathlib: `Quotient.out`, `Quotient.out_eq`, `Quotient.exact`, `LinearEquiv.map_eq_zero_iff`,
`Submodule`, `LinearMap.codRestrict`,
`Set.Finite`, `Pi.add_apply`, `Pi.smul_apply`, `Pi.zero_apply`.

## Source and provenance

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après Harish-Chandra*,
J. Inst. Math. Jussieu 2 (2003), 235–333, DOI 10.1017/S1474748003000082 (literature id
`waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`). Printed page numbers; the
PDF page is the printed page minus 234. The author checked the quotations on the rendered PDF
pages 62, 71, 82, 86 and 87.

- VI.3, printed p. 305: "Notons `Θ` l'ensemble des couples `(O, P = MU)` où `P` est un
  sous-groupe parabolique semi-standard de `G` et `O ⊂ E₂(M)` une orbite sous l'action de
  `Im X(M)`. On pose `C^∞(Θ) = ⊕_{(O,P) ∈ Θ} C^∞(O, P)`. Pour `ψ ∈ C^∞(Θ)`, on note `ψ[O, P]` sa
  composante dans `C^∞(O, P)`."
- VII.1, printed p. 316: "Soit `O` une orbite dans `E₂(M)` pour l'action de `Im X(M)`. Pour
  `f ∈ C(G)`, on définit une fonction `ψ_f[O, P]` sur `O` par: `ψ_f[O, P]_ω = f̂(ω, P)` pour tout
  `ω ∈ O`. Proposition VII.1.3. Pour tout `f ∈ C(G)`, la fonction `ψ_f[O, P]` appartient à
  `C^∞(O, P)`. L'application `C(G) → C^∞(O, P)`, `f ↦ ψ_f[O, P]` est continue."
- VIII.1, printed p. 320, assertion (1): "pour tout `f ∈ C(G)`, l'ensemble des `(O, P) ∈ Θ` tels
  que `ψ_f[O, P] ≠ 0` est fini".
- Remarque VIII.1.3, printed p. 321: "Supposons le Théorème VIII.1.2 vrai pour tout sous-groupe
  de Lévi d'un sous-groupe parabolique semi-standard, resp. et propre, de `G`. Alors […] (ii) pour
  tout `f ∈ C(G)`, l'ensemble des `(O, P) ∈ Θ`, resp. `Θ − Θ_G`, tels que `ψ_f[O, P] ≠ 0` est
  fini."
- VIII.2, printed p. 321, uses this to define an element of `C^∞(Θ)` from the components
  `ψ_f[O, P]`: "on peut définir `ψ ∈ C^∞(Θ)` par `ψ[O, P] = 0` si `P = G`, `ψ_f[O, P]` si
  `P ≠ G`".

- VI.1, printed p. 296, on the smoothness of a section `ψ` over `O`: "Fixons `(ω, E) ∈ O`, posons
  `L_K(ω, P) = I^{K×K}_{K∩P, K∩P}(E ⊗ Ě)`. Pour tout `χ ∈ Im X(M)`, `L(ω ⊗ χ, P)` s'identifie à
  `L_K(ω, P)` par restriction à `K`. La fonction `ψ` s'identifie à une fonction sur `Im X(M)` à
  valeurs dans `L_K(ω, P)`. Alors `ψ` est `C^∞` si cette dernière fonction l'est." The choice of
  `(ω, E)` does not matter; the Library proves this for its model in
  `ProductInducedOrbitBaseChange`.

So with the family `(ψ_f[O, P])_{(O, P) ∈ Θ}` in the product of the `C^∞(O, P)`, Remarque VIII.1.3
(ii) says that it lies in the direct sum `C^∞(Θ)`. This module formalizes that step for the
standard parabolic subgroups `P_I(F)`.

Encoding choices (internal, not in the source):

- `Θ` restricted to the standard parabolics is indexed by dependent pairs `⟨I, O⟩` of a finite set
  `I` of simple roots (the standard parabolic `P_I(F)`) and an orbit `O` of `Im X(M_I)` in
  `E₂(M_I)`, as in Unit 31.
- A component `ψ[O, P_I]` is a section over the twist orbit of a chosen representative of `O`
  (`rationalOrbitRepresentative`, a `Quotient.out` choice). The Library's section spaces
  `ProductInducedOrbitSections ν π …` are indexed by a representative `π`. The choice does not
  matter: for any other representative `π'` of `O`, the Library's base change gives linear
  equivalences of the section spaces and of `C^∞(O, P_I)` that keep every value at every actual
  representative, and they send `ψ_f[O, P_I]` built from the chosen representative to
  `ψ_f[O, P_I]` built from `π'` (see the Contents).
- The product over `Θ` is curried as `∀ I O, …` rather than indexed by the pair `⟨I, O⟩`: it is
  the same product, and the curried form keeps the parabolic `I` a variable in the types, which
  elaborates much faster.
- The direct sum `C^∞(Θ) = ⊕ C^∞(O, P)` is realized as the submodule of the product of the full
  section spaces whose components lie in `C^∞(O, P_I)` and which have finite support.

## Contents

The setting of Units 19–31: `F` a nonarchimedean local field, `G` a connected reductive group
scheme over `F` (`hG`) with `[IsAffineHom G.X.hom]`, `[LocallyOfFiniteType G.X.hom]`, `i` a maximal
split torus (`hi`), `ν` a generic cocharacter (`hν`), `K` a compact open subgroup of `G(F)` with
`(P_∅(F), K)` an Iwasawa pair (`hKc`, `hPK`). For a finite set `I` of simple roots, `M_I(F)` is the
subtype `𝐌` of `G(F)`, `L = Standard.leviScheme i ν (rootSet i ν I)` the Levi scheme (local
notation `𝐋`) and `𝐉` the root set `rootSet i ν I`. For every `I`, `a I : T I → L` is a split
component of `L` (`ha I`), `A_{M_I}(F) = rationalLeviSplitCenter I (a I)` and `mu I` is a Haar
measure on `M_I(F) ⧸ A_{M_I}(F)`.

### Index (section `Index`)

- `RationalLeviOrbitClass a ha mu I` (abbrev): `DiscreteSeriesOrbitClass` for `M_I(F)`, the
  orbits of `Im X(M_I)` (`leviRationalNormCharacters i ν I`) in `E₂(M_I)` (discrete series of
  `M_I(F)` modulo `A_{M_I}(F)`).
- **`RationalStandardTheta a ha mu`** (abbrev): the dependent pairs `⟨I, O⟩` with
  `O : RationalLeviOrbitClass a ha mu I`, the standard part of `Θ`.
- **`rationalOrbitRepresentative a ha mu I O`**: the irreducible admissible representation
  `O.out.val.out` of `M_I(F)` (a representative of the class chosen as representative of the
  orbit).
- `rationalOrbitRepresentative_isSquareIntegrable`: it is square integrable modulo `A_{M_I}(F)`.
- `mk_discreteSeriesClass_rationalOrbitRepresentative`: the orbit of its discrete-series class is
  `O`.
- `rationalOrbitRepresentativeMember a ha mu I O π' hsq' hO` (with
  `rationalOrbitRepresentativeMember_val`): an irreducible admissible `π'` of `M_I(F)`, square
  integrable modulo `A_{M_I}(F)` (`hsq'`), whose discrete-series class has orbit `O` (`hO`), as a
  member of `UnitaryOrbitRepresentative` of the chosen representative (an element of its unitary
  unramified twist orbit).
- `selfUnitaryOrbitRepresentative I π`: `π` as a representative of its own twist orbit (twist by
  the trivial character).

### The family (section `Family`)

- **`RationalStandardThetaSections hG hi hν a ha mu`** (abbrev): the product
  `∀ I O, ProductInducedOrbitSections (leviRationalNormCharacters i ν I)
  (rationalOrbitRepresentative a ha mu I O) …` (for `P_I(F) = M_I(F) U_I(F)`), the product over the
  standard part of `Θ` of the section spaces: at each representative `ω` of the orbit, a value in
  `L(ω, P_I)`.
- Six closure lemmas used for the submodule below, each stated for the concrete product:
  `add_mem_rationalInducedSmoothOrbitSections_of_forall`,
  `zero_mem_rationalInducedSmoothOrbitSections_apply`,
  `smul_mem_rationalInducedSmoothOrbitSections_of_forall` (componentwise membership in
  `C^∞(O, P_I)` is preserved by `+`, `0`, `c •`) and `finite_support_add_of_finite`,
  `finite_support_zero`, `finite_support_smul_of_finite` (finiteness of
  `{⟨I, O⟩ | ψ I O ≠ 0}` is preserved).
- **`rationalStandardThetaSmoothSections hG hi hν hKc hPK a ha mu`** (definition): the submodule
  of `RationalStandardThetaSections` of the families `ψ` with
  `ψ I O ∈ rationalInducedSmoothOrbitSections hG hi hν I hKc hPK (rationalOrbitRepresentative a
  ha mu I O)` (that is, `ψ[O, P_I] ∈ C^∞(O, P_I)`) for all `I`, `O`, and
  `{p : RationalStandardTheta a ha mu | ψ p.1 p.2 ≠ 0}` finite: the standard part of `C^∞(Θ)`.
- `mem_rationalStandardThetaSmoothSections`: the membership condition, by `Iff.rfl`.
- **`rationalOrbitSectionsBaseEquiv hG hi hν a ha mu I O π' hsq' hO`**: for `π'` as above, the
  linear equivalence from the sections over the orbit of the chosen representative to the sections
  over the orbit of `π'`; it is the Library's `productInducedOrbitBaseEquiv` at
  `rationalOrbitRepresentativeMember … π' hsq' hO`, which keeps the value at every actual
  representative.
- **`rationalOrbitSmoothSectionsBaseEquiv hG hi hν hKc hPK a ha mu I O π' hsq' hO`**: the linear
  equivalence `C^∞(O, P_I)` (built from the chosen representative) `≃ₗ[ℂ]` `C^∞(O, P_I)` (built
  from `π'`), the Library's `productInducedSmoothOrbitBaseEquiv`;
  `rationalOrbitSmoothSectionsBaseEquiv_val`: its underlying section is
  `rationalOrbitSectionsBaseEquiv` of the underlying section.

For the Fourier family, moreover (as in Unit 31): `ρ`, `hρ`, `hKρ` (the height and `C(G)`),
`hM : ∀ I, …` (Iwasawa pairs for the `M_I(F)`), `[∀ I, (mu I).IsInvInvariant]`, a bi-invariant
measure `muG` on `G(F)` with `hsw` (Lemma II.1.5), and `hTA : ∀ I π, … → ∀ A, IsRationalLeviTempered
hKc ρ (hM I) A.val.obj` (every representative of the orbit of a discrete series `π` of `M_I(F)` is
tempered).

- **`rationalFourierThetaFamily … f`** (definition): for `f ∈ C(G)`, the family
  `fun I O => rationalFourierOrbitSection … (rationalOrbitRepresentative a ha mu I O) … f`, that
  is `(ψ_f[O, P_I])_{(I, O)}` in `RationalStandardThetaSections`.
- **`finite_support_rationalFourierThetaFamily … hVIII f`**: given
  `hVIII : RationalDiscreteSeriesOrbitFinitenessStatement` (the published statement of Theorem
  VIII.1.2), `{p | ψ_f[O_p, P_{I_p}] ≠ 0}` is finite (Remarque VIII.1.3 (ii) for the family).
- **`rationalOrbitSectionsBaseEquiv_rationalFourierThetaFamily … I O π' hsq' hO f`**:
  `rationalOrbitSectionsBaseEquiv … I O π' hsq' hO (rationalFourierThetaFamily … f I O)` is
  `rationalFourierOrbitSection … π' … (hTA I π' hsq') hsw f`, that is `ψ_f[O, P_I]` built from
  `π'`.
- `rationalFourierThetaFamily_eq_zero_iff … I O π' hsq' hO f`: the component of the family is
  zero iff `ψ_f[O, P_I]` built from `π'` is zero, so the support of the family does not depend on
  the chosen representatives.

For linearity, moreover the hypotheses of Unit 24's `rationalFourierOrbitSmoothSectionLinear`,
now for every `I`: `[muG.IsInvInvariant]`, `[SigmaFinite muG]`, `hμK : muG K = 1`; measures `μL I`
on `M_I(F)` (left and right invariant, inverse-invariant, s-finite) with `hswM I` (Lemma II.1.5
for `M_I`) and `hMK I : μL I (K ∩ M_I(F)) = 1`; Haar measures `νU I` on `U_I(F)` with
`hUK I : νU I (K ∩ U_I(F)) = 1`; `hE I : ConstantTermEstimate …` (conclusion of Proposition II.4.5);
`hPKiw I` (`m u ∈ K ↔ m ∈ K ∧ u ∈ K`); `hnσ I` (`‖H_{M_I}(m)‖ ≤ Cn I (1 + σ(m))` in lattice
coordinates); `hint`: for every `I` and every `π` square integrable modulo `A_{M_I}(F)` (the same
guard as `hTA`), every `f ∈ C(G)`, every representative `A` of the orbit of `π` and every
`ψ ∈ L(A, P_I)`, the function `(g, k) ↦ conj(⟨ψ(k g, k)⟩) f(g)` is integrable on `G(F) × K`.
Unit 24's `hint` concerns its one fixed discrete series `π`; here it is required only for the
discrete series of the `M_I(F)`, and it is used at the chosen representatives. (Without the
guard it would fail: for a nonunitary character `π` of a split torus, the integral diverges for
some `f ∈ C(G)`.) The temperedness of the chosen representative itself is `hTA` at the trivial
twist.

- `rationalFourierThetaComponentLinear … I O`: the linear map `f ↦ ψ_f[O, P_I]` into
  `C^∞(O, P_I)`, Unit 24's `rationalFourierOrbitSmoothSectionLinear` for the chosen
  representative; `rationalFourierThetaComponentLinear_val`: its value is the family's component.
- `rationalFourierThetaFamilyLinear …`: `f ↦ rationalFourierThetaFamily … f` as a linear map
  `C(G) →ₗ[ℂ] RationalStandardThetaSections …`; `rationalFourierThetaFamilyLinear_apply` (`rfl`).
- **`rationalFourierThetaLinear … hVIII`** (definition, the recorded declaration): given
  `hVIII`, the linear map `C(G) →ₗ[ℂ] rationalStandardThetaSmoothSections …`, `f ↦ ψ_f`: each
  component lies in `C^∞(O, P_I)` (Proposition VII.1.3, first assertion) and the support is finite
  (Remarque VIII.1.3 (ii)), so `ψ_f` lies in the standard part of `C^∞(Θ)`.
- `rationalFourierThetaLinear_val`: the underlying family of `rationalFourierThetaLinear … f` is
  `rationalFourierThetaFamily … f`.

## Proofs

- `rationalOrbitRepresentative_isSquareIntegrable`: the property of `O.out`, after rewriting its
  class as `Quotient.mk _ (O.out.val.out)` with `Quotient.out_eq`.
- `mk_discreteSeriesClass_rationalOrbitRepresentative`: `discreteSeriesClass … = O.out` by
  `Subtype.ext` and `Quotient.out_eq`, then `Quotient.out_eq O`.
- `rationalOrbitRepresentativeMember`: `hO` and
  `mk_discreteSeriesClass_rationalOrbitRepresentative` give equal orbits; `Quotient.exact` gives a
  unitary unramified `χ` with `χ • class(chosen) = class(π')`, whose underlying classes are the
  twist required by `UnitaryOrbitRepresentative`.
- `rationalOrbitSectionsBaseEquiv`, `rationalOrbitSmoothSectionsBaseEquiv`: the Library's base
  change with the actual data of `rationalInducedSmoothOrbitSections`; `_val` by `rfl`.
- `rationalOrbitSectionsBaseEquiv_rationalFourierThetaFamily`: at each member `B` of the orbit of
  `π'`, both sides are `f̂(B, P_I)` by `rationalFourierOrbitSection_apply` (for the chosen
  representative at the same object `B`, and for `π'`); they agree up to proofs.
- `rationalFourierThetaFamily_eq_zero_iff`: rewrite with the previous theorem and use
  `LinearEquiv.map_eq_zero_iff`.
- The closure lemmas: `Submodule.add_mem`, `zero_mem`, `Submodule.smul_mem` componentwise; for the
  supports, the support of `ψ + φ` lies in the union of the supports, that of `0` is empty and that
  of `c • ψ` lies in that of `ψ` (with `Pi.add_apply`, `Pi.zero_apply`, `Pi.smul_apply`). They are
  separate theorems because the same terms written inside the `Submodule` structure time out
  during elaboration.
- `finite_support_rationalFourierThetaFamily`: Unit 31's
  `exists_finite_sigma_rationalFourierOrbitSection_ne_zero_of_statement` gives a finite set `T'`
  containing `⟨I, O_π⟩` whenever `ψ_f[O_π, P_I] ≠ 0`; apply it to `π` the chosen representative
  and rewrite its orbit to `O` by `mk_discreteSeriesClass_rationalOrbitRepresentative`.
- `rationalFourierThetaComponentLinear` and `_val`: Unit 24's definition and `_val` lemma with the
  per-`I` hypotheses.
- `rationalFourierThetaFamilyLinear`: additivity and homogeneity componentwise, by rewriting each
  component as the value of `rationalFourierThetaComponentLinear` and using `map_add`, `map_smul`,
  `Submodule.coe_add`, `Submodule.coe_smul`.
- `rationalFourierThetaLinear`: `LinearMap.codRestrict` of `rationalFourierThetaFamilyLinear`; the
  membership is `mem_rationalStandardThetaSmoothSections` with the components from
  `rationalFourierThetaComponentLinear` (their `property`, rewritten by `_val`) and the support
  from `finite_support_rationalFourierThetaFamily`.

## Scope

- Only the standard parabolic subgroups `P_I(F)` are treated, not all semi-standard ones. Each
  orbit uses one chosen representative; independence of this choice is proved as above. The
  circle coordinates `leviRationalUnitaryCoordinates` of `Im X(M_I)` are fixed, and the dependence
  on them is not studied here.
- Theorem VIII.1.2 is not proved: `rationalFourierThetaLinear` and
  `finite_support_rationalFourierThetaFamily` take its published statement `hVIII`, which is open.
  The other analytic inputs are hypotheses as in Unit 24: `hsw`, `hswM` (Lemma II.1.5), `hE`
  (Proposition II.4.5), `hTA` (Corollary III.1.2); their actual statements are published but
  unproved. `hPKiw`, the measure normalizations, `hnσ` and `hint` are hypotheses as in Unit 24
(`hint` for the discrete series of each `M_I(F)`; given the coefficient bound of Corollary
III.1.2, it follows from the published `integrable_rationalCoefficientPairingIntegrand`, which is
not used here).
- The continuity of `f ↦ ψ_f` into `C^∞(Θ)` is not stated (the continuity of each component is
  Unit 32's `rationalFourierOrbitSectionCLM`). No topology on `C^∞(Θ)` is defined.
- Not covered: the map `κ̃ : C^∞(Θ) → C(G)` and the space `C^∞(Θ)_inv` of VI.3, which need
  `f_ψ ∈ C(G)` (the rest of Proposition VI.3.1) and the constants `C(G|M)`, `γ(G|M)`.
