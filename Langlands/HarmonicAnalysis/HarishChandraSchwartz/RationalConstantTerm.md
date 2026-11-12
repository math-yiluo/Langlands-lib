# The constant term `C(G) → C(M_J)` on actual rational points (III.6, Proposition II.4.5)

Author: Worker 3642, task `1ef6854b-f0e9-4d96-bbe5-cb8c4b52f927` (revision 1).

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalConstantTerm`,
namespace `Langlands.HarishChandraSchwartz`.

The module brings the Library's generic constant term of III.6 (module `ConstantTerm`) to the
actual standard parabolic subgroups `P_J(F) = M_J(F) U_J(F)` of a connected reductive group. It
contains:

- proofs of the hypotheses `IsConjModulus` and `ConstantTermData` of the generic constant term
  for a Haar measure on `U_J(F)` and the Haar modulus `δ_{U_J}`;
- a proof that `Ξ^{M_J} = rationalLeviXi` is positive;
- the structural predicate `StandardLeviCartanCovering`, the covering clause of the Cartan
  decomposition of `M_J(F)` (Renard V.5.1 (5) applied to (4));
- the statement `RationalConstantTermEstimateStatement` of Proposition II.4.5 for the opposite
  parabolic `P̄_J`, in the Library's form `ConstantTermEstimate`, conditional on Renard's
  structural inputs;
- the continuous linear map `rationalConstantTerm : C(G) → C(M_J)`, `f ↦ f^{(P_J)}`, defined
  from that estimate.

The recorded declaration is the statement `RationalConstantTermEstimateStatement`. It is a
proposition definition, not a proof.

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après Harish-Chandra*,
J. Inst. Math. Jussieu 2 (2003), 235–333, DOI 10.1017/S1474748003000082 (literature id
`waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`). Page numbers below are the
printed ones; the PDF page is the printed page minus 234. The author checked the quotations
against the text of PDF pages 18, 28, 29 and 38.

- Proposition II.4.5, printed p. 262, for a standard parabolic `P = MU`: "Soit `d ∈ ℕ`. Il
  existe `d' ∈ ℕ` et `c > 0` tels que pour tout `m ∈ M`, on ait l'inégalité
  `δ_P(m)^{−1/2} ∫_Ū Ξ(mū)(1 + σ(mū))^{−d'} dū ⩽ cΞ^M(m)(1 + σ(m))^{−d}`."
- Its proof, printed pp. 262–263, begins: "On a l'égalité `M = (K ∩ M)M̄₀^{M+}(K ∩ M)`. On peut se
  limiter à démontrer l'inégalité de l'énoncé pour `m ∈ M̄₀^{M+}`", where
  `M̄₀^{M+} = {m ∈ M₀ ; ∀α ∈ Δ^M_0, ⟨α, H₀(m)⟩ ⩾ 0}`. It then uses Lemma II.4.4, Lemma II.3.1,
  Lemma II.1.1 for `M` (`δ₀(m)^{1/2} δ_P(m)^{−1/2} = δ₀^M(m)^{1/2} ⩽ C₃Ξ^M(m)`) and Lemma II.4.2.
- The remark after the proof, printed p. 263: "Au début du paragraphe, on a supposé `P` standard
  mais le Lemme II.4.3 et la Proposition II.4.5 sont aussi valables si `P` n'est que
  semi-standard (il suffit de changer de `P₀`)."
- III.6, printed p. 272: "Soit `P = MU` un sous-groupe parabolique semi-standard de `G`. Pour
  `f ∈ C(G)` et `m ∈ M`, posons `f^{(P)}(m) = δ_P(m)^{1/2} ∫_U f(mu) du`. Il résulte de la
  Proposition II.4.5 appliquée à `P̄` que l'intégrale est convergente et que la fonction `f^{(P)}`
  ainsi définie sur `M` appartient à `C(M)`. De plus l'application `C(G) → C(M)`, `f ↦ f^{(P)}`
  est continue."
- II.1, printed p. 252: `Ξ^M` is defined on `M` "comme on vient de définir `Ξ` sur `G`".

D. Renard, *Représentations des groupes réductifs p-adiques* (2026 version; literature id
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`), V.5.1, printed p. 122
(PDF p. 128): a maximal compact open `K₀` with (1) `G = K₀P_∅`, (3)
`K₀ ∩ P = (K₀ ∩ M)(K₀ ∩ N)`, (4) the Cartan decomposition `G = ⋃ K₀ a f K₀`
(`a ∈ C_∅^+`, `f ∈ F_∅`), and "(5) Pour tout parabolique standard `P = MN` le sous-groupe
compact maximal `K₀ ∩ M` de `M` vérifie les propriétés (1) à (4) pour le parabolique minimal
`P_∅ ∩ M` de `M`." V.5.2, printed p. 123: the simultaneous standard basis. These are rows S19
and S20–S23 of the Library's note `notes/renard/chapter-v-structural-inputs.md`.

## Setting

`F` is a nonarchimedean local field of any characteristic. `G` is a group scheme over `Spec F`
with `[IsAffineHom G.X.hom]` and `[LocallyOfFiniteType G.X.hom]`; the results below that need it
assume `hG : IsConnectedReductive G`. `G(F) = rationalPoints G` carries the canonical topology
and its Borel σ-algebra (the local instances of `RationalWeights`), with second countability,
the Hausdorff property and the nonarchimedean group property. `i : S → G` is a maximal split
torus (`hi`), `ν` a generic cocharacter (`hν`) and `J ⊆ simpleRelativeRoots i ν` (`hJ`).
`P₀(F) = standardParabolicPoints i ν ∅`, `M_J(F) = standardLeviPoints i ν J`,
`U_J(F) = standardUnipotentPoints i ν J`; `U_J(F)` carries the subspace σ-algebra and
`ν_U` (written `nuU` in Lean) is a Haar measure on it. `δ_{U_J} = standardUnipotentModulus i ν J`
is the Haar modulus of conjugation of `M_J(F)` on `U_J(F)` (the Library's
`HaarModulus.closedRestrictCharacter`). For connected reductive `G` it is Mathlib's modular
character of `P_J(F)` (`modularCharacter_standardParabolicPoints`), Waldspurger's `δ_P`.
`K` is a compact open subgroup with `hPK : G(F) = P₀(F) K` and
`hM : M_J(F) = (P₀(F) ∩ M_J(F))(K ∩ M_J(F))`. `Ξ = rationalXi hKc hPK`,
`Ξ^{M_J} = rationalLeviXi hKc hM`, and `σ = rationalHeight ρ` for a matrix representation
`ρ : G → GL_N`, restricted to `M_J(F)` for `C(M_J)`.

## Proved results

- `rationalIsConjModulus nuU`: `IsConjModulus` for `ν_U` and `δ_{U_J}`: for `m ∈ M_J(F)` the image
  of `ν_U` under `u ↦ m u m⁻¹` is `δ_{U_J}(m)⁻¹ ν_U`. This is the Library's
  `isConjModulus_restrictCharacter` (module `ConstantTermInd`), after identifying
  `closedRestrictCharacter` with `restrictCharacter` (`HaarModulus.closedRestrictCharacter_eq`).
  Its regularity premise holds because `U_J(F)` is closed in `G(F)`, hence locally compact,
  second countable and metrizable (`metrizableSpace_of_t3_secondCountable`), so every locally
  finite Borel measure on it is regular
  (`Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure`).
- `rationalConstantTermData nuU`: the Library's `ConstantTermData ν_U δ_{U_J}`: `M_J(F)` is
  closed, it normalizes `U_J(F)`, and for `m ∈ M_J(F)` in a compact open subgroup,
  `δ_{U_J}(m) = 1` and `ν_U` is invariant under conjugation by `m`. This is the Library's
  `constantTermData_restrictCharacter` with `isClosed_standardLeviPoints`. No reductivity is
  needed for these two results.
- `standardLeviMinimalModulusOf_eq_one hKo hKc hG hi hν hJ p hp`: `δ₀^{M_J}(p) = 1` for
  `p ∈ P₀(F) ∩ M_J(F) ∩ K`. By the published factorization `δ₀ = δ₀^{M_J} δ_{U_J}`
  (`rationalMinimalModulus_eq_mul`), since `δ₀(p) = 1` (`rationalMinimalModulus_eq_one`) and
  `δ_{U_J}(p) = 1` (`standardUnipotentModulus_eq_one`).
- `rationalLeviXi_pos hKo hKc hG hi hν hJ hM m`: `Ξ^{M_J}(m) > 0`, from the Library's `xi_pos`
  for the group `M_J(F)`, the previous result and the openness of `K ∩ M_J(F)` in `M_J(F)`.

## The structural predicate `StandardLeviCartanCovering`

`StandardLeviCartanCovering F i ν J K0` (an `abbrev`, for a subgroup `K0` of `G(F)`): there is a
finite set `F₀` of points of the torus centralizer `centralizerPoints i` (Waldspurger's `M₀`)
such that every `m ∈ M_J(F)` can be written `m = k₁ f a k₂` with `k₁, k₂ ∈ K0 ∩ M_J(F)`,
`f ∈ F₀` and `a ∈ CocharacterUniformizer.CAplus F S J`, the points `a` of `S(F)` with
`|α(a)|_F ≤ 1` for every `α ∈ J` (the chamber `C_∅^+` of `M_J`, whose simple roots are `J`;
`|α(a)|_F ≤ 1` is Waldspurger's `⟨α, H₀(a)⟩ ⩾ 0`).

It is the covering clause of Renard V.5.1 (4) for the Levi subgroup `M_J`, which V.5.1 (5)
provides for `K0 ∩ M_J` when `K0` is the compact subgroup of V.5.1. It has the same form as the
Library's `FiniteCartanCovering F i ν K0` (module `RationalCuspidalCompactRestrictionStatement`),
with `G(F)`, `K0` and the simple roots of `G` replaced by `M_J(F)`, `K0 ∩ M_J(F)` and `J`. Its
existence for a special `K0` is a structural input at the Renard Chapter V boundary and is not
proved in the Library. It is used only as a premise of the statement below.

## Proposition II.4.5 (statement)

**`RationalConstantTermEstimateStatement`** (universe `u`): for every universe-`u`
nonarchimedean local field `F`, every connected reductive `G`, maximal split torus `i`, generic
cocharacter `ν`, every `J ⊆ Δ`, and every subgroup `K0` of `G(F)` such that

- `K0` is open and compact,
- `SimultaneousStandardBasisAt i ν K0` holds (Renard V.5.2),
- `FiniteCartanCovering F i ν K0` holds (Renard V.5.1 (4) for `G`), and
- `StandardLeviCartanCovering F i ν J K0` holds (Renard V.5.1 (5) and (4) for `M_J`),

and for every compact open `K` with `hPK` and `hM`, every `N ≥ 1`, every closed matrix
representation `ρ : G → GL_N` (`IsClosedSubgroup ρ`) and every Haar measure `ν_U` on `U_J(F)`:

`ConstantTermEstimate ν_U δ_{U_J} Ξ σ Ξ^{M_J} σ|_{M_J}`,

that is, for every real `d` there are a real `d'` and `c ≥ 0` such that for all `m ∈ M_J(F)`

`δ_{U_J}(m)^{1/2} ∫⁻_{U_J(F)} Ξ(m u) (1 + σ(m u))^{-d'} dν_U(u) ≤ c Ξ^{M_J}(m) (1 + σ(m))^{-d}`

(lower Lebesgue integral in `ℝ≥0∞`).

### Correspondence with the source

- This is Proposition II.4.5 for the semi-standard parabolic `P̄_J = M_J Ū_J`, as allowed by the
  remark on p. 263. For `P̄_J` the unipotent radical of the opposite is `U_J`, and
  `δ_{P̄_J}(m)^{−1/2} = δ_{P_J}(m)^{1/2}`. This is the form that III.6 uses ("la Proposition II.4.5
  appliquée à `P̄`"), and the form of the Library's `ConstantTermEstimate`. Here `δ_{P_J}` is
  `δ_{U_J}`, identified with the modular character of `P_J(F)` as recalled in the Setting.
- The source has natural-number exponents `d, d'` and `c > 0`; the Library's form has real
  exponents and `c ≥ 0`. The two forms are equivalent, since `1 + σ ≥ 1` and the
  exponents and constants can be enlarged.
- The source fixes a special `K`. The statement allows every compact open `K` with `hPK` and
  `hM`, and every closed `ρ`. The conclusion remains true in this generality. For two such
  subgroups, the functions `Ξ` (and `Ξ^{M_J}`) are bounded by constant multiples of each other,
  as explained in `RationalSquareIntegrableDecay.md`. Changing `ρ` changes `1 + σ` only by powers
  and constants (`exists_one_add_rationalHeight_le`). The integral does not depend on the
  normalization of `ν_U` beyond a constant factor.
- The structural premises are the external inputs of the source's argument: the Cartan
  decomposition of `M` for the reduction to `M̄₀^{M+}`, and Renard's V.5.2 basis behind Lemmas
  II.1.1, II.4.2 and II.4.4. The covering clause for `G` is mathematically the case `J = Δ` of
  the Levi clause (for `J = Δ`, `M_J = G`); it is kept for uniformity with the published statements of Lemma II.1.5 and Corollary III.1.2.
  `K0` is assumed compact open so that the covering clauses are not trivially satisfied.
- Lemmas II.4.2, II.4.4, II.3.1 and II.1.1 for `M_J` are obligations of a proof, not premises.
  The Library's `ConstantTermBound` derives `ConstantTermEstimate` from abstract forms of these
  lemmas; `LeviWeightIntegrability` derives Lemma II.4.3 from Lemma II.4.2. Their actual-point
  inputs are not established here.

## The constant term (section `ConstantTerm`)

- **`rationalConstantTerm hKo hKc hPK hM ρ nuU hG hi hν hJ hE`** (definition): given
  `hE : ConstantTermEstimate ν_U δ_{U_J} Ξ σ Ξ^{M_J} σ|_{M_J}` (the conclusion of the statement),
  the continuous linear map from `RationalSchwartzSpace hKc hPK ρ` (`C(G)` for `Ξ`, `σ`) to the
  Library's `Space Ξ^{M_J} σ|_{M_J}` (`C(M_J)`). It is the Library's `Space.constantTerm` with
  `rationalConstantTermData`, the positivity of `Ξ` and `Ξ^{M_J}`, the nonnegativity of `σ`, and
  the compact open subgroup `K` (which supplies `Nonempty (CompactOpenSubgroup G(F))`).
- `coe_rationalConstantTerm`: the value is
  `f^{(P_J)}(m) = δ_{U_J}(m)^{1/2} ∫_{U_J(F)} f(m u) dν_U(u)` (Bochner integral), Waldspurger's
  `f^{(P)}` of III.6.
- `RationalConstantTermEstimateStatement.constantTermEstimate`: the statement applied to one
  group and one `J`, under its structural hypotheses. Composing it with `rationalConstantTerm`
  gives the constant term `C(G) → C(M_J)` of III.6 conditionally on the statement.

## Scope

- Proposition II.4.5 is not proved here.
- Only standard parabolics `P_J` (with the estimate for their opposites) are treated; the
  reduction from semi-standard parabolics is not formalized.
- The `G × G`-equivariant map `f ↦ f^{(P),Ind}` and the transitivity diagram of III.6 (Library
  module `ConstantTermInd`, which needs `TransitivityData`) are not specialized here.
- `C(M_J)` is the Library's generic space on the subgroup `M_J(F)` of `G(F)`. Its comparison
  with the Schwartz space of the Levi group scheme `Standard.leviScheme i ν J` is not formalized.
- Provenance: the statement is a direct translation of Proposition II.4.5 (for `P̄_J`) with its
  structural premises displayed. `StandardLeviCartanCovering` is the covering clause of Renard
  V.5.1 (5) with (4). `rationalConstantTerm` is the constant term of III.6 through the Library's
  generic `ConstantTerm`. The remaining declarations are internal glue.
