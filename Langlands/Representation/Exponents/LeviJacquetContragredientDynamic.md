# Jacquet modules of contragredients for dynamic opposite parabolics

Author: Worker 937. Lean module
`Langlands.Representation.Exponents.LeviJacquetContragredientDynamic`. The declarations are
in the namespaces `Langlands.Aubert.General`, `Langlands.Aubert.General.RationalPointFamily`
and `Langlands.Aubert.General.RepresentedParabolic`.

## Source

Renard 2026, *Représentations des groupes réductifs p-adiques*, VI.9.6 Theorem (VI.9.6.2)
(printed p.201, PDF p.207): `r_{P̄}^G(π~) ≅ (r_P^G π)~` for every smooth `π`. The source
ID is `renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. Renard proves it with
the `M`-equivariant duality `⟨,⟩_P` of the Proposition on PDF p.208. That duality uses an
element `t` of the centre of `M` contracting `N`, compact open subgroups with an Iwahori
decomposition, and the stabilization of compression from the Proposition of VI.9.1 (PDF
pp.201-203).

The abstract form of the isomorphism is
`Aubert.General.nonempty_contragredient_normalizedJacquet_iso_of_splits`
(`Aubert/General/IwahoriNaturalJacquetDuality.lean`). It takes closed subgroups `U`, `O`
normalized by `M`, an element `g` commuting with `M` with an opposite contraction basis,
reciprocal inverse-half Haar characters and two compression splittings. This module supplies
`g` and its basis for the parabolic of a cocharacter `χ`, with `N = N(χ)`, `M = M(χ)` and
`N̄ = N(χ⁻¹)`. It obtains the splittings from the VI.9.1 statement. It then transports the
result to represented parabolics with
`RepresentedParabolic.nonempty_leviJacquetContragredient_iso_of_pointImage`
(`Exponents/LeviJacquetContragredientReduction.lean`).

Three inputs are hypotheses here and are not proved:

- `hstab : UniformCompressionStabilizationStatement`, the Proposition of VI.9.1
  (`Exponents/UniformCompressionStabilizationStatement.lean`);
- reciprocity of the Haar scaling characters of `N(χ⁻¹)` and `N(χ)` on `M(χ)`;
- for represented parabolics, the identifications of the point images of `N`, `M` and `N̄`
  with `N(χ)`, `M(χ)` and `N(χ⁻¹)`.

So nothing here proves `LeviJacquetContragredientStatement`. The module is a reduction of it
to these inputs.

Notation on rational points:
`N(χ) = (Dynamic.unipotent χ).carrier (Over.mk (𝟙 _))`,
`M(χ) = (Dynamic.centralizer χ).carrier (Over.mk (𝟙 _))` and
`N(χ⁻¹) = (Dynamic.unipotent (Dynamic.inverseCocharacter χ)).carrier (Over.mk (𝟙 _))`.

## Setting

The field `k : Type u` has `[Field k] [ValuativeRel k] [TopologicalSpace k]
[IsNonarchimedeanLocalField k] [T2Space k]`. `G` is a group scheme over `Spec k` with
`[IsAffineHom G.X.hom]`. `G(k)` carries the local instance `RationalPointFamily.pointTopology`
and is assumed `[LocallyCompactSpace]` and `[NonarchimedeanGroup]`. This is the setting of
`UniformCompressionStabilizationStatement` and of `LeviJacquetContragredientStatement`.

## Declarations

### `closedInverseHalfCharacter_mul_eq_one_of_closedRestrictCharacter`

Namespace `Langlands.Aubert.General`. The setting is a locally compact topological group `Γ`,
closed subgroups `U`, `O` and a subgroup `M` normalizing both, and `m : M`. If
`HaarModulus.closedRestrictCharacter U hU M hMU m * HaarModulus.closedRestrictCharacter O hO M hMO m = 1`,
then the complex values of `HaarModulus.closedInverseHalfCharacter` for `U` and `O` at `m`
multiply to `1`. So reciprocity of the full Haar scaling characters gives the reciprocity
premise of `nonempty_contragredient_normalizedJacquet_iso_of_splits`. In Renard's notation,
`δ_{N̄} δ_N = 1` on `M` gives `δ_{N̄}^{-1/2} δ_N^{-1/2} = 1`.

Proof: the inverse-half character is the composite of the scaling character with
`NNReal.sqrt`, the inclusion into `ℂ` and inversion. All three are monoid homomorphisms, so
the product is the image of the product `1`.

### `RationalPointFamily.dynamic_exists_central_hasOppositeIwahoriContractionBasis`

For `hG : IsConnectedReductive G` and a cocharacter `χ`, there is `g ∈ G(k)` commuting with
every element of `M(χ)` such that
`Jacquet.HasOppositeIwahoriContractionBasis N(χ) M(χ) N(χ⁻¹) g` holds.

The published `RationalPointFamily.dynamic_hasOppositeIwahoriContractionBasis`
(`Exponents/ArbitraryParabolicJacquetAdmissibilityReduction.lean`) gives the basis but does
not say that `g` is central in `M(χ)`. Renard's `t` is central, and the splitting hypotheses
of the VI.9.1 statement require it. The proof repeats the published one and keeps the
centrality. `BruhatTits.DynamicUnipotentContainment.exists_central_contractingPoint` gives `g`
in `M(χ)`, commuting with `M(χ)`, such that conjugation by `g^n` pushes every compact subset of
`N(χ)` into any neighbourhood of `1` for large `n`, and conjugation by `g^{-n}` does the same
for `N(χ⁻¹)`. In the Library this `g` is `χ(t)` for a unit `t` of `k` whose powers tend to `0`.
`Jacquet.hasOppositeIwahoriContractionBasis_of_contraction` turns this into the basis. Its
remaining inputs are:

- closedness of both radicals (`isClosed_unipotentPoints`);
- normalization of both by `M(χ)` (`Dynamic.centralizer_le_normalizer_unipotent`, with
  `Dynamic.centralizer_inverseCocharacter` for `N(χ⁻¹)`);
- uniqueness of the factorization `N(χ⁻¹) M(χ) N(χ)` (`dynamic_opposite_factorization_unique`);
- the open cell as a neighbourhood of `1` (`Dynamic.opposite_cell_mem_nhds_one`). It is stated
  for the scheme topology, which equals the point topology by
  `rationalPointTopology_eq_rationalSchemeTopology`.

### `RationalPointFamily.compactCompressionSplits_of_uniformCompressionStabilization`

Given `hstab`, `hG`, `χ`, an element `g` commuting with `M(χ)`, a smooth representation `A`,
a compact open `K` and `Jacquet.IsIwahoriContraction K N(χ) M(χ) N(χ⁻¹) g`, the compression of
`g` splits: `Jacquet.CompactCompressionSplits A.representation A.isSmooth K hK g`. This is the
second conclusion of `hstab`, at the exponent it provides. It is the Fitting splitting
`V^K = V^K_0 ⊕ V^K_*` of the VI.9.1 Proposition. The uniformity of the exponent is not used.

### `RationalPointFamily.nonempty_contragredient_normalizedJacquet_iso_of_dynamic`

Hypotheses: `hstab`, `hG`, `χ`, subgroups `U`, `M`, `O` of `G(k)` with `U = N(χ⁻¹)`,
`M = M(χ)` and `O = N(χ)`, closedness proofs `hU`, `hO`, normalization proofs `hMU`, `hMO`,
and

`hrec : ∀ x : M, HaarModulus.closedRestrictCharacter U hU M hMU x * HaarModulus.closedRestrictCharacter O hO M hMO x = 1`.

Conclusion:

`Nonempty (SmoothRep.contragredientFunctor ⋙ normalizedJacquetFunctor U M hU hMU ≅ (normalizedJacquetFunctor O M hO hMO).op ⋙ SmoothRep.contragredientFunctor)`.

These are functors `(SmoothRep ℂ G(k))ᵒᵖ ⥤ SmoothRep ℂ M`, at carrier universe `v`. In words,
`r_{N(χ⁻¹)}(π~) ≅ (r_{N(χ)} π)~` naturally in every smooth `π`. The subgroups are abstract
and the equalities are hypotheses, so the closedness and normalization proofs can be the ones
fixed by a caller.

Proof: substitute the equalities. Apply
`dynamic_exists_central_hasOppositeIwahoriContractionBasis` to `χ⁻¹`. Rewrite with
`Dynamic.centralizer_inverseCocharacter` and `Dynamic.inverseCocharacter_inverseCocharacter`.
This gives `g` commuting with `M(χ)` and a basis for `(N(χ⁻¹), M(χ), N(χ))`, the orientation
`nonempty_contragredient_normalizedJacquet_iso_of_splits` needs with `U = N(χ⁻¹)` and
`O = N(χ)`. The reciprocity premise comes from `hrec` through
`closedInverseHalfCharacter_mul_eq_one_of_closedRestrictCharacter`. The upper splitting is
`compactCompressionSplits_of_uniformCompressionStabilization` for `χ⁻¹` and `g`. The lower
splitting is the same lemma for `χ` and `g⁻¹`, which also commutes with `M(χ)`. The
contraction hypotheses of `nonempty_contragredient_normalizedJacquet_iso_of_splits` have
exactly the form the lemma needs, so both splitting families apply.

### `RationalPointFamily.exists_isStableLiftDuality_of_dynamic`

Hypotheses: exactly those of `nonempty_contragredient_normalizedJacquet_iso_of_dynamic`.
Conclusion: there is `g ∈ G(k)` with

- `∀ m ∈ M, m * g = g * m`,
- `Jacquet.HasOppositeIwahoriContractionBasis U M O g`, and
- a natural isomorphism
  `Ψ : SmoothRep.contragredientFunctor ⋙ normalizedJacquetFunctor U M hU hMU ≅ (normalizedJacquetFunctor O M hO hMO).op ⋙ SmoothRep.contragredientFunctor`
  with `Aubert.General.IsStableLiftDuality U M O hU hO hMU hMO g Ψ`
  (`Aubert/General/IwahoriJacquetStableLift.lean`).

So the isomorphism of the previous theorem can be chosen to pair the class of a `K`-fixed
smooth functional `Λ` with a class `x` of `r_{N(χ)}(π)` by `Λ(v)`, for one `K`-fixed
representative `v` of `x`, on all small compact open `K` with the two Iwahori contractions for
`g` and `g⁻¹`. This is the defining formula of Renard's duality `⟨,⟩_P` (PDF pp.208-209). The
element `g` is exported because the formula refers to it.

Proof: the same as for the previous theorem, with
`Aubert.General.exists_isStableLiftDuality_of_splits` in place of
`nonempty_contragredient_normalizedJacquet_iso_of_splits`; the element `g`, its centrality
and its basis are returned.

### `RepresentedParabolic.nonempty_leviJacquetContragredient_iso_of_dynamic`

Data: those of `LeviJacquetContragredientStatement`, namely `p : P ⟶ G`, `m : M ⟶ P`,
`n : N ⟶ P`, `pbar : Pbar ⟶ G`, `mbar : M ⟶ Pbar`, `nbar : Nbar ⟶ Pbar`, the parabolic,
rational Levi, geometric unipotent radical and isomorphic-multiplication hypotheses, and
`hP : mbar ≫ pbar = m ≫ p`. Further hypotheses:

- `hstab` and `hG`;
- a cocharacter `χ`;
- `hN : pointImage (n ≫ p) = N(χ)`;
- `hM : pointImage (m ≫ p) = M(χ)`;
- `hNbar : pointImage (nbar ≫ pbar) = N(χ⁻¹)`;
- `hrec`: for all closedness proofs of `pointImage (nbar ≫ pbar)` and `pointImage (n ≫ p)`, all
  proofs that `pointImage (m ≫ p)` normalizes them, and all `x` in `pointImage (m ≫ p)`, the
  two `closedRestrictCharacter` values multiply to `1`.

With `M(F)` given `leviPointTopology m hm` and `leviPoints_nonarchimedeanGroup p m hp hm`, the
conclusion is the conclusion of `LeviJacquetContragredientStatement`:

`Nonempty (SmoothRep.contragredientFunctor ⋙ leviJacquetFunctor pbar mbar nbar … ≅ (leviJacquetFunctor p m n …).op ⋙ SmoothRep.contragredientFunctor)`.

Proof: `nonempty_leviJacquetContragredient_iso_of_pointImage` reduces the conclusion to the
isomorphism for `U = pointImage (nbar ≫ pbar)`, `M = pointImage (m ≫ p)` and
`O = pointImage (n ≫ p)`, for all closedness and normalization proofs. Each instance is
`nonempty_contragredient_normalizedJacquet_iso_of_dynamic` with `hNbar`, `hM` and `hN`.

## Where the hypotheses are discharged

The statement's second equality `P(F) ∩ P̄(F) = M(F)` is not used here. None of the
hypotheses is proved in this module. The later modules of this development supply them as
follows:

- `hrec`, the modulus reciprocity `δ_{N̄} δ_N = 1` on `M`, comes from
  `Dynamic.LeviAdjointDeterminantReciprocityStatement` in
  `Exponents/LeviJacquetContragredientReciprocity.lean`, through
  `Aubert/General/DynamicOppositeHaarReciprocity.lean`.
- `hN` and `hM` come from a cocharacter with `P = P(χ)` and `M = M(χ)`, given by
  `ParabolicDynamicStatement` and the proved `dynamicGeometricUnipotentRadical`. `hNbar`
  comes from `P(F) ∩ P̄(F) = M(F)` and `OppositeDynamicParabolicUniquenessStatement`
  (`pointImage_opposite_radical_eq_dynamic`). Both are done in
  `Exponents/LeviJacquetContragredientStructure.lean`.
- `hstab` is the VI.9.1 Proposition, `UniformCompressionStabilizationStatement`. It remains
  a premise of `LeviJacquetContragredientFromInputsStatement`. Renard's proof of it uses the
  Bernstein decomposition VI.7, the families of VI.8 and the uniform admissibility theorem
  VI.2.3.
- `hG`, connected reductivity of `G`, is a hypothesis of `LeviJacquetContragredientStatement`.

## Checks

`lean_check` of this module, together with the other modules of the proof of
`LeviJacquetContragredientFromInputsStatement`, over Library commit 6f182f92 returned
0 errors and 0 warnings in a Lake build.
