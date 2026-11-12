# Unipotence of the center of `M_J` on the Jacquet modules of `I_{P₀}^G 1` (statement)

Author: Worker 3642, task `1ef6854b-f0e9-4d96-bbe5-cb8c4b52f927` (revision 1).

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalMinimalInducedJacquetStatement`,
namespace `Langlands.HarishChandraSchwartz`. It imports
`Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalXiCoefficient` (for
`rationalMinimalInduced`, Waldspurger's `I_{P₀}^G 1`, and the decomposition
`isSemidirectDecomposition_minimalStandard`),
`Langlands.Representation.Jacquet.StandardFixedVectorGeneration` (for
`standardLeviPoints_le_normalizer_standardUnipotentPoints`) and
`Langlands.Representation.Jacquet.StandardCasselmanPairing` (for
`IsCompatibleStandardSplitComponent.map_commute`). It uses the local instances of
`RationalWeights` (the canonical topology `rationalPointTopology F G.X` on
`G(F) = rationalPoints G`).

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après Harish-Chandra*,
J. Inst. Math. Jussieu 2 (2003), 235–333, DOI 10.1017/S1474748003000082 (literature id
`waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`). Page numbers are printed
pages; the PDF page is the printed page minus 234. The author checked the quotations below on
the rendered PDF pages 9, 10 and 17.

- I.3, printed p. 243: "Notons `V_P` le module de Jacquet de `V` relativement à `P` et
  `j_P : V → V_P` la projection naturelle. On munit `V_P` de la représentation admissible `π_P` de
  `M` définie par `π_P(m)j_P(v) = δ_P(m)^{-1/2}j_P(π(m)v)` pour tous `m ∈ M`, `v ∈ V`."
- I.3, printed p. 244: the filtration `(F_w)` of `I_P^G V` by the double cosets
  `P w^{-1} P'`, and "la représentation `((I_P^G π)_{P'}, (I_P^G V)_{P'})` admet une filtration
  dont le gradué associé est `⊕_{w ∈ ^{P'}W^P} (I^{M'}_{M'∩w·P} wπ_{M∩w^{-1}·P'}, …)`"
  (cf. [BZ, 2.12]).
- II.1, printed pp. 250–251: `(π, V) = (I_{P_0}^G 1, I_{P_0}^G ℂ)`.
- Proof of Lemme II.1.1, printed p. 251: "Pour tout sous-groupe parabolique standard `P`, posons
  `M̄_0^+(P) = {m ∈ M̄_0^+ ; P_{m,t} = P}`. [...] On sait calculer `π_P`, cf. I.3. On voit qu'il
  existe un entier `d` tel que pour tout `a ∈ A_M`, `(π_P(a) − 1)^d` annule `V_P`. Il existe donc
  un polynôme `Q` sur `a_M` de degré `⩽ d` tel que `⟨π_P(ah)j_P(e), ǰ_P̄(e)⟩_P = Q(H_M(a))` pour
  tout `a ∈ A_M`."

The statement of this module strengthens the displayed sentence "il existe un entier `d` tel
que pour tout `a ∈ A_M`, `(π_P(a) − 1)^d` annule `V_P`", for `π = I_{P₀}^G 1` and the standard
parabolic subgroups `P`, from the split component `A_M` to the whole center of `M(F)`; the
source's form is the corollary `RationalMinimalInducedJacquetUnipotentStatement.splitComponent`.
The source gives no further proof. It is the input of the upper bound of Lemma II.1.1 (the
published `RationalXiUpperBoundStatement`) besides Proposition I.4.3. The central form is the one
the upper bound needs on actual points: the uniformizer powers `ϖ^x` with `⟨α, x⟩ = 0` for
`α ∈ J` are central in `M_J(F)` (the Library's `commute_uniformizerPowers`), and their exponents
`x` run over the whole lattice `{x ; ⟨α, x⟩ = 0 for α ∈ J}`, whereas the Library does not identify the
cocharacters of a compatible split component with a finite-index sublattice of it.

## Declarations

- `rationalMinimalInducedJacquet i ν h J` (definition): the representation of the actual
  standard Levi `M_J(F) = standardLeviPoints i ν J` on the coinvariants
  `Jacquet.Coinvariants π U_J(F)` of `π = (rationalMinimalInduced i ν h).representation` under
  the actual standard radical `U_J(F) = standardUnipotentPoints i ν J`, given by the Library's
  `Jacquet.normalizedActionOfModulus` with the modulus
  `δ_{U_J} = HaarModulus.closedRestrictCharacter U_J(F) … M_J(F) …`, the Haar modulus of
  conjugation by `M_J(F)` on the closed subgroup `U_J(F)`. Thus
  `π_P(m) j(v) = δ_{U_J}(m)^{-1/2} j(π(m) v)` (`normalizedActionOfModulus_mk`). Here
  `h : P₀(F) = M₀(F) ⋉ U₀(F)` is any decomposition of the actual minimal standard parabolic.
- `RationalMinimalInducedJacquetUnipotentStatement.{u}` (the recorded `Prop`): for every
  nonarchimedean local field `F : Type u`, every group scheme `G` over `Spec F` with
  `[IsAffineHom G.X.hom]`, `[LocallyOfFiniteType G.X.hom]` and `hG : IsConnectedReductive G`,
  every maximal split torus `i : S → G` (`hi`), every generic cocharacter `ν` (`hν`) and every
  `J ⊆ simpleRelativeRoots i ν`, there is `d : ℕ` such that for every `z ∈ M_J(F)` with
  `z * m = m * z` for all `m ∈ M_J(F)`,

  `(rationalMinimalInducedJacquet i ν (isSemidirectDecomposition_minimalStandard hG hi hν) J z - 1) ^ d = 0`

  as an endomorphism of the Jacquet module. The decomposition is the Library's proved
  `isSemidirectDecomposition_minimalStandard` (from `standardCocharacter`), so `π` is the actual
  `I_{P₀}^G 1`. `d` does not depend on `z`.
- `RationalMinimalInducedJacquetUnipotentStatement.splitComponent` (proved from the statement):
  for every compatible split component `q : A → S` of `M_J`
  (`IsCompatibleStandardSplitComponent i ν J A q`) there is `d` with
  `(π_P(a) − 1)^d = 0` for `a = rationalPoints.map (q ≫ i) x`, every `x ∈ A(F)`. Proof: these
  points lie in `M_J(F)` (`IsCompatibleStandardSplitComponent.map_mem_standardLeviPoints`) and are
  central there (`IsCompatibleStandardSplitComponent.map_commute`).

### Correspondence with the source

- `P = P_J` runs over the standard parabolic subgroups (`J ⊆ Δ`) and `M = M_J`. In the corollary,
  `A(F)` is the source's `A_M`: `IsCompatibleStandardSplitComponent` says that `A` is a split
  component of the connected reductive group representing `M_J`, compatible with `S`. The center
  of `M_J(F)` contains `A_M`.
- `π = I_{P₀}^G 1` is `rationalMinimalInduced`: the Library's normalized induction of the trivial
  character of `M₀(F)`, whose vectors are the smooth `f` with `f(p g) = δ₀(p)^{1/2} f(g)`.
- The normalization of `V_P` uses `δ_{U_J}`, the Haar modulus of conjugation on `U_J(F)`. For
  connected reductive `G` (the setting here) the restriction of Waldspurger's `δ_P` (the modulus of
  `P(F)`) to `M_J(F)` is `|det Ad(m)|_{Lie U_J}|_F = δ_{U_J}(m)`; this standard identity is not
  proved in the Library and is background for the comparison. Normalizing by another positive
  character `χ` would multiply `π_P(z)` by the scalar `(δ_{U_J}(z)/χ(z))^{1/2}` and change the
  statement unless `χ = δ_{U_J}` on the center; so the identity `δ_P = δ_{U_J}` on the center of
  `M_J(F)` is what makes the Lean statement the source's.

### Why the statement holds (background; not proved here)

By I.3 (the geometric lemma [BZ, 2.12]), `(I_{P₀}^G 1)_{P}` has a finite filtration by
`M`-submodules whose graded pieces are `I^{M}_{M ∩ w·P₀}(w 1_{M₀ ∩ w^{-1}·P}) = I^M_{M∩w·P₀} 1`
(normalized induction of a trivial character: `w^{-1}` normalizes `M₀`, so
`M₀ ∩ w^{-1}·P = M₀` and the Jacquet module of the trivial representation of `M₀` along it is
the trivial representation). An element `z` of the center of `M(F)` centralizes `S(F)`, which is
Zariski dense in `S`, so `z ∈ Z_G(S)(F) = M₀(F) ⊆ w·P₀`, and `z ∈ M ∩ w·P₀`. Then
`(π(z) f)(x) = f(x z) = f(z x) = δ_{M ∩ w·P₀}(z)^{1/2} f(x) = f(x)` on such a piece, since
conjugation by the central `z` is trivial on the radical of `M ∩ w·P₀`, which lies in `M`. So
`π_P(z) − 1` kills every graded piece, and `d` = the number of double cosets `P₀ \ G / P` works,
uniformly in `z`. A Lean proof needs the geometric lemma on
actual rational points for this pair (for example the Library's
`RepresentedGeometricLemmaStatement`, unproved, Task 4822, together with bridges from
`rationalMinimalInduced` and `Jacquet.Coinvariants` to the represented-parabolic functors, or a
direct support filtration through the Library's `closedSubgroupMackeyFiltration`), the finiteness
of `P₀(F) \ G(F) / P(F)`, and the modulus comparisons on the pieces.

## Status and scope

- This is a statement target; it is not proved here.
- Standard parabolic subgroups only, as in the source's proof of II.1.1.
- `d` may depend on `F, G, i, ν, J`, not on `z`; the source's `d` is likewise chosen after `P`.
- The central form is stronger than the source's sentence (which concerns `A_M`); it is a derived
  strengthening justified by the same argument, and the source's form is the proved corollary.
- No structural (Renard Chapter V) hypothesis occurs: the decomposition `P₀(F) = M₀(F) ⋉ U₀(F)`
  is proved in the Library for connected reductive `G` and generic `ν`.
- Provenance: `rationalMinimalInducedJacquet` is internal (the Library's normalized coinvariants
  applied to `I_{P₀}^G 1` and the actual standard subgroups); the statement is derived from the
  quoted sentence of the proof of Lemma II.1.1 by replacing `A_M` with the center of `M(F)`.
