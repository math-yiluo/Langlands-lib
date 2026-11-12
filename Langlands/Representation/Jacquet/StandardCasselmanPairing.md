# Casselman's pairing for actual standard parabolic subgroups (Waldspurger, Théorème I.4.1)

Author: Worker 19, task `1ef6854b-f0e9-4d96-bbe5-cb8c4b52f927` (revision 1).

Lean module: `Langlands.Representation.Jacquet.StandardCasselmanPairing`, namespace
`Langlands.BruhatTits.SpecialCompact`.

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333, DOI 10.1017/S1474748003000082
(literature id `waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`). Printed page numbers; the
PDF page is the printed page minus 234.

- Théorème I.4.1, printed p. 245 (PDF p. 11), attributed by Waldspurger to Casselman
  ([C, Proposition 4.2.3 et Théorème 4.2.4]), as quoted in the Library's
  `StablePairingAsymptotics.md`: "Il existe un produit bilinéaire non dégénéré et invariant par
  `M` sur `V_P × (V̌_P̄)`, noté `⟨·,·⟩_P`, de sorte que pour tout `(v, v̌) ∈ V × V̌`, il existe
  `ε > 0` tel que, pour tout `a ∈ A_M` vérifiant `|α(a)|_F < ε` pour tout `α ∈ Δ(P)`, on ait
  `⟨π_P(a) j_P(v), ǰ_P̄(v̌)⟩_P = δ_P(a)^{-1/2} ⟨π(a)v, v̌⟩`."
- I.3, printed p. 243 (PDF p. 9), as quoted in the Library's
  `Langlands/HarmonicAnalysis/HarishChandraSchwartz/TemperedExponentCone.md`: `V_P` is
  the Jacquet module and "`π_P(m)j_P(v) = δ_P(m)^{-1/2}j_P(π(m)v)` pour tous `m ∈ M`, `v ∈ V`".
- I.1, printed p. 239 (PDF p. 5): `Σ(P)` and `Δ(P)` are the positive and the simple roots of
  `A_M` relative to `P` (as quoted in `TemperedExponentCone.md`).

The present author could not open the PDF in this session and relies on these checked Library
quotations.

The structural inputs are Renard's V.5.2(i)–(iv) (rows S20–S23 of the Library note
`notes/renard/chapter-v-structural-inputs.md`: a basis of compact open subgroups normal in `K₀`,
the simultaneous Iwahori factorizations `K = K_{N̄} K_M K_N`, the normalization and contraction
by the chambers `C_A`, `C_A^+`, `C_A^{++}`, and the exhaustion, compact-containment and
neighbourhood-basis properties), encoded by the Library predicates
`StandardParabolicBasisMember` and `SimultaneousStandardBasisAt`
(`Langlands.BruhatTits.SpecialCompact.StandardBasisProperty`), and the existence of a standard
cocharacter for the face `J` (`IsStandardCocharacter`; its existence for every face is part of
the Library's unproved `StandardCocharacterStatement`, derived there from Borel–Tits §4.2, §5.12
and Renard V.4.2). These are structural assertions at the Renard Chapter V boundary; they stay
explicit hypotheses here and are not proved.

The Library's `StablePairingAsymptotics.md` lists two obligations left open by the abstract
theorem: constructing `StablePairingData` for an actual parabolic subgroup of an actual reductive
group, and showing that the elements of `A_M` with `|α(a)|_F < ε` on `Δ(P)` satisfy its
contraction conditions. This module discharges both for actual standard parabolic subgroups, with
the structural inputs above as hypotheses.

## Setting and conventions

`F` is a nonarchimedean local field (any characteristic), `G` a group scheme over `Spec F` with
`[IsAffineHom G.X.hom]` and `[LocallyOfFiniteType G.X.hom]`, connected reductive (`hG`), with the
canonical topology `rationalPointTopology F G.X` on `G(F) = rationalPoints G` (a topological group by
`rationalPoint_isTopologicalGroup`). `i : S → G` is a maximal split torus (`hi`), `ν` a generic
cocharacter (`hν`) fixing the positive system, `J ⊆ Δ` a set of simple relative roots and `ζ` a
standard cocharacter for `J` (`hζ`). The actual standard parabolic `P_J = M_J U_J` has Levi points
`standardLeviPoints i ν J`, radical `standardUnipotentPoints i ν J` and opposite radical
`standardOppositeUnipotentPoints i ν J` (the radical of the reversed chamber and face).

The structural data for the face `J` are: a set `B` of subgroups with
`hB : CompactOpenNormalBasis K0 B` (members are contained in and normal in `K0`, open and compact,
and they form a neighbourhood basis of `1`), a
split subtorus `q : A → S` with `hA : IsCompatibleStandardSplitComponent i ν J A q` (its points are
the split component `A_{M_J}(F)` of the standard Levi), and
`hmem : ∀ K ∈ B, StandardParabolicBasisMember i ν J q K`. `Δ(P_J)` is
`standardParabolicComponentCharacters i ν J q` (the restrictions to `A` of the simple roots outside
`J`) and `|α(a)|_F` is `CocharacterUniformizer.characterNorm F A α a`.

Waldspurger's `V_P` is `Coinvariants ρ (standardUnipotentPoints i ν J)` and his `V̌_P̄` is
`Coinvariants (smoothContragredient ρ) (standardOppositeUnipotentPoints i ν J)`; the pairing
`b(ǰ(ℓ), j(v))` corresponds to `⟨j_P(v), ǰ_P̄(ℓ)⟩_P` (arguments in the opposite order, as in the
Library's `StablePairingAsymptotics`). The asymptotic identity is stated in the unnormalized form
`ℓ(ρ(a)v) = b(ǰ(ℓ), j(ρ(a)v))`. Since `π_P(a) j_P(v) = δ_P(a)^{-1/2} j_P(π(a)v)`, this is
Waldspurger's identity multiplied by `δ_P(a)^{1/2}`, for any choice of the positive character `δ_P`
used to normalize `π_P`; no modulus character is needed to state it.

## Contents

### Opposite contraction (section `Opposite`, generic)

- `isIwahoriContraction_inv_of_contractionAndCofinality`: for a topological group `H`, subgroups
  `K, M, N, Nbar` with `K` open, the ordered decomposition `HasIwahoriIntersectionDecomposition K M N Nbar`,
  the clauses `ContractionAndCofinality K M N Nbar CA CA⁺ CA⁺⁺ CAε` and an element `g` in `M`, `CA`,
  `CA⁺` and `CA⁺⁺`, the Library's `IsIwahoriContraction` holds for `K`, `Nbar`, `M`, `N` and `g⁻¹`.
  It complements the Library's `isIwahoriContraction_of_contractionAndCofinality` (the orientation
  `N`, `M`, `Nbar`, `g`).

### Actual standard subgroups (section `Standard`)

- `IsCompatibleStandardSplitComponent.map_commute`: the image in `G(F)` of every point of a
  compatible split component commutes with every point of the standard Levi `M_J(F)`.
- `standardLeviPoints_neg_eq` (needs `hG`, `hi`, `hν`, `hζ`): reversing the chamber and the face
  (`-ν`, `-J`) gives the same standard Levi points.
- `standardLeviPoints_le_normalizer_standardOppositeUnipotentPoints` (same hypotheses): `M_J(F)`
  normalizes the opposite radical `Ū_J(F)`.

### The pairing data and Théorème I.4.1 (section `Pairing`)

Hypotheses `hG`, `hi`, `hν`, `hζ`, `hB`, `hA`, `hmem` as above.

- `basisOpenSubgroup hB hK`: a member `K ∈ B` as an open subgroup.
- `basis_isIwahoriContraction`: for `K ∈ B` and the chosen strict element
  `g = hA.strictElement i ν hi hζ` of the split component (the Library's
  `IsCompatibleStandardSplitComponent.strictElement`), both `IsIwahoriContraction K Ū M U g⁻¹` and
  `IsIwahoriContraction K U M Ū g` hold.
- `hasOppositeIwahoriContractionBasis_standard`: the Library's
  `HasOppositeIwahoriContractionBasis Ū_J M_J U_J g⁻¹`.
- `strictElement_inv_commute`: `g⁻¹` commutes with `M_J(F)`.
- **`standardCasselmanPairingData`** (definition, the recorded declaration): the Library's
  `StablePairingData` of `G(F)` with `N = Ū_J`, `Nbar = U_J`, `M = M_J` and contracting element
  `g⁻¹`, built by `stablePairingDataOfIwahoriContractions`. These are the data of Casselman's
  pairing for `P_J` in the Library's abstract framework (`StablePairingProof`,
  `StablePairingAsymptotics`).
- `good_of_mem`: every `K ∈ B` is a good subgroup of these data.
- `standardCasselmanPairingData_admits`: for every admissible `ρ` (`IsAdmissible`), the data satisfy
  the Library's `Admits` (from `admits_of_iwahoriContractions`).
- **`exists_standardCasselmanPairing`** (Théorème I.4.1 on Renard's chambers): for every admissible
  smooth complex representation `ρ` of `G(F)` (carrier in any universe `uV`) there is a bilinear
  `b : V̌_{Ū_J} → V_{U_J} → ℂ` with `b` and `b.flip` injective (nondegenerate), invariant under
  `M_J(F)` acting on both coinvariant spaces, such that for every `v` and smooth functional `ℓ` there
  is `ε > 0` with `ℓ(ρ(a) v) = b(ǰ(ℓ), j(ρ(a) v))` for every `a` in
  `standardComponentCAepsilon i ν J q ε` (lattice points of `A(F)` with `|α(a)|_F < ε` for
  `α ∈ Δ(P_J)`, mapped into `G(F)`).
- **`exists_standardCasselmanPairing_splitComponent`** (Théorème I.4.1 on the whole `A_{M_J}(F)`):
  the same, with the identity for every `x ∈ A(F)` with `|α(x)|_F < ε` for all `α ∈ Δ(P_J)` and
  `a` the image of `x` in `G(F)`. This is Waldspurger's quantifier "pour tout `a ∈ A_M` vérifiant
  `|α(a)|_F < ε` pour tout `α ∈ Δ(P)`".

### Assembly from the Renard property (section `Assembly`)

- **`SimultaneousStandardBasisAt.exists_casselmanPairing`**: if `K0` satisfies Renard's
  simultaneous standard basis property (`SimultaneousStandardBasisAt i ν K0`), then for every
  `J ⊆ Δ` with a standard cocharacter there are a compatible split component `q : A → S` of `M_J`
  and, for every admissible `ρ`, a pairing with all the properties of
  `exists_standardCasselmanPairing_splitComponent`.

## Proof notes

- *Opposite contraction.* Factorization: apply the ordered decomposition to `k⁻¹` and invert.
  `g⁻¹` maps `K ∩ Nbar` into itself and `g` maps `K ∩ N` into itself (weak chamber contraction);
  `g` normalizes `K ∩ M` (Levi normalization); `Nbar` is exhausted by the conjugates
  `g^n (K ∩ Nbar) g^{-n}` (strict exhaustion); and the conjugates `g^s (K ∩ N) g^{-s}` form a
  neighbourhood basis of `1` in `N`, giving the uniform contraction into every open subgroup.
- *Centrality.* `hA` provides the representing closed immersion `j : M → G` of the standard Levi and
  a split component `a : A → M` with `a ≫ j = q ≫ i`. Points of `M_J(F)` are images of points of
  `M(F)` under the multiplicative bijection `pointsEquiv`, and `a(A(F))` is central in `M(F)`
  (`IsCentral.range_le_center`).
- *Opposite normalizer.* By the Library's `standard_eq_dynamic_of_relativeRootNegation` (with the
  proved `relativeRootNegation`), the standard Levi of `(ν, J)` is the centralizer of `ζ` and that of
  `(-ν, -J)` is the centralizer of `-ζ` (`IsStandardCocharacter.neg`), which is the centralizer of the
  inverse cocharacter, hence of `ζ`. The normalizer statement is then the Library's
  `standardLeviPoints_le_normalizer_standardUnipotentPoints` for `(-ν, -J)`.
- *Pairing.* `admits_of_iwahoriContractions` and `exists_isStablePairing` give a stable pairing,
  which is nondegenerate and `M`-invariant (`IsStablePairing.injective`, `flip_injective`,
  `map_action`).
- *Asymptotics on the chamber.* For `v`, `ℓ` choose `K ∈ B` fixing both. The Library's
  `IsStablePairing.exists_finset_asymptotics_of_commute` gives a finite `F ⊆ U_J` such that the
  identity holds for every `a` with (i) `a⁻¹ (K ∩ Ū_J) a ⊆ K`, (ii) the compressions by `a` and by
  `g` on `K`-fixed vectors commute, (iii) `a F a⁻¹ ⊆ K`. For `a` in the image of `C_A^ε` with
  `ε ≤ 1`, `a` lies in `C_A^+`, so (i) is weak chamber contraction; (ii) is the Library's
  `compressedAction_commute_of_factor` for the Iwahori factorization of `K` and the commuting pair
  `a`, `g` (both images of points of the commutative `A(F)`), each satisfying its three contraction
  conditions; (iii) is the uniform compact containment of the finite set `F` (row S22), which gives
  the threshold `ε`.
- *Whole split component.* `A(F)` is the product of the lattice points `C_A` with the compact norm
  kernel (the Library's `isUniformizerLatticeSection` and `isCompact_commonNormKernel` for split tori).
  The orbit map `k ↦ ρ(k)v` on the norm kernel is locally constant (an open subgroup fixes `v`), so
  it has finite range; taking the least threshold over this range, `x = c k` with `c ∈ C_A` and `k`
  in the kernel has `|α(c)| = |α(x)|`, and the identity for `w = ρ(k)v` at `c` gives it for `v` at
  `x`.

## Scope

- Standard parabolic subgroups only; semi-standard ones (conjugates by Weyl representatives) are
  not treated.
- The structural inputs (the basis `B` with the clauses of Renard V.5.2, the compatible split
  component, and the standard cocharacter `ζ`) are hypotheses; `SimultaneousStandardBasisAt` is a
  property of `K0`, whose existence for a special maximal compact subgroup is the Library's unproved
  `JointSpecialCompactBasisExistenceStatement`.
- The pairing is one stable pairing in the sense of the Library; its uniqueness, and its
  normalized form with an explicit modulus `δ_P` of `P_J`, are not stated here.
- Waldspurger's Proposition I.4.3 (the asymptotic identity uniformly on `M̄_0^+` with
  `P = P_{m,t}`) is not formalized here; this module supplies the pairing data, `Admits` and the
  asymptotic identity on each split component required by the Library's abstract
  `exists_uniform_asymptotics`.
