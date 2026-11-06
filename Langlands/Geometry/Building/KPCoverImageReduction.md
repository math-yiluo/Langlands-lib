# KP Corollary 2.6.28 for the actual minimal-Levi zero subgroup, from its structural inputs

Worker 1512 and Worker 1532. This module is an internal conditional assembly
toward the second conjunct of
`Langlands.Geometry.Building.ZeroSubgroupDatum.MinimalLeviZeroComparisonStatement`,
namely `E.CentralizerZeroIntersectionStatement`:
`G(F)^0 ∩ Z(F)^1 = Z(F)^0` for the actual zero datum `E` of a connected
reductive `G` over a non-archimedean local field `F`, with `Z = Z_G(S)` for a
maximal split torus `S`. It follows the proof of Corollary 2.6.28 in
Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (Cambridge University
Press, 2023, registered as `kaletha-prasad-2023-bruhat-tits-new-approach`),
printed p. 106 / PDF p. 137. The first conjunct (KP Lemma 2.6.27) is
`centralizerZeroNormKernel_of_inputs` from
`Langlands.Geometry.Building.KPMinimalLeviZeroNormKernelReduction`; the last
declaration below combines both conjuncts. The module does not prove the
structural inputs listed below.

Throughout, `K = UnramifiedClosure F`, `v = fixedFieldValuation F` is the
valuation of `K`, and `M(K)^1 = characterValuationKernel v M`.

## Structural inputs

The following published Library statements have not yet been proved. They
appear as explicit hypotheses:

- `hC : CocenterQuotientExistenceStatement`
  (`Langlands.GroupScheme.Derived.CocenterQuotientStatement`),
  `hF : SplitTorusCentralizerCocenterInducedStatement`
  (`Langlands.GroupScheme.Rational.SplitTorusCentralizerCocenterStatement`) and
  `hB1 : InducedTorusIwahoriStatement`
  (`Langlands.Geometry.Building.KPInducedTorusIwahoriStatement`, KP Lemma
  2.5.18). They are used only through
  `characterValuationKernel_le_derivedRange_sup_torusNormIwahori` of module
  `Langlands.Geometry.Building.KPMinimalLeviZeroNormKernelReduction`, the
  `K`-level core of KP Lemma 2.6.27. That module describes them.
- `hPL : SplitTorusCentralizerCoverPreimageStatement`
  (`Langlands.GroupScheme.SimplyConnected.SplitTorusCentralizerCoverPreimageStatement`).
  The preimage `M'` of a split-torus centralizer `M` in a simply connected
  cover is again such a centralizer. It is connected reductive, a multiple of
  each of its characters comes from `M`, its derived subgroup lifts to the
  simply connected cover of `M_der`, and one of its maximal tori maps to a
  given maximal torus `T` of `M` and splits wherever `T` splits.
- `hsc : IsSimplyConnectedFieldExtensionStatement`
  (`Langlands.GroupScheme.SimplyConnected.FieldExtensionStatement`). Simple
  connectedness is preserved by field extension; it is used for `F → K`.

The base change from `F` to `K` of the other structure uses Library proofs:
`connectedReductiveFieldExtensionStatement`,
`derivedSubgroup_baseChange_eq_of_field` with
`IsDerivedSubgroup.baseChange_of_eq`, `IsCentralIsogeny.baseChange`,
`IsSplitTorus.baseChange`, `IsClosedSubgroup.baseChange`,
`torusCentralizer_baseChange` and `IsRepresentedBy.baseChange`. The descent of
the norm-one subgroup from `K` to `F` is `characterValuationKernelDescent_proof`
(KP 2.6.16(4) with 2.6.17).

## Declarations

### `GroupScheme.rationalCharacterEval_nsmul`

`rationalCharacterEval (n • χ) g = rationalCharacterEval χ g ^ n`, by induction
on `n`.

### `GroupScheme.exists_rationalPoint_of_range_eq_comap`

Let `j : M → G` be a monomorphism, and let `j' : M' → C`, `f : C → G` and
`p : M' → M` satisfy `j' ≫ f = p ≫ j` and
`SubgroupFunctor.range j' = (SubgroupFunctor.range j).comap f`. If
`f(c) = j(z)` for `k`-points `c ∈ C(k)` and `z ∈ M(k)`, then there is
`m ∈ M'(k)` with `j'(m) = c` and `p(m) = z`. Proof: `c` lies in the comap on
the terminal test scheme, so it lies in the range of `j'`. The equation
`p(m) = z` follows by cancelling the monomorphism `j`.

### `comap_characterValuationKernel_le_of_nsmul`

For any valuation `v` on `k` and `p : M' → M`, suppose a positive multiple
`n • χ'` of every rational character `χ'` of `M'` equals `p ≫ χ` for some
rational character `χ` of `M`. Then
`(characterValuationKernel v M).comap p ≤ characterValuationKernel v M'`.
Proof: `v(χ'(m))^n = v(χ(p m)) = 1`, and `pow_eq_one_iff_left` in the
linearly ordered value group gives `v(χ'(m)) = 1`. This is the inclusion part
of KP's "the preimage of `M_0(K)^1` in `M'_0(K)` equals `M'_0(K)^1`".

### `derivedRange_sup_torusNormIwahori_le_comap_zeroPoints`

Let `EM : UnramifiedZeroDatum F M` be data of KP Definition 2.6.23(1) for a
`K`-group `M` (maximal torus `EM.T`, splitting field `EM.L`, simply connected
derived cover `EM.π`, `EM.d`), and let `p : M' → M`. Suppose
`b ≫ EM.π ≫ EM.d = d' ≫ p` for a derived subgroup `d' : D' → M'`, and
`t' ≫ p = g ≫ EM.i` for a torus `t' : T' → M'` with `T'` affine. Then `p` maps
`D'(K) ⊔ t'(T'(K)^0)` into `EM.zeroPoints`, where `T'(K)^0` is
`torusNormIwahori K EM.L` with the valuation `intermediateValuation F EM.L`.
Proof: `p(d' y) = (EM.π ≫ EM.d)(b y)` lies in the simply connected image, which
lies in the zero points (`simplyConnectedImage_le_zeroPoints`). Also
`p(t' s) = EM.i(g s)`, and `map_torusNormIwahori_le` (KP torus norm naturality,
for the same field `EM.L`) puts `g s` in `EM.T(K)^0`. Then
`map_torusIwahori_le_zeroPoints` applies.

### `coverImage_inf_characterValuationKernel_le_zeroPoints`

This is the `K`-level cover-image containment, stated without a
`ZeroSubgroupDatum`. Assume `hC hF hB1 hPL`. Let `G` be connected reductive
over `K`, with derived subgroup `d : D → G` and a central isogeny `π : C → D`
from a simply connected `C`. Let `a : A → G` be a split subtorus, `j : M → G` a
representative of its centralizer, and `EM : UnramifiedZeroDatum F M`. Then

`(simplyConnectedImage d π).comap j ⊓ characterValuationKernel v M ≤ EM.zeroPoints`,

that is, `G(K)^♮ ∩ M(K)^1 ⊆ M(K)^0`. Proof as implemented, following KP:

1. Write `j(z) = (π ≫ d)(c)` with `c ∈ C(K)`.
2. Apply `hPL` over `K` to `G, d, π, a, j`, the cover `EM.d, EM.π` of `M_der`
   and the maximal torus `EM.i`. This gives `M' = Z_C(A')` with
   `p : M' → M`, the characters clause, `d'` and `b`, and `t'`, `g`. `T'` is
   affine because `t'` is a closed immersion into the affine `M'`.
3. `exists_rationalPoint_of_range_eq_comap` gives `m ∈ M'(K)` with
   `j'(m) = c` and `p(m) = z` (KP: "the image of `M'_0(K)` is
   `G(K)^♮ ∩ M_0(K)`").
4. `comap_characterValuationKernel_le_of_nsmul` gives `m ∈ M'(K)^1`.
5. `characterValuationKernel_le_derivedRange_sup_torusNormIwahori` applies to
   `M' ⊆ C` with `t'` and `L = EM.L`, which splits `T'` by `hPL`. It gives
   `m ∈ D'(K) ⊔ t'(T'(K)^0)`; this is KP's use of Lemma 2.6.27 for `M'_0`.
6. `derivedRange_sup_torusNormIwahori_le_comap_zeroPoints` gives
   `z = p(m) ∈ M(K)^0` (KP: "`M'_0 → M_0` maps `M'_0(K)^0` to `M_0(K)^0`").

Because `T'` maps into the given torus `EM.T` and is split by the same field
`EM.L`, KP Lemma 2.6.24 (independence of the choice of `T` and `L`) is not
needed.

### `ZeroSubgroupDatum.coverImageCentralizerNormKernel_of_inputs`

Assume `hC hF hB1 hPL hsc`. For every actual
`E : ZeroSubgroupDatum i j` this proves `E.CoverImageCentralizerNormKernelStatement`:
`E.simplyConnectedImage.comap j ⊓ rationalCommonNormKernel Z ≤ E.centralizerZero`.
Proof: base change `G`, `E.d`, `E.π`, `i` and `j` to `K`, using the Library
proofs listed above and `hsc` for `E.C`. A point
`z ∈ Z(F)` in the norm kernel extends to `z_K ∈ Z(K)^1` by
`characterValuationKernelDescent_proof`. If `j(z) = (E.π ≫ E.d)(c)`, then
`rationalExtend_map` gives `j_K(z_K) = (π_K ≫ d_K)(c_K)`. The `K`-level
containment with `EM = E.centralizerDatum` puts `z_K` in its zero points, and
`centralizerZero` and `mem_anisotropicZeroPoints` turn this into
`z ∈ E.centralizerZero`. This is KP's reduction from `k` to `K` in the proof of
Corollary 2.6.28.

### `ZeroSubgroupDatum.centralizerZeroIntersection_of_inputs`

Assume `hC hF hB1 hPL hsc`. Then `E.CentralizerZeroIntersectionStatement` holds.
It is `centralizerZeroIntersection_of_coverImage`
(`Langlands.Geometry.Building.KPCentralizerParahoricAssembly`) applied to the
previous theorem; that Library reduction supplies the normality argument from
`G(F)^♮` to `G(F)^0`.

### `ZeroSubgroupDatum.minimalLeviZeroComparison_of_inputs`

Assume `hC hF hB1 hPL hsc` and
`hG : SplitTorusCentralizerDerivedSimplyConnectedStatement`
(`Langlands.GroupScheme.SimplyConnected.SplitTorusCentralizerDerivedStatement`:
in a simply connected group, the derived subgroup of a split-torus centralizer
is simply connected; also not yet proved). Then
`E.MinimalLeviZeroComparisonStatement` holds for every actual
`E : ZeroSubgroupDatum i j`. It is the pair of
`E.centralizerZeroNormKernel_of_inputs hC hF hG hB1 hsc` (KP Lemma 2.6.27,
from `KPMinimalLeviZeroNormKernelReduction`) and
`E.centralizerZeroIntersection_of_inputs hC hF hB1 hPL hsc`. It is a
proof-valued `def` (with `linter.defProp` off) so that it can serve as a
definition-kind entry; Worker 1532 suggested it.

All declarations use only the axioms `propext`, `Classical.choice` and
`Quot.sound`.
