# Renard VII.3.5 (i): inheritance of regularity, reduced to Bruhat-order geometry

Author: Worker 102. Module
`Langlands.Representation.Intertwining.PQCompositionRegularityReduction`, namespace
`Langlands.Aubert.General.RepresentedParabolic`. Universe parameters `u` (the field) and `v`
(the representation).

This is a conditional reduction. It proves `PQCompositionRegularityStatement` (the regularity
part of clause 2 of the published `PQIntertwiningCompositionStatement`, stated on its own in
`Langlands.Representation.Intertwining.PQIntertwiningCompositionReduction`) from one new
proposition about double cosets, `PQCompositionBruhatStatement`. That proposition is not
proved here, so `PQCompositionRegularityStatement` is not yet proved unconditionally.

The recorded declaration is the definition `pqCompositionRegularityOfBruhat`, of type
`PQCompositionBruhatStatement.{u} → PQCompositionRegularityStatement.{u, v}`. It follows the
Library pattern for conditional reductions. The module also uses the helper modules
`PQRegularityPerClass` and `PieceKernelFaithful`, submitted with it.

## Notation

`G` is a connected reductive group over a nonarchimedean local field `F = k`. `P₁ = MN₁`,
`P₂ = MN₂`, `P₃ = MN₃` are parabolic subgroups with the same Levi embedding of `M`, and `P̄ⱼ`
are opposite parabolics. `a : A ⟶ M` is a split component, and `d(Pᵢ, Pⱼ)` counts the
indivisible roots of `A` in `Nᵢ ∩ N̄ⱼ`. All of this is as in `PQCompositionRegularityStatement`.
For `z ∈ G(F)`, `PᵢzPⱼ <_{PᵢPⱼ} PᵢPⱼ` is the strict Bruhat relation
`Geometric.BruhatLT (pointImage pᵢ) (pointImage pⱼ) (DoubleCoset.mk … z)
(identityParabolicDoubleCoset pᵢ pⱼ)`. That is, `PᵢzPⱼ` lies in the closure of `PᵢPⱼ` and is a
different double coset. `inn z = (G.innerIso z).hom` is conjugation by `z`.

## The new statement `PQCompositionBruhatStatement`

The binders and hypotheses are exactly those of `PQCompositionRegularityStatement`, up to and
including `d(P₁, P₂) + d(P₂, P₃) = d(P₁, P₃)` and `d(P₁, P₂) = 1`. The representation `σ` is
dropped. The conclusion is:

for every `z ∈ G(F)`, every split torus `T` with `i : T ⟶ G` a maximal split torus of `G`, and
every `ta, tb : T ⟶ M` with `ta ≫ l₁ ≫ p₁ = i` and `tb ≫ l₁ ≫ p₁ ≫ inn z = i` (so `T ⊆ M` and
`T ⊆ zMz⁻¹`):

1. if `P₂zP₃ <_{P₂P₃} P₂P₃`, then `P₁zP₃ <_{P₁P₃} P₁P₃`;
2. if `P₁zP₂ <_{P₁P₂} P₁P₂`, then
   - `P₁zP₃ <_{P₁P₃} P₁P₃`,
   - `range (l₁ ≫ p₁) ⊓ range (p₂ ≫ inn z) = range (l₁ ≫ p₁) ⊓ range (p₃ ≫ inn z)`
     (as subgroup functors of `G`; that is, `M ∩ zP₂z⁻¹ = M ∩ zP₃z⁻¹`), and
   - `range (l₁ ≫ p₁) ⊓ range (r₂ ≫ p₂ ≫ inn z) = range (l₁ ≫ p₁) ⊓ range (r₃ ≫ p₃ ≫ inn z)`
     (that is, `M ∩ zN₂z⁻¹ = M ∩ zN₃z⁻¹`).

### Correspondence with Renard

Renard, proof of VII.3.5, printed pp.237–238 / PDF pp.243–244:

- "`w̄ <_{P₂P₃} 1̄` implique que `P₂wP₃ ⊂ \overline{P₂P₃}`, donc `P₁wP₃ ⊂ … ⊂ \overline{P₁P₃}`
  … Ceci montre que `w̄ <_{P₂P₃} 1̄` implique `w̄ <_{P₁P₃} 1̄`" is item 1.
- "De même … `w̄ <_{P₁P₂} 1̄` implique `w̄ <_{P₁P₃} 1̄`" is the first part of item 2.
- "`M ∩ w·P₃ = M ∩ w·(P₃ ∩ L) = M ∩ w·(P₂ ∩ L) = M ∩ w·P₂`" for `w̄ <_{P₁P₂} 1̄` is the second
  part of item 2. Renard states only the equality of parabolics. The published intersection
  data record both `M ∩ zQz⁻¹` and its unipotent radical `M ∩ zUz⁻¹`, so the statement includes
  both equalities. (The second follows from the same argument: `L ∩ N₂ = L ∩ N₃`.)

Renard indexes double cosets by `W_M\W_G/W_M`. Here they are represented by points `z ∈ G(F)`
with `M ∩ zMz⁻¹` containing a maximal split torus of `G`. This is the form in which the
published geometric lemma (`geometricLemmaIntersectionDatumOfTorusFactors`) supplies
representatives. Renard does not prove separately that `P₁zP₃` differs from `P₁P₃`; for
Weyl-group representatives this is implicit in his indexing. The statement makes it
explicit.

Provenance: derived, a formalization of the geometric steps of Renard's proof in the
represented-double-coset setting. The proposition is not proved here.

## Transfer of intersection data

`GeometricLemmaIntersectionDatum p l r … q lQ rQ … z` is the published data of a
geometric-lemma piece at `z`: `P' = M ∩ zQz⁻¹ = M'N'`, `Q' = L ∩ z⁻¹Pz = L'U'`, the
conjugation `φ : L' ≅ M'`, its points `e`, and a maximal split torus of `G` in `M'`. The module
defines:

- `leviIsoOfSameLevi D D' hM`: for data `D` (for `(P, Q)`) and `D'` (for `(P₁, Q)`) at the
  same `z`, with `l ≫ p = l₁ ≫ p₁`, the isomorphism `D.L' ≅ D'.L'` over `G`. Both represent the
  subgroup functor `range (D.lQ' ≫ D.q' ≫ lQ ≫ q)`, by the `levi_eq'` fields and `hM`.
  `leviIsoOfSameLevi_hom_comp` records the compatibility with the embeddings.
- `withSourceOf D D' hM`: a datum for `(P₁, Q)` at `z`. It keeps the `P'`-side, `L'`, `φ`, `e`
  and the torus of `D`, and takes the `Q'`-side (`Q'`, `U'`, `q'`, `rQ'`) from `D'`, with
  `lQ' = (leviIsoOfSameLevi D D' hM).hom ≫ D'.lQ'`. The fields about `P'` hold for `P₁`
  because they only involve `l ≫ p = l₁ ≫ p₁`.
  (`IsRationalLeviSubgroup.iso_comp` and `isIso_subgroupMultiplication_iso_comp` handle the
  reparametrized Levi.)
- `withTargetOfEq D hL hpar hrad`: a datum for `(P, Q₁)` at `z` with all fields of `D`, when
  `lQ ≫ q = lQ₁ ≫ q₁`, `M ∩ zQz⁻¹ = M ∩ zQ₁z⁻¹` and `M ∩ zUz⁻¹ = M ∩ zU₁z⁻¹` (as subgroup
  functors). Only the `parabolic_eq`, `radical_eq` and `Q`-side compatibility proofs change.

The piece kernels do not change:

- `pieceSplitComponentKernel_withSourceOf`: for a split component `a`,
  `pieceSplitComponentKernel a (D.withSourceOf D' hM) σ = pieceSplitComponentKernel a D σ`.
  Proof: both equal the inner kernel `innerSplitComponentKernel b σ`
  (`pieceSplitComponentKernel_eq_inner`, from `PieceKernelFaithful`) for a factor `b : A ⟶ L'`
  of `a` (`exists_isCentralSplitTorus_factor`). The inner kernel only involves the `P'`-side
  and `e`, which the two data share. The final step is `rfl`, run with
  `maxHeartbeats 1600000`.
- `pieceSplitComponentKernel_withTargetOfEq`: the same for `withTargetOfEq`, by the same
  argument. A direct `rfl` on the piece kernels times out, so the proof goes through the inner
  kernels.

## Proof of the reduction `pqCompositionRegularity_of_bruhat`

Assume `σ` is `P₁P₃`-regular. By `isPQRegular_iff_forall_piece` (`PQRegularityPerClass`),
`I_σ ⊔ (piece kernel of D) = ⊤` for every `z` with `P₁zP₃ <_{P₁P₃} P₁P₃` and every
`(P₁, P₃)`-datum `D` at `z`. The same lemma reduces each conclusion to pieces.

- `P₂P₃`-regularity. Let `z` satisfy `P₂zP₃ <_{P₂P₃} P₂P₃`, and let `D` be a `(P₂, P₃)`-datum at
  `z`. Its torus gives `i = D.t ≫ D.l' ≫ D.p' ≫ l₂ ≫ p₂`, a maximal split torus of `G`, with
  `ta = D.t ≫ D.l' ≫ D.p'` and `tb = D.t ≫ D.φ.inv ≫ D.lQ' ≫ D.q'`. The equation for `tb` comes
  from `D.φ_comp`. Item 1 of the Bruhat statement gives `P₁zP₃ <_{P₁P₃} P₁P₃`. The published
  `geometricLemmaIntersectionDatumOfTorusFactors parabolicDynamic` builds a `(P₁, P₃)`-datum
  `D'` at `z` from the same torus. Then `D.withSourceOf D' h21` is a `(P₁, P₃)`-datum at `z`
  with the piece kernel of `D`, and `P₁P₃`-regularity gives `I_σ ⊔ (kernel of D) = ⊤`.
  (`splitComponentKernel` of `σ` does not depend on which `lⱼ` is used: the Levi topologies
  agree definitionally.)
- `P₁P₂`-regularity. Let `z` satisfy `P₁zP₂ <_{P₁P₂} P₁P₂`, and let `D` be a `(P₁, P₂)`-datum at
  `z`. The same torus and item 2 give `P₁zP₃ <_{P₁P₃} P₁P₃` and the two equalities. Then
  `D.withTargetOfEq` is a `(P₁, P₃)`-datum at `z` with the same piece kernel, and
  `P₁P₃`-regularity concludes.

`pqCompositionRegularityOfBruhat` is `pqCompositionRegularity_of_bruhat` as a definition.

## How the Bruhat statement is expected to be proved (not part of this unit)

Item 1 and the first part of item 2 have two parts. The closure inclusions come from
`P₂P₃ ⊆ P₁P₃`. This holds because `P₂ ⊆ P₁ (N̄₁ ∩ N₂)` and `N̄₁ ∩ N₂ ⊆ N₃` under the root
hypothesis (compare `RelativeRoot.dynamicUnipotent_inf_le_of_positiveRoots`). Strictness
reduces to: a point `z ∈ P₁P₃` with `T ⊆ M ∩ zMz⁻¹` lies in `M(F)`. The equalities in item 2
follow Renard's argument with the Levi `L` generated by `M` and the root groups of `±α`.

## Source

David Renard, *Représentations des groupes réductifs p-adiques*, French version dated
9 July 2026, literature ID `renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. Proposition VII.3.5,
printed p.237 / PDF p.243. The regularity part of the proof of (i) is on printed pp.237–238 /
PDF pp.243–244.
