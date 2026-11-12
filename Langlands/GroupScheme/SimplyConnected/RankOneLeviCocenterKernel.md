# Kernels of cocenter maps and cocenters of subgroup intersections

Authors: Worker 183.

The module `Langlands.GroupScheme.SimplyConnected.RankOneLeviCocenterKernel` proves five
lemmas about group schemes over an arbitrary base scheme `S`. They are the abstract part of
the comparison, used in `RankOneLeviCocenterGenerationReduction`, between the kernel of the map
from the cocenter of the minimal Levi subgroup to the cocenter of a standard Levi subgroup and
the image of the cocenter of the intersection with a rank-one Levi factor. They use only the
standard axioms.

## Setting

All lemmas share the following data: homomorphisms `j : M ⟶ G`, `a : A ⟶ G`, `l : L ⟶ G`,
`e : E ⟶ L`, `aE : A ⟶ E`, `pA : E ⟶ A`, `d : D ⟶ M` and `δ : D ⟶ E`. The intended reading is
that `M` is the minimal Levi subgroup, `A` a rank-one Levi factor, `L` a standard Levi
subgroup, `E` its derived group, `aE` the inclusion of `A` into `E` with retraction `pA`, `D`
the derived group of `M`, and `δ` the inclusion of `D` into `E`. The hypotheses used are:

- `haE : aE ≫ e ≫ l = a` and `hpA : aE ≫ pA = 𝟙 A`;
- `hK`: every point `y` of `E` with `y ≫ pA = 1` maps into the range of `d ≫ j` in `G`;
- `hδ : δ ≫ e ≫ l = d ≫ j`, and `D` is perfect (`derivedSubgroup D = ⊤`);
- `j`, `a` and `e ≫ l` are monomorphisms.

`M ∩ A` is the published `subgroupIntersection j a`, with projections
`subgroupIntersectionFst` and `subgroupIntersectionSnd`.

## The lemmas

1. `retraction_inv_mul_comp_eq_one`: for a retraction `pA` of `aE` and a point `y` of `E`,
   the point `(y ≫ pA ≫ aE)⁻¹ * y` is killed by `pA`. This is a direct computation with
   `MonObj.mul_comp` and `aE ≫ pA = 𝟙`.

2. `retraction_comp_eq_mul_inv`: if `y ≫ (e ≫ l) = g ≫ j` for a point `g` of `M`, then there
   is a point `t` of `D` with `(y ≫ pA) ≫ a = (g * (t ≫ d)⁻¹) ≫ j`. Proof: apply `hK` to
   `w = (y ≫ pA ≫ aE)⁻¹ * y` (lemma 1) to get `t` with `t ≫ d ≫ j = w ≫ e ≫ l`; then
   `y ≫ pA ≫ aE = y * w⁻¹`, and pushing this identity to `G` with `haE` gives the claim.

3. `comap_range_kernelι_le_range_kernelι_intersection`: let `q : M ⟶ Q` be an fppf quotient
   with kernel the range of `d`, `dα` exhibit the derived subgroup of `M ∩ A`, and
   `qα : M ∩ A ⟶ Qα` an fppf quotient with kernel the range of `dα`. Then every point of
   `M ∩ A` whose image in `M` lies in the kernel of `q` lies in the kernel of `qα`. Proof: let
   `z` be such a point, so its `M`-coordinate is `x ≫ d` for a point `x` of `D`.
   - Comparing images in `G` and cancelling the monomorphism `e ≫ l` gives
     `x ≫ δ = z ≫ snd ≫ aE`, hence `x ≫ δ ≫ pA = z ≫ snd`.
   - Lemma 2 shows that the range of `δ ≫ pA ≫ a` lies in the range of `j`, so
     `IsRepresentedBy.factorHom` gives `f1 : D ⟶ M` with `f1 ≫ j = δ ≫ pA ≫ a`. Then
     `ψ = pullback.lift f1 (δ ≫ pA) : D ⟶ M ∩ A` is a homomorphism.
   - `x ≫ ψ = z`, checked on both projections of the pullback
     (`subgroupIntersection_isPullback`, cancelling `j` on the first one).
   - `D` is perfect, so `mem_derivedSubgroup_comp ψ` puts `x ≫ ψ` in the derived subgroup of
     `M ∩ A`, which is the kernel of `qα`.

4. `mono_of_cocenter_square`: under the hypotheses of lemma 3, if `IsDerivedSubgroup d`, `qα`
   is quasi-compact and `φ : Qα ⟶ Q` satisfies `subgroupIntersectionFst j a ≫ q = qα ≫ φ`,
   then `φ` is a monomorphism. Proof: the published `quotientSubgroupHom_unique` identifies `φ`
   with `SubgroupFunctor.quotientSubgroupHom`. The kernel inclusion in one direction holds
   because derived subgroups map to derived subgroups (`mem_derivedSubgroup_comp`). Lemma 3 is
   the inclusion in the other direction. `quotientSubgroupHom_mono` then applies.

5. `mem_range_of_comp_eq_one`: let `q` be as in lemma 3 and quasi-compact, `qα` and a
   monomorphism `φ` with `fst ≫ q = qα ≫ φ`, `jL : M ⟶ L` with `jL ≫ l = j`, `r : L ⟶ R` with
   kernel the range of `e`, and `π : Q ⟶ R` with `q ≫ π = jL ≫ r`. Then every point `x` of `Q`
   with `x ≫ π = 1`, on any test scheme `T`, lies in the range of `φ`. Proof: the published
   `mem_range_of_local_quotient_lift` (fpqc descent of membership in the range of a
   monomorphism) reduces to the case where `b ≫ x = g ≫ q` for a point `g` of `M` on an fpqc
   cover `b`.
   - Then `g ≫ jL ≫ r = 1`, so `g ≫ jL = y ≫ e` for a point `y` of `E`.
   - Lemma 2 gives `t` with `(y ≫ pA) ≫ a = (g * (t ≫ d)⁻¹) ≫ j`. So
     `g * (t ≫ d)⁻¹` and `y ≫ pA` define a point `z` of `M ∩ A`.
   - Since `t ≫ d ≫ q = 1`, we get `z ≫ qα ≫ φ = (g * (t ≫ d)⁻¹) ≫ q = g ≫ q = b ≫ x`.

## Relation to the literature

These lemmas formalize the relative half of the computation `M/[M,M] ≅ ∏ T_Θ` in the proof of
Theorem A of Prasad–Raghunathan, *On the Kneser–Tits problem* (1985), printed p.110,
registered as `prasad-raghunathan-1985-kneser-tits`. The derived group of the Levi subgroup of
`α` is the product of the rank-one factor and a complement contained in `[M, M]`, so the part
of `M/[M,M]` coming from that derived group is the image of `(M ∩ A)/[M ∩ A, M ∩ A]`. The
argument through the retraction and fpqc descent is internal to this formalization.
