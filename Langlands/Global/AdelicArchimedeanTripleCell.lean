import Langlands.Global.AdelicGroupLocalPoints
import Langlands.Global.AdelicGroupProduct
import Langlands.Global.InfiniteAdelicGroupProduct
import Langlands.Global.AdelicGroupNormOneFunctorial
import Langlands.GroupScheme.AffinePointClosedImmersion

/-! # Adelic identity neighborhoods from archimedean triple cells

Let `G` be an affine group scheme of finite type over a number field `F`, with three closed
subgroup schemes `iₖ : Nₖ → G`. Suppose that at every archimedean place `v`, for every identity
neighborhood `A` of `G(F_v)`, the products `a b c` with `a, b, c ∈ A` lying in the images of
`N₁(F_v)`, `N₂(F_v)`, `N₃(F_v)` form an identity neighborhood. Then
`exists_nhds_eq_ofFinite_mul_triple` gives an identity neighborhood `W` of `G(𝔸)`, compact sets
`Kₖ ⊆ Nₖ(𝔸)` and a compact `L ⊆ G(𝔸_f)` such that every `g ∈ W` is
`g = l · i₁(x₁) · i₂(x₂) · i₃(x₃)` with `l ∈ L` (included at the finite places) and `xₖ ∈ Kₖ`.
The archimedean factors are assembled from the places by `InfiniteAdelicGroupPoints.assemble`
and included with finite part one. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain Topology
open scoped CategoryTheory.MonObj

namespace Langlands.Global

open Langlands.GroupScheme AdelicGroupPoints

variable {F : Type u} [Field F] [NumberField F]

section Naturality

variable {G H : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left] [IsAffine H.X.left]
  (f : H ⟶ G)

omit [NumberField F] in
/-- The projection to an archimedean completion commutes with a homomorphism. -/
theorem atPlace_affinePointsTarget (v : InfinitePlace F) (y : InfiniteAdelicGroupPoints F H) :
    InfiniteAdelicGroupPoints.atPlace F G v
        (H.affinePointsTarget f (CommAlgCat.of F (InfiniteAdeleRing F)) y) =
      H.affinePointsTarget f (CommAlgCat.of F v.Completion)
        (InfiniteAdelicGroupPoints.atPlace F H v y) := by
  apply G.affinePointEvaluation_injective (CommAlgCat.of F v.Completion)
  funext a
  change G.affinePointEvaluation (CommAlgCat.of F v.Completion)
      (InfiniteAdelicGroupPoints.atPlace F G v (y ≫ f.hom.hom)) a =
    G.affinePointEvaluation (CommAlgCat.of F v.Completion)
      (InfiniteAdelicGroupPoints.atPlace F H v y ≫ f.hom.hom) a
  rw [InfiniteAdelicGroupPoints.atPlace_evaluation, affinePointEvaluation_postcomp,
    affinePointEvaluation_postcomp, InfiniteAdelicGroupPoints.atPlace_evaluation]

/-- The infinite part commutes with the adelic map of a homomorphism. -/
theorem infinite_map' (g : AdelicGroupPoints F H) :
    infinite F G (map F H G f g) =
      H.affinePointsTarget f (CommAlgCat.of F (InfiniteAdeleRing F)) (infinite F H g) :=
  DFunLike.congr_fun (H.affinePointsTarget_naturality f
    (CommAlgCat.ofHom (AlgHom.fst F (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)))) g

end Naturality

variable {G N₁ N₂ N₃ : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom] [IsAffine N₁.X.left] [IsAffine N₂.X.left] [IsAffine N₃.X.left]

/-- **Adelic identity neighborhoods from archimedean triple cells.** If at every archimedean
place `v` and for every identity neighborhood `A` of `G(F_v)` the products `a b c` with `a`, `b`,
`c` in `A` and in the images of `N₁(F_v)`, `N₂(F_v)`, `N₃(F_v)` form an identity neighborhood,
then some identity neighborhood `W` of `G(𝔸)` consists of products `l · i₁(x₁) · i₂(x₂) · i₃(x₃)`
with `l` in a compact subset of `G(𝔸_f)` (included at the finite places) and `xₖ` in compact
subsets of `Nₖ(𝔸)`. -/
theorem exists_nhds_eq_ofFinite_mul_triple (i₁ : N₁ ⟶ G) (i₂ : N₂ ⟶ G) (i₃ : N₃ ⟶ G)
    [IsClosedImmersion i₁.hom.hom.left] [IsClosedImmersion i₂.hom.hom.left]
    [IsClosedImmersion i₃.hom.hom.left]
    (hcell : ∀ v : InfinitePlace F, ∀ A ∈ 𝓝 (1 : InfinitePlaceGroupPoints F G v),
      {x : InfinitePlaceGroupPoints F G v |
        ∃ a ∈ A ∩ Set.range (N₁.affinePointsTarget i₁ (CommAlgCat.of F v.Completion)),
        ∃ b ∈ A ∩ Set.range (N₂.affinePointsTarget i₂ (CommAlgCat.of F v.Completion)),
        ∃ c ∈ A ∩ Set.range (N₃.affinePointsTarget i₃ (CommAlgCat.of F v.Completion)),
          x = a * b * c} ∈ 𝓝 (1 : InfinitePlaceGroupPoints F G v)) :
    ∃ W ∈ 𝓝 (1 : AdelicGroupPoints F G),
      ∃ K₁ : Set (AdelicGroupPoints F N₁), IsCompact K₁ ∧
      ∃ K₂ : Set (AdelicGroupPoints F N₂), IsCompact K₂ ∧
      ∃ K₃ : Set (AdelicGroupPoints F N₃), IsCompact K₃ ∧
      ∃ L : Set (FiniteAdelicGroupPoints F G), IsCompact L ∧
      ∀ g ∈ W, ∃ l ∈ L, ∃ x₁ ∈ K₁, ∃ x₂ ∈ K₂, ∃ x₃ ∈ K₃,
        g = ofFinite F G l * map F N₁ G i₁ x₁ * map F N₂ G i₂ x₂ * map F N₃ G i₃ x₃ := by
  classical
  have hA : ∀ v : InfinitePlace F, ∃ A : Set (InfinitePlaceGroupPoints F G v),
      IsCompact A ∧ A ∈ 𝓝 (1 : InfinitePlaceGroupPoints F G v) := by
    intro v
    have : LocallyCompactSpace (InfinitePlaceGroupPoints F G v) :=
      G.affinePointsLocallyCompactSpace (CommAlgCat.of F v.Completion)
    obtain ⟨A, hAc, hA1⟩ := exists_compact_mem_nhds (1 : InfinitePlaceGroupPoints F G v)
    exact ⟨A, hAc, hA1⟩
  choose A hAc hA1 using hA
  let Winf : Set (InfiniteAdelicGroupPoints F G) :=
    ⋂ v, InfiniteAdelicGroupPoints.atPlace F G v ⁻¹'
      {x : InfinitePlaceGroupPoints F G v |
        ∃ a ∈ A v ∩ Set.range (N₁.affinePointsTarget i₁ (CommAlgCat.of F v.Completion)),
        ∃ b ∈ A v ∩ Set.range (N₂.affinePointsTarget i₂ (CommAlgCat.of F v.Completion)),
        ∃ c ∈ A v ∩ Set.range (N₃.affinePointsTarget i₃ (CommAlgCat.of F v.Completion)),
          x = a * b * c}
  have hWinf : Winf ∈ 𝓝 (1 : InfiniteAdelicGroupPoints F G) := by
    refine Filter.iInter_mem.mpr fun v => ?_
    have hc : Continuous (InfiniteAdelicGroupPoints.atPlace F G v) :=
      (InfiniteAdelicGroupPoints.atPlace F G v).continuous
    have h1 : InfiniteAdelicGroupPoints.atPlace F G v 1 = 1 := map_one _
    exact hc.continuousAt.preimage_mem_nhds (by rw [h1]; exact hcell v (A v) (hA1 v))
  obtain ⟨L, hLc, hL1⟩ := exists_compact_mem_nhds (1 : FiniteAdelicGroupPoints F G)
  let W : Set (AdelicGroupPoints F G) := infinite F G ⁻¹' Winf ∩ finite F G ⁻¹' L
  have hci : Continuous (infinite F G) := (infinite F G).continuous
  have hcf : Continuous (finite F G) := (finite F G).continuous
  have hi1 : infinite F G 1 = 1 := map_one _
  have hf1 : finite F G 1 = 1 := map_one _
  have hW : W ∈ 𝓝 (1 : AdelicGroupPoints F G) := Filter.inter_mem
    (hci.continuousAt.preimage_mem_nhds (by rw [hi1]; exact hWinf))
    (hcf.continuousAt.preimage_mem_nhds (by rw [hf1]; exact hL1))
  -- compact sets of assembled factors
  have hK : ∀ {N : GroupScheme (Spec (CommRingCat.of F))} [IsAffine N.X.left] (i : N ⟶ G)
      [IsClosedImmersion i.hom.hom.left],
      IsCompact (ofInfinite F N '' (InfiniteAdelicGroupPoints.assemble F N ''
        Set.univ.pi fun v => N.affinePointsTarget i (CommAlgCat.of F v.Completion) ⁻¹' A v)) := by
    intro N _ i _
    refine ((isCompact_univ_pi fun v => ?_).image
      (InfiniteAdelicGroupPoints.continuous_assemble F N)).image (ofInfinite F N).continuous
    exact (isClosedEmbedding_affinePointsTarget N G (CommAlgCat.of F v.Completion)
      i).isCompact_preimage (hAc v)
  refine ⟨W, hW, _, hK i₁, _, hK i₂, _, hK i₃, L, hLc, ?_⟩
  rintro g ⟨hgi, hgf⟩
  have hcomp : ∀ v : InfinitePlace F,
      ∃ a ∈ A v ∩ Set.range (N₁.affinePointsTarget i₁ (CommAlgCat.of F v.Completion)),
        ∃ b ∈ A v ∩ Set.range (N₂.affinePointsTarget i₂ (CommAlgCat.of F v.Completion)),
        ∃ c ∈ A v ∩ Set.range (N₃.affinePointsTarget i₃ (CommAlgCat.of F v.Completion)),
          InfiniteAdelicGroupPoints.atPlace F G v (infinite F G g) = a * b * c :=
    fun v => Set.mem_iInter.mp hgi v
  choose a ha b hb c hc hx using hcomp
  choose y₁ hy₁ using fun v => (ha v).2
  choose y₂ hy₂ using fun v => (hb v).2
  choose y₃ hy₃ using fun v => (hc v).2
  refine ⟨finite F G g, hgf,
    ofInfinite F N₁ (InfiniteAdelicGroupPoints.assemble F N₁ y₁),
      ⟨_, ⟨y₁, fun v _ => ?_, rfl⟩, rfl⟩,
    ofInfinite F N₂ (InfiniteAdelicGroupPoints.assemble F N₂ y₂),
      ⟨_, ⟨y₂, fun v _ => ?_, rfl⟩, rfl⟩,
    ofInfinite F N₃ (InfiniteAdelicGroupPoints.assemble F N₃ y₃),
      ⟨_, ⟨y₃, fun v _ => ?_, rfl⟩, rfl⟩, ?_⟩
  · change N₁.affinePointsTarget i₁ _ (y₁ v) ∈ A v
    rw [hy₁]
    exact (ha v).1
  · change N₂.affinePointsTarget i₂ _ (y₂ v) ∈ A v
    rw [hy₂]
    exact (hb v).1
  · change N₃.affinePointsTarget i₃ _ (y₃ v) ∈ A v
    rw [hy₃]
    exact (hc v).1
  have hinf : infinite F G g =
      N₁.affinePointsTarget i₁ (CommAlgCat.of F (InfiniteAdeleRing F))
          (InfiniteAdelicGroupPoints.assemble F N₁ y₁) *
        N₂.affinePointsTarget i₂ (CommAlgCat.of F (InfiniteAdeleRing F))
          (InfiniteAdelicGroupPoints.assemble F N₂ y₂) *
        N₃.affinePointsTarget i₃ (CommAlgCat.of F (InfiniteAdeleRing F))
          (InfiniteAdelicGroupPoints.assemble F N₃ y₃) := by
    apply (InfiniteAdelicGroupPoints.completions F G).injective
    funext v
    rw [InfiniteAdelicGroupPoints.completions_apply, InfiniteAdelicGroupPoints.completions_apply,
      map_mul, map_mul, atPlace_affinePointsTarget, atPlace_affinePointsTarget,
      atPlace_affinePointsTarget, InfiniteAdelicGroupPoints.atPlace_assemble,
      InfiniteAdelicGroupPoints.atPlace_assemble, InfiniteAdelicGroupPoints.atPlace_assemble,
      hy₁, hy₂, hy₃]
    exact hx v
  rw [AdelicGroupPoints.map_ofInfinite, AdelicGroupPoints.map_ofInfinite, AdelicGroupPoints.map_ofInfinite, mul_assoc, mul_assoc, ← map_mul,
    ← map_mul, ← mul_assoc, ← hinf]
  conv_lhs => rw [← pair_projections F G g]
  rw [ofInfinite_eq_pair, ofFinite_eq_pair, pair_mul, one_mul, mul_one]

end Langlands.Global
