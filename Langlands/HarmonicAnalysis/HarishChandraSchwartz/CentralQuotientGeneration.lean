import Langlands.HarmonicAnalysis.HarishChandraSchwartz.CentralFourierInversion
import Langlands.Representation.Plancherel.RationalNormKernelCentralCover
import Langlands.Representation.Plancherel.RationalImageLattice
import Langlands.Representation.Plancherel.RationalCharacterTopology
import Langlands.AlgebraicGeometry.PointTopology.RationalPointGroups
import Langlands.AlgebraicGeometry.PointTopology.RepresentedSubgroup
import Langlands.GroupScheme.Rational.Characters

/-! # Finite generation of `A / (A ∩ K)` for central subgroups of `G(F)`

`CentralFourierInversion` assumes `HasFGCompactOpenQuotients A`: for every compact open
subgroup `K` of `G`, `A / (A ∩ K)` is finitely generated. This module proves that hypothesis

* for a central subgroup `A` containing a compact subgroup `A¹` with `A = ⟨s₀⟩ A¹`, `s₀` finite;
* for a central subgroup `A` and a homomorphism `v` with `A ∩ ker v` compact and `v(A)` finitely
  generated;
* for every closed central subgroup `A` of the rational points `G(F)` of a connected reductive
  group over a nonarchimedean local field, with `v` the valuation of the rational characters
  (Waldspurger I.1: `G¹ = ⋂_χ Ker |χ|_F` is its kernel, and `A ∩ G¹` is compact);
* in particular for Waldspurger's `A_G`, the image of the rational points of a split component.
-/

noncomputable section

open scoped Pointwise CategoryTheory.MonObj

namespace Langlands.HarishChandraSchwartz

universe u w

section Generic

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- **`A / (A ∩ K)` is finitely generated** for every compact open `K`, when `A` is central and
contains a compact subgroup `A¹` such that `A = ⟨s₀⟩ A¹` for a finite set `s₀`: finitely many
translates `c K`, `c ∈ A¹`, cover `A¹`, and `⟨s₀ ∪ {c}⟩ (A ∩ K) = A`. -/
theorem hasFGCompactOpenQuotients_of_isCompact {A A₁ : Subgroup G}
    (hAc : A ≤ Subgroup.center G) (hA₁ : A₁ ≤ A) (hc : IsCompact (A₁ : Set G))
    {s₀ : Set A} (hs₀ : s₀.Finite)
    (hgen : Subgroup.closure s₀ ⊔ A₁.subgroupOf A = ⊤) :
    HasFGCompactOpenQuotients A := by
  intro K
  have hcomm : ∀ a b : A, a * b = b * a := fun a b =>
    Subtype.ext (Subgroup.mem_center_iff.mp (hAc b.2) a)
  have : (A₁.subgroupOf A).Normal := ⟨fun n hn g => by rwa [hcomm g n, mul_inv_cancel_right]⟩
  have hcover : (A₁ : Set G) ⊆ ⋃ c ∈ (A₁ : Set G), c • (K.toSubgroup : Set G) := fun x hx =>
    Set.mem_biUnion hx (Set.mem_smul_set.mpr ⟨1, K.toSubgroup.one_mem, mul_one x⟩)
  obtain ⟨t, htA₁, ht, htcover⟩ := hc.elim_finite_subcover_image
    (fun c _ => K.1.isOpen.smul c) hcover
  refine ⟨s₀ ∪ Subtype.val ⁻¹' t, hs₀.union (ht.preimage Subtype.val_injective.injOn), ?_⟩
  rw [eq_top_iff]
  rintro a -
  have ha : a ∈ Subgroup.closure s₀ ⊔ A₁.subgroupOf A := by rw [hgen]; exact Subgroup.mem_top a
  obtain ⟨w, hw, b, hb, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp ha
  have hbA₁ : (b : G) ∈ A₁ := hb
  obtain ⟨c, hct, hbc⟩ := Set.mem_iUnion₂.mp (htcover hbA₁)
  obtain ⟨k, hk, hck⟩ := Set.mem_smul_set.mp hbc
  let c' : A := ⟨c, hA₁ (htA₁ hct)⟩
  have hc' : c' ∈ Subgroup.closure (s₀ ∪ Subtype.val ⁻¹' t) :=
    Subgroup.subset_closure (Or.inr hct)
  have hw' : w ∈ Subgroup.closure (s₀ ∪ Subtype.val ⁻¹' t) :=
    Subgroup.closure_mono Set.subset_union_left hw
  have hkA : c'⁻¹ * b ∈ K.toSubgroup.subgroupOf A := by
    change ((c'⁻¹ * b : A) : G) ∈ K.toSubgroup
    rw [Subgroup.coe_mul, Subgroup.coe_inv]
    change c⁻¹ * (b : G) ∈ K.toSubgroup
    rw [← hck, smul_eq_mul, inv_mul_cancel_left]
    exact hk
  have : w * b = (w * c') * (c'⁻¹ * b) := by group
  rw [this]
  exact Subgroup.mul_mem_sup (mul_mem hw' hc') hkA

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- For a homomorphism `v` and a finite generating set of `v(A)`, chosen preimages `s₀ ⊆ A`
satisfy `A = ⟨s₀⟩ (A ∩ ker v)`. -/
theorem exists_closure_sup_ker_eq_top {M : Type w} [Group M] (A : Subgroup G) (v : G →* M)
    (hfg : (A.map v).FG) :
    ∃ s₀ : Set A, s₀.Finite ∧ Subgroup.closure s₀ ⊔ (A ⊓ v.ker).subgroupOf A = ⊤ := by
  obtain ⟨S, hS, hSfin⟩ := (Subgroup.fg_iff _).mp hfg
  have hpre : ∀ y : S, ∃ a : A, v a = y := fun y => by
    have hy : (y : M) ∈ A.map v := hS ▸ Subgroup.subset_closure y.2
    obtain ⟨a, ha, hav⟩ := Subgroup.mem_map.mp hy
    exact ⟨⟨a, ha⟩, hav⟩
  choose f hf using hpre
  have : Finite S := hSfin.to_subtype
  refine ⟨Set.range f, Set.finite_range f, ?_⟩
  rw [eq_top_iff]
  rintro a -
  let vA : A →* M := v.comp A.subtype
  have himage : vA '' Set.range f = S := by
    ext y
    constructor
    · rintro ⟨_, ⟨z, rfl⟩, rfl⟩
      change v (f z : G) ∈ S
      rw [hf z]
      exact z.2
    · intro hy
      exact ⟨f ⟨y, hy⟩, ⟨⟨y, hy⟩, rfl⟩, hf ⟨y, hy⟩⟩
  have hva : vA a ∈ (Subgroup.closure (Set.range f)).map vA := by
    rw [MonoidHom.map_closure, himage, hS]
    exact Subgroup.mem_map_of_mem v a.2
  obtain ⟨w, hw, hwa⟩ := Subgroup.mem_map.mp hva
  have hker : w⁻¹ * a ∈ (A ⊓ v.ker).subgroupOf A := by
    refine ⟨(w⁻¹ * a).2, ?_⟩
    change v ((w⁻¹ * a : A) : G) = 1
    rw [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]
    change (vA w)⁻¹ * vA a = 1
    rw [hwa, inv_mul_cancel]
  have : a = w * (w⁻¹ * a) := by group
  rw [this]
  exact Subgroup.mul_mem_sup hw hker

/-- **`A / (A ∩ K)` is finitely generated** for every compact open `K`, when `A` is central and
there is a homomorphism `v` with `A ∩ ker v` compact and `v(A)` finitely generated. -/
theorem hasFGCompactOpenQuotients_of_map_fg {M : Type w} [Group M] {A : Subgroup G}
    (hAc : A ≤ Subgroup.center G) (v : G →* M) (hc : IsCompact ((A ⊓ v.ker : Subgroup G) : Set G))
    (hfg : (A.map v).FG) : HasFGCompactOpenQuotients A := by
  obtain ⟨s₀, hs₀, hgen⟩ := exists_closure_sup_ker_eq_top A v hfg
  exact hasFGCompactOpenQuotients_of_isCompact hAc inf_le_left hc hs₀ hgen


end Generic

/-- A subgroup `H ≤ I` of a commutative group is finitely generated when `I` is a Noetherian
`ℤ`-module (for instance a finitely generated abelian group). -/
theorem fg_of_le_of_isNoetherian {M : Type w} [CommGroup M] {H I : Subgroup M} (hHI : H ≤ I)
    [IsNoetherian ℤ (Additive I)] : H.FG := by
  have hP : (AddSubgroup.toIntSubmodule (Subgroup.toAddSubgroup (H.subgroupOf I))).FG :=
    IsNoetherian.noetherian _
  have h1 : (H.subgroupOf I).FG := by
    rw [Subgroup.fg_iff_add_fg]
    have := (Submodule.fg_iff_addSubgroup_fg _).mp hP
    simpa using this
  obtain ⟨T, hT, hTfin⟩ := (Subgroup.fg_iff _).mp h1
  refine (Subgroup.fg_iff _).mpr ⟨I.subtype '' T, ?_, hTfin.image _⟩
  rw [← MonoidHom.map_closure, hT, Subgroup.subgroupOf_map_subtype, inf_of_le_left hHI]

section Rational

open _root_.CategoryTheory _root_.AlgebraicGeometry Langlands.GroupScheme
  Langlands.AlgebraicGeometry.PointTopology Langlands.Plancherel

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] (G : GroupScheme (Spec (CommRingCat.of F)))

/-- Waldspurger's `A¹ = A ∩ G¹` (I.1, `G¹ = ⋂_{χ ∈ Rat(G)} Ker |χ|_F`) for a subgroup `A` of
the rational points: the intersection of `A` with the actual common norm kernel. -/
def rationalNormKernelPart (A : Subgroup (rationalPoints G)) : Subgroup (rationalPoints G) :=
  A ⊓ rationalCommonNormKernel G

/-- **`A ∩ G¹` is compact** for every closed central subgroup `A` of `G(F)`: it is a closed
subset of `G¹ ∩ Z(G(F))`, which is compact (`isCompact_rationalCommonNormKernel_inf_center`). -/
theorem isCompact_rationalNormKernelPart (hG : IsConnectedReductive G)
    (A : Subgroup (rationalPoints G)) :
    haveI := hG.isAffineHom
    letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
    A ≤ Subgroup.center (rationalPoints G) → IsClosed (A : Set (rationalPoints G)) →
      IsCompact (rationalNormKernelPart G A : Set (rationalPoints G)) := by
  have := hG.isAffineHom
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  intro hAc hA
  refine (isCompact_rationalCommonNormKernel_inf_center G hG).of_isClosed_subset
    (hA.inter (isClosed_rationalCommonNormKernel G)) ?_
  rintro x ⟨hxA, hxK⟩
  exact ⟨hxK, hAc hxA⟩

/-- **`A / (A ∩ K)` is finitely generated** for every closed central subgroup `A` of the
rational points `G(F)` of a connected reductive group over a nonarchimedean local field and
every compact open subgroup `K`, in the canonical topology of `G(F)`. -/
theorem hasFGCompactOpenQuotients_rationalPoints (hG : IsConnectedReductive G)
    (A : Subgroup (rationalPoints G)) :
    haveI := hG.isAffineHom
    letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
    A ≤ Subgroup.center (rationalPoints G) → IsClosed (A : Set (rationalPoints G)) →
      HasFGCompactOpenQuotients A := by
  have := hG.isAffineHom
  have := hG.smooth
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  let : IsTopologicalGroup (rationalPoints G) := rationalPoint_isTopologicalGroup F G
  intro hAc hA
  refine hasFGCompactOpenQuotients_of_map_fg hAc (rationalCharacterValuation G) ?_ ?_
  · rw [rationalCharacterValuation_ker]
    exact isCompact_rationalNormKernelPart G hG A hAc hA
  · have hfin : Module.Finite ℤ (Additive (rationalCharacterValuationImage G)) :=
      (rationalReductiveImage_free_finite G hG).2
    have : IsNoetherian ℤ (Additive (rationalCharacterValuationImage G)) :=
      isNoetherian_of_isNoetherianRing_of_finite ℤ _
    refine fg_of_le_of_isNoetherian (I := rationalCharacterValuationImage G) ?_
    rintro y ⟨g, -, rfl⟩
    exact ⟨g, rfl⟩

/-- **Waldspurger's `A_G`**: for a split component `i : A ⟶ G` (`IsSplitComponent`, the
Library's form of Waldspurger's `A_G`), the image `A_G(F)` of `A(F)` in `G(F)` satisfies
`HasFGCompactOpenQuotients`: it is central (`IsCentralSplitTorus.range_le_center`) and closed
(the image of a closed immersion, `isClosedEmbedding_rationalPointMap`). -/
theorem hasFGCompactOpenQuotients_splitComponent (hG : IsConnectedReductive G)
    {A : CommGroupScheme (Spec (CommRingCat.of F))} (i : A.toGrp ⟶ G) (hi : IsSplitComponent i) :
    haveI := hG.isAffineHom
    letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
    HasFGCompactOpenQuotients (rationalPoints.map i).range := by
  have := hG.isAffineHom
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  have : IsClosedImmersion i.hom.hom.left := hi.isCentralSplitTorus.isSplitSubtorus.2
  have : IsAffine A.toGrp.X.left := isAffine_of_isAffineHom i.hom.hom.left
  have : T2Space F := BruhatTits.localField_t2Space F
  refine hasFGCompactOpenQuotients_rationalPoints G hG _ hi.isCentralSplitTorus.range_le_center ?_
  let : TopologicalSpace (RationalPoint F A.toGrp.X) := rationalPointTopology F A.toGrp.X
  have hce : Topology.IsClosedEmbedding (fun p : RationalPoint F A.toGrp.X => p ≫ i.hom.hom) :=
    isClosedEmbedding_rationalPointMap F i.hom.hom
  rw [MonoidHom.coe_range]
  exact hce.isClosed_range

end Rational

end Langlands.HarishChandraSchwartz
