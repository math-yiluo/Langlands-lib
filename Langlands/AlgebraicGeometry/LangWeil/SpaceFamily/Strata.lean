import Langlands.AlgebraicGeometry.LangWeil.SpaceFamily.FibreCharts
import Langlands.AlgebraicGeometry.SchemeEtalePureFibreDimension
import Langlands.AlgebraicGeometry.SmoothPureDimensionProof
import Langlands.AlgebraicGeometry.SchemeLocalFiberDimension

/-!
# Degree strata of the base of a separated algebraic space with a smooth chart

Let `X` be a separated algebraic space with an affine étale chart (a `SepChart`), `g : X → M` a
morphism to a scheme and `π : U → M` a smooth map of relative dimension `d` with `a ≫ g = π`.
The maps `p_n : V_n → M` have pure fibre dimension `d`. A point `y` of `M` lies in the stratum
of degree `k` when it is in the image of `p_k` but in no image of `p_n` for `k < n` below the
tuple-length bound. When the points of the fibre of `g` over `y` are irreducible:

* the fibres of `p_k` over field points of `M` lying in the stratum of degree `k` are
  irreducible, since `e_k` is injective on their points with values in algebraically closed
  fields;
* for `n < k` the fibre over `y` of the exact-degree scheme `D_n → M` has dimension less than
  `d`: it is a closed subset with empty interior in the fibre of `p_n`, because an open subset
  of it would meet the image of the fibre of `p_k` in `X`, against the comparison of degrees.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite Topology TopologicalSpace
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.LangWeil.SpaceFamily

open Langlands.AlgebraicGeometry.AlgebraicSpace
open Langlands.AlgebraicGeometry (EtaleEquivalenceRelation)
open Langlands.AlgebraicGeometry.SchemeFiberGeometry

set_option backward.isDefEq.respectTransparency false

/-- A closed subspace with empty interior of a Noetherian space of dimension at most `d` has
dimension less than `d`: every chain of irreducible closed subsets of the subspace extends by
an irreducible component of the ambient space not contained in the subspace. -/
theorem topologicalKrullDim_lt_of_isClosedEmbedding {G F : Type*} [TopologicalSpace G]
    [TopologicalSpace F] [NoetherianSpace F] {j : G → F} (hj : IsClosedEmbedding j)
    (hint : ∀ O : Set F, IsOpen O → O ⊆ Set.range j → O = ∅) {d : ℕ}
    (hF : topologicalKrullDim F ≤ d) : topologicalKrullDim G < d := by
  rw [topologicalKrullDim, Order.krullDim_lt_coe_iff]
  intro p
  let φ := IrreducibleCloseds.map j hj.continuous
  have hφ : StrictMono φ := IrreducibleCloseds.map_strictMono_of_isInducing hj.isInducing
  let q := p.map φ hφ
  obtain ⟨Y, hY, hqY⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
    (q.last : Set F) q.last.isIrreducible
  have hsub : (q.last : Set F) ⊆ Set.range j :=
    closure_minimal (Set.image_subset_range _ _) hj.isClosed_range
  have hYj : ¬ Y ⊆ Set.range j := by
    intro h
    obtain ⟨o, ho, hne, hoY⟩ :=
      NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent Y hY
    exact hne.ne_empty (hint o ho (hoY.trans h))
  let Yc : IrreducibleCloseds F := ⟨Y, hY.1, isClosed_of_mem_irreducibleComponents Y hY⟩
  have hlt : q.last < Yc := by
    refine lt_of_le_of_ne (show (q.last : Set F) ⊆ Y from hqY) ?_
    intro h
    apply hYj
    have h' : (q.last : Set F) = Y := congrArg (fun Z : IrreducibleCloseds F => (Z : Set F)) h
    rw [← h']
    exact hsub
  have h2 := (Order.LTSeries.length_le_krullDim (q.snoc Yc hlt)).trans hF
  simp only [RelSeries.snoc_length, q, LTSeries.map_length] at h2
  have h3 : p.length + 1 ≤ d := by exact_mod_cast h2
  exact_mod_cast (h3 : p.length < d)

namespace SepChart

variable (c : SepChart.{u}) {M : Scheme.{u}}
  (g : c.X.presheaf ⟶ (schemeYoneda S0).obj (toOver M))

/-- The map `e_n` followed by `g` is the map induced by `p_n`. -/
theorem e_g (n : ℕ) : c.e n ≫ g = (schemeYoneda S0).map (overHom (c.p g n)) := by
  have h : overHom (V := c.quot n) (c.p g n) = (schemeYoneda S0).preimage (c.e n ≫ g) := by
    ext; rfl
  rw [h, Functor.map_preimage]

/-- A point of `V_n` in the next threshold maps into the image of `p_{n+1}`, and `n + 1` is
below the tuple-length bound. -/
theorem mem_range_p_of_mem_threshold {n : ℕ} {v : c.E.tupleSymmetricScheme n}
    (hv : v ∈ c.E.tupleSymmetricThresholdOpen n (n + 1)) :
    n + 1 < c.N ∧ c.p g n v ∈ Set.range (c.p g (n + 1)) := by
  obtain ⟨w, hw, rfl⟩ := hv
  have hw' : c.E.tupleDistinctProjection n 0 w ∈ c.E.tupleThresholdOpen (n + 1) := hw
  refine ⟨?_, ?_⟩
  · by_contra hN
    rw [c.E.tupleThresholdOpen_eq_bot (n + 1) (not_lt.mp hN)] at hw'
    exact hw'
  · let K := (c.E.tupleDistinctScheme n).residueField w
    let Ω := AlgebraicClosure K
    let a : Spec (CommRingCat.of Ω) ⟶ c.E.tupleDistinctScheme n :=
      Spec.map (CommRingCat.ofHom (algebraMap K Ω)) ≫
        (c.E.tupleDistinctScheme n).fromSpecResidueField w
    have ha : a (IsLocalRing.closedPoint Ω) = w :=
      (c.E.tupleDistinctScheme n).fromSpecResidueField_apply w _
    let o := a ≫ c.E.tupleDistinctProjection n 0
    have ho : o (IsLocalRing.closedPoint Ω) ∈ c.E.tupleThresholdOpen (n + 1) := by
      rw [Scheme.Hom.comp_apply, ha]
      exact hw'
    obtain ⟨b, hb⟩ := exists_tuple_of_mem_threshold (n + 1) o ho
    have hE : c.ptE (n + 1) (b ≫ c.E.tupleSymmetricMap (n + 1)) =
        c.ptE n (a ≫ c.E.tupleSymmetricMap n) := by
      rw [c.ptE_symmetricMap, c.ptE_symmetricMap, hb]
    have hM : (b ≫ c.E.tupleSymmetricMap (n + 1)) ≫ c.p g (n + 1) =
        (a ≫ c.E.tupleSymmetricMap n) ≫ c.p g n := by
      apply eq_of_map_toOverHom_eq
      rw [← ptE_g, ← ptE_g, hE]
    refine ⟨c.E.tupleSymmetricMap (n + 1) (b (IsLocalRing.closedPoint Ω)), ?_⟩
    have := congrArg (fun φ => φ (IsLocalRing.closedPoint Ω)) hM
    simp only [Scheme.Hom.comp_apply] at this
    rw [this, ha]

/-- The stratum of degree `k`: points in the image of `p_k` and in no image of `p_n` for
`k < n` below the tuple-length bound. -/
def InStratum (k : ℕ) (y : M) : Prop :=
  y ∈ Set.range (c.p g k) ∧ ∀ n, k < n → n < c.N → y ∉ Set.range (c.p g n)

variable {c g}

/-- A point of `V_k` over the stratum of degree `k` lies outside the next threshold. -/
theorem not_mem_threshold_of_inStratum {k : ℕ} {y : M} (hy : c.InStratum g k y)
    {v : c.E.tupleSymmetricScheme k} (hv : c.p g k v = y) :
    v ∉ c.E.tupleSymmetricThresholdOpen k (k + 1) := fun hmem => by
  obtain ⟨hN, hr⟩ := c.mem_range_p_of_mem_threshold g hmem
  exact hy.2 (k + 1) (Nat.lt_succ_self k) hN (hv ▸ hr)

/-- The point of the spectrum of a field. -/
theorem spec_point_eq {K : Type u} [Field K] (x : Spec (CommRingCat.of K)) :
    x = IsLocalRing.closedPoint K :=
  Subsingleton.elim _ _

/-- A point of the fibre of `p_k` over a field point maps under the first projection to a
point over the image of the field point. -/
theorem p_pullback_fst {k : ℕ} {K : Type u} [Field K] (s : Spec (CommRingCat.of K) ⟶ M)
    (z : (pullback (c.p g k) s : Scheme.{u})) :
    c.p g k (pullback.fst (c.p g k) s z) = s (IsLocalRing.closedPoint K) := by
  rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
  exact congrArg (fun x => s x) (spec_point_eq _)

/-- Two points of the fibre charts of `e_n` and `e_k` with the same image in the fibre of `g`
have the same image in `X` under `e_n` and `e_k`. -/
theorem ptE_eq_of_fibChart {n k : ℕ} {T T' : Scheme.{u}} (s : T ⟶ M)
    (ξ₁ : T' ⟶ pullback (c.p g n) s) (ξ₂ : T' ⟶ pullback (c.p g k) s)
    (h : (schemeYoneda S0).map (homOver ξ₁) ≫ fibChart g (c.e n) (c.p g n) (c.e_g g n) s =
      (schemeYoneda S0).map (homOver ξ₂) ≫ fibChart g (c.e k) (c.p g k) (c.e_g g k) s) :
    c.ptE n (ξ₁ ≫ pullback.fst _ _) = c.ptE k (ξ₂ ≫ pullback.fst _ _) := by
  have hE := congrArg (· ≫ pullback.fst g ((schemeYoneda S0).map (toOverHom s))) h
  simp only [Category.assoc] at hE
  exact (homOver_fibChart_fst g (c.e n) (c.p g n) (c.e_g g n) s ξ₁).symm.trans
    (hE.trans (homOver_fibChart_fst g (c.e k) (c.p g k) (c.e_g g k) s ξ₂))

/-- Two points of the fibre charts of `e_n` and `e_k` with the same image in the fibre of `g`
have the same image in the base of the fibre. -/
theorem snd_eq_of_fibChart {n k : ℕ} {T T' : Scheme.{u}} (s : T ⟶ M)
    (ξ₁ : T' ⟶ pullback (c.p g n) s) (ξ₂ : T' ⟶ pullback (c.p g k) s)
    (h : (schemeYoneda S0).map (homOver ξ₁) ≫ fibChart g (c.e n) (c.p g n) (c.e_g g n) s =
      (schemeYoneda S0).map (homOver ξ₂) ≫ fibChart g (c.e k) (c.p g k) (c.e_g g k) s) :
    ξ₁ ≫ pullback.snd _ _ = ξ₂ ≫ pullback.snd _ _ := by
  have hE := congrArg (· ≫ pullback.snd g ((schemeYoneda S0).map (toOverHom s))) h
  simp only [Category.assoc] at hE
  exact eq_of_map_toOverHom_eq
    ((homOver_fibChart_snd g (c.e n) (c.p g n) (c.e_g g n) s ξ₁).symm.trans
      (hE.trans (homOver_fibChart_snd g (c.e k) (c.p g k) (c.e_g g k) s ξ₂)))

/-- **Irreducible fibres on the top stratum.** If a field point `s` of `M` lies in the stratum
of degree `k` and the points of the fibre of `g` over `s` form an irreducible space, then the
fibre of `p_k` over `s` is irreducible. -/
theorem irreducibleSpace_pullback_p {k : ℕ} {K : Type u} [Field K]
    (s : Spec (CommRingCat.of K) ⟶ M) (hs : c.InStratum g k (s (IsLocalRing.closedPoint K)))
    (hirr : @IrreducibleSpace (Points (fib g s)) (pointTopology _)) :
    IrreducibleSpace (pullback (c.p g k) s : Scheme.{u}) := by
  have hb := c.e_g g k
  have hbe : IsEtale (fibChart g (c.e k) (c.p g k) hb s) :=
    fibChart_isEtale g _ _ hb (c.e_isEtale k) s
  obtain ⟨v, hv⟩ := hs.1
  obtain ⟨z₀, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := c.p g k) (g := s) v
    (IsLocalRing.closedPoint K) hv
  refine @IrreducibleSpace.mk _ _ ⟨?_⟩ ⟨z₀⟩
  rintro W₁ W₂ hW₁ hW₂ ⟨x₁, -, hx₁⟩ ⟨x₂, -, hx₂⟩
  obtain ⟨Ω, _, _, ξ₁, ξ₂, h₁, h₂, h⟩ := exists_common_point_of_isOpen g s hirr _ _ hbe hbe
    hW₁ hW₂ ⟨x₁, hx₁⟩ ⟨x₂, hx₂⟩
  have hξ : ξ₁ = ξ₂ := by
    apply pullback.hom_ext
    · refine eq_of_ptE_eq (ξ₁ ≫ pullback.fst _ _) ?_ (ξ₂ ≫ pullback.fst _ _)
        (ptE_eq_of_fibChart s ξ₁ ξ₂ h)
      rw [Scheme.Hom.comp_apply]
      exact not_mem_threshold_of_inStratum hs (p_pullback_fst s _)
    · exact snd_eq_of_fibChart s ξ₁ ξ₂ h
  exact ⟨ξ₁ (IsLocalRing.closedPoint Ω), trivial, h₁, hξ ▸ h₂⟩

/-- **Small fibres on the lower strata.** If a point `y` of `M` lies in the stratum of degree
`k`, the points of the fibre of `g` over `y` form an irreducible space, and `p_n` is
quasi-compact of pure fibre dimension `d`, then for `n < k` the fibre over `y` of the
exact-degree scheme `D_n → M` has dimension less than `d`. -/
theorem topologicalKrullDim_fiber_lt {n k : ℕ} (hnk : n < k) {y : M} (hy : c.InStratum g k y)
    (hirr : @IrreducibleSpace (Points (fib g (M.fromSpecResidueField y))) (pointTopology _))
    {d : ℕ} (hpfd : PureFibreDimensionMorphismProperty d (c.p g n)) [QuasiCompact (c.p g n)] :
    topologicalKrullDim ((c.E.tupleSymmetricDegreeι n ≫ c.p g n).fiber y) < d := by
  have : LocallyOfFiniteType (c.p g n) := hpfd.1
  let s := M.fromSpecResidueField y
  let ι := c.E.tupleSymmetricDegreeι n
  let j : pullback (ι ≫ c.p g n) s ⟶ pullback (c.p g n) s :=
    pullback.lift (pullback.fst _ _ ≫ ι) (pullback.snd _ _)
      (by rw [Category.assoc]; exact pullback.condition)
  have hj_fst : j ≫ pullback.fst _ _ = pullback.fst _ _ ≫ ι := pullback.lift_fst _ _ _
  have hj_snd : j ≫ pullback.snd _ _ = pullback.snd _ _ := pullback.lift_snd _ _ _
  have hpb : IsPullback j (pullback.fst (ι ≫ c.p g n) s) (pullback.fst (c.p g n) s) ι := by
    refine IsPullback.of_right ?_ hj_fst (IsPullback.of_hasPullback (c.p g n) s).flip
    rw [hj_snd]
    exact (IsPullback.of_hasPullback _ _).flip
  have : IsClosedImmersion j :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) hpb.flip inferInstance
  have : CompactSpace ((c.p g n).fiber y) := inferInstance
  have : IsNoetherian (pullback (c.p g n) s) := { toCompactSpace := this }
  change topologicalKrullDim (pullback (ι ≫ c.p g n) s : Scheme.{u}) < d
  apply topologicalKrullDim_lt_of_isClosedEmbedding j.isClosedEmbedding
  · intro O hO hOj
    by_contra hne
    have hbn := c.e_g g n
    have hbk := c.e_g g k
    obtain ⟨v, hv⟩ := hy.1
    obtain ⟨z₀, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := c.p g k) (g := s) v
      (IsLocalRing.closedPoint _) (by rw [hv, Scheme.fromSpecResidueField_apply])
    obtain ⟨Ω, _, _, ξ₁, ξ₂, h₁, -, h⟩ := exists_common_point_of_isOpen g s hirr
      (fibChart g (c.e n) (c.p g n) hbn s) (fibChart g (c.e k) (c.p g k) hbk s)
      (fibChart_isEtale g _ _ hbn (c.e_isEtale n) s)
      (fibChart_isEtale g _ _ hbk (c.e_isEtale k) s) hO isOpen_univ
      (Set.nonempty_iff_ne_empty.mpr hne) ⟨z₀, trivial⟩
    have hE := ptE_eq_of_fibChart s ξ₁ ξ₂ h
    have hw : (ξ₁ ≫ pullback.fst (c.p g n) s) (IsLocalRing.closedPoint Ω) ∉
        c.E.tupleSymmetricThresholdOpen n (n + 1) := by
      obtain ⟨z, hz⟩ := hOj h₁
      have h3 : (ξ₁ ≫ pullback.fst (c.p g n) s) (IsLocalRing.closedPoint Ω) =
          ι (pullback.fst (ι ≫ c.p g n) s z) := by
        have := congrArg (fun φ => φ z) hj_fst
        simp only [Scheme.Hom.comp_apply] at this
        rw [Scheme.Hom.comp_apply, ← hz]
        exact this
      rw [h3]
      exact c.E.tupleSymmetricDegreeι_not_mem_threshold n _
    exact absurd (le_of_ptE_eq _ hw _ hE) (not_le.mpr hnk)
  · rw [topologicalKrullDim_eq_iSup_irreducibleComponents]
    exact iSup_le fun Z => (hpfd.2 y Z.1 Z.2).le

/-- The symmetric quotient map followed by `p_n` is the first coordinate followed by `π`. -/
theorem symmetricMap_p (π : c.U.left ⟶ M) (ha : c.a ≫ g = (schemeYoneda S0).map (overHom π))
    (n : ℕ) :
    c.E.tupleSymmetricMap n ≫ c.p g n = c.E.tupleDistinctProjection n 0 ≫ π := by
  apply eq_of_map_toOverHom_eq
  have h := c.ptE_symmetricMap n (𝟙 _)
  rw [Category.id_comp, Category.id_comp] at h
  rw [← ptE_g, h, ptA, Category.assoc, ha, ← Functor.map_comp]
  rfl

/-- The maps `p_n` have pure fibre dimension `d` when `π` is smooth of relative dimension
`d`. -/
theorem pureFibreDimension_p (π : c.U.left ⟶ M)
    (ha : c.a ≫ g = (schemeYoneda S0).map (overHom π)) {d : ℕ}
    [hπ : SmoothOfRelativeDimension d π] (n : ℕ) :
    PureFibreDimensionMorphismProperty d (c.p g n) := by
  have : Smooth π := hπ.smooth
  have hπd : PureFibreDimensionMorphismProperty d π :=
    ⟨inferInstance, smoothPureDimension.2 _ _ π d hπ⟩
  have : Etale (c.E.tupleDistinctProjection n 0) := inferInstance
  have h := pureFibreDimension_precomp_etale d (c.E.tupleDistinctProjection n 0) π
    inferInstance hπd
  rw [← symmetricMap_p π ha n] at h
  exact pureFibreDimension_of_precomp_etale_surjective d _ _ inferInstance inferInstance h

end SepChart

end Langlands.AlgebraicGeometry.LangWeil.SpaceFamily
