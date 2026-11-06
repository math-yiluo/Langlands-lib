import Langlands.GroupScheme.HomScheme.ChartCoverTransport

/-! # Extension of chart covers along open immersions of bases -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.GroupScheme.TorusSubgroupModuli

variable {S S' : Scheme.{u}} {G : GroupScheme S}

/-- `familyHom_pushFamily` for a test object over `S` given with an explicit factorization
of its structure morphism through `S'`. -/
theorem familyHom_pushFamily_homMk (f : S' ⟶ S) {U : Over S'} {K : GroupScheme U.left}
    (j : K ⟶ (baseChange U.hom).obj ((baseChange f).obj G)) {T : Over S}
    (t : T.left ⟶ S') (h : t ≫ f = T.hom) (c : T.left ⟶ U.left) (hc : c ≫ U.hom = t) :
    familyHom (pushFamily f j)
        (Over.homMk c (by rw [← h, ← hc]; simp) : T ⟶ (Over.map f).obj U) =
      familyHom j (Over.homMk c hc : Over.mk t ⟶ U) ≫
        (Descent.pullbackComparison f t T.hom h G).hom := by
  revert t c h hc
  obtain ⟨X, ⟨⟨⟩⟩, r⟩ := T
  intro (t : X ⟶ S') h (c : X ⟶ U.left) hc
  subst hc
  change (c ≫ U.hom) ≫ f = r at h
  subst h
  exact familyHom_pushFamily f j (Over.homMk c rfl : Over.mk (c ≫ U.hom) ⟶ U)

/-- Evaluations of a pushed family along an explicit factorization agree exactly when the
corresponding evaluations over the changed base agree. -/
theorem evaluate_pushFamily_homMk_iff (f : S' ⟶ S) {U V : Over S'} {K : GroupScheme U.left}
    {L : GroupScheme V.left} (j : K ⟶ (baseChange U.hom).obj ((baseChange f).obj G))
    (i : L ⟶ (baseChange V.hom).obj ((baseChange f).obj G)) {T : Over S}
    (t : T.left ⟶ S') (h : t ≫ f = T.hom) (c : T.left ⟶ U.left) (hc : c ≫ U.hom = t)
    (d : T.left ⟶ V.left) (hd : d ≫ V.hom = t) :
    evaluate (pushFamily f j)
        (Over.homMk c (by rw [← h, ← hc]; simp) : T ⟶ (Over.map f).obj U) =
      evaluate (pushFamily f i)
        (Over.homMk d (by rw [← h, ← hd]; simp) : T ⟶ (Over.map f).obj V) ↔
    evaluate j (Over.homMk c hc : Over.mk t ⟶ U) =
      evaluate i (Over.homMk d hd : Over.mk t ⟶ V) := by
  rw [evaluate, evaluate, familyHom_pushFamily_homMk f j t h c hc,
    familyHom_pushFamily_homMk f i t h d hd]
  exact range_postcomp_eq_iff (Descent.pullbackComparison f t T.hom h G) _ _

/-- Pushing a family along a monomorphism of bases preserves injectivity of evaluation. -/
theorem pushFamily_injective (f : S' ⟶ S) [Mono f] {U : Over S'} {K : GroupScheme U.left}
    (j : K ⟶ (baseChange U.hom).obj ((baseChange f).obj G))
    (hj : ∀ (T : Over S') (a b : T ⟶ U), evaluate j a = evaluate j b → a = b)
    (T : Over S) (a b : T ⟶ (Over.map f).obj U)
    (h : evaluate (pushFamily f j) a = evaluate (pushFamily f j) b) : a = b := by
  have ht : (a.left ≫ U.hom) ≫ f = T.hom := (Category.assoc _ _ _).trans (Over.w a)
  have hb : b.left ≫ U.hom = a.left ≫ U.hom := by
    rw [← cancel_mono f, Category.assoc, Category.assoc]
    exact (Over.w b).trans (Over.w a).symm
  have key := (evaluate_pushFamily_homMk_iff f j j (a.left ≫ U.hom) ht
    a.left rfl b.left hb).mp h
  exact Over.OverMorphism.ext (congrArg (fun x => x.left) (hj _ _ _ key))

/-- The open locus of a family pushed along an open immersion of bases. -/
theorem pushFamily_isOpen (f : S' ⟶ S) [IsOpenImmersion f] {U : Over S'}
    {K : GroupScheme U.left} (j : K ⟶ (baseChange U.hom).obj ((baseChange f).obj G))
    (hj : IsOpenChart j) (T : Over S) (L : GroupScheme T.left)
    (i : L ⟶ (baseChange T.hom).obj G) (hi : IsClosedSubgroup i)
    (hL : RelativeTorus.IsTorus L) :
    ∃ V : T.left.Opens, ∀ (T' : Over S) (b : T' ⟶ T),
      (∃ a : T' ⟶ (Over.map f).obj U, evaluate (pushFamily f j) a = evaluate i b) ↔
        Set.range b.left.base ⊆ V := by
  -- The part of `T` lying over the open subscheme `S'`.
  let ι : pullback f T.hom ⟶ T.left := pullback.snd f T.hom
  let t : pullback f T.hom ⟶ S' := pullback.fst f T.hom
  let ιW : Over.mk (t ≫ f) ⟶ T := Over.homMk ι pullback.condition.symm
  let i₀ : (baseChange ιW.left).obj L ⟶ (baseChange (Over.mk t).hom).obj ((baseChange f).obj G) :=
    familyHom i ιW ≫ (Descent.pullbackComparison f t (t ≫ f) rfl G).inv
  have hi₀ : IsClosedSubgroup i₀ := by
    have hc := isClosedSubgroup_familyHom (S := S) (G := G) (M := T) (T := Over.mk (t ≫ f))
      (K := L) i hi ιW
    let : IsClosedImmersion (familyHom (S := S) (G := G) (M := T) (T := Over.mk (t ≫ f))
      (K := L) i ιW).hom.hom.left := hc
    change IsClosedImmersion ((familyHom (S := S) (G := G) (M := T) (T := Over.mk (t ≫ f))
      (K := L) i ιW).hom.hom.left ≫
        (Descent.pullbackComparison f t (t ≫ f) rfl G).inv.hom.hom.left)
    infer_instance
  have hpush : pushFamily (S := S) (S' := S') (G := G) (U := Over.mk t)
      (K := (baseChange ιW.left).obj L) f i₀ = familyHom i ιW := by
    simp only [pushFamily, i₀, Category.assoc]
    change familyHom i ιW ≫ (Descent.pullbackComparison f t (t ≫ f) rfl G).inv ≫
      (Descent.pullbackComparison f t (t ≫ f) rfl G).hom = _
    rw [Iso.inv_hom_id, Category.comp_id]
  obtain ⟨V', hV'⟩ := hj.isOpen (Over.mk t) _ i₀ hi₀ (hL.baseChange ιW.left)
  refine ⟨ι ''ᵁ V', fun T' b => ?_⟩
  -- The comparison for a test morphism factoring through the part of `T` over `S'`.
  have core : ∀ (c : T'.left ⟶ pullback f T.hom) (hcb : c ≫ ι = b.left)
      (d : T'.left ⟶ U.left) (hd : d ≫ U.hom = c ≫ t),
      evaluate (pushFamily f j)
          (Over.homMk d (by
            rw [Over.map_obj_hom, ← Category.assoc, hd, Category.assoc, pullback.condition,
              ← Category.assoc, hcb]
            exact Over.w b) : T' ⟶ (Over.map f).obj U) = evaluate i b ↔
        evaluate j (Over.homMk d hd : Over.mk (c ≫ t) ⟶ U) =
          evaluate i₀ (Over.homMk c rfl : Over.mk (c ≫ t) ⟶ Over.mk t) := by
    intro c hcb d hd
    have h₂ : (c ≫ t) ≫ f = T'.hom := by
      rw [Category.assoc, pullback.condition, ← Category.assoc, hcb]
      exact Over.w b
    have hb : evaluate i b = evaluate
        (pushFamily (U := Over.mk t) (K := (baseChange ιW.left).obj L) f i₀)
        (Over.homMk c (by rw [← h₂]; simp) : T' ⟶ (Over.map f).obj (Over.mk t)) := by
      rw [hpush, evaluate_comp]
      congr 1
      exact Over.OverMorphism.ext hcb.symm
    rw [hb]
    exact evaluate_pushFamily_homMk_iff (V := Over.mk t) (L := (baseChange ιW.left).obj L)
      f j i₀ (c ≫ t) h₂ d hd c rfl
  constructor
  · rintro ⟨a, ha⟩
    have hab : (a.left ≫ U.hom) ≫ f = b.left ≫ T.hom :=
      ((Category.assoc _ _ _).trans (Over.w a)).trans (Over.w b).symm
    let c : T'.left ⟶ pullback f T.hom := pullback.lift (a.left ≫ U.hom) b.left hab
    have hcb : c ≫ ι = b.left := pullback.lift_snd _ _ _
    have hd : a.left ≫ U.hom = c ≫ t := (pullback.lift_fst _ _ _).symm
    have hc := (hV' (Over.mk (c ≫ t)) (Over.homMk c rfl)).mp
      ⟨Over.homMk a.left hd, (core c hcb a.left hd).mp ha⟩
    rw [← hcb, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Hom.coe_image]
    exact Set.image_mono hc
  · intro hsub
    have hr : Set.range b.left.base ⊆ Set.range ι.base := by
      refine hsub.trans ?_
      rw [Scheme.Hom.coe_image]
      exact Set.image_subset_range _ _
    let c : T'.left ⟶ pullback f T.hom := IsOpenImmersion.lift ι b.left hr
    have hcb : c ≫ ι = b.left := IsOpenImmersion.lift_fac _ _ _
    have hc : Set.range (Over.homMk c rfl : Over.mk (c ≫ t) ⟶ Over.mk t).left.base ⊆ V' := by
      rintro _ ⟨y, rfl⟩
      have hy : b.left.base y ∈ ((ι ''ᵁ V' : T.left.Opens) : Set T.left) := hsub ⟨y, rfl⟩
      rw [Scheme.Hom.coe_image] at hy
      obtain ⟨v, hv, hvy⟩ := hy
      have hcy : ι.base (c.base y) = b.left.base y := by
        rw [← hcb, Scheme.Hom.comp_base, TopCat.comp_app]
      rw [← hcy] at hvy
      change c.base y ∈ V'
      rwa [← ι.isOpenEmbedding.injective hvy]
    obtain ⟨a', ha'⟩ := (hV' (Over.mk (c ≫ t)) (Over.homMk c rfl)).mpr hc
    exact ⟨_, (core c hcb a'.left (Over.w a')).mpr ha'⟩

/-- Pushing an open chart along an open immersion of bases gives an open chart. -/
theorem isOpenChart_pushFamily (f : S' ⟶ S) [IsOpenImmersion f] {U : Over S'}
    {K : GroupScheme U.left} (j : K ⟶ (baseChange U.hom).obj ((baseChange f).obj G))
    (hj : IsOpenChart j) :
    IsOpenChart (S := S) (G := G) (U := (Over.map f).obj U) (K := K) (pushFamily f j) where
  isClosedSubgroup := isClosedSubgroup_pushFamily f j hj.isClosedSubgroup
  isTorus := hj.isTorus
  smooth := by
    let : Smooth U.hom := hj.smooth
    change Smooth (U.hom ≫ f)
    infer_instance
  injective := pushFamily_injective f j hj.injective
  isOpen := pushFamily_isOpen f j hj

/-- Field points of `S` factoring through `S'` are covered by the pushed families. -/
theorem exists_evaluate_pushFamily (f : S' ⟶ S) {I : Type u} {U : I → Over S'}
    {K : ∀ k, GroupScheme (U k).left}
    (j : ∀ k, K k ⟶ (baseChange (U k).hom).obj ((baseChange f).obj G))
    (hc : CoversFieldPoints j) (F : Type u) [Field F]
    (x' : Spec (CommRingCat.of F) ⟶ S') (x : Spec (CommRingCat.of F) ⟶ S) (hx : x' ≫ f = x)
    (L : GroupScheme (Spec (CommRingCat.of F)))
    (i : L ⟶ (baseChange (Over.mk x).hom).obj G) (hi : IsClosedSubgroup i)
    (hL : RelativeTorus.IsTorus L) :
    ∃ (k : I) (a : Over.mk x ⟶ (Over.map f).obj (U k)),
      evaluate (pushFamily f (j k)) a = SubgroupFunctor.range i := by
  subst hx
  let i' : L ⟶ (baseChange (Over.mk x').hom).obj ((baseChange f).obj G) :=
    i ≫ (Descent.pullbackComparison f x' (x' ≫ f) rfl G).inv
  have hi' : IsClosedSubgroup i' := by
    let : IsClosedImmersion i.hom.hom.left := hi
    change IsClosedImmersion (i.hom.hom.left ≫
      (Descent.pullbackComparison f x' (x' ≫ f) rfl G).inv.hom.hom.left)
    infer_instance
  obtain ⟨k, a', ha'⟩ := hc F x' L i' hi' hL
  refine ⟨k, (Over.map f).map a', ?_⟩
  have h := range_postcomp_congr (familyHom (j k) a') i'
    (Descent.pullbackComparison f x' (x' ≫ f) rfl G).hom ha'
  have h' : SubgroupFunctor.range (familyHom (j k) a' ≫
      (Descent.pullbackComparison f x' (x' ≫ f) rfl G).hom) = SubgroupFunctor.range i := by
    simpa only [i', Category.assoc, Iso.inv_hom_id, Category.comp_id] using h
  rw [evaluate, familyHom_pushFamily f (j k) a']
  exact h'

/-- A chart cover exists as soon as one exists over each member of a family of open
subschemes covering the base. -/
theorem hasChartCover_of_openCover {J : Type u} {S' : J → Scheme.{u}} (p : ∀ l, S' l ⟶ S)
    [∀ l, IsOpenImmersion (p l)] (hp : ∀ s : S, ∃ l, s ∈ Set.range (p l).base)
    (h : ∀ l, HasChartCover ((baseChange (p l)).obj G)) : HasChartCover G := by
  choose I U K j hj hc using h
  refine ⟨Σ l, I l, fun k => (Over.map (p k.1)).obj (U k.1 k.2), fun k => K k.1 k.2,
    fun k => pushFamily (p k.1) (j k.1 k.2),
    fun k => isOpenChart_pushFamily (p k.1) (j k.1 k.2) (hj k.1 k.2), ?_⟩
  intro F _ x L i hi hL
  obtain ⟨l, hl⟩ := hp (x.base default)
  have hr : Set.range x.base ⊆ Set.range (p l).base := by
    rintro _ ⟨y, rfl⟩
    rwa [Subsingleton.elim y default]
  obtain ⟨k, a, ha⟩ := exists_evaluate_pushFamily (p l) (j l) (hc l) F
    (IsOpenImmersion.lift (p l) x hr) x (IsOpenImmersion.lift_fac _ _ _) L i hi hL
  exact ⟨⟨l, k⟩, a, ha⟩

end Langlands.GroupScheme.TorusSubgroupModuli
