import Langlands.GroupScheme.HomScheme.TorusSubgroupChartAffineTests
import Langlands.GroupScheme.HomScheme.AdmissiblePresheaf
import Langlands.GroupScheme.SubgroupFunctor.ZariskiLocality
import Langlands.GroupScheme.Rational.ParabolicAmbientTransport

/-! # Passing from affine tests to all tests for torus-subgroup charts -/

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.TorusSubgroupModuli

open SubgroupFunctor (coverObj coverMap)

variable {S : Scheme.{u}} {G : GroupScheme S}
variable {U M T T' : Over S} {K : GroupScheme U.left} {L : GroupScheme M.left}

/-- Equality of evaluations is preserved by every restriction of the test scheme. -/
theorem evaluate_eq_comp
    (j : K ⟶ (baseChange U.hom).obj G)
    (i : L ⟶ (baseChange M.hom).obj G) (a : T ⟶ U) (b : T ⟶ M)
    (h : evaluate j a = evaluate i b) (c : T' ⟶ T) :
    evaluate j (c ≫ a) = evaluate i (c ≫ b) := by
  rw [← evaluate_comp, ← evaluate_comp]
  exact evaluate_eq_of_range_eq (familyHom j a) (familyHom i b) h c

/-- Equality of evaluations of closed families is local on any open cover. -/
theorem evaluate_eq_iff_openCover
    (j : K ⟶ (baseChange U.hom).obj G)
    (i : L ⟶ (baseChange M.hom).obj G)
    (hj : IsClosedSubgroup j) (hi : IsClosedSubgroup i)
    (a : T ⟶ U) (b : T ⟶ M) (𝒰 : Scheme.OpenCover.{v} T.left) :
    evaluate j a = evaluate i b ↔ ∀ k,
      evaluate j (coverMap 𝒰 k ≫ a) = evaluate i (coverMap 𝒰 k ≫ b) := by
  constructor
  · exact fun h k => evaluate_eq_comp j i a b h (coverMap 𝒰 k)
  · intro h
    let : IsClosedImmersion (familyHom j a).hom.hom.left :=
      isClosedSubgroup_familyHom j hj a
    let : IsClosedImmersion (familyHom i b).hom.hom.left :=
      isClosedSubgroup_familyHom i hi b
    let : Mono (familyHom j a).hom.hom := Over.mono_of_mono_left _
    let : Mono (familyHom i b).hom.hom := Over.mono_of_mono_left _
    apply (SubgroupFunctor.range_eq_iff_baseChange_openCover 𝒰
      (familyHom j a) (familyHom i b)).mpr
    intro k
    have hk := h k
    rw [← evaluate_comp, ← evaluate_comp] at hk
    have hr := (SubgroupFunctor.range_comp_iso_eq_iff
      ((baseChange (coverMap 𝒰 k).left).map (familyHom j a))
      ((baseChange (coverMap 𝒰 k).left).map (familyHom i b))
      (Descent.pullbackComparison T.hom (coverMap 𝒰 k).left
        (coverObj 𝒰 k).hom (Over.w (coverMap 𝒰 k)) G)).mp hk
    dsimp [coverMap, Over.homMk, Over.Hom.left, CostructuredArrow.homMk] at hr
    simpa only [SubgroupFunctor.range_baseChangeHom] using hr

/-- Affine injectivity implies injectivity on every test scheme. -/
theorem IsOpenChartOnAffines.injective_all
    {j : K ⟶ (baseChange U.hom).obj G} (hj : IsOpenChartOnAffines j)
    (T : Over S) (a b : T ⟶ U) (h : evaluate j a = evaluate j b) : a = b := by
  apply Over.OverMorphism.ext
  apply T.left.affineCover.hom_ext
  intro k
  have hk := hj.injective (coverObj T.left.affineCover k)
    (inferInstanceAs (IsAffine (T.left.affineCover.X k)))
    (coverMap T.left.affineCover k ≫ a) (coverMap T.left.affineCover k ≫ b)
    (evaluate_eq_comp j j a b h (coverMap T.left.affineCover k))
  exact congrArg (fun f => f.left) hk

/-- Parameters for a closed family glue along arbitrary open covers. -/
theorem IsOpenChartOnAffines.exists_evaluate_iff_openCover
    {j : K ⟶ (baseChange U.hom).obj G} (hj : IsOpenChartOnAffines j)
    (i : L ⟶ (baseChange M.hom).obj G) (hi : IsClosedSubgroup i)
    (b : T ⟶ M) (𝒰 : Scheme.OpenCover.{v} T.left) :
    (∃ a : T ⟶ U, evaluate j a = evaluate i b) ↔
      ∀ k, ∃ a : coverObj 𝒰 k ⟶ U,
        evaluate j a = evaluate i (coverMap 𝒰 k ≫ b) := by
  classical
  constructor
  · rintro ⟨a, ha⟩ k
    exact ⟨coverMap 𝒰 k ≫ a, evaluate_eq_comp j i a b ha (coverMap 𝒰 k)⟩
  · intro h
    choose a ha using h
    have hc (k l : 𝒰.I₀) :
        pullback.fst (𝒰.f k) (𝒰.f l) ≫ (a k).left =
          pullback.snd (𝒰.f k) (𝒰.f l) ≫ (a l).left := by
      let W : Over S :=
        Over.mk (pullback.fst (𝒰.f k) (𝒰.f l) ≫ 𝒰.f k ≫ T.hom)
      let p : W ⟶ coverObj 𝒰 k := Over.homMk (pullback.fst (𝒰.f k) (𝒰.f l))
      let q : W ⟶ coverObj 𝒰 l := Over.homMk (pullback.snd (𝒰.f k) (𝒰.f l))
        (by simpa only [W, coverObj, Over.mk_hom] using
          (pullback.condition_assoc (f := 𝒰.f k) (g := 𝒰.f l) T.hom).symm)
      have hpq : p ≫ coverMap 𝒰 k = q ≫ coverMap 𝒰 l := by
        apply Over.OverMorphism.ext
        exact pullback.condition
      have he : p ≫ a k = q ≫ a l := by
        apply hj.injective_all
        exact (evaluate_eq_comp j i (a k) (coverMap 𝒰 k ≫ b) (ha k) p).trans
          (by rw [← Category.assoc, hpq, Category.assoc]
              exact (evaluate_eq_comp j i (a l) (coverMap 𝒰 l ≫ b) (ha l) q).symm)
      exact congrArg (fun f => f.left) he
    let d := 𝒰.glueMorphisms (fun k => (a k).left) hc
    have hd (k : 𝒰.I₀) : 𝒰.f k ≫ d = (a k).left :=
      𝒰.ι_glueMorphisms _ hc k
    have hw : d ≫ U.hom = T.hom := by
      apply 𝒰.hom_ext
      intro k
      rw [← Category.assoc, hd]
      exact Over.w (a k)
    let a' : T ⟶ U := Over.homMk d hw
    refine ⟨a', (evaluate_eq_iff_openCover j i hj.isClosedSubgroup hi a' b 𝒰).mpr ?_⟩
    intro k
    have he : coverMap 𝒰 k ≫ a' = a k := by
      apply Over.OverMorphism.ext
      exact hd k
    rw [he]
    exact ha k

/-- For an affine target the affine openness condition already handles every
source test scheme. -/
theorem IsOpenChartOnAffines.isOpen_affineTarget
    {j : K ⟶ (baseChange U.hom).obj G} (hj : IsOpenChartOnAffines j)
    (M : Over S) (hM : IsAffine M.left) (L : GroupScheme M.left)
    (i : L ⟶ (baseChange M.hom).obj G)
    (hi : IsClosedSubgroup i) (hL : RelativeTorus.IsTorus L) :
    ∃ V : M.left.Opens, ∀ (T : Over S) (b : T ⟶ M),
      (∃ a : T ⟶ U, evaluate j a = evaluate i b) ↔ Set.range b.left.base ⊆ V := by
  obtain ⟨V, hV⟩ := hj.isOpen M hM L i hi hL
  refine ⟨V, fun T b => ?_⟩
  rw [hj.exists_evaluate_iff_openCover i hi b T.left.affineCover]
  constructor
  · intro h y hy
    obtain ⟨x, rfl⟩ := hy
    obtain ⟨k, z, hz⟩ := T.left.affineCover.exists_eq x
    have hk := (hV (coverObj T.left.affineCover k)
      (coverMap T.left.affineCover k ≫ b)
      (inferInstanceAs (IsAffine (T.left.affineCover.X k)))).mp (h k)
    exact hk ⟨z, by change b.left (T.left.affineCover.f k z) = b.left x; rw [hz]⟩
  · intro h k
    apply (hV (coverObj T.left.affineCover k) (coverMap T.left.affineCover k ≫ b)
      (inferInstanceAs (IsAffine (T.left.affineCover.X k)))).mpr
    rintro y ⟨z, rfl⟩
    exact h ⟨T.left.affineCover.f k z, rfl⟩

/-- The union of the open loci on an affine cover represents the chart
pullback on every test scheme. -/
theorem IsOpenChartOnAffines.isOpen_all
    {j : K ⟶ (baseChange U.hom).obj G} (hj : IsOpenChartOnAffines j)
    (M : Over S) (L : GroupScheme M.left)
    (i : L ⟶ (baseChange M.hom).obj G)
    (hi : IsClosedSubgroup i) (hL : RelativeTorus.IsTorus L) :
    ∃ V : M.left.Opens, ∀ (T : Over S) (b : T ⟶ M),
      (∃ a : T ⟶ U, evaluate j a = evaluate i b) ↔ Set.range b.left.base ⊆ V := by
  classical
  let 𝒰 := M.left.affineCover
  choose V hV using fun k : 𝒰.I₀ => hj.isOpen_affineTarget
    (coverObj 𝒰 k) (inferInstanceAs (IsAffine (M.left.affineCover.X k)))
    ((baseChange (𝒰.f k)).obj L) (familyHom i (coverMap 𝒰 k))
    (isClosedSubgroup_familyHom i hi (coverMap 𝒰 k)) (hL.baseChange (𝒰.f k))
  let W (k : 𝒰.I₀) : Over S := Over.mk ((V k).ι ≫ 𝒰.f k ≫ M.hom)
  let e (k : 𝒰.I₀) : W k ⟶ coverObj 𝒰 k := Over.homMk (V k).ι
  let c (k : 𝒰.I₀) : W k ⟶ M := e k ≫ coverMap 𝒰 k
  have hc_open (k : 𝒰.I₀) : IsOpenImmersion (c k).left := by
    change IsOpenImmersion ((V k).ι ≫ 𝒰.f k)
    infer_instance
  have hc (k : 𝒰.I₀) : ∃ a : W k ⟶ U, evaluate j a = evaluate i (c k) := by
    have hv : Set.range (e k).left.base ⊆ V k := by
      rintro x ⟨y, rfl⟩
      exact y.property
    simpa only [evaluate_comp] using (hV k (W k) (e k)).mpr hv
  refine ⟨⨆ k, (c k).left.opensRange, fun T b => ?_⟩
  constructor
  · rintro ⟨a, ha⟩ y ⟨x, rfl⟩
    let 𝒟 : Scheme.OpenCover T.left := 𝒰.pullback₁ b.left
    obtain ⟨k, z, hz⟩ := 𝒟.exists_eq x
    let q : coverObj 𝒟 k ⟶ coverObj 𝒰 k :=
      Over.homMk (pullback.snd b.left (𝒰.f k)) (by
        change pullback.snd b.left (𝒰.f k) ≫ 𝒰.f k ≫ M.hom =
          pullback.fst b.left (𝒰.f k) ≫ T.hom
        rw [← pullback.condition_assoc, Over.w b])
    have hq : q ≫ coverMap 𝒰 k = coverMap 𝒟 k ≫ b := by
      apply Over.OverMorphism.ext
      exact pullback.condition.symm
    have he : evaluate j (coverMap 𝒟 k ≫ a) =
        evaluate (familyHom i (coverMap 𝒰 k)) q := by
      rw [evaluate_comp, hq]
      exact evaluate_eq_comp j i a b ha (coverMap 𝒟 k)
    have hv := (hV k (coverObj 𝒟 k) q).mp ⟨_, he⟩
    apply TopologicalSpace.Opens.mem_iSup.mpr
    refine ⟨k, ?_⟩
    change b.left x ∈ Set.range (c k).left
    refine ⟨⟨q.left z, hv ⟨z, rfl⟩⟩, ?_⟩
    change 𝒰.f k (pullback.snd b.left (𝒰.f k) z) = b.left x
    rw [← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply]
    exact congrArg b.left hz
  · intro h
    let Q (k : 𝒰.I₀) : T.left.Opens := b.left ⁻¹ᵁ (c k).left.opensRange
    have hQ : TopologicalSpace.IsOpenCover Q := by
      apply TopologicalSpace.IsOpenCover.mk
      apply TopologicalSpace.Opens.ext
      ext x
      constructor
      · intro _
        trivial
      · intro _
        apply TopologicalSpace.Opens.mem_iSup.mpr
        have hx := h ⟨x, rfl⟩
        obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
        exact ⟨k, hk⟩
    let 𝒟 := T.left.openCoverOfIsOpenCover Q hQ
    apply (hj.exists_evaluate_iff_openCover i hi b 𝒟).mpr
    intro k
    let f : coverObj 𝒟 k ⟶ M := coverMap 𝒟 k ≫ b
    have hf : Set.range f.left ⊆ Set.range (c k).left := by
      rintro y ⟨x, rfl⟩
      exact x.property
    let l := IsOpenImmersion.lift (c k).left f.left hf
    have hl : l ≫ (c k).left = f.left := IsOpenImmersion.lift_fac _ _ hf
    let q : coverObj 𝒟 k ⟶ W k := Over.homMk l (by
      rw [← Over.w (c k), ← Category.assoc, hl]
      exact Over.w f)
    have hq : q ≫ c k = f := by
      apply Over.OverMorphism.ext
      exact hl
    obtain ⟨a, ha⟩ := hc k
    refine ⟨q ≫ a, ?_⟩
    simpa only [hq] using evaluate_eq_comp j i a (c k) ha q

/-- Affine tests suffice for open charts of actual closed torus subgroups. -/
theorem isOpenChartOfAffines : IsOpenChartOfAffinesStatement.{u} := by
  intro S G U K j hj
  exact ⟨hj.isClosedSubgroup, hj.isTorus, hj.smooth, hj.injective_all, hj.isOpen_all⟩

end Langlands.GroupScheme.TorusSubgroupModuli
