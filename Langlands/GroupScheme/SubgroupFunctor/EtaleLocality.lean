import Langlands.GroupScheme.SubgroupBaseChange
import Langlands.AlgebraicGeometry.Sites.EtaleFppfComparison
import Mathlib.CategoryTheory.Sites.EffectiveEpimorphic
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Langlands.GroupScheme.SubgroupFunctor.EtaleDescent

/-! # Etale locality of represented subgroup membership -/

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SubgroupFunctor

variable {S : Scheme.{u}} {G H K : GroupScheme S}

/-- A member of an etale cover of a relative test scheme, regarded over the
original base. -/
abbrev etaleCoverObj {T : Over S} (𝒰 : T.left.Cover.{v} (Scheme.precoverage @Etale))
    (k : 𝒰.I₀) : Over S :=
  Over.mk (𝒰.f k ≫ T.hom)

/-- The relative inclusion of a member of an etale cover. -/
def etaleCoverMap {T : Over S} (𝒰 : T.left.Cover.{v} (Scheme.precoverage @Etale))
    (k : 𝒰.I₀) : etaleCoverObj 𝒰 k ⟶ T :=
  Over.homMk (𝒰.f k) rfl

/-- An arbitrary etale cover is an effective epimorphic family of schemes. -/
theorem effectiveEpiFamily_etaleCover {X : Scheme.{u}}
    (𝒰 : X.Cover.{v} (Scheme.precoverage @Etale)) :
    EffectiveEpiFamily 𝒰.X 𝒰.f := by
  rw [← Sieve.effectiveEpimorphic_family,
    Presieve.EffectiveEpimorphic.iff_forall_isSheafFor_yoneda]
  intro Y
  exact (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable
    (J := Scheme.fppfTopology) (yoneda.obj Y)).isSheafFor _
      (Precoverage.generate_mem_toGrothendieck
        (Langlands.AlgebraicGeometry.Sites.etalePrecoverage_le_fppfPrecoverage _ 𝒰.mem₀))

/-- A point factors through a monomorphic group-scheme inclusion if it does so
on every member of an arbitrary etale cover of the test scheme. -/
theorem mem_range_iff_etaleCover (i : H ⟶ G) [Mono i.hom.hom] {T : Over S}
    (𝒰 : T.left.Cover.{v} (Scheme.precoverage @Etale)) (x : T ⟶ G.X) :
    x ∈ (range i).carrier T ↔ ∀ k,
      etaleCoverMap 𝒰 k ≫ x ∈ (range i).carrier (etaleCoverObj 𝒰 k) := by
  let : EffectiveEpiFamily 𝒰.X 𝒰.f := effectiveEpiFamily_etaleCover 𝒰
  constructor
  · intro hx k
    exact (range i).comp_mem (etaleCoverMap 𝒰 k) hx
  · intro hx
    choose y hy using fun k => mem_range.mp (hx k)
    have hy' (k : 𝒰.I₀) :
        (y k).left ≫ i.hom.hom.left = 𝒰.f k ≫ x.left :=
      congrArg (fun f => f.left) (hy k)
    have hc {Z : Scheme.{u}} (k l : 𝒰.I₀)
        (a : Z ⟶ 𝒰.X k) (b : Z ⟶ 𝒰.X l) (hab : a ≫ 𝒰.f k = b ≫ 𝒰.f l) :
        a ≫ (y k).left = b ≫ (y l).left := by
      apply (cancel_mono i.hom.hom.left).mp
      simpa only [Category.assoc, hy'] using
        congrArg (fun f => f ≫ x.left) hab
    let d := EffectiveEpiFamily.desc 𝒰.X 𝒰.f (fun k => (y k).left) hc
    have hd (k : 𝒰.I₀) : 𝒰.f k ≫ d = (y k).left :=
      EffectiveEpiFamily.fac 𝒰.X 𝒰.f _ hc k
    have hw : d ≫ H.X.hom = T.hom := by
      apply EffectiveEpiFamily.hom_ext 𝒰.X 𝒰.f
      intro k
      rw [← Category.assoc, hd]
      exact Over.w (y k)
    refine mem_range.mpr ⟨Over.homMk d hw, ?_⟩
    apply Over.OverMorphism.ext
    apply EffectiveEpiFamily.hom_ext 𝒰.X 𝒰.f
    intro k
    change 𝒰.f k ≫ (d ≫ i.hom.hom.left) = 𝒰.f k ≫ x.left
    rw [← Category.assoc, hd, hy']

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Containment in a monomorphically represented subgroup can be checked on
an arbitrary etale cover of the base. -/
theorem le_range_iff_baseChange_etaleCover (𝒰 : S.Cover.{v} (Scheme.precoverage @Etale))
    {F : SubgroupFunctor G} (i : H ⟶ G) [Mono i.hom.hom] :
    F ≤ range i ↔
      ∀ k : 𝒰.I₀, F.baseChange (𝒰.f k) ≤ (range i).baseChange (𝒰.f k) := by
  let : Scheme.IsJointlySurjectivePreserving (@Etale.{u}) :=
    Scheme.isJointlySurjectivePreserving _
  constructor
  · intro h k U x hx
    exact h _ hx
  · intro h U x hx
    apply (mem_range_iff_etaleCover i (𝒰.pullback₁ U.hom) x).mpr
    intro k
    let V : Over (𝒰.X k) := Over.mk (pullback.snd U.hom (𝒰.f k))
    let q : (Over.map (𝒰.f k)).obj V ⟶ U :=
      Over.homMk (pullback.fst U.hom (𝒰.f k)) pullback.condition
    let x' := (baseChangePointsEquiv (𝒰.f k) G V).symm (q ≫ x)
    have hx' : x' ∈ (F.baseChange (𝒰.f k)).carrier V := by
      rw [mem_baseChange]
      change baseChangePointsEquiv (𝒰.f k) G V
        ((baseChangePointsEquiv (𝒰.f k) G V).symm (q ≫ x)) ∈ F.carrier _
      rw [MulEquiv.apply_symm_apply]
      exact F.comp_mem q hx
    have hi := h k V hx'
    rw [mem_baseChange] at hi
    have hi' : q ≫ x ∈ (range i).carrier ((Over.map (𝒰.f k)).obj V) := by
      simpa only [x', MulEquiv.apply_symm_apply] using hi
    let r : etaleCoverObj (𝒰.pullback₁ U.hom) k ⟶ (Over.map (𝒰.f k)).obj V :=
      Over.homMk (𝟙 _) (by
        change 𝟙 _ ≫ (pullback.snd U.hom (𝒰.f k) ≫ 𝒰.f k) =
          pullback.fst U.hom (𝒰.f k) ≫ U.hom
        simpa only [Category.id_comp] using
          (pullback.condition (f := U.hom) (g := 𝒰.f k)).symm)
    have hr : r ≫ q = etaleCoverMap (𝒰.pullback₁ U.hom) k := by
      apply Over.OverMorphism.ext
      exact Category.id_comp _
    simpa only [← Category.assoc, hr] using (range i).comp_mem r hi'

/-- Equality of two monomorphically represented subgroup functors is
etale local on the base, without any finiteness assumption on the cover. -/
theorem range_eq_iff_baseChange_etaleCover (𝒰 : S.Cover.{v} (Scheme.precoverage @Etale))
    (i : H ⟶ G) (j : K ⟶ G) [Mono i.hom.hom] [Mono j.hom.hom] :
    range i = range j ↔
      ∀ k : 𝒰.I₀, (range i).baseChange (𝒰.f k) =
        (range j).baseChange (𝒰.f k) := by
  constructor
  · intro h k
    rw [h]
  · intro h
    apply le_antisymm
    · exact (le_range_iff_baseChange_etaleCover 𝒰 j).mpr fun k => (h k).le
    · exact (le_range_iff_baseChange_etaleCover 𝒰 i).mpr fun k => (h k).ge

/-- The same equality criterion for explicit representatives of subgroup
functors. -/
theorem eq_iff_isRepresentedBy_baseChange_etaleCover
    (𝒰 : S.Cover.{v} (Scheme.precoverage @Etale)) {F F' : SubgroupFunctor G}
    {i : H ⟶ G} {j : K ⟶ G} (hi : F.IsRepresentedBy i) (hj : F'.IsRepresentedBy j) :
    F = F' ↔ ∀ k : 𝒰.I₀, F.baseChange (𝒰.f k) = F'.baseChange (𝒰.f k) := by
  let : Mono i.hom.hom := hi.1
  let : Mono j.hom.hom := hj.1
  rw [← hi.2, ← hj.2]
  exact range_eq_iff_baseChange_etaleCover 𝒰 i j

end Langlands.GroupScheme.SubgroupFunctor

section IntegratedCompanion

/-! # Detecting represented subgroup containment on an étale cover -/



open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.SubgroupFunctor

variable {S : Scheme.{u}} {G H : GroupScheme S}

/-- Containment in a monomorphically represented subgroup can be checked after
pullback along a jointly surjective étale cover of the base. -/
theorem le_range_iff_baseChange_etaleCover_sameUniverse
    (𝒰 : Scheme.Cover.{u} (Scheme.precoverage @Etale) S)
    {F : SubgroupFunctor G} (i : H ⟶ G) [Mono i.hom.hom] :
    F ≤ range i ↔
      ∀ k : 𝒰.I₀, F.baseChange (𝒰.f k) ≤ (range i).baseChange (𝒰.f k) := by
  constructor
  · exact fun h k V x hx => h _ hx
  · intro h V x hx
    have hi : (range i).IsRepresentedBy i := ⟨inferInstance, rfl⟩
    apply ((range i).schemeCondition_iff_mem x).mp
    apply hi.isClosed_schemeSieve x.left
    let 𝒱 : Scheme.Cover.{u} (Scheme.precoverage @Etale) V.left :=
      𝒰.pullback₁ V.hom
    have hcover : Sieve.generate (Presieve.ofArrows 𝒱.X 𝒱.f) ∈
        Scheme.fppfTopology V.left := by
      apply Precoverage.generate_mem_toGrothendieck
      rw [Scheme.fppfPrecoverage, Scheme.ofArrows_mem_precoverage_iff]
      refine ⟨fun v => ⟨𝒱.idx v, 𝒱.covers v⟩, fun k => ?_⟩
      have : Etale (𝒱.f k) := 𝒱.map_prop k
      exact ⟨inferInstance, inferInstance⟩
    apply Scheme.fppfTopology.superset_covering ?_ hcover
    intro W u hu
    obtain ⟨_, a, _, ⟨k⟩, ha⟩ := hu
    let Z : Over (𝒰.X k) :=
      Over.mk (a ≫ pullback.snd V.hom (𝒰.f k))
    let q : (Over.map (𝒰.f k)).obj Z ⟶ V := Over.homMk u (by
      change u ≫ V.hom = (a ≫ pullback.snd V.hom (𝒰.f k)) ≫ 𝒰.f k
      rw [← ha]
      change (a ≫ pullback.fst V.hom (𝒰.f k)) ≫ V.hom = _
      rw [Category.assoc, pullback.condition, ← Category.assoc])
    let y := (baseChangePointsEquiv (𝒰.f k) G Z).symm (q ≫ x)
    have hy : y ∈ (F.baseChange (𝒰.f k)).carrier Z := by
      rw [mem_baseChange]
      simpa only [y, MulEquiv.apply_symm_apply] using F.comp_mem q hx
    have hz := h k Z hy
    rw [mem_baseChange] at hz
    have hz' : q ≫ x ∈ (range i).carrier ((Over.map (𝒰.f k)).obj Z) := by
      simpa only [y, MulEquiv.apply_symm_apply] using hz
    exact ((range i).schemeCondition_iff_mem (q ≫ x)).mpr hz'

end Langlands.GroupScheme.SubgroupFunctor

end IntegratedCompanion
