import Langlands.AlgebraicGeometry.DenseDivisionComparison
import Langlands.GroupScheme.RelativeIdentityComponent.BaseChange
import Mathlib.AlgebraicGeometry.Morphisms.IsIso

/-! # Comparing a solution on an open where the entire law is defined -/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory TopologicalSpace
open scoped CategoryTheory.MonObj

namespace Langlands.AlgebraicGeometry

open Langlands.GroupScheme.RelativeIdentityComponent (overPullback_isPullback range_of_isPullback)

namespace BirationalGroupLaw

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {S X : Scheme.{u}} {f : X ⟶ S} (m : BirationalGroupLaw f)

/-- The domain of the representative, regarded as a scheme over the base. -/
abbrev overDomain : Over S := Over.mk (m.domain.ι ≫ pullback.fst f f ≫ f)

/-- The domain inclusion into the relative product. -/
abbrev overInclusion : m.overDomain ⟶ Over.mk f ⊗ Over.mk f := Over.homMk m.domain.ι rfl

/-- The product of the representative over the base. -/
abbrev overMul : m.overDomain ⟶ Over.mk f := Over.homMk m.mul m.mul_comp

namespace Solution

variable {m} (σ : m.Solution)

abbrev overChart : Over S := Over.mk (σ.domain.ι ≫ f)

abbrev firstChart : σ.overChart ⟶ Over.mk f := Over.homMk σ.domain.ι rfl

abbrev secondChart : σ.overChart ⟶ σ.group.X := Over.homMk σ.embedding σ.embedding_comp

/-- Multiplication compatibility of a solution on three points of the common chart. -/
theorem mul_eq_over {T : Over S} (a : T ⟶ m.overDomain) (x y z : T ⟶ σ.overChart)
    (hx : a ≫ m.overInclusion ≫ fst _ _ = x ≫ σ.firstChart)
    (hy : a ≫ m.overInclusion ≫ snd _ _ = y ≫ σ.firstChart)
    (hz : a ≫ m.overMul = z ≫ σ.firstChart) :
    lift (x ≫ σ.secondChart) (y ≫ σ.secondChart) ≫ μ[σ.group.X] = z ≫ σ.secondChart := by
  apply Over.OverMorphism.ext
  exact (σ.mul_eq T.left a.left x.left y.left z.left (congrArg Over.Hom.left hx)
    (congrArg Over.Hom.left hy) (congrArg Over.Hom.left hz)).symm

end Solution

private abbrev project {B : Scheme.{u}} (b : B ⟶ S) (A : Over S) :
    ((Over.map b).obj ((Over.pullback b).obj A)) ⟶ A := (Over.mapPullbackAdj b).counit.app A

private abbrev descendPoint {B : Scheme.{u}} (b : B ⟶ S) {T : Over B} {A : Over S}
    (x : T ⟶ (Over.pullback b).obj A) : (Over.map b).obj T ⟶ A := (Over.map b).map x ≫ project b A

private theorem descendPoint_comp {B : Scheme.{u}} (b : B ⟶ S)
    {T : Over B} {A A' : Over S} (x : T ⟶ (Over.pullback b).obj A) (a : A ⟶ A') :
    descendPoint b (x ≫ (Over.pullback b).map a) = descendPoint b x ≫ a := by
  have h := (Over.mapPullbackAdj b).counit.naturality a
  change (Over.map b).map ((Over.pullback b).map a) ≫ project b A' = project b A ≫ a at h
  simp only [descendPoint, Functor.map_comp, Category.assoc, h]

private theorem descendPoint_lift {B : Scheme.{u}} (b : B ⟶ S)
    {T : Over B} {A A' : Over S} (x : T ⟶ (Over.pullback b).obj A)
    (y : T ⟶ (Over.pullback b).obj A') :
    descendPoint b (lift x y ≫ inv (CartesianMonoidalCategory.prodComparison (Over.pullback b) A A')) =
      lift (descendPoint b x) (descendPoint b y) := by
  have h₁ : inv (CartesianMonoidalCategory.prodComparison (Over.pullback b) A A') ≫ (Over.pullback b).map (fst A A') =
      fst _ _ := by
    rw [← CartesianMonoidalCategory.prodComparison_fst, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
  have h₂ : inv (CartesianMonoidalCategory.prodComparison (Over.pullback b) A A') ≫ (Over.pullback b).map (snd A A') =
      snd _ _ := by
    rw [← CartesianMonoidalCategory.prodComparison_snd, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
  apply CartesianMonoidalCategory.hom_ext
  · rw [lift_fst, ← descendPoint_comp, Category.assoc, h₁, lift_fst]
  · rw [lift_snd, ← descendPoint_comp, Category.assoc, h₂, lift_snd]

/-- Wherever the representative and both open translations cover the entire relative
product, a solution identifies the whole restriction of `X` with its group. -/
theorem Solution.exists_iso_over_open (σ : m.Solution) (B : S.Opens)
    [S.IsSeparated] [IsReduced S] [IsNoetherian S] [Smooth f] [IsSeparated f] [QuasiCompact f]
    (hcover : ∀ p : ↑(pullback f f), (pullback.fst f f ≫ f) p ∈ B →
      p ∈ m.domain ∧ p ∈ Set.range (leftTranslation f m.domain m.mul m.mul_comp) ∧
      p ∈ Set.range (rightTranslation f m.domain m.mul m.mul_comp)) :
    ∃ e : pullback f B.ι ≅ pullback σ.group.X.hom B.ι,
      ((Over.pullback B.ι).map σ.firstChart).left ≫ e.hom =
        ((Over.pullback B.ι).map σ.secondChart).left := by
  let b := B.ι
  let F := Over.pullback b
  let A := Over.mk f
  let A' := F.obj A
  let P := CartesianMonoidalCategory.prodComparison F A A
  let a : F.obj m.overDomain ⟶ F.obj (A ⊗ A) := F.map m.overInclusion
  let μ₀ : F.obj m.overDomain ⟶ A' := F.map m.overMul
  let l : m.overDomain ⟶ A ⊗ A := lift (m.overInclusion ≫ fst A A) m.overMul
  let r : m.overDomain ⟶ A ⊗ A := lift m.overMul (m.overInclusion ≫ snd A A)
  have hl : l.left = leftTranslation f m.domain m.mul m.mul_comp := rfl
  have hr : r.left = rightTranslation f m.domain m.mul m.mul_comp := rfl
  have hIso (k : m.overDomain ⟶ A ⊗ A) (hk : IsOpenImmersion k.left)
      (hkr : ∀ p : (A ⊗ A).left, (A ⊗ A).hom p ∈ B → p ∈ Set.range k.left) : IsIso (F.map k) := by
    have hb := (overPullback_isPullback b k)
    have : IsOpenImmersion (F.map k).left := MorphismProperty.of_isPullback hb.flip hk
    have : Surjective (F.map k).left := by
      constructor
      intro p
      change p ∈ Set.range (F.map k).left
      rw [range_of_isPullback hb]
      apply hkr
      have hbase := congrArg (fun g : pullback (A ⊗ A).hom b ⟶ S => g p)
        (pullback.condition (f := (A ⊗ A).hom) (g := b))
      change (A ⊗ A).hom (pullback.fst (A ⊗ A).hom b p) = b (pullback.snd (A ⊗ A).hom b p) at hbase
      change (A ⊗ A).hom (pullback.fst (A ⊗ A).hom b p) ∈ B
      rw [hbase]
      exact (pullback.snd (A ⊗ A).hom b p).2
    have : IsIso (F.map k).left := (isIso_iff_isOpenImmersion_and_surjective _).mpr
      ⟨inferInstance, inferInstance⟩
    have : IsIso ((Over.forget B.toScheme).map (F.map k)) := ‹IsIso (F.map k).left›
    exact isIso_of_reflects_iso (F.map k) (Over.forget B.toScheme)
  have ha : IsIso a := hIso m.overInclusion (inferInstanceAs (IsOpenImmersion m.domain.ι))
    (fun p hp => by
    change p ∈ Set.range m.domain.ι
    rw [Scheme.Opens.range_ι]
    exact (hcover p hp).1)
  have hl' : IsIso (F.map l) := hIso l (hl ▸ m.isOpenImmersion_leftTranslation) (fun p hp =>
    hl ▸ (hcover p hp).2.1)
  have hr' : IsIso (F.map r) := hIso r (hr ▸ m.isOpenImmersion_rightTranslation) (fun p hp =>
    hr ▸ (hcover p hp).2.2)
  let iD := a ≫ P
  have : IsIso iD := inferInstanceAs (IsIso (a ≫ P))
  let μK : A' ⊗ A' ⟶ A' := inv iD ≫ μ₀
  have hP₁ : P ≫ fst A' A' = F.map (fst A A) := CartesianMonoidalCategory.prodComparison_fst F A A
  have hP₂ : P ≫ snd A' A' = F.map (snd A A) := CartesianMonoidalCategory.prodComparison_snd F A A
  have h₁ : iD ≫ lift (fst A' A') μK = F.map l ≫ P := by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, lift_fst, iD, hP₁, ← Functor.map_comp, l,
        lift_fst, a]
    · simp only [Category.assoc, lift_snd, μK, IsIso.hom_inv_id_assoc, hP₂, ← Functor.map_comp, l, lift_snd, μ₀]
  have h₂ : iD ≫ lift μK (snd A' A') = F.map r ≫ P := by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, lift_fst, μK, IsIso.hom_inv_id_assoc, hP₁, ← Functor.map_comp, r, lift_fst, μ₀]
    · simp only [Category.assoc, lift_snd, iD, hP₂, ← Functor.map_comp, r,
        lift_snd, a]
  let L : InvertibleTranslations A' :=
    ⟨μK, by rw [(IsIso.eq_inv_comp iD).mpr h₁]; infer_instance,
      by rw [(IsIso.eq_inv_comp iD).mpr h₂]; infer_instance⟩
  let G := (Langlands.GroupScheme.baseChange b).obj σ.group
  let i := F.map σ.firstChart
  let j := F.map σ.secondChart
  have : IsOpenImmersion σ.embedding := σ.isOpenImmersion_embedding
  have : IsOpenImmersion i.left := MorphismProperty.of_isPullback
    (overPullback_isPullback b σ.firstChart).flip (inferInstanceAs (IsOpenImmersion σ.domain.ι))
  have : IsOpenImmersion j.left := MorphismProperty.of_isPullback
    (overPullback_isPullback b σ.secondChart).flip σ.isOpenImmersion_embedding
  have hi : FibreGenerizationDense A'.hom (Set.range i.left) := by
    rw [range_of_isPullback (overPullback_isPullback b σ.firstChart)]
    change FibreGenerizationDense (pullback.snd f b) (pullback.fst f b ⁻¹' Set.range σ.domain.ι)
    rw [Scheme.Opens.range_ι]
    exact σ.domain_dense.preimage_of_isPullback (IsPullback.of_hasPullback f b)
  have hj : FibreGenerizationDense G.X.hom (Set.range j.left) := by
    rw [range_of_isPullback (overPullback_isPullback b σ.secondChart)]
    exact σ.embedding_dense.preimage_of_isPullback (IsPullback.of_hasPullback σ.group.X.hom b)
  have : Smooth σ.group.X.hom := σ.smooth
  have : IsSeparated σ.group.X.hom := σ.isSeparated
  have : IsReduced B.toScheme := isReduced_of_isOpenImmersion b
  have : IsLocallyNoetherian B.toScheme := isLocallyNoetherian_of_isOpenImmersion b
  have : NoetherianSpace B.toScheme := b.isEmbedding.isInducing.noetherianSpace
  have : CompactSpace B.toScheme := inferInstance
  have : B.toScheme.IsSeparated := separatedScheme_of_separated_over b
  have : Smooth A'.hom := inferInstanceAs (Smooth (pullback.snd f b))
  have : Smooth G.X.hom := inferInstanceAs (Smooth (pullback.snd σ.group.X.hom b))
  have : QuasiCompact A'.hom := inferInstanceAs (QuasiCompact (pullback.snd f b))
  have : IsSeparated A'.hom := inferInstanceAs (IsSeparated (pullback.snd f b))
  have : IsSeparated G.X.hom := inferInstanceAs (IsSeparated (pullback.snd σ.group.X.hom b))
  have : A'.left.IsSeparated := separatedScheme_of_separated_over A'.hom
  have : G.X.left.IsSeparated := separatedScheme_of_separated_over G.X.hom
  refine L.exists_iso_of_chart (.ofGroup G) i j hi hj (fun {T} x y z h => ?_)
  let c := lift (x ≫ i) (y ≫ i) ≫ inv iD
  have hc : c ≫ a = lift (x ≫ i) (y ≫ i) ≫ inv P := by
    apply (cancel_mono P).mp
    simp only [c, Category.assoc, ← show iD = a ≫ P from rfl, IsIso.inv_hom_id,
      Category.comp_id]
  have hc' : c ≫ μ₀ = z ≫ i := by exact h
  have hd : descendPoint b c ≫ m.overInclusion =
      lift (descendPoint b x ≫ σ.firstChart) (descendPoint b y ≫ σ.firstChart) := by
    rw [← descendPoint_comp, hc, descendPoint_lift, descendPoint_comp, descendPoint_comp]
  have hmul := σ.mul_eq_over (descendPoint b c) (descendPoint b x) (descendPoint b y)
    (descendPoint b z) (by rw [← Category.assoc, hd, lift_fst])
    (by rw [← Category.assoc, hd, lift_snd])
    (by rw [← descendPoint_comp, hc', descendPoint_comp])
  change lift (x ≫ j) (y ≫ j) ≫ Functor.LaxMonoidal.μ F σ.group.X σ.group.X ≫
      F.map μ[σ.group.X] = z ≫ j
  apply Over.OverMorphism.ext
  apply (cancel_mono (pullback.fst σ.group.X.hom b)).mp
  change (descendPoint b (lift (x ≫ j) (y ≫ j) ≫ Functor.LaxMonoidal.μ F σ.group.X σ.group.X ≫
      F.map μ[σ.group.X])).left = (descendPoint b (z ≫ j)).left
  congr 1
  rw [← Category.assoc, descendPoint_comp, Functor.Monoidal.μ_of_cartesianMonoidalCategory]
  have he : (prodComparisonIso F σ.group.X σ.group.X).inv =
      inv (CartesianMonoidalCategory.prodComparison F σ.group.X σ.group.X) := by
    apply IsIso.eq_inv_of_hom_inv_id
    exact (prodComparisonIso F σ.group.X σ.group.X).hom_inv_id
  rw [he]
  rw [descendPoint_lift, descendPoint_comp, descendPoint_comp, descendPoint_comp]
  exact hmul

end BirationalGroupLaw

end Langlands.AlgebraicGeometry
