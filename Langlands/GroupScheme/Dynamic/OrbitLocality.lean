import Langlands.GroupScheme.Dynamic.Uniqueness
import Langlands.GroupScheme.SubgroupFunctor.ZariskiDescent

/-! # Locality of actual orbit extensions on test schemes -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme.DynamicLocality

open SubgroupFunctor

variable {S : Scheme.{u}}

/-- A chart of the pullback of a product's first projection maps to the
product of the chart with the second factor. -/
def tensorChart (T Y : Over S) {Z : Scheme.{u}} (a : Z ⟶ T.left) :
    pullback (fst T Y).left a ⟶ (Over.mk (a ≫ T.hom) ⊗ Y).left :=
  pullback.lift (pullback.snd _ _) (pullback.fst _ _ ≫ (snd T Y).left) (by
    change pullback.snd _ _ ≫ a ≫ T.hom = _
    rw [← Category.assoc, ← pullback.condition]
    simp only [Category.assoc]
    rw [Over.w (fst T Y), Over.w (snd T Y)])

/-- The chart comparison is compatible with the original product map. -/
theorem tensorChart_comp (T Y : Over S) {Z : Scheme.{u}} (a : Z ⟶ T.left) :
    tensorChart T Y a ≫
      ((Over.homMk a rfl : Over.mk (a ≫ T.hom) ⟶ T) ▷ Y).left =
        pullback.fst _ _ := by
  apply pullback.hom_ext
  · rw [Category.assoc, Over.whiskerRight_left_fst, tensorChart,
      pullback.lift_fst_assoc]
    exact pullback.condition.symm
  · rw [Category.assoc, Over.whiskerRight_left_snd, tensorChart, pullback.lift_snd]
    rfl

/-- The canonical map in the other direction. -/
def tensorChartSection (T Y : Over S) {Z : Scheme.{u}} (a : Z ⟶ T.left) :
    (Over.mk (a ≫ T.hom) ⊗ Y).left ⟶ pullback (fst T Y).left a :=
  pullback.lift
    ((Over.homMk a rfl : Over.mk (a ≫ T.hom) ⟶ T) ▷ Y).left
    (fst (Over.mk (a ≫ T.hom)) Y).left
    (Over.whiskerRight_left_fst _)

/-- The canonical map followed by the chart comparison is the identity. -/
theorem tensorChartSection_comp (T Y : Over S) {Z : Scheme.{u}} (a : Z ⟶ T.left) :
    tensorChartSection T Y a ≫ tensorChart T Y a = 𝟙 _ := by
  apply pullback.hom_ext
  · simp only [Category.assoc, tensorChart, pullback.lift_fst,
      tensorChartSection, pullback.lift_snd, Category.id_comp]
    rfl
  · simp only [Category.assoc, tensorChart, pullback.lift_snd,
      tensorChartSection, pullback.lift_fst_assoc, Category.id_comp]
    exact Over.whiskerRight_left_snd _

/-- The test cover pulled back to a product. -/
abbrev tensorCover {T : Over S} (𝒰 : Scheme.OpenCover.{u} T.left) (Y : Over S) :
    Scheme.OpenCover.{u} (T ⊗ Y).left :=
  𝒰.pullback₁ (fst T Y).left

/-- The product chart regarded as a morphism over the original base. -/
def tensorCoverChart {T : Over S} (𝒰 : Scheme.OpenCover.{u} T.left)
    (Y : Over S) (i : 𝒰.I₀) :
    coverObj (T := T ⊗ Y) (tensorCover 𝒰 Y) i ⟶ coverObj 𝒰 i ⊗ Y :=
  Over.homMk (tensorChart T Y (𝒰.f i)) (by
    change tensorChart T Y (𝒰.f i) ≫ (coverObj 𝒰 i ⊗ Y).hom =
      pullback.fst (fst T Y).left (𝒰.f i) ≫ (T ⊗ Y).hom
    have hw := Over.w ((Over.homMk (𝒰.f i) rfl :
      Over.mk (𝒰.f i ≫ T.hom) ⟶ T) ▷ Y)
    rw [← hw, ← Category.assoc, tensorChart_comp])

/-- Product charts commute with their cover inclusions. -/
theorem tensorCoverChart_comp {T : Over S} (𝒰 : Scheme.OpenCover.{u} T.left)
    (Y : Over S) (i : 𝒰.I₀) :
    tensorCoverChart 𝒰 Y i ≫ (coverMap 𝒰 i ▷ Y) =
      coverMap (T := T ⊗ Y) (tensorCover 𝒰 Y) i :=
  Over.OverMorphism.ext (tensorChart_comp T Y (𝒰.f i))

/-- Equality on products can be checked on an open cover of the first factor. -/
theorem tensor_hom_ext {T Y Z : Over S} (𝒰 : Scheme.OpenCover.{u} T.left)
    {e e' : T ⊗ Y ⟶ Z}
    (h : ∀ i, (coverMap 𝒰 i ▷ Y) ≫ e = (coverMap 𝒰 i ▷ Y) ≫ e') : e = e' := by
  apply Over.OverMorphism.ext
  apply (tensorCover 𝒰 Y).hom_ext
  intro i
  change pullback.fst _ (𝒰.f i) ≫ e.left = pullback.fst _ (𝒰.f i) ≫ e'.left
  rw [← tensorChart_comp T Y (𝒰.f i), Category.assoc, Category.assoc,
    ← Over.comp_left, ← Over.comp_left]
  exact congrArg (tensorChart T Y (𝒰.f i) ≫ ·.left) (h i)

/-- Compatible morphisms on products with test-cover charts glue over the base. -/
theorem exists_tensor_glue {T Y Z : Over S} (𝒰 : Scheme.OpenCover.{u} T.left)
    (e : ∀ i, coverObj 𝒰 i ⊗ Y ⟶ Z)
    (hc : ∀ (i j : 𝒰.I₀) {W : Over S}
      (a : W ⟶ coverObj 𝒰 i ⊗ Y) (b : W ⟶ coverObj 𝒰 j ⊗ Y),
      a ≫ (coverMap 𝒰 i ▷ Y) = b ≫ (coverMap 𝒰 j ▷ Y) →
        a ≫ e i = b ≫ e j) :
    ∃ e₀ : T ⊗ Y ⟶ Z, ∀ i, (coverMap 𝒰 i ▷ Y) ≫ e₀ = e i := by
  let 𝒱 := tensorCover 𝒰 Y
  let z := tensorCoverChart 𝒰 Y
  have hglue (i j : 𝒱.I₀) :
      pullback.fst (𝒱.f i) (𝒱.f j) ≫ (z i ≫ e i).left =
        pullback.snd (𝒱.f i) (𝒱.f j) ≫ (z j ≫ e j).left := by
    let W : Over S :=
      Over.mk (pullback.fst (𝒱.f i) (𝒱.f j) ≫ 𝒱.f i ≫ (T ⊗ Y).hom)
    let a : W ⟶ coverObj (T := T ⊗ Y) 𝒱 i :=
      Over.homMk (pullback.fst _ _) rfl
    let b : W ⟶ coverObj (T := T ⊗ Y) 𝒱 j :=
      Over.homMk (pullback.snd _ _) (by
        change pullback.snd (𝒱.f i) (𝒱.f j) ≫ (𝒱.f j ≫ (T ⊗ Y).hom) = _
        rw [← Category.assoc, ← pullback.condition, Category.assoc]
        rfl)
    have hab : a ≫ coverMap 𝒱 i = b ≫ coverMap 𝒱 j :=
      Over.OverMorphism.ext pullback.condition
    have h := hc i j (a ≫ z i) (b ≫ z j) (by
      simpa only [Category.assoc, z, tensorCoverChart_comp] using hab)
    exact congrArg Over.Hom.left h
  let d := 𝒱.glueMorphisms (fun i => (z i ≫ e i).left) hglue
  have hd (i : 𝒱.I₀) : 𝒱.f i ≫ d = (z i ≫ e i).left :=
    𝒱.ι_glueMorphisms _ hglue i
  have hw : d ≫ Z.hom = (T ⊗ Y).hom := by
    apply 𝒱.hom_ext
    intro i
    rw [← Category.assoc, hd]
    exact Over.w (z i ≫ e i)
  refine ⟨Over.homMk d hw, fun i => Over.OverMorphism.ext ?_⟩
  change (coverMap 𝒰 i ▷ Y).left ≫ d = (e i).left
  have hs : tensorChartSection T Y (𝒰.f i) ≫ 𝒱.f i =
      (coverMap 𝒰 i ▷ Y).left := pullback.lift_fst _ _ _
  rw [← hs, Category.assoc, hd]
  change tensorChartSection T Y (𝒰.f i) ≫
    (tensorChart T Y (𝒰.f i) ≫ (e i).left) = (e i).left
  rw [← Category.assoc, tensorChartSection_comp, Category.id_comp]

open Langlands.GroupScheme.Dynamic

variable {G : GroupScheme S} (χ : (Gm S).toGrp ⟶ G) [IsSeparated G.X.hom]

/-- Orbit extensions agree under every comparison of product charts. -/
theorem orbitExtension_compatible {T : Over S} (𝒰 : Scheme.OpenCover.{u} T.left)
    (g : T ⟶ G.X) (e : ∀ i, coverObj 𝒰 i ⊗ AffineLine.scheme S ⟶ G.X)
    (he : ∀ i, IsOrbitExtension χ (coverMap 𝒰 i ≫ g) (e i))
    (i j : 𝒰.I₀) {W : Over S}
    (a : W ⟶ coverObj 𝒰 i ⊗ AffineLine.scheme S)
    (b : W ⟶ coverObj 𝒰 j ⊗ AffineLine.scheme S)
    (hab : a ≫ (coverMap 𝒰 i ▷ AffineLine.scheme S) =
      b ≫ (coverMap 𝒰 j ▷ AffineLine.scheme S)) :
    a ≫ e i = b ≫ e j := by
  have hbase :
      (a ≫ fst _ _) ≫ coverMap 𝒰 i = (b ≫ fst _ _) ≫ coverMap 𝒰 j := by
    simpa only [Category.assoc, whiskerRight_fst] using
      congrArg (· ≫ fst T (AffineLine.scheme S)) hab
  have hcoord : a ≫ snd _ _ = b ≫ snd _ _ := by
    simpa only [Category.assoc, whiskerRight_snd] using
      congrArg (· ≫ snd T (AffineLine.scheme S)) hab
  have hp : (a ≫ fst _ _) ≫ (coverMap 𝒰 i ≫ g) =
      (b ≫ fst _ _) ≫ (coverMap 𝒰 j ≫ g) := by
    simpa only [Category.assoc] using congrArg (· ≫ g) hbase
  have hi := (he i).whiskerRight χ (a ≫ fst _ _)
  have hj := (he j).whiskerRight χ (b ≫ fst _ _)
  rw [hp] at hi
  have hh := hi.unique χ hj
  have h := congrArg (lift (𝟙 W) (a ≫ snd _ _) ≫ ·) hh
  simp only [← Category.assoc, lift_whiskerRight, Category.id_comp,
    lift_comp_fst_snd] at h
  simpa only [hcoord, lift_comp_fst_snd] using h

/-- Local orbit extensions glue to an actual extension on the whole test scheme. -/
theorem exists_orbitExtension_of_openCover {T : Over S}
    (𝒰 : Scheme.OpenCover.{u} T.left) (g : T ⟶ G.X)
    (e : ∀ i, coverObj 𝒰 i ⊗ AffineLine.scheme S ⟶ G.X)
    (he : ∀ i, IsOrbitExtension χ (coverMap 𝒰 i ≫ g) (e i)) :
    ∃ e₀ : T ⊗ AffineLine.scheme S ⟶ G.X,
      IsOrbitExtension χ g e₀ ∧
        ∀ i, (coverMap 𝒰 i ▷ AffineLine.scheme S) ≫ e₀ = e i := by
  obtain ⟨e₀, hre⟩ := exists_tensor_glue 𝒰 e
    (orbitExtension_compatible χ 𝒰 g e he)
  refine ⟨e₀, ?_, hre⟩
  apply tensor_hom_ext 𝒰
  intro i
  rw [← whisker_exchange_assoc, hre i, he i, whiskerRight_orbit]

/-- Existence of an orbit extension is Zariski local on arbitrary test schemes. -/
theorem parabolic_isZariskiLocal : IsZariskiLocal (parabolic χ) := by
  intro T 𝒰 g
  constructor
  · intro hg i
    exact (parabolic χ).comp_mem (coverMap 𝒰 i) hg
  · intro hg
    choose e he using hg
    obtain ⟨e₀, hglobal, _⟩ := exists_orbitExtension_of_openCover χ 𝒰 g e he
    exact ⟨e₀, hglobal⟩

/-- The identity-limit condition is Zariski local on arbitrary test schemes. -/
theorem unipotent_isZariskiLocal : IsZariskiLocal (unipotent χ) := by
  intro T 𝒰 g
  constructor
  · intro hg i
    exact (unipotent χ).comp_mem (coverMap 𝒰 i) hg
  · intro hg
    choose e he hzero using hg
    obtain ⟨e₀, hglobal, hre⟩ := exists_orbitExtension_of_openCover χ 𝒰 g e he
    refine ⟨e₀, hglobal, ?_⟩
    apply Over.OverMorphism.ext
    apply 𝒰.hom_ext
    intro i
    have hi := congrArg evalZero (hre i)
    rw [evalZero_whiskerRight, hzero i] at hi
    have h : coverMap 𝒰 i ≫ evalZero e₀ =
        coverMap 𝒰 i ≫ (1 : T ⟶ G.X) := by
      simpa only [MonObj.comp_one] using hi
    exact congrArg Over.Hom.left h

omit [IsSeparated G.X.hom] in
/-- Constancy of the orbit is Zariski local on arbitrary test schemes. -/
theorem centralizer_isZariskiLocal : IsZariskiLocal (centralizer χ) := by
  intro T 𝒰 g
  constructor
  · intro hg i
    exact (centralizer χ).comp_mem (coverMap 𝒰 i) hg
  · intro hg
    apply tensor_hom_ext 𝒰
    intro i
    rw [whiskerRight_orbit, whiskerRight_fst_assoc]
    exact hg i

end Langlands.GroupScheme.DynamicLocality
