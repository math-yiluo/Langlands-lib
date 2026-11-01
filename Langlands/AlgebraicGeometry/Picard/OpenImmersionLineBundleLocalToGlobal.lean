import Langlands.AlgebraicGeometry.Picard.LineBundleAtlasEnlargement
import Langlands.AlgebraicGeometry.Picard.AffineOpenImmersionLineBundleExtensionStatement
import Mathlib.RingTheory.UniqueFactorizationDomain.Basic

/-! # From affine extension to arbitrary targets -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard

namespace OpenImmersionLineBundleLocalToGlobal

/-- Affine extension produces a compatible trivial chart near every target point. -/
lemma exists_compatible_chart
    (hAff : AffineOpenImmersionLineBundleExtensionStatement.{u})
    {X : Scheme.{u}} [IsLocallyNoetherian X]
    {V : Scheme.{u}} (v : V ⟶ X) [IsOpenImmersion v]
    (hfac : ∀ x : X, x ∉ Set.range v →
      UniqueFactorizationMonoid (X.presheaf.stalk x))
    (L : LineBundle V) (x : X) :
    ∃ T : X.Opens, x ∈ T ∧
      Nonempty ((Scheme.Modules.pullback (pullback.fst v T.ι)).obj L.obj ≅
        (Scheme.Modules.pullback (pullback.snd v T.ι)).obj
          (LineBundle.trivial T.toScheme).obj) := by
  obtain ⟨W, hW, hxW, _⟩ :=
    exists_isAffineOpen_mem_and_subset (show x ∈ (⊤ : X.Opens) from trivial)
  let : IsAffine W.toScheme := hW
  let a := pullback.fst v W.ι
  let b := pullback.snd v W.ι
  have hfacW : ∀ y : W.toScheme, y ∉ Set.range b →
      UniqueFactorizationMonoid (W.toScheme.presheaf.stalk y) := by
    intro y hy
    have hyv : W.ι y ∉ Set.range v := by
      intro hyv
      apply hy
      change y ∈ Set.range (pullback.snd v W.ι)
      rw [IsOpenImmersion.range_pullbackSnd v W.ι]
      exact hyv
    exact ((asIso (W.ι.stalkMap y)).commRingCatIsoToRingEquiv).toMulEquiv
      |>.uniqueFactorizationMonoid (hfac (W.ι y) hyv)
  obtain ⟨E, ⟨e⟩⟩ := hAff W.toScheme (pullback v W.ι) b hfacW
    ((LineBundle.pullback a).obj L)
  obtain ⟨U, hyU, ⟨eU⟩⟩ := E.property ⟨x, hxW⟩
  let f := U.ι ≫ W.ι
  let T := f.opensRange
  let t : T.toScheme ⟶ W.toScheme := f.isoOpensRange.inv ≫ U.ι
  have ht : t ≫ W.ι = T.ι := by
    dsimp only [t, T, f]
    rw [Category.assoc, Scheme.Hom.isoOpensRange_inv_comp]
  have hxT : x ∈ T := by
    exact ⟨⟨⟨x, hxW⟩, hyU⟩, rfl⟩
  let eT : (Scheme.Modules.pullback t).obj E.obj ≅
      (LineBundle.trivial T.toScheme).obj :=
    ((Scheme.Modules.pullbackComp f.isoOpensRange.inv U.ι).app E.obj).symm ≪≫
      (Scheme.Modules.pullback f.isoOpensRange.inv).mapIso
        (((Scheme.Modules.restrictFunctorIsoPullback U.ι).app E.obj).symm ≪≫ eU) ≪≫
          Langlands.Scheme.Modules.pullbackUnitIso f.isoOpensRange.inv
  let p := pullback.fst v T.ι
  let q := pullback.snd v T.ι
  have hpq : p ≫ v = (q ≫ t) ≫ W.ι := by
    rw [Category.assoc, ht]
    exact pullback.condition
  let r : pullback v T.ι ⟶ pullback v W.ι := pullback.lift p (q ≫ t) hpq
  have hra : r ≫ a = p := pullback.lift_fst _ _ _
  have hrb : r ≫ b = q ≫ t := pullback.lift_snd _ _ _
  refine ⟨T, hxT, ⟨?_⟩⟩
  exact (Langlands.Scheme.Modules.compIso r a p hra L.obj).symm ≪≫
    (Scheme.Modules.pullback r).mapIso e.symm ≪≫
      Langlands.Scheme.Modules.squarePullbackIso t r q b hrb E.obj ≪≫
        (Scheme.Modules.pullback q).mapIso eT

/-- The original bundle together with every trivial open chart, a small family. -/
def chartFamily {X Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]
    (D : LineBundle Y) : LineBundleChartFamily X where
  Index := Option X.Opens
  source
    | none => Y
    | some U => U.toScheme
  map
    | none => j
    | some U => U.ι
  isOpen i := by cases i <;> infer_instance
  bundle
    | none => D
    | some U => LineBundle.trivial U.toScheme

/-- Any individual chart is realized by its own actual line bundle. -/
def singletonRealization {X : Scheme.{u}} (F : LineBundleChartFamily X) (i₀ : F.Index) :
    F.CommonSource {i₀} where
  space := F.source i₀
  into := F.map i₀
  mono := inferInstance
  module := (F.bundle i₀).obj
  chart i := eqToHom (congrArg F.source (Set.mem_singleton_iff.mp i.property))
  fac i := by
    rcases i with ⟨i, hi⟩
    have hi' : i = i₀ := Set.mem_singleton_iff.mp hi
    subst i
    simp
  comparison i := by
    rcases i with ⟨i, hi⟩
    have hi' : i = i₀ := Set.mem_singleton_iff.mp hi
    subst i
    exact (Scheme.Modules.pullbackId _).app _

open Langlands.CategoryTheory.StrictCocycleAtlas

/-- The distinguished original chart starts a good strict atlas. -/
lemma exists_good_atlas {X : Scheme.{u}} (F : LineBundleChartFamily X) (i₀ : F.Index) :
    ∃ S : Set F.AtlasLabel, F.GoodAtlas i₀ S := by
  let R := singletonRealization F i₀
  exact ⟨graph {i₀} R.transition,
    graph_good {i₀} R.transition (Set.mem_singleton i₀) R.tripleCompatible⟩

/-- A maximal atlas contains trivial charts covering the entire target. -/
lemma maximal_region_eq_top
    (hAff : AffineOpenImmersionLineBundleExtensionStatement.{u})
    {X : Scheme.{u}} [IsLocallyNoetherian X]
    {Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]
    (hfac : ∀ x : X, x ∉ Set.range j →
      UniqueFactorizationMonoid (X.presheaf.stalk x))
    (D : LineBundle Y) {S : Set (chartFamily j D).AtlasLabel}
    (hm : Maximal ((chartFamily j D).GoodAtlas none) S) :
    (chartFamily j D).region (domain S) = ⊤ := by
  let F := chartFamily j D
  let R := F.atlasRealization hm.1
  have : IsOpenImmersion R.into := by
    dsimp only [R, LineBundleChartFamily.atlasRealization,
      LineBundleChartFamily.realization]
    infer_instance
  let L : LineBundle R.space := ⟨R.module, (F.glue _ _).property⟩
  have hj : Set.range j ⊆ Set.range R.into := by
    change Set.range (F.map none) ⊆ Set.range (F.region (domain S)).ι
    rw [Scheme.Opens.range_ι]
    exact F.range_le_region ⟨none, hm.1.1⟩
  have hfacR : ∀ x : X, x ∉ Set.range R.into →
      UniqueFactorizationMonoid (X.presheaf.stalk x) :=
    fun x hx ↦ hfac x (fun hxj ↦ hx (hj hxj))
  apply top_unique
  intro x _
  obtain ⟨T, hxT, ⟨φ⟩⟩ := exists_compatible_chart hAff R.into hfacR L x
  have hT : some T ∈ domain S := F.maximal_contains_chart hm (some T) φ
  exact F.range_le_region ⟨some T, hT⟩ ⟨⟨x, hxT⟩, rfl⟩

/-- Affine-target extension suffices for the unchanged arbitrary-target statement. -/
theorem of_affine (hAff : AffineOpenImmersionLineBundleExtensionStatement.{u}) :
    OpenImmersionLineBundleExtensionStatement.{u} := by
  intro X _ Y j _ hfac D
  let F := chartFamily j D
  obtain ⟨S₀, hS₀⟩ := exists_good_atlas F none
  obtain ⟨S, _, hm⟩ := exists_maximal_extension hS₀
  have htop : F.region (domain S) = ⊤ := maximal_region_eq_top hAff j hfac D hm
  let R := F.atlasRealization hm.1
  have : IsIso R.into := by
    change IsIso (F.region (domain S)).ι
    rw [htop]
    change IsIso X.topIso.hom
    infer_instance
  let i := asIso R.into
  let L : LineBundle R.space := ⟨R.module, (F.glue _ _).property⟩
  let E := (LineBundle.pullback i.inv).obj L
  let e : (Scheme.Modules.pullback R.into).obj E.obj ≅ R.module :=
    (Scheme.Modules.pullbackComp i.hom i.inv).app L.obj ≪≫
      (Scheme.Modules.pullbackCongr i.hom_inv_id).app L.obj ≪≫
        (Scheme.Modules.pullbackId R.space).app L.obj
  let i₀ : domain S := ⟨none, hm.1.1⟩
  exact ⟨E, ⟨(Langlands.Scheme.Modules.compIso (R.chart i₀) R.into j
      (R.fac i₀) E.obj).symm ≪≫
    (Scheme.Modules.pullback (R.chart i₀)).mapIso e ≪≫ R.comparison i₀⟩⟩

end OpenImmersionLineBundleLocalToGlobal

end Langlands.AlgebraicGeometry.Picard
