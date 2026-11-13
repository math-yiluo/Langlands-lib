import Langlands.GroupScheme.HomScheme.AdmissibleClosedRepresentability
import Langlands.GroupScheme.SmoothNormalizer.Global
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-! # Gluing finitely presented closed representatives of subgroup functors -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.SubgroupFunctor

variable {S : Scheme.{u}} {G : GroupScheme S} (F : SubgroupFunctor G)

/-- A Zariski-local subgroup with finitely presented closed representatives
over a base cover has a finitely presented closed representative globally. -/
theorem exists_closed_finitelyPresented_of_openCover (hF : IsZariskiLocal F)
    (𝒰 : Scheme.OpenCover.{u} S)
    (h : ∀ i, ∃ (H : GroupScheme (𝒰.X i))
      (j : H ⟶ (GroupScheme.baseChange (𝒰.f i)).obj G),
      IsClosedImmersion j.hom.hom.left ∧
        LocallyOfFinitePresentation j.hom.hom.left ∧
          (F.baseChange (𝒰.f i)).IsRepresentedBy j) :
    ∃ (H : GroupScheme S) (j : H ⟶ G),
      IsClosedImmersion j.hom.hom.left ∧
        LocallyOfFinitePresentation j.hom.hom.left ∧ F.IsRepresentedBy j := by
  choose H j hjc hjl hjr using h
  let c : ∀ i, (H i).X.left ⟶ pullback G.X.hom (𝒰.f i) :=
    fun i => (j i).hom.hom.left
  have : ∀ i, IsClosedImmersion (c i) := hjc
  let 𝒱 : G.X.left.OpenCover := 𝒰.pullback₁ G.X.hom
  have hchart (i : 𝒰.I₀) :
      Scheme.ClosedSubschemeGluing.IsChart (fun _ x => F.schemeCondition x)
        (𝒱.f i) (c i) := by
    intro Z z
    exact (F.schemeCondition_baseChange_iff (𝒰.f i) z).trans
      (schemeCondition_iff_exists_of_isRepresentedBy
        (F.baseChange (𝒰.f i)) (hjr i) z)
  obtain ⟨L₀, c₀, hc₀, hfac⟩ :=
    Scheme.ClosedSubschemeGluing.exists_isClosedImmersion
      (P := fun _ x => F.schemeCondition x)
      (fun _ _ a z hz => F.schemeCondition_comp z a hz)
      (fun i : 𝒰.I₀ => 𝒱.f i) c hchart
      (fun x => ⟨𝒱.idx x, 𝒱.covers x⟩)
      (fun Z z hz => by
        choose U hU hPU using hz
        let 𝒲 : Z.OpenCover := Scheme.Cover.mkOfCovers Z
          (fun p => (U p : Scheme.{u})) (fun p => (U p).ι)
          (fun p => ⟨p, ⟨p, hU p⟩, rfl⟩)
        exact (F.schemeCondition_iff_openCover hF z 𝒲).mpr hPU)
  have : IsClosedImmersion c₀ := hc₀
  have hlfp : LocallyOfFinitePresentation c₀ := by
    have : IsZariskiLocalAtTarget @LocallyOfFinitePresentation :=
      HasRingHomProperty.instIsZariskiLocalAtTarget _
    refine IsZariskiLocalAtTarget.of_openCover 𝒱 fun i => ?_
    have : IsClosedImmersion (c i) := hjc i
    have : LocallyOfFinitePresentation (c i) := hjl i
    obtain ⟨e, he⟩ := SmoothNormalizer.exists_iso_pullback_chart
      (c := c i) hfac (hchart i)
    change LocallyOfFinitePresentation (pullback.snd c₀ (𝒱.f i))
    rw [← he]
    infer_instance
  let i₀ : Over.mk (c₀ ≫ G.X.hom) ⟶ G.X := Over.homMk c₀ rfl
  have : Mono i₀ := Over.mono_of_mono_left _
  have hi₀ : ∀ (T : Over S) (x : T ⟶ G.X),
      x ∈ F.carrier T ↔
        ∃ y : T ⟶ Over.mk (c₀ ≫ G.X.hom), y ≫ i₀ = x := by
    intro T x
    rw [← F.schemeCondition_iff_mem x, hfac x.left]
    constructor
    · rintro ⟨a, ha⟩
      refine ⟨Over.homMk a ?_, Over.OverMorphism.ext ha⟩
      change a ≫ c₀ ≫ G.X.hom = T.hom
      rw [← Category.assoc, ha, Over.w x]
    · rintro ⟨y, hy⟩
      exact ⟨y.left, congrArg CommaMorphism.left hy⟩
  have hj₀ : (F.representingHom i₀ hi₀).hom.hom.left = c₀ := by
    rw [representingHom_hom]
    rfl
  refine ⟨_, F.representingHom i₀ hi₀, ?_, ?_,
    F.isRepresentedBy_representingHom i₀ hi₀⟩
  · rw [hj₀]
    exact hc₀
  · rw [hj₀]
    exact hlfp

end Langlands.GroupScheme.SubgroupFunctor
