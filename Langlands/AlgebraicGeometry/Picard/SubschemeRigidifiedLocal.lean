import Langlands.AlgebraicGeometry.Picard.SubschemeRigidifiedClasses
import Langlands.AlgebraicGeometry.Picard.FinitePointsGeneratingSection

/-! # Line bundles can be rigidified along a finite morphism near every point -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard.SubschemeRigidification

open Langlands.SchemeModule

variable {S X Z : Scheme.{u}} (f : X ⟶ S) (g : Z ⟶ S) (z : Z ⟶ X) (hz : z ≫ f = g)

/-- If `g` is finite, every line bundle on `T ×_S X` admits a rigidification along
`z` after restriction to an open neighbourhood of any given point of `T`. -/
theorem exists_open_rigidification [IsFinite g] (T : Over S)
    (L : LineBundle ((relativeSpace f).obj T)) (t : T.left) :
    ∃ (W : Over S) (ι : W ⟶ T), IsOpenImmersion ι.left ∧ t ∈ Set.range ι.left ∧
      ∃ q : Classes f g z hz W, forgetClasses f g z hz W q =
        RelativePicard.classOf f W ((LineBundle.pullback ((relativeSpace f).map ι)).obj L) := by
  classical
  obtain ⟨T₀, hT₀, htT₀, -⟩ : ∃ T₀ : T.left.Opens, IsAffineOpen T₀ ∧ t ∈ T₀ ∧ T₀ ≤ ⊤ :=
    Opens.isBasis_iff_nbhd.mp T.left.isBasis_affineOpens (show t ∈ (⊤ : T.left.Opens) from trivial)
  have : IsAffine T₀.toScheme := hT₀
  let T₀' : Over S := Over.mk (T₀.ι ≫ T.hom)
  let ι₀ : T₀' ⟶ T := Over.homMk T₀.ι
  let L₀ := (LineBundle.pullback ((relativeSpace f).map ι₀)).obj L
  let N := (LineBundle.pullback ((zRel f g z hz).app T₀')).obj L₀
  let p : (relativeSpace g).obj T₀' ⟶ T₀.toScheme := pullback.fst T₀'.hom g
  have hYaff : IsAffine (pullback (T₀.ι ≫ T.hom) g) := inferInstance
  have : IsAffine ((relativeSpace g).obj T₀') := hYaff
  have : IsFinite p := inferInstanceAs (IsFinite (pullback.fst T₀'.hom g))
  obtain ⟨W, σ, htW, hle⟩ :=
    FinitePointsGeneratingSection.exists_nbhd_le_trivializationOpen p N ⟨t, htT₀⟩
  let W' : Over S := Over.mk (W.ι ≫ T₀'.hom)
  let ιW : W' ⟶ T₀' := Over.homMk W.ι
  have hrange : Set.range ((relativeSpace g).map ιW) ⊆
      (trivializationOpen N.obj σ : Set _) := by
    rintro _ ⟨v, rfl⟩
    apply hle
    have hnat := (relativeProjection g).naturality ιW
    change (relativeSpace g).map ιW ≫ p = pullback.fst W'.hom g ≫ W.ι at hnat
    change p ((relativeSpace g).map ιW v) ∈ W
    rw [← Scheme.Hom.comp_apply, hnat, Scheme.Hom.comp_apply]
    exact (pullback.fst W'.hom g v).2
  obtain ⟨e⟩ := FinitePointsGeneratingSection.nonempty_pullback_iso_of_le_trivializationOpen
    N σ _ hrange
  let ε := (zRel f g z hz).app W'
  have heq : ε ≫ (relativeSpace f).map (ιW ≫ ι₀) =
      (relativeSpace g).map ιW ≫ ((zRel f g z hz).app T₀' ≫ (relativeSpace f).map ι₀) := by
    rw [Functor.map_comp, ← Category.assoc, ← (zRel f g z hz).naturality ιW, Category.assoc]
  let i₁ := (Scheme.Modules.pullbackComp ε ((relativeSpace f).map (ιW ≫ ι₀))).app L.obj
  let i₂ := (Scheme.Modules.pullbackCongr heq).app L.obj
  let i₃ := ((Scheme.Modules.pullbackComp ((relativeSpace g).map ιW)
    ((zRel f g z hz).app T₀' ≫ (relativeSpace f).map ι₀)).app L.obj).symm
  let i₄ := (Scheme.Modules.pullback ((relativeSpace g).map ιW)).mapIso
    ((Scheme.Modules.pullbackComp ((zRel f g z hz).app T₀') ((relativeSpace f).map ι₀)).app
      L.obj).symm
  let α := (i₁ ≪≫ i₂ ≪≫ i₃ ≪≫ i₄ ≪≫ e).symm
  refine ⟨W', ιW ≫ ι₀, ?_, ?_, ⟨classOf f g z hz
    (RigidifiedLineBundle.ofLineBundle
      ((LineBundle.pullback ((relativeSpace f).map (ιW ≫ ι₀))).obj L) α), rfl⟩⟩
  · change IsOpenImmersion (W.ι ≫ T₀.ι)
    infer_instance
  · exact ⟨⟨⟨t, htT₀⟩, htW⟩, rfl⟩

end Langlands.AlgebraicGeometry.Picard.SubschemeRigidification

namespace Langlands.AlgebraicGeometry.Picard

open SubschemeRigidification

/-- For a finite morphism `g : Z ⟶ S` and `z : Z ⟶ X` over `S`, every line bundle on
`T ×_S X` admits a rigidification along `T ×_S Z ⟶ T ×_S X` after restriction to an open
neighbourhood of any given point of any test scheme `T`. -/
def OpenSubschemeRigidificationStatement : Prop :=
  ∀ (S X Z : Scheme.{u}) (f : X ⟶ S) (g : Z ⟶ S) (z : Z ⟶ X) (hz : z ≫ f = g) [IsFinite g]
    (T : Over S) (L : LineBundle ((relativeSpace f).obj T)) (t : T.left),
    ∃ (W : Over S) (ι : W ⟶ T), IsOpenImmersion ι.left ∧ t ∈ Set.range ι.left ∧
      ∃ q : Classes f g z hz W, forgetClasses f g z hz W q =
        RelativePicard.classOf f W ((LineBundle.pullback ((relativeSpace f).map ι)).obj L)

theorem openSubschemeRigidification : OpenSubschemeRigidificationStatement.{u} :=
  fun _ _ _ f g z hz _ T L t ↦ exists_open_rigidification f g z hz T L t

end Langlands.AlgebraicGeometry.Picard
