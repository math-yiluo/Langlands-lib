import Langlands.AlgebraicGeometry.ProjectiveBundle.CocycleGluing
import Langlands.AlgebraicGeometry.LinearSystem.LinearActionTwistNaturality

/-! # Coherent degree-one twists on projective coordinate charts -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.SchemeModule Langlands.AlgebraicGeometry.Picard

universe u

namespace Langlands.AlgebraicGeometry.LinearSystem

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Compose actual pullback comparisons, together with their section formula. -/
def compositePullbackCoordinateIso {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (L : X.Modules) (M : Y.Modules) (N : Z.Modules)
    {ι : Type*} (s : ι → GlobalSections N) (t : ι → GlobalSections M)
    (r : ι → GlobalSections L)
    (β : (Scheme.Modules.pullback g).obj N ≅ M)
    (hβ : ∀ i, β.hom.app ⊤ (pullbackSection g N (s i)) = t i)
    (αdata : {α : (Scheme.Modules.pullback f).obj M ≅ L //
      ∀ i, α.hom.app ⊤ (pullbackSection f M (t i)) = r i}) :
    {γ : (Scheme.Modules.pullback (f ≫ g)).obj N ≅ L //
      ∀ i, γ.hom.app ⊤ (pullbackSection (f ≫ g) N (s i)) = r i} := by
  let α := αdata.val
  have hα := αdata.property
  refine ⟨(Scheme.Modules.pullbackComp f g).symm.app N ≪≫
    (Scheme.Modules.pullback f).mapIso β ≪≫ α, ?_⟩
  intro i
  change ((Scheme.Modules.pullbackComp f g).inv.app N ≫
    (Scheme.Modules.pullback f).map β.hom ≫ α.hom).app ⊤ _ = _
  rw [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply,
    pullbackComp_inv_coordinate]
  exact (pullbackMap_comp_coordinate f β.hom α.hom (pullbackSection g N (s i))).trans
    (by rw [hβ, hα])

/-- A covering family of frames detects the comparison law between three schemes. -/
lemma pullback_comparison_comp_between {X Y Z : Scheme.{u}}
    {L : X.Modules} {M : Y.Modules} {N : Z.Modules}
    (hN : IsLocallyFreeRankOne N) {ι : Type*} (s : ι → GlobalSections N)
    (hs : (⨆ i, trivializationOpen N (s i)) = ⊤)
    (a : X ⟶ Y) (b : Y ⟶ Z) (c : X ⟶ Z) (w : a ≫ b = c)
    (α : (Scheme.Modules.pullback a).obj M ⟶ L)
    (β : (Scheme.Modules.pullback b).obj N ⟶ M)
    (γ : (Scheme.Modules.pullback c).obj N ⟶ L)
    (h : ∀ i, α.app ⊤ (pullbackSection a M (β.app ⊤ (pullbackSection b N (s i)))) =
      γ.app ⊤ (pullbackSection c N (s i))) :
    (Scheme.Modules.pullback a).map β ≫ α =
      (Scheme.Modules.pullbackComp a b).hom.app N ≫
        (Scheme.Modules.pullbackCongr w).hom.app N ≫ γ := by
  have hs' := frameCover_pullback hN s hs b
  have hs'' := frameCover_pullback (hN.pullback b)
    (fun i ↦ pullbackSection b N (s i)) hs' a
  apply hom_ext_of_generating_sections
    (fun i ↦ pullbackSection a ((Scheme.Modules.pullback b).obj N)
      (pullbackSection b N (s i))) hs''
  intro i
  exact (pullbackMap_comp_coordinate a β α (pullbackSection b N (s i))).trans
    ((h i).trans (pullbackComp_comparison_coordinate a b w N γ (s i)).symm)

/-- A coordinate-preserving sheaf map over an identity arrow is the canonical map. -/
lemma pullback_comparison_id_hom {X : Scheme.{u}} {M : X.Modules}
    (hM : IsLocallyFreeRankOne M) {ι : Type*} (s : ι → GlobalSections M)
    (hs : (⨆ i, trivializationOpen M (s i)) = ⊤)
    (f : X ⟶ X) (w : f = 𝟙 X)
    (α : (Scheme.Modules.pullback f).obj M ⟶ M)
    (hα : ∀ i, α.app ⊤ (pullbackSection f M (s i)) = s i) :
    α = (Scheme.Modules.pullbackCongr w).hom.app M ≫
      (Scheme.Modules.pullbackId X).hom.app M := by
  apply hom_ext_of_generating_sections _ (frameCover_pullback hM s hs f)
  intro i
  exact (hα i).trans
    ((pullbackCongr_trans_coordinate w M ((Scheme.Modules.pullbackId X).app M) (s i)).trans
      (pullbackId_coordinate M (s i))).symm

end Langlands.AlgebraicGeometry.LinearSystem

namespace Langlands.AlgebraicGeometry.ProjectiveBundle.CoordinateCocycle

open RelativeProjectiveSpace LinearSystem

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {S : Scheme.{u}} {n : ℕ} {𝒰 : S.OpenCover}
  [hcat : Category* 𝒰.I₀] [hdir : 𝒰.LocallyDirected] (d : CoordinateCocycle n 𝒰)

/-- The actual twist comparison on a projective chart transition, with its coordinates. -/
def chartTwistData {i j : 𝒰.I₀} (hij : i ⟶ j) :
    {φ : (Scheme.Modules.pullback (d.chartFunctor.map hij)).obj
        (RelativeProjectiveSpace.twistOne (𝒰.X j) n).obj ≅
        (RelativeProjectiveSpace.twistOne (𝒰.X i) n).obj //
      ∀ k, φ.hom.app ⊤
        (pullbackSection (d.chartFunctor.map hij)
          (RelativeProjectiveSpace.twistOne (𝒰.X j) n).obj
          (RelativeProjectiveSpace.twistOneCoordinate (𝒰.X j) n k)) =
        changedRelativeProjectiveCoordinates (𝒰.X i).toSpecΓ (d.transition hij) k} :=
  compositePullbackCoordinateIso
    (globalLinearAction n (d.transition hij)) (map n (𝒰.trans hij))
    (RelativeProjectiveSpace.twistOne (𝒰.X i) n).obj
    (RelativeProjectiveSpace.twistOne (𝒰.X i) n).obj
    (RelativeProjectiveSpace.twistOne (𝒰.X j) n).obj
    (RelativeProjectiveSpace.twistOneCoordinate (𝒰.X j) n)
    (RelativeProjectiveSpace.twistOneCoordinate (𝒰.X i) n)
    (changedRelativeProjectiveCoordinates (𝒰.X i).toSpecΓ (d.transition hij))
    ((LineBundle.forget _).mapIso (twistOnePullbackIso n (𝒰.trans hij)))
    (twistOnePullbackIso_coordinate n (𝒰.trans hij))
    (relativeLinearActionTwistData (𝒰.X i).toSpecΓ (d.transition hij))

/-- The actual pullback of O(1) along each twisted projective chart restriction. -/
def chartTwistIso {i j : 𝒰.I₀} (hij : i ⟶ j) :
    (Scheme.Modules.pullback (d.chartFunctor.map hij)).obj
        (RelativeProjectiveSpace.twistOne (𝒰.X j) n).obj ≅
      (RelativeProjectiveSpace.twistOne (𝒰.X i) n).obj :=
  (d.chartTwistData hij).val

/-- The transition comparison realizes precisely the prescribed coordinate change. -/
lemma chartTwistIso_coordinate {i j : 𝒰.I₀} (hij : i ⟶ j) (k : Fin (n + 1)) :
    (d.chartTwistIso hij).hom.app ⊤
        (pullbackSection (d.chartFunctor.map hij)
          (RelativeProjectiveSpace.twistOne (𝒰.X j) n).obj
          (RelativeProjectiveSpace.twistOneCoordinate (𝒰.X j) n k)) =
      changedRelativeProjectiveCoordinates (𝒰.X i).toSpecΓ (d.transition hij) k :=
  (d.chartTwistData hij).property k

/-- The identity law with explicitly identified chart objects. -/
lemma chartMap_id (i : 𝒰.I₀) :
    d.chartFunctor.map (𝟙 i) = 𝟙 (RelativeProjectiveSpace (𝒰.X i) n) :=
  d.chartFunctor.map_id i

/-- The composition law with explicitly identified chart objects. -/
lemma chartMap_comp {i j k : 𝒰.I₀} (hij : i ⟶ j) (hjk : j ⟶ k) :
    d.chartFunctor.map hij ≫ d.chartFunctor.map hjk = d.chartFunctor.map (hij ≫ hjk) :=
  (d.chartFunctor.map_comp hij hjk).symm

/-- The identity transition leaves the coordinate sections fixed. -/
lemma changedCoordinates_id (i : 𝒰.I₀) :
    changedRelativeProjectiveCoordinates (𝒰.X i).toSpecΓ (d.transition (𝟙 i)) =
      RelativeProjectiveSpace.twistOneCoordinate (𝒰.X i) n := by
  rw [d.transition_id]
  exact linearChangeSections_id (L := RelativeProjectiveSpace.twistOne (𝒰.X i) n)
    (RelativeProjectiveSpace.toBase (𝒰.X i) n ≫ (𝒰.X i).toSpecΓ)
    (RelativeProjectiveSpace.twistOneCoordinate (𝒰.X i) n)

/-- The identity transition comparison fixes each homogeneous coordinate. -/
lemma chartTwistIso_id_coordinate (i : 𝒰.I₀) (k : Fin (n + 1)) :
    (d.chartTwistIso (𝟙 i)).hom.app ⊤
        (pullbackSection (d.chartFunctor.map (𝟙 i))
          (RelativeProjectiveSpace.twistOne (𝒰.X i) n).obj
          (RelativeProjectiveSpace.twistOneCoordinate (𝒰.X i) n k)) =
      RelativeProjectiveSpace.twistOneCoordinate (𝒰.X i) n k :=
  (d.chartTwistIso_coordinate (𝟙 i) k).trans (congrFun (d.changedCoordinates_id i) k)

omit hcat hdir in
/-- The coordinate frame opens cover each actual projective chart. -/
lemma chartCoordinates_frameCover (i : 𝒰.I₀) :
    (⨆ k, trivializationOpen (RelativeProjectiveSpace.twistOne (𝒰.X i) n).obj
      (RelativeProjectiveSpace.twistOneCoordinate (𝒰.X i) n k)) = ⊤ := by
  simpa only [trivializationOpen_twistOneCoordinate] using iSup_coordinateOpen (𝒰.X i) n

omit hcat hdir in
/-- The relative twist is locally free of rank one. -/
lemma chartTwist_rankOne (i : 𝒰.I₀) :
    IsLocallyFreeRankOne (RelativeProjectiveSpace.twistOne (𝒰.X i) n).obj :=
  (RelativeProjectiveSpace.twistOne (𝒰.X i) n).property

/-- The identity criterion specialized to the concrete chart, with arbitrary comparison. -/
lemma chartTwist_id_criterion (i : 𝒰.I₀)
    (w : d.chartFunctor.map (𝟙 i) = 𝟙 (RelativeProjectiveSpace (𝒰.X i) n))
    (α : (Scheme.Modules.pullback (d.chartFunctor.map (𝟙 i))).obj
        (RelativeProjectiveSpace.twistOne (𝒰.X i) n).obj ⟶
      (RelativeProjectiveSpace.twistOne (𝒰.X i) n).obj)
    (hα : ∀ k, α.app ⊤ (pullbackSection (d.chartFunctor.map (𝟙 i))
      (RelativeProjectiveSpace.twistOne (𝒰.X i) n).obj
      (RelativeProjectiveSpace.twistOneCoordinate (𝒰.X i) n k)) =
        RelativeProjectiveSpace.twistOneCoordinate (𝒰.X i) n k) :
    α = (Scheme.Modules.pullbackCongr w).hom.app
          (RelativeProjectiveSpace.twistOne (𝒰.X i) n).obj ≫
        (Scheme.Modules.pullbackId (RelativeProjectiveSpace (𝒰.X i) n)).hom.app
          (RelativeProjectiveSpace.twistOne (𝒰.X i) n).obj := by
  exact pullback_comparison_id_hom
    (chartTwist_rankOne (𝒰 := 𝒰) i)
    (RelativeProjectiveSpace.twistOneCoordinate (𝒰.X i) n)
    (chartCoordinates_frameCover (𝒰 := 𝒰) i)
    (d.chartFunctor.map (𝟙 i)) w α hα

/-- The comparison over an identity chart arrow is the canonical identity pullback. -/
lemma chartTwistIso_id (i : 𝒰.I₀) :
    (d.chartTwistIso (𝟙 i)).hom =
      (Scheme.Modules.pullbackCongr (d.chartMap_id i)).hom.app
          (RelativeProjectiveSpace.twistOne (𝒰.X i) n).obj ≫
        (Scheme.Modules.pullbackId (RelativeProjectiveSpace (𝒰.X i) n)).hom.app
          (RelativeProjectiveSpace.twistOne (𝒰.X i) n).obj := by
  exact d.chartTwist_id_criterion i (d.chartMap_id i)
    (d.chartTwistIso (𝟙 i)).hom (d.chartTwistIso_id_coordinate i)

/-- The chart arrow respects both the projective base and its global-function coefficient map. -/
lemma chartMap_toSpecΓ {i j : 𝒰.I₀} (hij : i ⟶ j) :
    (RelativeProjectiveSpace.toBase (𝒰.X i) n ≫ (𝒰.X i).toSpecΓ) ≫
        Spec.map (CommRingCat.ofHom (𝒰.trans hij).appTop.hom) =
      d.chartFunctor.map hij ≫
        (RelativeProjectiveSpace.toBase (𝒰.X j) n ≫ (𝒰.X j).toSpecΓ) := by
  calc
    _ = RelativeProjectiveSpace.toBase (𝒰.X i) n ≫
        ((𝒰.X i).toSpecΓ ≫ Spec.map (𝒰.trans hij).appTop) := Category.assoc _ _ _
    _ = RelativeProjectiveSpace.toBase (𝒰.X i) n ≫
        (𝒰.trans hij ≫ (𝒰.X j).toSpecΓ) :=
      congrArg (fun h ↦ RelativeProjectiveSpace.toBase (𝒰.X i) n ≫ h)
        (Scheme.toSpecΓ_naturality (𝒰.trans hij)).symm
    _ = (RelativeProjectiveSpace.toBase (𝒰.X i) n ≫ 𝒰.trans hij) ≫
        (𝒰.X j).toSpecΓ := (Category.assoc _ _ _).symm
    _ = (d.chartFunctor.map hij ≫ RelativeProjectiveSpace.toBase (𝒰.X j) n) ≫
        (𝒰.X j).toSpecΓ :=
      congrArg (fun h ↦ h ≫ (𝒰.X j).toSpecΓ) (d.chartFunctor_map_toBase hij).symm
    _ = _ := Category.assoc _ _ _

/-- The comparison for a composite chart arrow has the composite coordinate formula. -/
lemma chartTwistIso_comp_coordinate {i j k : 𝒰.I₀} (hij : i ⟶ j) (hjk : j ⟶ k)
    (l : Fin (n + 1)) :
    (d.chartTwistIso (hij ≫ hjk)).hom.app ⊤
        (pullbackSection (d.chartFunctor.map (hij ≫ hjk))
          (RelativeProjectiveSpace.twistOne (𝒰.X k) n).obj
          (RelativeProjectiveSpace.twistOneCoordinate (𝒰.X k) n l)) =
      linearChangeSections (L := RelativeProjectiveSpace.twistOne (𝒰.X i) n)
        (RelativeProjectiveSpace.toBase (𝒰.X i) n ≫ (𝒰.X i).toSpecΓ)
        (RelativeProjectiveSpace.twistOneCoordinate (𝒰.X i) n)
        ((coordinatePullback n (𝒰.trans hij) (d.transition hjk)).toLinearMap.comp
          (d.transition hij).toLinearMap) l := by
  rw [d.chartTwistIso_coordinate, d.transition_comp]
  rfl

/-- The cross-chart composition criterion, with arbitrary comparison maps. -/
lemma chartTwist_comp_criterion {i j k : 𝒰.I₀} (hij : i ⟶ j) (hjk : j ⟶ k)
    (α : (Scheme.Modules.pullback (d.chartFunctor.map hij)).obj
      (RelativeProjectiveSpace.twistOne (𝒰.X j) n).obj ⟶
      (RelativeProjectiveSpace.twistOne (𝒰.X i) n).obj)
    (β : (Scheme.Modules.pullback (d.chartFunctor.map hjk)).obj
      (RelativeProjectiveSpace.twistOne (𝒰.X k) n).obj ⟶
      (RelativeProjectiveSpace.twistOne (𝒰.X j) n).obj)
    (γ : (Scheme.Modules.pullback (d.chartFunctor.map (hij ≫ hjk))).obj
      (RelativeProjectiveSpace.twistOne (𝒰.X k) n).obj ⟶
      (RelativeProjectiveSpace.twistOne (𝒰.X i) n).obj)
    (hα : ∀ l, α.app ⊤ (pullbackSection (d.chartFunctor.map hij)
      (RelativeProjectiveSpace.twistOne (𝒰.X j) n).obj
      (RelativeProjectiveSpace.twistOneCoordinate (𝒰.X j) n l)) =
        changedRelativeProjectiveCoordinates (𝒰.X i).toSpecΓ (d.transition hij) l)
    (hβ : ∀ l, β.app ⊤ (pullbackSection (d.chartFunctor.map hjk)
      (RelativeProjectiveSpace.twistOne (𝒰.X k) n).obj
      (RelativeProjectiveSpace.twistOneCoordinate (𝒰.X k) n l)) =
        changedRelativeProjectiveCoordinates (𝒰.X j).toSpecΓ (d.transition hjk) l)
    (hγ : ∀ l, γ.app ⊤ (pullbackSection (d.chartFunctor.map (hij ≫ hjk))
      (RelativeProjectiveSpace.twistOne (𝒰.X k) n).obj
      (RelativeProjectiveSpace.twistOneCoordinate (𝒰.X k) n l)) =
      linearChangeSections (L := RelativeProjectiveSpace.twistOne (𝒰.X i) n)
        (RelativeProjectiveSpace.toBase (𝒰.X i) n ≫ (𝒰.X i).toSpecΓ)
        (RelativeProjectiveSpace.twistOneCoordinate (𝒰.X i) n)
        ((coordinatePullback n (𝒰.trans hij) (d.transition hjk)).toLinearMap.comp
          (d.transition hij).toLinearMap) l) :
    (Scheme.Modules.pullback (d.chartFunctor.map hij)).map β ≫ α =
      (Scheme.Modules.pullbackComp (d.chartFunctor.map hij)
        (d.chartFunctor.map hjk)).hom.app
        (RelativeProjectiveSpace.twistOne (𝒰.X k) n).obj ≫
      (Scheme.Modules.pullbackCongr (d.chartMap_comp hij hjk)).hom.app
        (RelativeProjectiveSpace.twistOne (𝒰.X k) n).obj ≫ γ := by
  have H := pullback_comparison_comp_between
    (X := d.chartFunctor.obj i)
    (Y := d.chartFunctor.obj j)
    (Z := d.chartFunctor.obj k)
    (L := (RelativeProjectiveSpace.twistOne (𝒰.X i) n).obj)
    (M := (RelativeProjectiveSpace.twistOne (𝒰.X j) n).obj)
    (N := (RelativeProjectiveSpace.twistOne (𝒰.X k) n).obj)
    (chartTwist_rankOne (𝒰 := 𝒰) k)
    (RelativeProjectiveSpace.twistOneCoordinate (𝒰.X k) n)
    (chartCoordinates_frameCover (𝒰 := 𝒰) k)
    (d.chartFunctor.map hij) (d.chartFunctor.map hjk) (d.chartFunctor.map (hij ≫ hjk))
    (d.chartMap_comp hij hjk) α β γ
  have h : ∀ l, α.app ⊤ (pullbackSection (d.chartFunctor.map hij)
      (RelativeProjectiveSpace.twistOne (𝒰.X j) n).obj
      (β.app ⊤ (pullbackSection (d.chartFunctor.map hjk)
        (RelativeProjectiveSpace.twistOne (𝒰.X k) n).obj
        (RelativeProjectiveSpace.twistOneCoordinate (𝒰.X k) n l)))) =
      γ.app ⊤ (pullbackSection (d.chartFunctor.map (hij ≫ hjk))
        (RelativeProjectiveSpace.twistOne (𝒰.X k) n).obj
        (RelativeProjectiveSpace.twistOneCoordinate (𝒰.X k) n l)) := by
    intro l
    rw [hβ, hγ]
    exact (pullback_comparison_linearChange_baseChange
      (L := RelativeProjectiveSpace.twistOne (𝒰.X j) n)
      (M := RelativeProjectiveSpace.twistOne (𝒰.X i) n)
      (RelativeProjectiveSpace.toBase (𝒰.X j) n ≫ (𝒰.X j).toSpecΓ)
      (RelativeProjectiveSpace.toBase (𝒰.X i) n ≫ (𝒰.X i).toSpecΓ)
      (RelativeProjectiveSpace.twistOneCoordinate (𝒰.X j) n)
      (changedRelativeProjectiveCoordinates (𝒰.X i).toSpecΓ (d.transition hij))
      (d.chartFunctor.map hij) (𝒰.trans hij).appTop.hom (d.chartMap_toSpecΓ hij)
      α hα (d.transition hjk).toLinearMap
      (coordinatePullback n (𝒰.trans hij) (d.transition hjk)).toLinearMap
      (fun l m ↦ (coordinatePullback_coeff n (𝒰.trans hij) (d.transition hjk) l m).symm) l).trans
      (congrFun (linearChangeSections_comp
        (L := RelativeProjectiveSpace.twistOne (𝒰.X i) n)
        (RelativeProjectiveSpace.toBase (𝒰.X i) n ≫ (𝒰.X i).toSpecΓ)
        (RelativeProjectiveSpace.twistOneCoordinate (𝒰.X i) n)
        (d.transition hij).toLinearMap
        (coordinatePullback n (𝒰.trans hij) (d.transition hjk)).toLinearMap) l)
  exact H h

/-- Actual twist comparisons compose with the canonical pullback composition comparison. -/
lemma chartTwistIso_comp {i j k : 𝒰.I₀} (hij : i ⟶ j) (hjk : j ⟶ k) :
    (Scheme.Modules.pullback (d.chartFunctor.map hij)).map (d.chartTwistIso hjk).hom ≫
        (d.chartTwistIso hij).hom =
      (Scheme.Modules.pullbackComp (d.chartFunctor.map hij)
        (d.chartFunctor.map hjk)).hom.app
        (RelativeProjectiveSpace.twistOne (𝒰.X k) n).obj ≫
      (Scheme.Modules.pullbackCongr (d.chartMap_comp hij hjk)).hom.app
        (RelativeProjectiveSpace.twistOne (𝒰.X k) n).obj ≫
      (d.chartTwistIso (hij ≫ hjk)).hom := by
  exact d.chartTwist_comp_criterion hij hjk
    (d.chartTwistIso hij).hom (d.chartTwistIso hjk).hom (d.chartTwistIso (hij ≫ hjk)).hom
    (d.chartTwistIso_coordinate hij) (d.chartTwistIso_coordinate hjk)
    (d.chartTwistIso_comp_coordinate hij hjk)

end Langlands.AlgebraicGeometry.ProjectiveBundle.CoordinateCocycle
