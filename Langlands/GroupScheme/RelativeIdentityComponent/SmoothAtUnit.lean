import Langlands.GroupScheme.Lie.SmoothOpenSubgroup
import Langlands.GroupScheme.ReducedBaseSmooth.Translation
import Langlands.GroupScheme.RelativeIdentityComponent.OpenSubgroup
import Langlands.GroupScheme.RelativeIdentityComponent.SmoothExistenceProof

/-! # Relative identity components for groups smooth along their unit -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.GroupScheme.RelativeIdentityComponent

open Langlands.GroupScheme.FiniteEtaleImage (liftOver liftOver_fac)
open Langlands.CategoryTheory.GroupObjectDescent

/-- Local smoothness descends at all image points of a smooth morphism whose
source is smooth over the base. -/
private theorem range_subset_smoothLocus_of_smooth_comp {X Y S : Scheme.{u}}
    (p : X ⟶ Y) (g : Y ⟶ S) [Smooth p] [Smooth (p ≫ g)]
    [LocallyOfFinitePresentation g] : Set.range p ⊆ g.smoothLocus := by
  rintro _ ⟨x, rfl⟩
  obtain ⟨U, hU, hxU, -⟩ :=
    exists_isAffineOpen_mem_and_subset (show p x ∈ (⊤ : Y.Opens) from trivial)
  obtain ⟨W, hW, hxW, hWU⟩ :=
    exists_isAffineOpen_mem_and_subset (show x ∈ p ⁻¹ᵁ U from hxU)
  let V : Y.Opens := ⟨p '' W, p.isOpenMap _ W.2⟩
  have hVU : V ≤ U := by
    rintro _ ⟨w, hw, rfl⟩
    exact hWU hw
  have : IsAffine U := hU
  have : QuasiSeparatedSpace V := (Y.homOfLE hVU).isOpenEmbedding.quasiSeparatedSpace
  have hWV : W ≤ p ⁻¹ᵁ V := fun w hw => ⟨w, hw, rfl⟩
  let q := p.resLE V W hWV
  have : IsAffine W := hW
  have : Smooth q := IsZariskiLocalAtSource.resLE hWV inferInstance
  have : Surjective q := by
    constructor
    rintro ⟨_, w, hw, rfl⟩
    refine ⟨⟨w, hw⟩, V.ι.isOpenEmbedding.injective ?_⟩
    change (q ≫ V.ι) ⟨w, hw⟩ = _
    rw [Scheme.Hom.resLE_comp_ι]
    rfl
  have : QuasiCompact q := quasiCompact_of_compactSpace q
  have : Smooth (q ≫ V.ι ≫ g) := by
    rw [← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc]
    infer_instance
  have : Smooth (V.ι ≫ g) :=
    Smooth.of_comp_of_smooth_of_surjective_of_locallyOfFinitePresentation q (V.ι ≫ g)
  have hV : V.ι ⁻¹ᵁ g.smoothLocus = ⊤ := by
    rw [Scheme.Hom.preimage_smoothLocus_eq]
    exact (V.ι ≫ g).smoothLocus_eq_top
  exact show (⟨p x, x, hxW, rfl⟩ : V) ∈ V.ι ⁻¹ᵁ g.smoothLocus from hV ▸ trivial

/-- If the smooth locus contains the unit, it carries the restricted group
structure and its open inclusion is a group homomorphism. -/
theorem exists_smoothLocus_openSubgroup {S : Scheme.{u}} (G : GroupScheme S)
    [LocallyOfFinitePresentation G.X.hom]
    (he : Set.range (unitSection G) ⊆ G.X.hom.smoothLocus) :
    ∃ (P : GroupScheme S) (j : P ⟶ G), Smooth P.X.hom ∧
      IsOpenImmersion j.hom.hom.left ∧ Set.range j.hom.hom.left = G.X.hom.smoothLocus := by
  let U := G.X.hom.smoothLocus
  let P : Over S := Over.mk (U.ι ≫ G.X.hom)
  let i : P ⟶ G.X := Over.homMk U.ι
  have hr : Set.range i.left = U := Scheme.Opens.range_ι _
  have : IsOpenImmersion i.left := inferInstanceAs (IsOpenImmersion U.ι)
  have : Mono i := Over.mono_of_mono_left _
  have hP : Smooth P.hom := by
    change Smooth (U.ι ≫ G.X.hom)
    rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← Scheme.Hom.preimage_smoothLocus_eq]
    exact Scheme.Opens.ι_preimage_self _
  let m₀ := (i ⊗ₘ i) ≫ μ[G.X]
  have : Smooth m₀.left := ReducedBaseSmooth.smooth_tensorHom_comp_mul G i
  have : Smooth (m₀.left ≫ G.X.hom) := by
    rw [Over.w, Over.tensorObj_hom]
    infer_instance
  have hm : Set.range m₀.left ⊆ Set.range i.left := by
    rw [hr]
    exact range_subset_smoothLocus_of_smooth_comp m₀.left G.X.hom
  let w₀ := i ≫ ι[G.X]
  have : IsIso (ι[G.X]).left := (Over.forget S).map_isIso (ι[G.X])
  have : IsOpenImmersion w₀.left :=
    inferInstanceAs (IsOpenImmersion (i.left ≫ (ι[G.X]).left))
  have : Smooth (w₀.left ≫ G.X.hom) := by rw [Over.w]; exact hP
  have hw : Set.range w₀.left ⊆ Set.range i.left := by
    rw [hr]
    exact range_subset_smoothLocus_of_smooth_comp w₀.left G.X.hom
  have he' : Set.range η[G.X].left ⊆ Set.range i.left := hr ▸ he
  let e := liftOver i η[G.X] he'
  let m := liftOver i m₀ hm
  let w := liftOver i w₀ hw
  let hGrp := grpObjOfMono i e m w (liftOver_fac _ _ _) (liftOver_fac _ _ _) (liftOver_fac _ _ _)
  let : GrpObj P := hGrp
  have : IsMonHom i := isMonHom_grpObjOfMono i e m w
    (liftOver_fac _ _ _) (liftOver_fac _ _ _) (liftOver_fac _ _ _)
  let K : GroupScheme S := { X := P }
  let j : K ⟶ G := Grp.homMk i
  exact ⟨K, j, hP, ‹IsOpenImmersion i.left›, hr⟩

private theorem isRelativeIdentityComponent_comp_smoothOpen {S : Scheme.{u}}
    {G P H : GroupScheme S} (j : P ⟶ G) [IsOpenImmersion j.hom.hom.left]
    [Smooth P.X.hom] [LocallyOfFinitePresentation G.X.hom]
    (i : H ⟶ P) (hi : IsRelativeIdentityComponent P i) : IsRelativeIdentityComponent G (i ≫ j) := by
  let : IsOpenImmersion i.hom.hom.left := hi.isOpenImmersion
  have : IsOpenImmersion (i ≫ j).hom.hom.left :=
    inferInstanceAs (IsOpenImmersion (i.hom.hom.left ≫ j.hom.hom.left))
  apply IsRelativeIdentityComponent.of_range_residueFiber
  intro s
  let b := S.fromSpecResidueField s
  let Ps := (GroupScheme.baseChange b).obj P
  let Gs := (GroupScheme.baseChange b).obj G
  let js : Ps ⟶ Gs := (GroupScheme.baseChange b).map j
  have : IsOpenImmersion js.hom.hom.left :=
    MorphismProperty.of_isPullback (overPullback_isPullback b j.hom.hom).flip inferInstance
  have : LocallyOfFiniteType Gs.X.hom :=
    MorphismProperty.pullback_snd (P := @LocallyOfFiniteType) _ _ inferInstance
  have : Smooth Ps.X.hom := MorphismProperty.pullback_snd (P := @Smooth) _ _ inferInstance
  have : Smooth Gs.X.hom := smooth_of_smooth_open_subgroup Gs Ps js
  rw [Functor.map_comp]
  change Set.range (js.hom.hom.left ∘ ((GroupScheme.baseChange b).map i).hom.hom.left) =
    IdentityComponent.identitySet Gs
  rw [Set.range_comp, hi.range_residueFiber]
  exact image_identitySet_of_open js

/-- Smoothness along the unit of a locally finitely presented group suffices
for an actual smooth, geometrically connected relative identity component. -/
def SmoothAtUnitIdentityComponentStatement : Prop :=
  ∀ (S : Scheme.{u}) (G : GroupScheme S) [LocallyOfFinitePresentation G.X.hom],
    (∀ s : S, (G.X.hom.stalkMap (unitSection G s)).hom.FormallySmooth) →
    ∃ (H : GroupScheme S) (i : H ⟶ G),
      IsRelativeIdentityComponent G i ∧ Smooth H.X.hom ∧ GeometricallyConnected H.X.hom ∧
        (SubgroupFunctor.range i).IsNormal ∧
        ∀ (S' : Scheme.{u}) (b : S' ⟶ S),
          IsRelativeIdentityComponent ((GroupScheme.baseChange b).obj G)
            ((GroupScheme.baseChange b).map i)

theorem smoothAtUnitIdentityComponent : SmoothAtUnitIdentityComponentStatement.{u} := by
  intro S G _ he
  have h : Set.range (unitSection G) ⊆ G.X.hom.smoothLocus := by
    rintro _ ⟨s, rfl⟩
    exact Scheme.Hom.mem_smoothLocus.mpr (he s)
  obtain ⟨P, j, hP, hj, _⟩ := exists_smoothLocus_openSubgroup G h
  obtain ⟨H, i, hi, hH, hconn⟩ := smoothExistence S P hP
  have hrel := isRelativeIdentityComponent_comp_smoothOpen j i hi
  refine ⟨H, i ≫ j, hrel, hH, hconn, isNormal_of_geometricallyConnected hrel, ?_⟩
  intro S' b
  exact hrel.baseChange b

end Langlands.GroupScheme.RelativeIdentityComponent
