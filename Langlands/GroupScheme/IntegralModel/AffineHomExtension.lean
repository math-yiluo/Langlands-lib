import Langlands.GroupScheme.IntegralModel.LocalIntegralSeparation
import Langlands.GroupScheme.IntegralModel.GenericRigidity

/-! # Affine extension from containment of generic coordinates -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory CategoryTheory.MonObj AlgebraicGeometry
open scoped CategoryTheory.MonObj CategoryTheory.Obj
attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory
  CategoryTheory.Over.braidedCategory

namespace Langlands.GroupScheme.IntegralModel

open Langlands.AlgebraicGeometry.PointTopology

private theorem exists_affine_hom_of_coordinate
    {R : Type u} [CommRing R]
    (X Y : Over (Spec (CommRingCat.of R))) [IsAffine X.left] [IsAffine Y.left]
    (g : AffineCoordinateRing R Y →ₐ[R] AffineCoordinateRing R X) :
    ∃ φ : X ⟶ Y, φ.left.appTop.hom = g.toRingHom := by
  let φ : X.left ⟶ Y.left := X.left.isoSpec.hom ≫
    Spec.map (CommRingCat.ofHom g.toRingHom) ≫ Y.left.isoSpec.inv
  have hφ : φ.appTop = CommRingCat.ofHom g.toRingHom := by
    apply Spec.map_injective
    apply (cancel_epi X.left.isoSpec.hom).mp
    rw [Scheme.isoSpec_hom_naturality]
    simp [φ]
  have hw : φ ≫ Y.hom = X.hom := by
    apply (cancel_epi X.left.isoSpec.inv).mp
    rw [← affineCoordinateSpecMap R X]
    dsimp only [φ]
    rw [Category.assoc, Iso.inv_hom_id_assoc]
    rw [Category.assoc, ← affineCoordinateSpecMap R Y, ← Spec.map_comp]
    congr 1
    ext r
    exact g.commutes r
  exact ⟨Over.homMk φ hw, congrArg (fun k => k.hom) hφ⟩

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]
  {G H : GroupScheme (Spec (CommRingCat.of K))}
  (M : IntegralModel R K G) (N : IntegralModel R K H)

private instance extensionModelAffine : IsAffine M.group.X.left :=
  isAffine_of_isAffineHom M.group.X.hom

/-- Forget the generic field in the generic group, retaining the integral base. -/
private def genericOverIntegral : Over (Spec (CommRingCat.of R)) :=
  Over.mk (G.X.hom ≫ Spec.algebraMap R K)

private instance genericOverIntegralAffine [IsAffine G.X.left] :
    IsAffine (genericOverIntegral (R := R) (K := K) (G := G)).left :=
  inferInstanceAs (IsAffine G.X.left)

/-- The actual restriction morphism from the specified generic group to its model. -/
private def genericRestriction : genericOverIntegral (R := R) (K := K) (G := G) ⟶ M.group.X :=
  Over.homMk (M.genericIso.inv.hom.hom.left ≫
    pullback.fst M.group.X.hom (Spec.algebraMap R K)) (by
      rw [Category.assoc, pullback.condition, ← Category.assoc]
      exact congrArg (fun a => a ≫ Spec.algebraMap R K) (Over.w M.genericIso.inv.hom.hom))

private theorem affine_hom_ext {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    {f g : X ⟶ Y} (h : f.appTop.hom = g.appTop.hom) : f = g := by
  apply (cancel_mono Y.isoSpec.hom).mp
  rw [← Scheme.isoSpec_hom_naturality, ← Scheme.isoSpec_hom_naturality]
  congr 2
  exact CommRingCat.hom_ext h

include M in
private theorem genericAffine : IsAffine G.X.left := by
  let : IsAffine M.genericFibre.X.left := by
    change IsAffine (pullback M.group.X.hom (Spec.algebraMap R K))
    infer_instance
  exact IsAffine.of_isIso M.genericIso.inv.hom.hom.left

private theorem hom_of_genericSchemeHom (f : G ⟶ H) (φ : M.group.X ⟶ N.group.X)
    (hφ : (Over.pullback (Spec.algebraMap R K)).map φ =
      (M.genericIso.hom ≫ f ≫ N.genericIso.inv).hom.hom) :
    Nonempty (M.Hom N f) := by
  have : IsMonHom ((Over.pullback (Spec.algebraMap R K)).map φ) := by
    rw [hφ]
    infer_instance
  have hflat₀ : Flat (𝟙_ (Over (Spec (CommRingCat.of R)))).hom := by
    rw [Over.tensorUnit_hom]
    exact MorphismProperty.id_mem @Flat _
  have hflat₂ : Flat (M.group.X ⊗ M.group.X).hom := by
    rw [Over.tensorObj_hom]
    infer_instance
  have : IsMonHom φ :=
    Langlands.AbelianScheme.isMonHom_of_map (Over.pullback (Spec.algebraMap R K)) φ
      (fun _ _ h => Langlands.AbelianScheme.genericFibre_map_injective K h)
      (fun _ _ h => Langlands.AbelianScheme.genericFibre_map_injective K h)
  let φ' : M.group ⟶ N.group := Grp.homMk φ
  have hmap : (GroupScheme.baseChange (Spec.algebraMap R K)).map φ' =
      M.genericIso.hom ≫ f ≫ N.genericIso.inv := by
    apply Grp.hom_ext
    exact hφ
  refine ⟨⟨φ', ?_⟩⟩
  rw [hmap]
  simp

/-- Containment of the actual generic coordinate rings gives an extension of the
specified generic homomorphism to the supplied flat affine models. -/
theorem nonempty_hom_of_genericCoordinates (f : G ⟶ H)
    (h : ∀ b : AffineCoordinateRing R N.group.X,
      f.hom.hom.left.appTop.hom (N.genericCoordinate b) ∈ Set.range M.genericCoordinate) :
    Nonempty (M.Hom N f) := by
  let : IsAffine G.X.left := genericAffine M
  let : IsAffine H.X.left := genericAffine N
  let fR : genericOverIntegral (R := R) (K := K) (G := G) ⟶
      genericOverIntegral (R := R) (K := K) (G := H) :=
    Over.homMk f.hom.hom.left (by
      change f.hom.hom.left ≫ H.X.hom ≫ Spec.algebraMap R K =
        G.X.hom ≫ Spec.algebraMap R K
      rw [← Category.assoc, Over.w])
  let pM := affineCoordinatePullback R M.genericRestriction
  let pN := affineCoordinatePullback R N.genericRestriction
  let q := (affineCoordinatePullback R fR).comp pN
  have hrange : ∀ b : AffineCoordinateRing R N.group.X, ∃ a, pM a = q b := by
    intro b
    exact h b
  choose g hg using hrange
  have hinj : Function.Injective pM := M.genericCoordinate_injective
  let g' : AffineCoordinateRing R N.group.X →ₐ[R] AffineCoordinateRing R M.group.X :=
    { toFun := g
      map_one' := hinj (by rw [hg, map_one, map_one])
      map_mul' := fun a b => hinj (by simp only [map_mul, hg])
      map_zero' := hinj (by rw [hg, map_zero, map_zero])
      map_add' := fun a b => hinj (by simp only [map_add, hg])
      commutes' := fun r => hinj (by rw [hg, q.commutes, pM.commutes]) }
  obtain ⟨φ, hφ⟩ := exists_affine_hom_of_coordinate M.group.X N.group.X g'
  have hr : M.genericRestriction ≫ φ = fR ≫ N.genericRestriction := by
    apply Over.OverMorphism.ext
    apply affine_hom_ext
    simp only [Over.comp_left, Scheme.Hom.comp_appTop, CommRingCat.hom_comp]
    ext b
    change pM (φ.left.appTop.hom b) = q b
    rw [hφ]
    exact hg b
  apply hom_of_genericSchemeHom M N f φ
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · simp only [Over.pullback_map_left, pullback.lift_fst]
    apply (cancel_epi M.genericIso.inv.hom.hom.left).mp
    have hh := congrArg (fun a => a.left) hr
    change (M.genericIso.inv.hom.hom.left ≫
      pullback.fst M.group.X.hom (Spec.algebraMap R K)) ≫ φ.left =
      f.hom.hom.left ≫ N.genericIso.inv.hom.hom.left ≫
        pullback.fst N.group.X.hom (Spec.algebraMap R K) at hh
    let eM := (Over.forget _).mapIso ((Grp.forget _).mapIso M.genericIso)
    change eM.inv ≫ pullback.fst M.group.X.hom (Spec.algebraMap R K) ≫ φ.left =
      eM.inv ≫ (eM.hom ≫ f.hom.hom.left ≫ N.genericIso.inv.hom.hom.left) ≫
        pullback.fst N.group.X.hom (Spec.algebraMap R K)
    rw [Category.assoc, eM.inv_hom_id_assoc]
    exact hh
  · exact (Over.w ((Over.pullback (Spec.algebraMap R K)).map φ)).trans
      (Over.w ((M.genericIso.hom ≫ f ≫ N.genericIso.inv).hom.hom)).symm

end Langlands.GroupScheme.IntegralModel
