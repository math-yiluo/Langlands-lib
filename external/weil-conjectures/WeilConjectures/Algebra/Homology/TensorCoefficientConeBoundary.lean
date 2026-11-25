/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.TensorConeFiveTermExact
import WeilConjectures.Mathlib.Algebra.Homology.BifunctorShift

/-! # The coefficient comparison commutes with a concrete cone boundary

Source: Stacks Project, Tags 06Y6 and 0BYJ; cone summand calculation in the
parent tensor-comparison argument.
(blueprint: lem-pc-tensor-coefficient-cone-boundary). -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory
namespace ModuleCat

/-- The tensorator followed by a coefficient map commutes with the actual homology
boundary. This assertion contains no derived model or exactness assertion.

Source: Stacks Project, Tags 06Y6 and 0BYJ, explicit cone expansion of the
parent comparison argument.
Proof: the chain maps a(V)=μ_F(V,Q)⁻¹ followed by F(V) tensor t form a morphism
from F applied to the tensor-Q image of the cone triangle to the tensor-N image
of its F-extension. Naturality of μ gives the f and cone-inclusion squares.
For the third square, decompose the cone as P₂ plus P₁[1]. On each tensor
summand scalar extension and the tensorator preserve the summand inclusions;
a acts on the Q factor by t. The cone projection discards the P₂ summand and
is the shifted identity on P₁. The first-variable tensor-shift identification has no
extra sign on the homogeneous summands (ι_mapBifunctorShift₁Iso_hom_f). Both compositions are the
same reindexing followed by t, so the projection square commutes.
Apply homology to this triangle morphism and the naturality of the homology
shift isomorphism: H(a(P₃)) followed by the target boundary equals the source
boundary followed by H(a(P₁)) in degree i+1. No flatness, K-flatness or boundedness
is needed; this also applies to zero maps and zero rings.
(blueprint: lem-pc-tensor-coefficient-cone-boundary). -/
theorem tensorCoefficient_cone_boundary
    (A C : Type u) [CommRing A] [CommRing C] (ρ : A →+* C)
    (Q : CochainComplex (ModuleCat.{u} A) ℤ)
    (N : CochainComplex (ModuleCat.{u} C) ℤ)
    (t : ((extendScalars ρ).mapHomologicalComplex (.up ℤ)).obj Q ⟶ N)
    (P₁ P₂ : CochainComplex (ModuleCat.{u} A) ℤ) (f : P₁ ⟶ P₂) (i : ℤ) :
    let F := (extendScalars ρ).mapHomologicalComplex (.up ℤ)
    let H := (curriedTensor (ModuleCat.{u} A)).map₂CochainComplex.flip.obj Q
    let T := F.mapTriangle.obj (H.mapTriangle.obj (CochainComplex.mappingCone.triangle f))
    let a := fun V ↦ (Functor.Monoidal.μIso F V Q).inv ≫ (F.obj V ◁ t)
    CochainComplex.homologyδOfTriangle T i (i + 1) ≫
        HomologicalComplex.homologyMap (a P₁) (i + 1) =
      HomologicalComplex.homologyMap (a (CochainComplex.mappingCone f)) i ≫
        CochainComplex.homologyδOfTriangle (tensorConeTriangle ρ f N) i (i + 1) := by
  dsimp only
  let F := (extendScalars ρ).mapHomologicalComplex (.up ℤ)
  let H := (curriedTensor (ModuleCat.{u} A)).map₂CochainComplex.flip.obj Q
  let J := (curriedTensor (ModuleCat.{u} C)).map₂CochainComplex.flip.obj N
  let K := (curriedTensor (ModuleCat.{u} C)).map₂CochainComplex.flip.obj (F.obj Q)
  let δ : H ⋙ F ⟶ F ⋙ K :=
    (Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ)
      (extendScalars ρ)).flipApp Q
  have : NatTrans.CommShift δ ℤ :=
    HomologicalComplex.commShift_mapBifunctorComparisonNatTrans_flipApp
      (Functor.OplaxMonoidal.δNatTrans (extendScalars ρ)) Q
  let β : K ⟶ J := (curriedTensor (ModuleCat.{u} C)).map₂CochainComplex.flip.map t
  have : NatTrans.CommShift β ℤ :=
    inferInstanceAs (NatTrans.CommShift
      ((curriedTensor (ModuleCat.{u} C)).map₂CochainComplex.flip.map t) ℤ)
  let α : H ⋙ F ⟶ F ⋙ J := δ ≫ Functor.whiskerLeft F β
  have : NatTrans.CommShift α ℤ := inferInstance
  let S := CochainComplex.mappingCone.triangle f
  let U := (H ⋙ F).mapTriangle.obj S
  let V := (F ⋙ J).mapTriangle.obj S
  let φ : U ⟶ V :=
    { hom₁ := α.app S.obj₁
      hom₂ := α.app S.obj₂
      hom₃ := α.app S.obj₃
      comm₁ := α.naturality S.mor₁
      comm₂ := α.naturality S.mor₂
      comm₃ := by
        change ((H ⋙ F).map S.mor₃ ≫
          ((H ⋙ F).commShiftIso (1 : ℤ)).hom.app S.obj₁) ≫ (α.app S.obj₁)⟦(1 : ℤ)⟧' =
            α.app S.obj₃ ≫ (F ⋙ J).map S.mor₃ ≫
              ((F ⋙ J).commShiftIso (1 : ℤ)).hom.app S.obj₁
        rw [Category.assoc, NatTrans.shift_app_comm, ← Category.assoc, α.naturality,
          Category.assoc] }
  let U' := F.mapTriangle.obj (H.mapTriangle.obj S)
  let V' := J.mapTriangle.obj (F.mapTriangle.obj S)
  let ψ : U' ⟶ V' := (Functor.mapTriangleCompIso H F).inv.app S ≫ φ ≫
    (Functor.mapTriangleCompIso F J).hom.app S
  have h₁ : ψ.hom₁ = (Functor.Monoidal.μIso F P₁ Q).inv ≫ (F.obj P₁ ◁ t) := by
    change (𝟙 _ ≫ α.app P₁) ≫ 𝟙 _ = _
    simp only [Category.id_comp, Category.comp_id]
    rfl
  have h₃ : ψ.hom₃ = (Functor.Monoidal.μIso F (CochainComplex.mappingCone f) Q).inv ≫
      (F.obj (CochainComplex.mappingCone f) ◁ t) := by
    change (𝟙 _ ≫ α.app (CochainComplex.mappingCone f)) ≫ 𝟙 _ = _
    simp only [Category.id_comp, Category.comp_id]
    rfl
  have hb : CochainComplex.homologyδOfTriangle U' i (i + 1) rfl ≫
        HomologicalComplex.homologyMap ψ.hom₁ (i + 1) =
      HomologicalComplex.homologyMap ψ.hom₃ i ≫
        CochainComplex.homologyδOfTriangle V' i (i + 1) rfl := by
    simpa only [Functor.homologySequenceδ, Functor.shiftMap,
      CochainComplex.homologyFunctor_shift, HomologicalComplex.homologyFunctor_map,
      CochainComplex.homologyδOfTriangle] using
      (Functor.homologySequenceδ_naturality
        (HomologicalComplex.homologyFunctor (ModuleCat.{u} C) (.up ℤ) 0)
        ψ i (i + 1) rfl).symm
  rw [h₁, h₃] at hb
  simpa only [U', V', S, F, H, J, tensorConeTriangle, Functor.comp_obj,
    Functor.mapTriangle_obj] using hb

end ModuleCat
