/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RawAffineRestrictedCohomology

/-! # Concrete restricted affine coefficient constructions

Source: Stacks Project, Tags 09Z1 and 0EZM.
-/

@[expose] public section

universe v
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

/-- The diagram of the actual fibre products, with canonical pullback maps.
Source: Stacks Project, Tag 09Z1 proof, base change to an affine etale object.
(blueprint: def-sbc-restricted-affine-coefficient-construction). -/
@[implicit_reducible]
noncomputable def restrictedAffineDiagram {S : Scheme.{v}} {I : Type v} [Preorder I]
    (D : Iᵒᵖ ⥤ Over S) (U : S.Etale) : Iᵒᵖ ⥤ Scheme.{v} where
  obj i := pullback U.hom (D.obj i).hom
  map f := rawAffineRestrictedMap (D.map f).left (D.obj _).hom (D.obj _).hom
    (Over.w (D.map f)) U
  map_id i := by
    apply pullback.hom_ext <;> simp [rawAffineRestrictedMap]
  map_comp f g := by
    apply pullback.hom_ext <;> simp [rawAffineRestrictedMap, Category.assoc]

/-- The actual fibre-product cone. 
(blueprint: def-sbc-restricted-affine-coefficient-construction)
-/
@[implicit_reducible]
noncomputable def restrictedAffineCone {S : Scheme.{v}} {I : Type v} [Preorder I]
    (D : Iᵒᵖ ⥤ Over S) (c : Cone D) (U : S.Etale) :
    Cone (restrictedAffineDiagram D U) where
  pt := pullback U.hom c.pt.hom
  π :=
    { app := fun i ↦ rawAffineRestrictedMap (c.π.app i).left (D.obj i).hom c.pt.hom
        (Over.w (c.π.app i)) U
      naturality := by
        intro i j f
        apply pullback.hom_ext <;>
          simp [restrictedAffineDiagram, rawAffineRestrictedMap, Category.assoc,
            ← Over.comp_left, c.w f] }

/-- The restricted stage sheaf, placed in degree zero. 
(blueprint: def-sbc-restricted-affine-coefficient-construction)
-/
@[implicit_reducible]
noncomputable def restrictedAffineK {S : Scheme.{v}} {I : Type v} [Preorder I]
    (D : Iᵒᵖ ⥤ Over S)
    (F : ∀ i : I, Sheaf (D.obj (op i)).left.smallEtaleTopology AddCommGrpCat.{v + 1})
    (U : S.Etale) (i : Iᵒᵖ) :
    CochainComplex (Sheaf ((restrictedAffineDiagram D U).obj i).smallEtaleTopology
      AddCommGrpCat.{v + 1}) ℤ :=
  (CochainComplex.singleFunctor _ 0).obj
    ((upperStar AddCommGrpCat.{v + 1} (pullback.snd U.hom (D.obj i).hom)).obj (F i.unop))

/-- Restriction followed by the degree-zero single-complex functor. 
(blueprint: def-sbc-restricted-affine-coefficient-construction)
-/
@[implicit_reducible]
noncomputable def restrictedAffineSingle {S : Scheme.{v}} {Y : Scheme.{v}}
    (h : Y ⟶ S) (U : S.Etale) :=
  upperStar AddCommGrpCat.{v + 1} (pullback.snd U.hom h) ⋙ CochainComplex.singleFunctor _ 0

/-- The prescribed coefficient diagram, reindexed by double opposite. 
(blueprint: def-sbc-restricted-affine-coefficient-construction)
-/
@[implicit_reducible]
noncomputable def restrictedAffineG {S : Scheme.{v}} {I : Type v} [Preorder I]
    (D : Iᵒᵖ ⥤ Over S) (c : Cone D)
    (H : I ⥤ Sheaf c.pt.left.smallEtaleTopology AddCommGrpCat.{v + 1}) (U : S.Etale) :=
  unopUnop I ⋙ H ⋙ restrictedAffineSingle c.pt.hom U

/-- The image of the actual coefficient colimit cocone. 
(blueprint: def-sbc-restricted-affine-coefficient-construction)
-/
@[implicit_reducible]
noncomputable def restrictedAffineL {S : Scheme.{v}} {I : Type v} [Preorder I]
    (D : Iᵒᵖ ⥤ Over S) (c : Cone D)
    (H : I ⥤ Sheaf c.pt.left.smallEtaleTopology AddCommGrpCat.{v + 1})
    [HasColimit H] (U : S.Etale) : Cocone (restrictedAffineG D c H U) :=
  (restrictedAffineSingle c.pt.hom U).mapCocone
    ((colimit.cocone H).whisker (unopUnop I))

/-- Fibre-product restriction preserves the given inverse limit.
Source: Stacks Project, Tag 09Z1 proof, base change to an affine etale object.
(blueprint: def-sbc-restricted-affine-coefficient-construction).

Proof: Pullback on over categories is a right adjoint. The forgetful functor preserves
connected limits. Apply these facts to the given limit in Over S and then use pullback
symmetry to identify the result with the concrete diagram and cone. -/
noncomputable def restrictedAffineConeIsLimit {S : Scheme.{v}} {I : Type v}
    [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Over S) (c : Cone D)
    (hc : IsLimit ((Over.forget S).mapCone c)) (U : S.Etale) :
    IsLimit (restrictedAffineCone D c U) := by
  have : IsConnected I := IsFiltered.isConnected I
  let P := Over.pullback U.hom ⋙ Over.forget U.left
  let e : D ⋙ P ≅ restrictedAffineDiagram D U :=
    NatIso.ofComponents (fun i ↦ pullbackSymmetry (D.obj i).hom U.hom) (by
      intro i j f
      apply pullback.hom_ext <;>
        simp [P, restrictedAffineDiagram, rawAffineRestrictedMap, Category.assoc])
  have : PreservesLimitsOfShape Iᵒᵖ P := by
    dsimp only [P]
    infer_instance
  have h := isLimitOfPreserves P (isLimitOfReflects (Over.forget S) hc)
  apply ((IsLimit.postcomposeHomEquiv e (P.mapCone c)).symm h).ofIsoLimit
  refine Cone.ext (pullbackSymmetry c.pt.hom U.hom) ?_
  intro i
  apply pullback.hom_ext <;>
    simp [P, e, restrictedAffineCone, rawAffineRestrictedMap, Category.assoc]

/-- The restricted stages are compact because they are quasi-compact over affine U. 
(blueprint: def-sbc-restricted-affine-coefficient-construction)
-/
theorem restrictedAffineDiagram_compact {S : Scheme.{v}} {I : Type v} [Preorder I]
    (D : Iᵒᵖ ⥤ Over S) [∀ i : Iᵒᵖ, QuasiCompact (D.obj i).hom]
    (U : S.Etale) [IsAffine U.left] (i : Iᵒᵖ) :
    CompactSpace ((restrictedAffineDiagram D U).obj i) := by
  dsimp [restrictedAffineDiagram]
  infer_instance

/-- The restricted stages are quasi-separated by base change over affine U. 
(blueprint: def-sbc-restricted-affine-coefficient-construction)
-/
theorem restrictedAffineDiagram_quasiSeparated {S : Scheme.{v}} {I : Type v} [Preorder I]
    (D : Iᵒᵖ ⥤ Over S) [∀ i : Iᵒᵖ, QuasiSeparated (D.obj i).hom]
    (U : S.Etale) [IsAffine U.left] (i : Iᵒᵖ) :
    QuasiSeparatedSpace ((restrictedAffineDiagram D U).obj i) := by
  have : QuasiSeparatedSpace U.left := quasiSeparatedSpace_of_isAffine U.left
  exact @quasiSeparatedSpace_of_quasiSeparated
    (pullback U.hom (D.obj i).hom : Scheme.{v}) U.left
    (pullback.fst U.hom (D.obj i).hom) ‹QuasiSeparatedSpace U.left› inferInstance

/-- Transitions in the restricted diagram are base changes of affine morphisms. 
(blueprint: def-sbc-restricted-affine-coefficient-construction)
-/
theorem restrictedAffineDiagram_affine {S : Scheme.{v}} {I : Type v} [Preorder I]
    (D : Iᵒᵖ ⥤ Over S)
    [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f).left]
    (U : S.Etale) {i j : Iᵒᵖ} (f : i ⟶ j) :
    IsAffineHom ((restrictedAffineDiagram D U).map f) := by
  dsimp [restrictedAffineDiagram, rawAffineRestrictedMap]
  exact MorphismProperty.pullbackMap (P := @IsAffineHom)
    (by infer_instance) (by infer_instance) (by simp) (Over.w (D.map f)).symm

/-- Restricting and taking degree-zero single complexes preserves the coefficient colimit. 
(blueprint: def-sbc-restricted-affine-coefficient-construction)
-/
noncomputable def restrictedAffineLIsColimit {S : Scheme.{v}} {I : Type v} [Preorder I]
    (D : Iᵒᵖ ⥤ Over S) (c : Cone D)
    (H : I ⥤ Sheaf c.pt.left.smallEtaleTopology AddCommGrpCat.{v + 1})
    [HasColimit H] (U : S.Etale) : IsColimit (restrictedAffineL D c H U) := by
  have : PreservesColimitsOfShape (Iᵒᵖ)ᵒᵖ (restrictedAffineSingle c.pt.hom U) := by
    change PreservesColimitsOfShape (Iᵒᵖ)ᵒᵖ
      (upperStar AddCommGrpCat.{v + 1} (pullback.snd U.hom c.pt.hom) ⋙
        HomologicalComplex.single _ (ComplexShape.up ℤ) 0)
    infer_instance
  apply isColimitOfPreserves
  exact (Functor.Final.isColimitWhiskerEquiv (unopUnop I) _).symm (colimit.isColimit H)

end AlgebraicGeometry.Etale
