import Langlands.Representation.Jacquet.FixedVectorSmallProgenerator

/-! # Comparing the compact Hom and Hecke functors -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory
open Langlands.Shimura.LevelHecke

universe uG uV

namespace Langlands.Jacquet

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (K : OpenSubgroup G) [Small.{uV} (G ⧸ K.toSubgroup)]

/-- Resizing identifies the Hecke algebra's underlying additive group with the fixed vectors
of the compact permutation generator. -/
def fixedVectorHeckeAddEquiv : LevelHeckeAlgebra ℂ K.toSubgroup ≃+
    fixedVectors (smallFixedVectorGenerator.{uG,uV} K).representation K.toSubgroup where
  toFun a := fixedVectorsMap (smallFixedVectorGeneratorEquiv K).toIntertwiningMap K.toSubgroup a
  invFun a := fixedVectorsMap (smallFixedVectorGeneratorEquiv K).symm.toIntertwiningMap K.toSubgroup a
  left_inv a := Subtype.ext ((smallFixedVectorCarrierEquiv K).symm_apply_apply a.val)
  right_inv a := Subtype.ext ((smallFixedVectorCarrierEquiv K).apply_symm_apply a.val)
  map_add' a b := map_add (fixedVectorsMap _ _) a b

/-- A Hecke element determines an endomorphism through its identity-coset value. -/
def fixedVectorHeckeEndAddEquiv : LevelHeckeAlgebra ℂ K.toSubgroup ≃+
    (End (fixedVectorProgenerator.{uG,uV} K))ᵐᵒᵖ :=
  ((fixedVectorHeckeAddEquiv K).trans
    (fixedVectorProgeneratorHomEquiv K (fixedVectorProgenerator K)).symm).trans
      MulOpposite.opAddEquiv

/-- The opposite endomorphism multiplication is precisely the published convolution. -/
def fixedVectorHeckeEndEquiv : LevelHeckeAlgebra ℂ K.toSubgroup ≃+*
    (End (fixedVectorProgenerator.{uG,uV} K))ᵐᵒᵖ :=
  { fixedVectorHeckeEndAddEquiv K with
    map_mul' := by
      intro a b
      apply MulOpposite.unop_injective
      apply (fixedVectorProgeneratorHomEquiv K (fixedVectorProgenerator K)).injective
      apply Subtype.ext
      change smallFixedVectorLift K (smallFixedVectorGenerator K).representation
          (fixedVectorHeckeAddEquiv K (a * b)) (smallFixedVectorUnit K) =
        smallFixedVectorLift K (smallFixedVectorGenerator K).representation
          (fixedVectorHeckeAddEquiv K b)
          (smallFixedVectorLift K (smallFixedVectorGenerator K).representation
            (fixedVectorHeckeAddEquiv K a) (smallFixedVectorUnit K))
      rw [smallFixedVectorLift_unit, smallFixedVectorLift_unit]
      change smallFixedVectorCarrierEquiv K (a * b).val =
        Langlands.Shimura.LevelHecke.frobenius (smallFixedVectorGenerator K).representation
          (fixedVectorHeckeAddEquiv K b)
          ((smallFixedVectorCarrierEquiv K).symm ((smallFixedVectorCarrierEquiv K) a.val))
      rw [LinearEquiv.symm_apply_apply]
      exact congrArg Subtype.val
        (fixedVectorsMap_heckeAct (smallFixedVectorGeneratorEquiv K).toIntertwiningMap
          K.toSubgroup K.toSubgroup a b) }

/-- Evaluation is linear for the Hecke action after scalar restriction along the ring equivalence. -/
def fixedVectorHomHeckeLinearEquiv
    (V : (fixedVectorGenerated.{uG,uV} K.toSubgroup).FullSubcategory) :
    ((preadditiveCoyonedaObj (fixedVectorProgenerator K) ⋙
      ModuleCat.restrictScalars (fixedVectorHeckeEndEquiv K).toRingHom).obj V) ≃ₗ[
        LevelHeckeAlgebra ℂ K.toSubgroup]
      ((fixedVectorGenerated K.toSubgroup).ι ⋙ heckeModuleFunctor ℂ K.toSubgroup).obj V :=
  { fixedVectorProgeneratorHomEquiv K V with
    map_smul' := by
      intro a f
      apply Subtype.ext
      change SmoothRep.hom f.hom
          (smallFixedVectorLift K (smallFixedVectorGenerator K).representation
            (fixedVectorHeckeAddEquiv K a) (smallFixedVectorUnit K)) = _
      rw [smallFixedVectorLift_unit]
      have h := smallFixedVectorLift_eval K V.obj.representation (SmoothRep.hom f.hom)
      have he := congrArg (fun t => t (fixedVectorHeckeAddEquiv K a)) h
      change Langlands.Shimura.LevelHecke.frobenius V.obj.representation
          ((fixedVectorProgeneratorHomEquiv K V) f)
          ((smallFixedVectorCarrierEquiv K).symm ((smallFixedVectorCarrierEquiv K) a.val)) = _ at he
      rw [LinearEquiv.symm_apply_apply] at he
      exact he.symm }

/-- The exact published Hecke functor is naturally isomorphic to the Hom functor with scalars restricted. -/
def fixedVectorHomHeckeIso :
    preadditiveCoyonedaObj (fixedVectorProgenerator.{uG,uV} K) ⋙
      ModuleCat.restrictScalars (fixedVectorHeckeEndEquiv K).toRingHom ≅
    (fixedVectorGenerated K.toSubgroup).ι ⋙ heckeModuleFunctor ℂ K.toSubgroup :=
  NatIso.ofComponents (fun V => (fixedVectorHomHeckeLinearEquiv K V).toModuleIso)
    (fun f => by
      apply ModuleCat.hom_ext
      ext h
      rfl)

/-- The fixed-vector Hecke functor is an equivalence whenever generation is closed under subobjects. -/
theorem fixedVectorHecke_isEquivalence (hK : IsCompact (K : Set G))
    [(fixedVectorGenerated.{uG,uV} K.toSubgroup).IsClosedUnderSubobjects] :
    ((fixedVectorGenerated.{uG,uV} K.toSubgroup).ι ⋙
      heckeModuleFunctor ℂ K.toSubgroup).IsEquivalence := by
  have := fixedVectorProgenerator_hom_isEquivalence K hK
  exact Functor.isEquivalence_of_iso (fixedVectorHomHeckeIso K)

end Langlands.Jacquet
