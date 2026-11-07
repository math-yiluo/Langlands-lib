import Langlands.Representation.Jacquet.SmallFixedVectorGenerator
import Langlands.Representation.Jacquet.FixedVectorGeneratedCategory
import Langlands.Representation.Compact.SurjectivityProof
import Langlands.CategoryTheory.Renard.SmallProgeneratorEquivalence

/-! # The compact fixed-vector small progenerator -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits
open Langlands.CategoryTheory.Renard Langlands.Renard

universe uG uV uW

namespace Langlands.Jacquet

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (K : OpenSubgroup G) [Small.{uV} (G ⧸ K.toSubgroup)]

/-- The resized compact permutation object belongs to the category it generates. -/
def fixedVectorProgenerator : (fixedVectorGenerated.{uG,uV} K.toSubgroup).FullSubcategory :=
  ⟨smallFixedVectorGenerator K, smallFixedVectorGenerator_generated K⟩

/-- Evaluation at the identity coset identifies maps with fixed vectors. -/
def fixedVectorProgeneratorHomEquiv
    (V : (fixedVectorGenerated.{uG,uV} K.toSubgroup).FullSubcategory) :
    (fixedVectorProgenerator K ⟶ V) ≃+
      fixedVectors V.obj.representation K.toSubgroup where
  toFun f := fixedVectorsMap (SmoothRep.hom f.hom) K.toSubgroup (smallFixedVectorUnit K)
  invFun v := ObjectProperty.homMk (SmoothRep.ofHom
    (smallFixedVectorLift K V.obj.representation v))
  left_inv f := by
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    apply Rep.hom_ext
    exact smallFixedVectorLift_eval K V.obj.representation (SmoothRep.hom f.hom)
  right_inv v := Subtype.ext (smallFixedVectorLift_unit K V.obj.representation v)
  map_add' f g := Subtype.ext (by rfl)

omit [IsTopologicalGroup G] [Small.{uV} (G ⧸ K.toSubgroup)] in
/-- Maps from a fixed-vector-generated object agree if they agree on fixed vectors. -/
theorem fixedVectorGenerated_hom_ext
    {V : SmoothRep.{0,uG,uV} ℂ G} {W : SmoothRep.{0,uG,uW} ℂ G}
    (hV : fixedVectorGenerated K.toSubgroup V)
    (f g : V.representation.IntertwiningMap W.representation)
    (h : ∀ v ∈ fixedVectors V.representation K.toSubgroup, f v = g v) : f = g := by
  have hz := fixedVectorGenerated_image_le K.toSubgroup hV (f - g) ⊥
    (fun v hv => show (f - g) v = 0 from sub_eq_zero.mpr (h v hv))
  apply Representation.IntertwiningMap.ext
  ext v
  exact sub_eq_zero.mp (hz v)

section Abelian

variable [(fixedVectorGenerated.{uG,uV} K.toSubgroup).IsClosedUnderSubobjects]

instance fixedVectorGenerated_ι_preservesEpimorphisms :
    (fixedVectorGenerated.{uG,uV} K.toSubgroup).ι.PreservesEpimorphisms :=
  ObjectProperty.preservesEpimorphisms_ι_of_isNormalMonoCategory _

omit [(fixedVectorGenerated.{uG,uV} K.toSubgroup).IsClosedUnderSubobjects] in
/-- Compact averaging supplies the lift of the identity-coset value through any epi. -/
theorem fixedVectorProgenerator_projective (hK : IsCompact (K : Set G)) :
    Projective (fixedVectorProgenerator.{uG,uV} K) where
  factors {E X} f e _ := by
    have he : Epi ((fixedVectorGenerated.{uG,uV} K.toSubgroup).ι.map e) := inferInstance
    have hs := (SmoothRep.epi_iff_surjective e.hom).mp he
    obtain ⟨v, hv⟩ := Langlands.Compact.fixedVectorSurjectivity G E.obj X.obj
      E.obj.representation X.obj.representation E.obj.isSmooth X.obj.isSmooth K hK
      (SmoothRep.hom e.hom) hs ((fixedVectorProgeneratorHomEquiv K X) f)
    refine ⟨(fixedVectorProgeneratorHomEquiv K E).symm v, ?_⟩
    apply (fixedVectorProgeneratorHomEquiv K X).injective
    change fixedVectorsMap (SmoothRep.hom e.hom) K.toSubgroup
      ((fixedVectorProgeneratorHomEquiv K E)
        ((fixedVectorProgeneratorHomEquiv K E).symm v)) = _
    rw [AddEquiv.apply_symm_apply]
    exact hv

/-- The compact permutation object detects all morphisms in the generated category. -/
theorem fixedVectorProgenerator_homGenerator :
    HomGenerator (fixedVectorProgenerator.{uG,uV} K) where
  map_injective {X Y} f g h := by
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    apply Rep.hom_ext
    apply fixedVectorGenerated_hom_ext K X.property
    intro v hv
    let l := (fixedVectorProgeneratorHomEquiv K X).symm ⟨v, hv⟩
    have hh := congrArg (fun t => t l) h
    have he := congrArg (fun t => (fixedVectorProgeneratorHomEquiv K Y) t) hh
    have hl : (fixedVectorProgeneratorHomEquiv K X) l = ⟨v, hv⟩ :=
      (fixedVectorProgeneratorHomEquiv K X).apply_symm_apply _
    change fixedVectorsMap (SmoothRep.hom f.hom) K.toSubgroup
      ((fixedVectorProgeneratorHomEquiv K X) l) =
      fixedVectorsMap (SmoothRep.hom g.hom) K.toSubgroup
        ((fixedVectorProgeneratorHomEquiv K X) l) at he
    rw [hl] at he
    exact congrArg Subtype.val he

/-- Actual finite group-algebra generation gives preservation of all carrier-sized coproducts. -/
theorem fixedVectorProgenerator_homPreservesCoproducts :
    HomPreservesCoproducts.{uV} (fixedVectorProgenerator.{uG,uV} K) := by
  intro I
  let : Module.Finite (MonoidAlgebra ℂ G)
      (fixedVectorProgenerator.{uG,uV} K).obj.representation.asModule :=
    smallFixedVectorGenerator_finite K
  exact SmoothRep.hom_preservesFullSubcategoryCoproducts
    (fixedVectorGenerated K.toSubgroup)
    (fun B _ => fixedVectorGenerated_directSum K.toSubgroup _ (fun i => (B i).property))
    (fixedVectorProgenerator K)

/-- The compact permutation object is a small progenerator once generation is closed under subobjects. -/
theorem fixedVectorProgenerator_smallProgenerator (hK : IsCompact (K : Set G)) :
    HomSmallProgenerator.{uV} (fixedVectorProgenerator.{uG,uV} K) :=
  ⟨⟨(homProjectiveComparison _).mpr (fixedVectorProgenerator_projective K hK),
    fixedVectorProgenerator_homPreservesCoproducts K⟩,
    fixedVectorProgenerator_homGenerator K⟩

/-- The actual endomorphism-module Hom functor is an equivalence. -/
theorem fixedVectorProgenerator_hom_isEquivalence (hK : IsCompact (K : Set G)) :
    (preadditiveCoyonedaObj (fixedVectorProgenerator.{uG,uV} K)).IsEquivalence :=
  preadditiveCoyonedaObj_isEquivalence_of_homSmallProgenerator
    (fixedVectorProgenerator_smallProgenerator K hK)

end Abelian

end Langlands.Jacquet
