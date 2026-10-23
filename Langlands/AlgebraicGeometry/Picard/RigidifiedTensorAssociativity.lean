import Langlands.AlgebraicGeometry.Picard.RigidifiedTensorSymmetry
import Langlands.AlgebraicGeometry.Picard.RigidifiedTensorPullback
import Langlands.AlgebraicGeometry.Modules.PullbackTensorAssociativityStatements
import Langlands.AlgebraicGeometry.Modules.TensorMonoidalComparisonStatements

/-! # Associativity of rigidified line-bundle tensor -/

universe u
open CategoryTheory AlgebraicGeometry
noncomputable section

namespace Langlands.Scheme.Modules
open MonoidalCategory
variable {X : Scheme.{u}}

lemma localizedTensorNatIso_hom_app (M N : X.Modules) :
    (localizedTensorNatIso X).hom.app (M, N) = (localizedTensorIso X M N).hom := by
  rfl

lemma localizedTensorIso_hom_naturality {M M' N N' : X.Modules}
    (f : M ⟶ M') (g : N ⟶ N') :
    (f ⊗ₘ g) ≫ (localizedTensorIso X M' N').hom =
      (localizedTensorIso X M N).hom ≫ tensorMap f g :=
by
  have hn := (localizedTensorNatIso X).hom.naturality ((f, g) : (M, N) ⟶ (M', N'))
  rw [localizedTensorNatIso_hom_app, localizedTensorNatIso_hom_app] at hn
  exact hn

lemma localizedTensorIso_inv_naturality {M M' N N' : X.Modules}
    (f : M ⟶ M') (g : N ⟶ N') :
    tensorMap f g ≫ (localizedTensorIso X M' N').inv =
      (localizedTensorIso X M N).inv ≫ (f ⊗ₘ g) :=
by
  apply (cancel_mono (localizedTensorIso X M' N').hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [localizedTensorIso_hom_naturality, Iso.inv_hom_id_assoc]

lemma localizedTensorIso_inv_naturality_assoc {M M' N N' Q : X.Modules}
    (f : M ⟶ M') (g : N ⟶ N') (k : M' ⊗ N' ⟶ Q) :
    tensorMap f g ≫ (localizedTensorIso X M' N').inv ≫ k =
      (localizedTensorIso X M N).inv ≫ (f ⊗ₘ g) ≫ k := by
  rw [← Category.assoc, localizedTensorIso_inv_naturality, Category.assoc]

lemma tensorAssociator_naturality {M M' N N' P P' : X.Modules}
    (f : M ⟶ M') (g : N ⟶ N') (h : P ⟶ P') :
    tensorMap (tensorMap f g) h ≫ (tensorAssociator M' N' P').hom =
      (tensorAssociator M N P).hom ≫ tensorMap f (tensorMap g h) := by
  simp only [tensorAssociator, Iso.trans_hom, Iso.symm_hom, tensorIso_hom,
    Iso.refl_hom, Category.assoc]
  rw [localizedTensorIso_inv_naturality_assoc]
  have hl : (tensorMap f g ⊗ₘ h) ≫ ((localizedTensorIso X M' N').inv ⊗ₘ 𝟙 P') =
      ((localizedTensorIso X M N).inv ⊗ₘ 𝟙 P) ≫ ((f ⊗ₘ g) ⊗ₘ h) := by
    simp only [tensorHom_comp_tensorHom, Category.comp_id, Category.id_comp,
      localizedTensorIso_inv_naturality]
  rw [← Category.assoc (tensorMap f g ⊗ₘ h), hl]
  simp only [Category.assoc]
  rw [associator_naturality_assoc]
  rw [← localizedTensorIso_hom_naturality]
  have hr : (f ⊗ₘ (g ⊗ₘ h)) ≫ (𝟙 M' ⊗ₘ (localizedTensorIso X N' P').hom) =
      (𝟙 M ⊗ₘ (localizedTensorIso X N P).hom) ≫ (f ⊗ₘ tensorMap g h) := by
    simp only [tensorHom_comp_tensorHom, Category.comp_id, Category.id_comp,
      localizedTensorIso_hom_naturality]
  rw [← Category.assoc (f ⊗ₘ (g ⊗ₘ h)), hr]
  simp only [Category.assoc]

include X in
lemma tensorAssociator_leftUnitor
    (comparison : TensorMonoidalLeftUnitorComparisonStatement.{u}) (M N : X.Modules) :
    (tensorAssociator (structureSheaf X) M N).hom ≫
        (tensorLeftUnitor (tensorObj M N)).hom =
      tensorMap (tensorLeftUnitor M).hom (𝟙 N) := by
  simp only [tensorAssociator, Iso.trans_hom, Iso.symm_hom, tensorIso_hom,
    Iso.refl_hom, Category.assoc]
  rw [comparison]
  rw [id_tensorHom]
  erw [leftUnitor_naturality]
  erw [leftUnitor_tensor_hom''_assoc]
  rw [← Category.assoc ((localizedTensorIso X (structureSheaf X) M).inv ⊗ₘ 𝟙 N),
    tensorHom_comp_tensorHom, Category.comp_id]
  have hm : (localizedTensorIso X (structureSheaf X) M).inv ≫ (λ_ M).hom =
      (tensorLeftUnitor M).hom := by
    rw [← comparison X M, Iso.inv_hom_id_assoc]
  rw [hm, localizedTensorIso_hom_naturality, Iso.inv_hom_id_assoc]

lemma tensorUnit_split_assoc
    (comparison : TensorMonoidalLeftUnitorComparisonStatement.{u}) :
    (tensorLeftUnitor (structureSheaf X)).inv ≫
        tensorMap (tensorLeftUnitor (structureSheaf X)).inv (𝟙 (structureSheaf X)) ≫
        (tensorAssociator (structureSheaf X) (structureSheaf X) (structureSheaf X)).hom =
      (tensorLeftUnitor (structureSheaf X)).inv ≫
        tensorMap (𝟙 (structureSheaf X)) (tensorLeftUnitor (structureSheaf X)).inv := by
  apply (cancel_mono (tensorLeftUnitor (tensorObj (structureSheaf X) (structureSheaf X))).hom).1
  simp only [Category.assoc]
  rw [tensorAssociator_leftUnitor comparison]
  rw [tensorMap_comp]
  rw [Iso.inv_hom_id, Category.id_comp]
  rw [tensorLeftUnitor_naturality]
  simp only [tensorMap_id, Category.comp_id, Iso.inv_hom_id_assoc]

end Langlands.Scheme.Modules

namespace Langlands.SchemeModule.RigidifiedModule

open Langlands.Scheme.Modules
variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})
variable {S X : Scheme.{u}} {ε : S ⟶ X}

lemma tensorTriple_left_rigidification_comp (L M N : RigidifiedModule ε) :
    (tensorObj preservation (tensorObj preservation L M) N).rigidification.hom ≫
        pullbackTensorComparisonApp ε (Langlands.Scheme.Modules.tensorObj L.carrier M.carrier)
          N.carrier ≫
        Langlands.Scheme.Modules.tensorMap
          (pullbackTensorComparisonApp ε L.carrier M.carrier)
          (𝟙 ((Scheme.Modules.pullback ε).obj N.carrier)) =
      (tensorLeftUnitor (structureModule S)).inv ≫
        Langlands.Scheme.Modules.tensorMap (tensorLeftUnitor (structureModule S)).inv
          (𝟙 (structureModule S)) ≫
        Langlands.Scheme.Modules.tensorMap
          (Langlands.Scheme.Modules.tensorMap L.rigidification.hom M.rigidification.hom)
          N.rigidification.hom := by
  erw [← Category.assoc,
    tensorObj_rigidification_comp preservation (tensorObj preservation L M) N,
    Category.assoc,
    Langlands.Scheme.Modules.tensorMap_comp
      (tensorObj preservation L M).rigidification.hom
      (pullbackTensorComparisonApp ε L.carrier M.carrier) N.rigidification.hom (𝟙 _),
    tensorObj_rigidification_comp preservation L M, Category.comp_id,
    Langlands.Scheme.Modules.tensorMap_comp
      (tensorLeftUnitor (structureModule S)).inv
      (Langlands.Scheme.Modules.tensorMap L.rigidification.hom M.rigidification.hom)
      (𝟙 _) N.rigidification.hom, Category.id_comp]

lemma tensorTriple_right_rigidification_comp (L M N : RigidifiedModule ε) :
    (tensorObj preservation L (tensorObj preservation M N)).rigidification.hom ≫
        pullbackTensorComparisonApp ε L.carrier
          (Langlands.Scheme.Modules.tensorObj M.carrier N.carrier) ≫
        Langlands.Scheme.Modules.tensorMap (𝟙 ((Scheme.Modules.pullback ε).obj L.carrier))
          (pullbackTensorComparisonApp ε M.carrier N.carrier) =
      (tensorLeftUnitor (structureModule S)).inv ≫
        Langlands.Scheme.Modules.tensorMap (𝟙 (structureModule S))
          (tensorLeftUnitor (structureModule S)).inv ≫
        Langlands.Scheme.Modules.tensorMap L.rigidification.hom
          (Langlands.Scheme.Modules.tensorMap M.rigidification.hom N.rigidification.hom) := by
  erw [← Category.assoc,
    tensorObj_rigidification_comp preservation L (tensorObj preservation M N),
    Category.assoc,
    Langlands.Scheme.Modules.tensorMap_comp L.rigidification.hom (𝟙 _)
      (tensorObj preservation M N).rigidification.hom
      (pullbackTensorComparisonApp ε M.carrier N.carrier),
    tensorObj_rigidification_comp preservation M N, Category.comp_id,
    Langlands.Scheme.Modules.tensorMap_comp (𝟙 _) L.rigidification.hom
      (tensorLeftUnitor (structureModule S)).inv
      (Langlands.Scheme.Modules.tensorMap M.rigidification.hom N.rigidification.hom),
    Category.id_comp]

lemma tensorAssociator_compatibility
    (associativity : ExplicitPullbackTensorAssociativityStatement.{u})
    (comparison : TensorMonoidalLeftUnitorComparisonStatement.{u})
    (L M N : RigidifiedModule ε) :
    (tensorObj preservation (tensorObj preservation L M) N).rigidification.hom ≫
        (Scheme.Modules.pullback ε).map
          (Langlands.Scheme.Modules.tensorAssociator L.carrier M.carrier N.carrier).hom =
      (tensorObj preservation L (tensorObj preservation M N)).rigidification.hom := by
  let := preservation ε
  let J := (Langlands.Scheme.Modules.tensorFunctor S).mapIso
    ((Iso.refl ((Scheme.Modules.pullback ε).obj L.carrier)).prod
      ((asIso (pullbackTensorComparison ε)).app (M.carrier, N.carrier)))
  apply (cancel_mono (((asIso (pullbackTensorComparison ε)).app
    (L.carrier, Langlands.Scheme.Modules.tensorObj M.carrier N.carrier)).hom ≫ J.hom)).1
  change (_ ≫ _) ≫ (pullbackTensorComparisonApp ε L.carrier
      (Langlands.Scheme.Modules.tensorObj M.carrier N.carrier) ≫
      Langlands.Scheme.Modules.tensorMap (𝟙 ((Scheme.Modules.pullback ε).obj L.carrier))
        (pullbackTensorComparisonApp ε M.carrier N.carrier)) = _ ≫
      (pullbackTensorComparisonApp ε L.carrier
        (Langlands.Scheme.Modules.tensorObj M.carrier N.carrier) ≫
      Langlands.Scheme.Modules.tensorMap (𝟙 ((Scheme.Modules.pullback ε).obj L.carrier))
        (pullbackTensorComparisonApp ε M.carrier N.carrier))
  erw [Category.assoc, ← associativity S X ε L.carrier M.carrier N.carrier]
  erw [← Category.assoc, ← Category.assoc,
    tensorTriple_left_rigidification_comp preservation L M N,
    tensorTriple_right_rigidification_comp preservation L M N]
  simp only [Category.assoc]
  erw [Langlands.Scheme.Modules.tensorAssociator_naturality
      L.rigidification.hom M.rigidification.hom N.rigidification.hom]
  have hu := congrArg
    (fun k ↦ k ≫ Langlands.Scheme.Modules.tensorMap L.rigidification.hom
      (Langlands.Scheme.Modules.tensorMap M.rigidification.hom N.rigidification.hom))
    (Langlands.Scheme.Modules.tensorUnit_split_assoc (X := S) comparison)
  erw [Category.assoc (tensorLeftUnitor (structureSheaf S)).inv,
    Category.assoc (Langlands.Scheme.Modules.tensorMap
      (tensorLeftUnitor (structureSheaf S)).inv (𝟙 (structureSheaf S))),
    Category.assoc (tensorLeftUnitor (structureSheaf S)).inv] at hu
  exact hu

end Langlands.SchemeModule.RigidifiedModule

namespace Langlands.AlgebraicGeometry.Picard.RigidifiedLineBundle

open Langlands.SchemeModule Langlands.Scheme.Modules
variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})
variable (associativity : ExplicitPullbackTensorAssociativityStatement.{u})
variable (comparison : TensorMonoidalLeftUnitorComparisonStatement.{u})
variable {S X : Scheme.{u}} {ε : S ⟶ X}

/-- The fixed sheaf associator lifts to an isomorphism preserving tensor rigidifications. -/
def tensorAssociator (L M N : RigidifiedLineBundle ε) :
    tensor preservation (tensor preservation L M) N ≅
      tensor preservation L (tensor preservation M N) :=
  isoMk (Langlands.Scheme.Modules.tensorAssociator L.obj.carrier M.obj.carrier N.obj.carrier)
    (RigidifiedModule.tensorAssociator_compatibility preservation associativity comparison
      L.obj M.obj N.obj)

variable (f : X ⟶ S) (ε : S ⟶ X) (section_eq : ε ≫ f = 𝟙 S)

include associativity comparison in
lemma classesTensor_assoc (T : Over S) (q r s : Classes f ε section_eq T) :
    classesTensor preservation f ε section_eq T
        (classesTensor preservation f ε section_eq T q r) s =
      classesTensor preservation f ε section_eq T q
        (classesTensor preservation f ε section_eq T r s) := by
  refine Quotient.inductionOn₃ q r s (fun L M N ↦ ?_)
  exact Quotient.sound ⟨tensorAssociator preservation associativity comparison L M N⟩

end Langlands.AlgebraicGeometry.Picard.RigidifiedLineBundle

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})
variable (associativity : ExplicitPullbackTensorAssociativityStatement.{u})
variable (comparison : TensorMonoidalLeftUnitorComparisonStatement.{u})
variable {S : Scheme.{u}} (A : AbelianScheme S)

include associativity comparison in
lemma picardZeroClassesTensor_assoc (T : Over S) (q r s : PicardZeroClasses A T) :
    picardZeroClassesTensor preservation A T
        (picardZeroClassesTensor preservation A T q r) s =
      picardZeroClassesTensor preservation A T q
        (picardZeroClassesTensor preservation A T r s) := by
  apply Subtype.ext
  exact RigidifiedLineBundle.classesTensor_assoc preservation associativity comparison
    A.X.hom (unitSection A) (unitSection_comp A) T q.val r.val s.val

end Langlands.AbelianScheme
