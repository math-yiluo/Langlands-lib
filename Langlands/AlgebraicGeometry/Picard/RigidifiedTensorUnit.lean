import Langlands.AlgebraicGeometry.Picard.RigidifiedLineBundleTensor
import Langlands.AlgebraicGeometry.Modules.PullbackTensorUnitStatements
import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas

/-! # Unit isomorphisms for rigidified line-bundle tensor -/

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace Langlands.Scheme.Modules

open MonoidalCategory

variable {X : Scheme.{u}}

local instance : MonoidalCategory X.PresheafOfModules :=
  inferInstanceAs (MonoidalCategory (PresheafOfModulesOfCommRing.{u} X.presheaf))

lemma tensorLeftUnitor_naturality {M N : X.Modules} (f : M ⟶ N) :
    tensorMap (𝟙 (structureSheaf X)) f ≫ (tensorLeftUnitor N).hom =
      (tensorLeftUnitor M).hom ≫ f := by
  change (sheafify X).map ((𝟙 _) ⊗ₘ f.val) ≫
      ((sheafify X).map (λ_ N.val).hom ≫ (sheafifyForgetIso X).hom.app N) =
    ((sheafify X).map (λ_ M.val).hom ≫ (sheafifyForgetIso X).hom.app M) ≫ f
  erw [← Category.assoc, ← Functor.map_comp, id_tensorHom, leftUnitor_naturality,
    Functor.map_comp, Category.assoc, Category.assoc]
  exact congrArg ((sheafify X).map (λ_ M.val).hom ≫ ·)
    ((sheafifyForgetIso X).hom.naturality f)

lemma tensorRightUnitor_naturality {M N : X.Modules} (f : M ⟶ N) :
    tensorMap f (𝟙 (structureSheaf X)) ≫ (tensorRightUnitor N).hom =
      (tensorRightUnitor M).hom ≫ f := by
  change (sheafify X).map (f.val ⊗ₘ (𝟙 _)) ≫
      ((sheafify X).map (ρ_ N.val).hom ≫ (sheafifyForgetIso X).hom.app N) =
    ((sheafify X).map (ρ_ M.val).hom ≫ (sheafifyForgetIso X).hom.app M) ≫ f
  erw [← Category.assoc, ← Functor.map_comp, tensorHom_id, rightUnitor_naturality,
    Functor.map_comp, Category.assoc, Category.assoc]
  exact congrArg ((sheafify X).map (ρ_ M.val).hom ≫ ·)
    ((sheafifyForgetIso X).hom.naturality f)

lemma tensorUnitors_equal (X : Scheme.{u}) :
    (tensorLeftUnitor (structureSheaf X)).hom =
      (tensorRightUnitor (structureSheaf X)).hom := by
  change (sheafify X).map (λ_ (𝟙_ X.PresheafOfModules)).hom ≫
      (sheafifyForgetIso X).hom.app (structureSheaf X) =
    (sheafify X).map (ρ_ (𝟙_ X.PresheafOfModules)).hom ≫
      (sheafifyForgetIso X).hom.app (structureSheaf X)
  erw [unitors_equal]

end Langlands.Scheme.Modules

namespace Langlands.AlgebraicGeometry.Picard.RigidifiedLineBundle

open Langlands.SchemeModule Langlands.Scheme.Modules

variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})
variable (coherence : PullbackTensorUnitCoherenceStatement.{u})
variable {S X : Scheme.{u}} {ε : S ⟶ X}

include coherence in
lemma tensorLeftUnitor_compatibility (L : RigidifiedLineBundle ε) :
    (tensor preservation (trivial ε) L).obj.rigidification.hom ≫
        (Scheme.Modules.pullback ε).map (tensorLeftUnitor L.obj.carrier).hom =
      L.obj.rigidification.hom := by
  erw [← coherence.1 S X ε L.obj.carrier, ← Category.assoc,
    ← Category.assoc,
    RigidifiedModule.tensorObj_rigidification_comp preservation (trivial ε).obj L.obj]
  erw [← Category.assoc, Category.assoc (tensorLeftUnitor (structureModule S)).inv,
    tensorMap_comp
    (trivial ε).obj.rigidification.hom (pullbackUnitIso ε).hom
    L.obj.rigidification.hom (𝟙 _)]
  change ((tensorLeftUnitor (structureSheaf S)).inv ≫
      tensorMap ((pullbackUnitIso ε).inv ≫ (pullbackUnitIso ε).hom)
        (L.obj.rigidification.hom ≫ 𝟙 _)) ≫
      (tensorLeftUnitor ((Scheme.Modules.pullback ε).obj L.obj.carrier)).hom =
    L.obj.rigidification.hom
  erw [Iso.inv_hom_id, Category.comp_id, Category.assoc,
    tensorLeftUnitor_naturality L.obj.rigidification.hom, ← Category.assoc,
    Iso.inv_hom_id, Category.id_comp]

/-- The explicit left unitor respects the rigidifications. -/
def tensorLeftUnitIso (L : RigidifiedLineBundle ε) :
    tensor preservation (trivial ε) L ≅ L :=
  isoMk (tensorLeftUnitor L.obj.carrier)
    (tensorLeftUnitor_compatibility preservation coherence L)

include coherence in
lemma tensorRightUnitor_compatibility (L : RigidifiedLineBundle ε) :
    (tensor preservation L (trivial ε)).obj.rigidification.hom ≫
        (Scheme.Modules.pullback ε).map (tensorRightUnitor L.obj.carrier).hom =
      L.obj.rigidification.hom := by
  erw [← coherence.2 S X ε L.obj.carrier, ← Category.assoc,
    ← Category.assoc,
    RigidifiedModule.tensorObj_rigidification_comp preservation L.obj (trivial ε).obj]
  erw [← Category.assoc, Category.assoc (tensorLeftUnitor (structureModule S)).inv,
    tensorMap_comp L.obj.rigidification.hom (𝟙 _)
      (trivial ε).obj.rigidification.hom (pullbackUnitIso ε).hom]
  change ((tensorLeftUnitor (structureSheaf S)).inv ≫
      tensorMap (L.obj.rigidification.hom ≫ 𝟙 _)
        ((pullbackUnitIso ε).inv ≫ (pullbackUnitIso ε).hom)) ≫
      (tensorRightUnitor ((Scheme.Modules.pullback ε).obj L.obj.carrier)).hom =
    L.obj.rigidification.hom
  erw [Category.comp_id, Iso.inv_hom_id, Category.assoc,
    tensorRightUnitor_naturality L.obj.rigidification.hom,
    ← tensorUnitors_equal S, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- The explicit right unitor respects the rigidifications. -/
def tensorRightUnitIso (L : RigidifiedLineBundle ε) :
    tensor preservation L (trivial ε) ≅ L :=
  isoMk (tensorRightUnitor L.obj.carrier)
    (tensorRightUnitor_compatibility preservation coherence L)

variable (f : X ⟶ S) (ε : S ⟶ X) (section_eq : ε ≫ f = 𝟙 S)

include coherence in
/-- The class of the canonically rigidified structure sheaf is a left tensor unit. -/
lemma classesTensor_left_unit (T : Over S) (q : Classes f ε section_eq T) :
    classesTensor preservation f ε section_eq T
        (classOf f ε section_eq (trivial ((relativeSection f ε section_eq).app T))) q = q := by
  refine Quotient.inductionOn q (fun L ↦ ?_)
  exact Quotient.sound ⟨tensorLeftUnitIso preservation coherence L⟩

include coherence in
/-- The class of the canonically rigidified structure sheaf is a right tensor unit. -/
lemma classesTensor_right_unit (T : Over S) (q : Classes f ε section_eq T) :
    classesTensor preservation f ε section_eq T q
        (classOf f ε section_eq (trivial ((relativeSection f ε section_eq).app T))) = q := by
  refine Quotient.inductionOn q (fun L ↦ ?_)
  exact Quotient.sound ⟨tensorRightUnitIso preservation coherence L⟩

end Langlands.AlgebraicGeometry.Picard.RigidifiedLineBundle
