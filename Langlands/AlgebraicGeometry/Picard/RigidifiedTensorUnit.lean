import Langlands.AlgebraicGeometry.Picard.RigidifiedLineBundleTensor
import Langlands.AlgebraicGeometry.Modules.PullbackTensorUnitStatements
import Langlands.AlgebraicGeometry.Modules.TensorUnitorLaws

/-! # Unit isomorphisms for rigidified line-bundle tensor -/

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

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
