import Langlands.AlgebraicGeometry.Picard.RigidifiedTensorUnit
import Langlands.AlgebraicGeometry.Picard.RigidificationAdjustment
import Langlands.AlgebraicGeometry.Modules.PullbackTensorUnitProofs

/-! # Rigidified line bundles with isomorphic underlying bundles -/

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard.RigidifiedLineBundle

open Langlands.SchemeModule Langlands.Scheme.Modules

variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})
variable {S X : Scheme.{u}} {ε : S ⟶ X}

/-- The structure sheaf rigidified by the canonical comparison twisted by an
automorphism of the structure sheaf of the base. -/
def twistedTrivial (ε : S ⟶ X) (c : structureModule S ≅ structureModule S) :
    RigidifiedLineBundle ε :=
  ofLineBundle (LineBundle.trivial X) (c ≪≫ (pullbackUnitIso ε).symm)

/-- Tensoring a section of a module with an endomorphism of the structure sheaf
and applying the unitors gives the composite. -/
lemma unitor_tensorMap_unitor {P : S.Modules} (b b' : structureSheaf S ⟶ P)
    (c c' : structureSheaf S ⟶ structureSheaf S) (hb : b' = b) (hc : c' = c) :
    ((tensorLeftUnitor (structureSheaf S)).inv ≫ tensorMap b' c') ≫
        (tensorRightUnitor P).hom = c ≫ b := by
  subst hb hc
  have hsplit : tensorMap b' c' = tensorMap (𝟙 _) c' ≫ tensorMap b' (𝟙 _) := by
    rw [tensorMap_comp, Category.id_comp, Category.comp_id]
  rw [hsplit, Category.assoc, Category.assoc, tensorRightUnitor_naturality b',
    ← tensorUnitors_equal S, ← Category.assoc (tensorMap (𝟙 _) c'),
    tensorLeftUnitor_naturality c', ← Category.assoc, ← Category.assoc,
    Iso.inv_hom_id, Category.id_comp]

lemma tensorTwistedTrivial_compatibility (L : RigidifiedLineBundle ε)
    (c : structureModule S ≅ structureModule S) :
    (tensor preservation L (twistedTrivial ε c)).obj.rigidification.hom ≫
        (Scheme.Modules.pullback ε).map (tensorRightUnitor L.obj.carrier).hom =
      c.hom ≫ L.obj.rigidification.hom := by
  erw [← pullbackTensorUnitCoherence.2 S X ε L.obj.carrier, ← Category.assoc,
    ← Category.assoc,
    RigidifiedModule.tensorObj_rigidification_comp preservation L.obj
      (twistedTrivial ε c).obj]
  erw [← Category.assoc, Category.assoc (tensorLeftUnitor (structureModule S)).inv,
    tensorMap_comp L.obj.rigidification.hom (𝟙 _)
      (twistedTrivial ε c).obj.rigidification.hom (pullbackUnitIso ε).hom]
  change ((tensorLeftUnitor (structureSheaf S)).inv ≫
      tensorMap (L.obj.rigidification.hom ≫ 𝟙 _)
        ((c.hom ≫ (pullbackUnitIso ε).inv) ≫ (pullbackUnitIso ε).hom)) ≫
      (tensorRightUnitor ((Scheme.Modules.pullback ε).obj L.obj.carrier)).hom =
    c.hom ≫ L.obj.rigidification.hom
  exact unitor_tensorMap_unitor _ _ _ _ (Category.comp_id _)
    ((Category.assoc _ _ _).trans
      ((congrArg (c.hom ≫ ·) (Iso.inv_hom_id _)).trans (Category.comp_id _)))

/-- If a rigidified line bundle admits a retraction of its rigidification
section, then any isomorphism of underlying module sheaves can be corrected to an
isomorphism of rigidified line bundles. -/
def isoOfCarrierIso (p : X ⟶ S) (hp : ε ≫ p = 𝟙 S) {L M : RigidifiedLineBundle ε}
    (e : L.obj.carrier ≅ M.obj.carrier) : L ≅ M :=
  let c : structureModule S ≅ structureModule S :=
    L.obj.rigidification ≪≫ (Scheme.Modules.pullback ε).mapIso e ≪≫
      M.obj.rigidification.symm
  isoMk (L := L) (M := tensor preservation M (twistedTrivial ε c))
      (e ≪≫ (tensorRightUnitor M.obj.carrier).symm) (by
        have h := tensorTwistedTrivial_compatibility preservation M c
        have h' : (tensor preservation M (twistedTrivial ε c)).obj.rigidification.hom =
            (c.hom ≫ M.obj.rigidification.hom) ≫
              (Scheme.Modules.pullback ε).map (tensorRightUnitor M.obj.carrier).inv := by
          exact (Iso.eq_comp_inv ((Scheme.Modules.pullback ε).mapIso
            (tensorRightUnitor M.obj.carrier))).mpr h
        rw [h']
        simp [c]
        exact congrArg (L.obj.rigidification.hom ≫ ·)
          ((Scheme.Modules.pullback ε).map_comp _ _)) ≪≫
    tensorIso preservation (Iso.refl M)
      (trivialIsoOfCarrierIso p ε hp (twistedTrivial ε c) (Iso.refl _)) ≪≫
    tensorRightUnitIso preservation pullbackTensorUnitCoherence M

include preservation in
/-- Rigidified line bundles with isomorphic underlying line bundles are
isomorphic, provided the rigidification section has a retraction. -/
theorem nonempty_iso_of_forget_iso (p : X ⟶ S) (hp : ε ≫ p = 𝟙 S)
    {L M : RigidifiedLineBundle ε} (e : (forget ε).obj L ≅ (forget ε).obj M) :
    Nonempty (L ≅ M) :=
  ⟨isoOfCarrierIso preservation p hp ((LineBundle.forget X).mapIso e)⟩

end Langlands.AlgebraicGeometry.Picard.RigidifiedLineBundle
