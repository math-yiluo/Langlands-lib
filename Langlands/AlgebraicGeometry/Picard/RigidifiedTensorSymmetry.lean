import Langlands.AlgebraicGeometry.Picard.RelativePicardZeroTensor
import Langlands.AlgebraicGeometry.Modules.PullbackTensorCompatibilityStatements

/-! # Symmetry of rigidified line-bundle tensor -/

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace Langlands.Scheme.Modules

open MonoidalCategory BraidedCategory

variable {X : Scheme.{u}}

local instance : MonoidalCategory X.PresheafOfModules :=
  inferInstanceAs (MonoidalCategory (PresheafOfModulesOfCommRing.{u} X.presheaf))

local instance : SymmetricCategory X.PresheafOfModules :=
  inferInstanceAs (SymmetricCategory (PresheafOfModulesOfCommRing.{u} X.presheaf))

/-- The explicit sheaf tensor swap is natural in both variables. -/
lemma tensorComm_naturality {M M' N N' : X.Modules} (f : M ⟶ M') (g : N ⟶ N') :
    tensorMap f g ≫ (tensorComm M' N').hom =
      (tensorComm M N).hom ≫ tensorMap g f := by
  change (sheafify X).map (f.val ⊗ₘ g.val) ≫ (sheafify X).map (β_ M'.val N'.val).hom =
    (sheafify X).map (β_ M.val N.val).hom ≫ (sheafify X).map (g.val ⊗ₘ f.val)
  erw [← Functor.map_comp, ← Functor.map_comp, braiding_naturality]

/-- Swapping the two copies of the structure sheaf is the identity. -/
lemma tensorComm_structureSheaf (X : Scheme.{u}) :
    (tensorComm (structureSheaf X) (structureSheaf X)).hom = 𝟙 _ := by
  change (sheafify X).map
    (β_ (𝟙_ X.PresheafOfModules) (𝟙_ X.PresheafOfModules)).hom = 𝟙 _
  erw [braiding_tensorUnit_left, unitors_equal, Iso.hom_inv_id]
  exact (sheafify X).map_id _

end Langlands.Scheme.Modules

namespace Langlands.AlgebraicGeometry.Picard.RigidifiedLineBundle

open Langlands.SchemeModule Langlands.Scheme.Modules

variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})
variable (symmetry : PullbackTensorSymmetryStatement.{u})
variable {S X : Scheme.{u}} {ε : S ⟶ X}

include symmetry in
/-- The actual sheaf tensor swap respects the two tensor rigidifications. -/
lemma tensorComm_compatibility (L M : RigidifiedLineBundle ε) :
    (tensor preservation L M).obj.rigidification.hom ≫
        (Scheme.Modules.pullback ε).map (Langlands.Scheme.Modules.tensorComm
          L.obj.carrier M.obj.carrier).hom =
      (tensor preservation M L).obj.rigidification.hom := by
  let := preservation ε
  apply (cancel_mono ((asIso (pullbackTensorComparison ε)).app
    (M.obj.carrier, L.obj.carrier)).hom).1
  change ((tensor preservation L M).obj.rigidification.hom ≫
      (Scheme.Modules.pullback ε).map
        (Langlands.Scheme.Modules.tensorComm L.obj.carrier M.obj.carrier).hom) ≫
        pullbackTensorComparisonApp ε M.obj.carrier L.obj.carrier =
    (tensor preservation M L).obj.rigidification.hom ≫
      pullbackTensorComparisonApp ε M.obj.carrier L.obj.carrier
  erw [Category.assoc, ← symmetry S X ε L.obj.carrier M.obj.carrier, ← Category.assoc,
    RigidifiedModule.tensorObj_rigidification_comp preservation L.obj M.obj,
    RigidifiedModule.tensorObj_rigidification_comp preservation M.obj L.obj,
    Category.assoc, tensorComm_naturality L.obj.rigidification.hom M.obj.rigidification.hom,
    ← Category.assoc, tensorComm_structureSheaf S, Category.comp_id]
  rfl

/-- The canonical tensor swap as a compatible rigidified line-bundle isomorphism. -/
def tensorComm (L M : RigidifiedLineBundle ε) :
    tensor preservation L M ≅ tensor preservation M L :=
  isoMk (Langlands.Scheme.Modules.tensorComm L.obj.carrier M.obj.carrier)
    (tensorComm_compatibility preservation symmetry L M)

variable (f : X ⟶ S) (ε : S ⟶ X) (section_eq : ε ≫ f = 𝟙 S)

include symmetry in
/-- Tensor on relative rigidified classes is commutative. -/
lemma classesTensor_comm (T : Over S) (q r : Classes f ε section_eq T) :
    classesTensor preservation f ε section_eq T q r =
      classesTensor preservation f ε section_eq T r q := by
  refine Quotient.inductionOn₂ q r (fun L M ↦ ?_)
  exact Quotient.sound ⟨tensorComm preservation symmetry L M⟩

end Langlands.AlgebraicGeometry.Picard.RigidifiedLineBundle

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules

variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})
variable (symmetry : PullbackTensorSymmetryStatement.{u})
variable {S : Scheme.{u}} (A : AbelianScheme S)

include symmetry in
/-- Tensor on relative Picard-zero classes is commutative. -/
lemma picardZeroClassesTensor_comm (T : Over S) (q r : PicardZeroClasses A T) :
    picardZeroClassesTensor preservation A T q r =
      picardZeroClassesTensor preservation A T r q := by
  apply Subtype.ext
  exact RigidifiedLineBundle.classesTensor_comm preservation symmetry
    A.X.hom (unitSection A) (unitSection_comp A) T q.val r.val

end Langlands.AbelianScheme
