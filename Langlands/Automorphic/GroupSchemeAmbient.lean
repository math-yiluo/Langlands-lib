import Langlands.Global.AdelicGroupQuotient
import Langlands.Automorphic.Ambient

/-! # Actual ambient functions for group schemes and the general-linear comparison -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open scoped CategoryTheory.MonObj

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F)))

/-- Complex functions on actual adelic points invariant under actual rational points. -/
abbrev RationalInvariantFunctions :=
  Representation.coindV (AdelicGroupPoints.rational F G)
    (Representation.trivial ℂ (RationalGroupPoints F G) ℂ)

/-- Positive right translation, using the same coinduction construction as the matrix space. -/
def rationalRightAction :
    Representation ℂ (AdelicGroupPoints F G) (RationalInvariantFunctions F G) :=
  Representation.coind (AdelicGroupPoints.rational F G)
    (Representation.trivial ℂ (RationalGroupPoints F G) ℂ)

@[simp]
theorem rationalRightAction_apply (g x : AdelicGroupPoints F G)
    (f : RationalInvariantFunctions F G) :
    (rationalRightAction F G g f).val x = f.val (x * g) := rfl

/-- The function descent equivalence preserves the actual complex vector space structures. -/
def quotientLinearEquiv :
    (AdelicGroupPoints.RationalQuotient F G → ℂ) ≃ₗ[ℂ] RationalInvariantFunctions F G where
  toEquiv := AdelicGroupPoints.rationalQuotientFunctionEquiv F G ℂ
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem quotientLinearEquiv_apply
    (f : AdelicGroupPoints.RationalQuotient F G → ℂ) (x : AdelicGroupPoints F G) :
    (quotientLinearEquiv F G f).val x =
      f (LeftCosetSpace.mk (AdelicGroupPoints.rationalSubgroup F G) x) := rfl

/-- Quotient pullback intertwines the positive right actions. -/
theorem quotientLinearEquiv_rightTranslate
    (f : AdelicGroupPoints.RationalQuotient F G → ℂ) (g : AdelicGroupPoints F G) :
    quotientLinearEquiv F G
      (fun q => f (LeftCosetSpace.rightTranslate (AdelicGroupPoints.rationalSubgroup F G) g q)) =
        rationalRightAction F G g (quotientLinearEquiv F G f) := rfl

variable [IsAffine G.X.left]

/-- Continuity cuts out a subrepresentation of the actual ambient group action. -/
def continuousSubrepresentation : Subrepresentation (rationalRightAction F G) where
  toSubmodule := (continuousSubmodule (AdelicGroupPoints F G) ℂ ℂ).comap
    (RationalInvariantFunctions F G).subtype
  apply_mem_toSubmodule g f hf := by
    change Continuous (fun x => f.val (x * g))
    exact hf.comp (continuous_id.mul continuous_const)

/-- Continuous rational-invariant functions on the actual adelic point group. -/
abbrev ContinuousRationalFunctions := (continuousSubrepresentation F G).toSubmodule

/-- Positive right translation on the continuous ambient space. -/
def continuousRightAction :
    Representation ℂ (AdelicGroupPoints F G) (ContinuousRationalFunctions F G) :=
  (continuousSubrepresentation F G).toRepresentation

/-- Continuous quotient functions are exactly continuous rational-invariant functions. -/
def continuousQuotientLinearEquiv :
    C(AdelicGroupPoints.RationalQuotient F G, ℂ) ≃ₗ[ℂ] ContinuousRationalFunctions F G where
  toFun f := ⟨quotientLinearEquiv F G f,
    f.continuous.comp (LeftCosetSpace.continuous_mk (AdelicGroupPoints.rationalSubgroup F G))⟩
  invFun f := ⟨(quotientLinearEquiv F G).symm f.val,
    (LeftCosetSpace.continuous_iff (AdelicGroupPoints.rationalSubgroup F G)).mpr f.property⟩
  left_inv f := by
    apply ContinuousMap.coe_injective
    exact (quotientLinearEquiv F G).left_inv f
  right_inv f := by
    apply Subtype.ext
    exact (quotientLinearEquiv F G).right_inv f.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem continuousQuotientLinearEquiv_apply
    (f : C(AdelicGroupPoints.RationalQuotient F G, ℂ)) (x : AdelicGroupPoints F G) :
    (continuousQuotientLinearEquiv F G f).val.val x =
      f (LeftCosetSpace.mk (AdelicGroupPoints.rationalSubgroup F G) x) := rfl

end Langlands.Automorphic.GroupSchemeFunctions

namespace Langlands.Global.GeneralLinearGroupPoints

variable (F : Type u) [Field F] [NumberField F] (n : ℕ)

/-- The inverse point comparison preserves the actual principal rational map. -/
theorem adelicHomeomorph_symm_rational (q : RationalGL F n) :
    (adelicHomeomorph F n).symm (AdelicGL.rational F n q) =
      AdelicGroupPoints.rational F
        (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F))
        ((rationalEquiv F n).symm q) := by
  apply (adelicHomeomorph F n).injective
  simp only [(adelicHomeomorph F n).apply_symm_apply, adelicHomeomorph_rational,
    MulEquiv.apply_symm_apply]

end Langlands.Global.GeneralLinearGroupPoints

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global

variable (F : Type u) [Field F] [NumberField F] (n : ℕ)

/-- The matrix group scheme is affine by its actual coordinate-ring presentation. -/
local instance generalLinearIsAffine :
    IsAffine (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of F)

/-- Actual point comparison identifies the general group-scheme and existing matrix ambient spaces. -/
def generalLinearEquiv :
    RationalInvariantFunctions F
      (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F))
      ≃ₗ[ℂ] Langlands.Automorphic.RationalInvariantFunctions F n where
  toFun f := ⟨fun x => f.val ((GeneralLinearGroupPoints.adelicHomeomorph F n).symm x), by
    intro q x
    change f.val ((GeneralLinearGroupPoints.adelicHomeomorph F n).symm
      (AdelicGL.rational F n q * x)) = _
    rw [map_mul, GeneralLinearGroupPoints.adelicHomeomorph_symm_rational]
    exact f.property ((GeneralLinearGroupPoints.rationalEquiv F n).symm q) _⟩
  invFun f := ⟨fun x => f.val (GeneralLinearGroupPoints.adelicHomeomorph F n x), by
    intro q x
    change f.val (GeneralLinearGroupPoints.adelicHomeomorph F n
      (AdelicGroupPoints.rational F _ q * x)) = _
    rw [map_mul, GeneralLinearGroupPoints.adelicHomeomorph_rational]
    exact f.property (GeneralLinearGroupPoints.rationalEquiv F n q) _⟩
  left_inv f := by
    apply Subtype.ext
    funext x
    exact congrArg f.val ((GeneralLinearGroupPoints.adelicHomeomorph F n).symm_apply_apply x)
  right_inv f := by
    apply Subtype.ext
    funext x
    exact congrArg f.val ((GeneralLinearGroupPoints.adelicHomeomorph F n).apply_symm_apply x)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem generalLinearEquiv_apply
    (f : RationalInvariantFunctions F
      (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)))
    (x : AdelicGL F n) :
    (generalLinearEquiv F n f).val x =
      f.val ((GeneralLinearGroupPoints.adelicHomeomorph F n).symm x) := rfl

/-- The comparison intertwines the actual positive right-translation representations. -/
theorem generalLinearEquiv_rightAction
    (f : RationalInvariantFunctions F
      (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)))
    (g : AdelicGroupPoints F
      (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F))) :
    generalLinearEquiv F n (rationalRightAction F _ g f) =
      Langlands.Automorphic.rationalRightAction F n
        (GeneralLinearGroupPoints.adelicHomeomorph F n g) (generalLinearEquiv F n f) := by
  apply Subtype.ext
  funext x
  change f.val ((GeneralLinearGroupPoints.adelicHomeomorph F n).symm x * g) =
    f.val ((GeneralLinearGroupPoints.adelicHomeomorph F n).symm
      (x * GeneralLinearGroupPoints.adelicHomeomorph F n g))
  rw [map_mul, (GeneralLinearGroupPoints.adelicHomeomorph F n).symm_apply_apply]

/-- The matrix comparison restricts to the existing continuous ambient space. -/
def continuousGeneralLinearEquiv :
    ContinuousRationalFunctions F
      (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F))
      ≃ₗ[ℂ] Langlands.Automorphic.ContinuousRationalFunctions F n where
  toFun f := ⟨generalLinearEquiv F n f.val,
    f.property.comp (GeneralLinearGroupPoints.adelicHomeomorph F n).symm.continuous⟩
  invFun f := ⟨(generalLinearEquiv F n).symm f.val,
    f.property.comp (GeneralLinearGroupPoints.adelicHomeomorph F n).continuous⟩
  left_inv f := by
    apply Subtype.ext
    exact (generalLinearEquiv F n).left_inv f.val
  right_inv f := by
    apply Subtype.ext
    exact (generalLinearEquiv F n).right_inv f.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Continuous comparison retains the same right-translation action. -/
theorem continuousGeneralLinearEquiv_rightAction
    (f : ContinuousRationalFunctions F
      (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)))
    (g : AdelicGroupPoints F
      (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F))) :
    continuousGeneralLinearEquiv F n (continuousRightAction F _ g f) =
      Langlands.Automorphic.continuousRightAction F n
        (GeneralLinearGroupPoints.adelicHomeomorph F n g)
        (continuousGeneralLinearEquiv F n f) := by
  apply Subtype.ext
  exact generalLinearEquiv_rightAction F n f.val g

end Langlands.Automorphic.GroupSchemeFunctions
