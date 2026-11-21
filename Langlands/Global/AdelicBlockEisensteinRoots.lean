import Langlands.Global.AdelicBlockEisensteinGeometry
import Langlands.Global.AdelicComplexParameters
import Langlands.GroupScheme.Rational.ParabolicCharacterLattice
import Langlands.GroupScheme.Absolute.DynamicParabolicRecognition
import Langlands.GroupScheme.Dynamic.GeneralLinearRepresentability
import Langlands.GroupScheme.Dynamic.GeometricUnipotentRadicalProof
import Langlands.GroupScheme.Rational.AffineGeometricUnipotentRadical
import Langlands.GroupScheme.Rational.ParabolicRootPresentationProof
import Langlands.GroupScheme.Rational.SplitComponentProof
import Langlands.GroupScheme.Reductive.GeneralLinear

/-! # Root and parameter data of the actual scheme block parabolic -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

namespace Langlands.Global.AdelicBlockEisensteinGeometry

open Langlands.GroupScheme Langlands.GroupScheme.GeneralLinear AdelicGroupPoints

variable (F : Type u) [Field F] {n : ℕ} (B : Langlands.GeneralLinear.BlockShape n)

local notation "𝕜" => CommRingCat.of F
local notation "GLG" => groupScheme (Fin n) 𝕜
local notation "wt" => blockShapeWeight B
local notation "P" => blockParabolicScheme (Fin n) 𝕜 wt
local notation "U" => blockUnipotentScheme (Fin n) 𝕜 wt
local notation "M" => blockLeviScheme (Fin n) 𝕜 wt
local notation "p" => blockParabolicHom (Fin n) 𝕜 wt
local notation "uG" => blockUnipotentHom (Fin n) 𝕜 wt
local notation "mG" => blockLeviHom (Fin n) 𝕜 wt
local notation "ζ" => diagonalCocharacter (Fin n) 𝕜 wt
local notation "l" => blockLeviInclusion F B
local notation "iU" => blockUnipotentInclusion F B

local instance blockRootsGeneralLinearIsAffineHom : IsAffineHom (GLG).X.hom :=
  isAffineHom_groupScheme (n := Fin n) (R := 𝕜)

/-- The scheme block parabolic represents the dynamic parabolic of the canonical cocharacter. -/
theorem blockParabolic_isParabolicSubgroup : IsParabolicSubgroup p :=
  isParabolicSubgroup_of_range_eq_dynamicParabolic (isConnectedReductive_generalLinear F (Fin n)) p
    (isClosedSubgroup_blockParabolicHom (Fin n) 𝕜 wt) ζ
    (isRepresentedBy_parabolic_diagonalCocharacter (Fin n) 𝕜 wt).2

/-- The block-unipotent inclusion is the geometric unipotent radical of the actual block parabolic. -/
theorem blockUnipotentInclusion_isGeometricUnipotentRadical :
    IsGeometricUnipotentRadical iU := by
  apply dynamicGeometricUnipotentRadical F GLG (isConnectedReductive_generalLinear F (Fin n)) ζ P U p iU
    (isRepresentedBy_parabolic_diagonalCocharacter (Fin n) 𝕜 wt)
  rw [blockUnipotentInclusion_comp]
  exact isRepresentedBy_unipotent_diagonalCocharacter (Fin n) 𝕜 wt

theorem blockParabolic_isAffine : IsAffine (P).X.left :=
  let : IsAffineHom (P).X.hom := (isClosedSubgroup_blockParabolicHom (Fin n) 𝕜 wt).isAffineHom
  isAffine_of_isAffineHom (P).X.hom

/-- The geometric radical satisfies the Levi-subgroup form used in the Eisenstein statement. -/
theorem blockUnipotentInclusion_isLeviGeometricUnipotentRadical :
    LeviSubgroup.IsGeometricUnipotentRadical iU :=
  let : IsAffineHom (P).X.hom := (isClosedSubgroup_blockParabolicHom (Fin n) 𝕜 wt).isAffineHom
  (blockUnipotentInclusion_isGeometricUnipotentRadical F B).leviSubgroup

/-- The actual block Levi is the connected reductive centralizer of the canonical cocharacter. -/
theorem blockLevi_isConnectedReductive : IsConnectedReductive M :=
  dynamicCentralizerReductive F GLG (isConnectedReductive_generalLinear F (Fin n)) ζ M mG
    (isClosedSubgroup_blockLeviHom (Fin n) 𝕜 wt)
    (isRepresentedBy_centralizer_diagonalCocharacter (Fin n) 𝕜 wt)

/-- The block-diagonal inclusion is a rational Levi for the same parabolic and radical. -/
theorem blockLeviInclusion_isRationalLeviSubgroup : IsRationalLeviSubgroup l :=
  Dynamic.isRationalLeviSubgroup_of_geometricUnipotentRadical
    (isRepresentedBy_parabolic_diagonalCocharacter (Fin n) 𝕜 wt)
    (isRepresentedBy_centralizer_diagonalCocharacter (Fin n) 𝕜 wt)
    (isRepresentedBy_unipotent_diagonalCocharacter (Fin n) 𝕜 wt)
    l iU (blockLeviInclusion_comp F B) (blockUnipotentInclusion_comp F B)
    (blockLevi_isConnectedReductive F B) (blockUnipotentInclusion_isGeometricUnipotentRadical F B)

/-- A split component of the block Levi with a compatible root presentation. -/
structure BlockRootData where
  A : CommGroupScheme (Spec 𝕜)
  a : A.toGrp ⟶ M
  root : ParabolicRootPresentation p l a

/-- Choose a split component and root presentation for the specified block model. -/
def blockRootData : BlockRootData F B :=
  let hG := isConnectedReductive_generalLinear F (Fin n)
  let h := (splitComponentStatement F M (blockLevi_isConnectedReductive F B)).1
  ⟨h.choose, h.choose_spec.choose, Classical.choice
    (parabolicRootPresentationExistence F GLG hG P M h.choose p l h.choose_spec.choose
      (blockParabolic_isParabolicSubgroup F B) (blockLeviInclusion_isRationalLeviSubgroup F B)
      h.choose_spec.choose_spec)⟩

variable {F B} (data : BlockRootData F B)

theorem BlockRootData.splitComponent : IsSplitTorus data.A.toGrp :=
  data.root.isCompatible.splitComponent.isCentralSplitTorus.1.1

theorem BlockRootData.splitTorus : IsSplitTorus data.root.data.T.toGrp :=
  data.root.isCompatible.maximalSplit.isSplitSubtorus.1

theorem BlockRootData.torus_mono : Mono data.root.data.i.hom.hom.left :=
  data.root.isCompatible.maximalSplit.isSplitSubtorus.2.mono

theorem BlockRootData.finite_weylGroup : Finite (relativeWeylGroup data.root.data.i) :=
  (isConnectedReductive_generalLinear F (Fin n)).finite_relativeWeylGroup _ data.root.isCompatible.maximalSplit

theorem BlockRootData.factor_mono : Mono (CommGroupScheme.groupHom data.root.data.f).hom.hom.left := by
  have hcomp : Mono ((CommGroupScheme.groupHom data.root.data.f).hom.hom.left ≫ data.root.data.i.hom.hom.left) := by
    change Mono (CommGroupScheme.groupHom data.root.data.f ≫ data.root.data.i).hom.hom.left
    rw [data.root.isCompatible.factor_comp]
    have := data.root.isCompatible.splitComponent.isCentralSplitTorus.1.mono
    have := data.root.isCompatible.levi.isClosedSubgroup.mono
    have := data.root.isCompatible.parabolic.isClosedSubgroup.mono
    change Mono (data.a.hom.hom.left ≫ (l).hom.hom.left ≫ (p).hom.hom.left)
    infer_instance
  exact mono_of_mono (CommGroupScheme.groupHom data.root.data.f).hom.hom.left data.root.data.i.hom.hom.left

variable [NumberField F]

include data in
/-- A complex coordinate chart for the full block-parabolic character parameter. -/
def BlockRootData.parameterCoordinates :
    (Fin (Module.finrank ℂ (ComplexCharacterParameter F P)) → ℂ) ≃ₗ[ℂ] ComplexCharacterParameter F P := by
  let : IsAffine (P).X.left := blockParabolic_isAffine F B
  have := (data.root.rationalCharacters_free_finite (isConnectedReductive_generalLinear F (Fin n))).2
  let : FiniteDimensional ℂ (ComplexCharacterParameter F P) := Module.Finite.base_change ℤ ℂ _
  let : Module.Free ℂ (ComplexCharacterParameter F P) :=
    Module.Free.of_divisionRing ℂ (ComplexCharacterParameter F P)
  exact (Module.finBasis ℂ (ComplexCharacterParameter F P)).equivFun.symm

end Langlands.Global.AdelicBlockEisensteinGeometry
