import Langlands.Representation.Plancherel.RationalUnramifiedRestriction
import Langlands.Representation.Plancherel.RationalCentralQuotient
import Langlands.Representation.Plancherel.TwistStabilizerComparison

/-! # The actual split-center restriction kernel -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped NNReal CategoryTheory.MonObj

namespace Langlands.Plancherel

universe u

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable {G H : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [IsAffine H.X.left]

local instance : TopologicalSpace (GroupScheme.rationalPoints G) :=
  rationalPointTopology F G.X
local instance : TopologicalSpace (GroupScheme.rationalPoints H) :=
  rationalPointTopology F H.X

/-- A character is in the actual restriction kernel precisely when it is
trivial at every image point. -/
theorem mem_rationalUnramifiedCharacterRestrict_ker (f : H ⟶ G)
    (chi : unramifiedCharacters (fun psi => (rationalNormCharacters G psi).toMul)) :
    chi ∈ (rationalUnramifiedCharacterRestrict f).toMonoidHom.ker ↔
      ∀ h : GroupScheme.rationalPoints H,
        chi.val (GroupScheme.rationalPoints.map f h) = 1 := by
  change rationalUnramifiedCharacterRestrict f chi = 1 ↔ _
  constructor
  · intro h y
    exact DFunLike.congr_fun (congrArg Subtype.val h) y
  · intro h
    apply Subtype.ext
    exact ContinuousMonoidHom.ext h

/-- The unitary restriction has the same pointwise kernel condition. -/
theorem mem_rationalUnitaryUnramifiedCharacterRestrict_ker (f : H ⟶ G)
    (chi : unitaryUnramifiedCharacters
      (fun psi => (rationalNormCharacters G psi).toMul)) :
    chi ∈ (rationalUnitaryUnramifiedCharacterRestrict f).toMonoidHom.ker ↔
      ∀ h : GroupScheme.rationalPoints H,
        chi.val (GroupScheme.rationalPoints.map f h) = 1 := by
  change rationalUnitaryUnramifiedCharacterRestrict f chi = 1 ↔ _
  constructor
  · intro h y
    exact DFunLike.congr_fun (congrArg Subtype.val h) y
  · intro h
    apply Subtype.ext
    exact ContinuousMonoidHom.ext h

/-- The actual scheme-morphism restriction kernel is the existing subgroup
of unramified characters trivial on the actual point-map range. -/
theorem rationalUnramifiedCharacterRestrict_ker (f : H ⟶ G) :
    (rationalUnramifiedCharacterRestrict f).toMonoidHom.ker =
      centralTrivialUnramifiedCharacters
        (fun psi => (rationalNormCharacters G psi).toMul)
        (GroupScheme.rationalPoints.map f).range := by
  ext chi
  rw [mem_rationalUnramifiedCharacterRestrict_ker,
    mem_centralTrivialUnramifiedCharacters]
  constructor
  · intro h a
    obtain ⟨y, hy⟩ := a.property
    simpa only [hy] using h y
  · intro h y
    exact h ⟨_, y, rfl⟩

section CentralImage

variable {T : CommGroupScheme (Spec (CommRingCat.of F))} [IsAffine T.X.left]

local instance : TopologicalSpace (GroupScheme.rationalPoints T.toGrp) :=
  rationalPointTopology F T.X

/-- Finite index of the actual central valuation image makes the complex
restriction kernel finite. -/
theorem finite_rationalUnramifiedCharacterRestrict_ker (s : T.toGrp ⟶ G)
    (hs : GroupScheme.IsCentral s) (hindex : (RenardCartan.splitValuationImage s).FiniteIndex) :
    Finite (rationalUnramifiedCharacterRestrict s).toMonoidHom.ker := by
  let := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
  let : Finite (GroupScheme.rationalPoints G ⧸
      (commonNormKernel (fun psi => (rationalNormCharacters G psi).toMul) ⊔
        (GroupScheme.rationalPoints.map s).range)) :=
    finite_rationalCentralQuotient s hs hindex
  rw [rationalUnramifiedCharacterRestrict_ker]
  exact finite_centralTrivialUnramifiedCharacters _ _

/-- Every complex character in this kernel is unitary under the same
explicit finite-index premise. -/
theorem rationalUnramifiedCharacterRestrict_ker_norm_eq_one (s : T.toGrp ⟶ G)
    (hs : GroupScheme.IsCentral s) (hindex : (RenardCartan.splitValuationImage s).FiniteIndex)
    (chi : (rationalUnramifiedCharacterRestrict s).toMonoidHom.ker)
    (g : GroupScheme.rationalPoints G) :
    ‖(chi.val.val g : ℂ)‖ = 1 := by
  let := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
  let : Finite (GroupScheme.rationalPoints G ⧸
      (commonNormKernel (fun psi => (rationalNormCharacters G psi).toMul) ⊔
        (GroupScheme.rationalPoints.map s).range)) :=
    finite_rationalCentralQuotient s hs hindex
  exact centralTrivialUnramifiedCharacter_norm_eq_one
    (fun psi => (rationalNormCharacters G psi).toMul)
    (GroupScheme.rationalPoints.map s).range
    ⟨chi.val, by
      rw [← rationalUnramifiedCharacterRestrict_ker s]
      exact chi.property⟩ g

/-- Under finite index of the actual central valuation image, the complex
and unitary restriction kernels consist of the same characters. -/
def rationalUnramifiedRestrictKernelEquivUnitary (s : T.toGrp ⟶ G)
    (hs : GroupScheme.IsCentral s) (hindex : (RenardCartan.splitValuationImage s).FiniteIndex) :
    (rationalUnramifiedCharacterRestrict s).toMonoidHom.ker ≃*
      (rationalUnitaryUnramifiedCharacterRestrict s).toMonoidHom.ker where
  toFun chi :=
    ⟨⟨chi.val.val, chi.val.property,
      rationalUnramifiedCharacterRestrict_ker_norm_eq_one s hs hindex chi⟩, by
      apply (mem_rationalUnitaryUnramifiedCharacterRestrict_ker s _).mpr
      exact (mem_rationalUnramifiedCharacterRestrict_ker s chi.val).mp chi.property⟩
  invFun chi :=
    ⟨⟨chi.val.val, chi.val.property.1⟩, by
      apply (mem_rationalUnramifiedCharacterRestrict_ker s _).mpr
      exact (mem_rationalUnitaryUnramifiedCharacterRestrict_ker s chi.val).mp chi.property⟩
  left_inv _ := Subtype.ext (Subtype.ext rfl)
  right_inv _ := Subtype.ext (Subtype.ext rfl)
  map_mul' _ _ := Subtype.ext (Subtype.ext rfl)

@[simp]
theorem rationalUnramifiedRestrictKernelEquivUnitary_apply (s : T.toGrp ⟶ G)
    (hs : GroupScheme.IsCentral s) (hindex : (RenardCartan.splitValuationImage s).FiniteIndex)
    (chi : (rationalUnramifiedCharacterRestrict s).toMonoidHom.ker)
    (g : GroupScheme.rationalPoints G) :
    (rationalUnramifiedRestrictKernelEquivUnitary s hs hindex chi).val.val g =
      chi.val.val g := rfl

/-- The unitary restriction kernel is finite under the explicit actual-image
finite-index premise. -/
theorem finite_rationalUnitaryUnramifiedCharacterRestrict_ker (s : T.toGrp ⟶ G)
    (hs : GroupScheme.IsCentral s) (hindex : (RenardCartan.splitValuationImage s).FiniteIndex) :
    Finite (rationalUnitaryUnramifiedCharacterRestrict s).toMonoidHom.ker := by
  let := finite_rationalUnramifiedCharacterRestrict_ker s hs hindex
  exact Finite.of_injective _ (rationalUnramifiedRestrictKernelEquivUnitary s hs hindex).symm.injective

end CentralImage

end Langlands.Plancherel
