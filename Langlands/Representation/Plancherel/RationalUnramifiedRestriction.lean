import Langlands.Representation.Plancherel.RationalUnramifiedCharacterTopology
import Langlands.AlgebraicGeometry.PointTopology.RepresentedSubgroup

/-! # Restriction of actual unramified characters -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped NNReal CategoryTheory.MonObj

namespace Langlands.Plancherel

universe u

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable {G H K : GroupScheme (Spec (CommRingCat.of F))}

/-- Actual point maps send the source common norm kernel into the target one. -/
theorem rationalCommonNormKernel_le_comap (f : H ⟶ G) :
    rationalCommonNormKernel H ≤
      (rationalCommonNormKernel G).comap (GroupScheme.rationalPoints.map f) := by
  intro y hy
  apply (mem_rationalCommonNormKernel G _).mpr
  intro chi
  have h := (mem_rationalCommonNormKernel H y).mp hy
    (GroupScheme.characterRestrict f chi)
  simpa only [GroupScheme.rationalCharacterEval_characterRestrict] using h

section CanonicalTopology

variable [IsAffine G.X.left] [IsAffine H.X.left]

local instance : TopologicalSpace (GroupScheme.rationalPoints G) :=
  rationalPointTopology F G.X
local instance : TopologicalSpace (GroupScheme.rationalPoints H) :=
  rationalPointTopology F H.X

/-- The existing point homomorphism is continuous in the canonical topologies. -/
def rationalContinuousPointsMap (f : H ⟶ G) :
    GroupScheme.rationalPoints H →ₜ* GroupScheme.rationalPoints G where
  toMonoidHom := GroupScheme.rationalPoints.map f
  continuous_toFun := continuous_rationalPointMap F f.hom.hom

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] in
@[simp]
theorem rationalContinuousPointsMap_apply (f : H ⟶ G)
    (h : GroupScheme.rationalPoints H) :
    rationalContinuousPointsMap f h = GroupScheme.rationalPoints.map f h := rfl

/-- Restriction along the actual point map preserves unramified characters
and their compact-open topologies. -/
def rationalUnramifiedCharacterRestrict (f : H ⟶ G) :
    unramifiedCharacters (fun chi => (rationalNormCharacters G chi).toMul) →ₜ*
      unramifiedCharacters (fun chi => (rationalNormCharacters H chi).toMul) where
  toFun chi :=
    ⟨chi.val.comp (rationalContinuousPointsMap f), fun _ hy =>
      chi.property (rationalCommonNormKernel_le_comap f hy)⟩
  map_one' := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl
  continuous_toFun :=
    ((rationalContinuousPointsMap f).continuous_comp_left.comp
      continuous_subtype_val).subtype_mk _

@[simp]
theorem rationalUnramifiedCharacterRestrict_apply (f : H ⟶ G)
    (chi : unramifiedCharacters (fun psi => (rationalNormCharacters G psi).toMul))
    (h : GroupScheme.rationalPoints H) :
    (rationalUnramifiedCharacterRestrict f chi).val h =
      chi.val (GroupScheme.rationalPoints.map f h) := rfl

/-- The same restriction preserves the actual norm-one subgroup. -/
def rationalUnitaryUnramifiedCharacterRestrict (f : H ⟶ G) :
    unitaryUnramifiedCharacters (fun chi => (rationalNormCharacters G chi).toMul) →ₜ*
      unitaryUnramifiedCharacters (fun chi => (rationalNormCharacters H chi).toMul) where
  toFun chi :=
    ⟨chi.val.comp (rationalContinuousPointsMap f),
      ⟨fun _ hy => chi.property.1 (rationalCommonNormKernel_le_comap f hy),
        fun y => chi.property.2 (GroupScheme.rationalPoints.map f y)⟩⟩
  map_one' := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl
  continuous_toFun :=
    ((rationalContinuousPointsMap f).continuous_comp_left.comp
      continuous_subtype_val).subtype_mk _

@[simp]
theorem rationalUnitaryUnramifiedCharacterRestrict_apply (f : H ⟶ G)
    (chi : unitaryUnramifiedCharacters
      (fun psi => (rationalNormCharacters G psi).toMul))
    (h : GroupScheme.rationalPoints H) :
    (rationalUnitaryUnramifiedCharacterRestrict f chi).val h =
      chi.val (GroupScheme.rationalPoints.map f h) := rfl

/-- Forgetting unitary membership commutes with the restriction. -/
theorem rationalUnitaryUnramifiedCharacterRestrict_coe (f : H ⟶ G)
    (chi : unitaryUnramifiedCharacters
      (fun psi => (rationalNormCharacters G psi).toMul)) :
    (rationalUnitaryUnramifiedCharacterRestrict f chi).val =
      (rationalUnramifiedCharacterRestrict f ⟨chi.val, chi.property.1⟩).val := rfl

@[simp]
theorem rationalUnramifiedCharacterRestrict_id
    (chi : unramifiedCharacters (fun psi => (rationalNormCharacters G psi).toMul)) :
    rationalUnramifiedCharacterRestrict (𝟙 G) chi = chi := by
  apply Subtype.ext
  apply ContinuousMonoidHom.ext
  intro g
  change chi.val (g ≫ 𝟙 G.X) = chi.val g
  rw [Category.comp_id]

variable [IsAffine K.X.left]

local instance : TopologicalSpace (GroupScheme.rationalPoints K) :=
  rationalPointTopology F K.X

/-- Successive restrictions agree with restriction along the composite. -/
theorem rationalUnramifiedCharacterRestrict_comp (f : K ⟶ H) (g : H ⟶ G)
    (chi : unramifiedCharacters (fun psi => (rationalNormCharacters G psi).toMul)) :
    rationalUnramifiedCharacterRestrict (f ≫ g) chi =
      rationalUnramifiedCharacterRestrict f (rationalUnramifiedCharacterRestrict g chi) := by
  apply Subtype.ext
  apply ContinuousMonoidHom.ext
  intro k
  change chi.val (k ≫ (f ≫ g).hom.hom) =
    chi.val ((k ≫ f.hom.hom) ≫ g.hom.hom)
  exact congrArg chi.val (Category.assoc _ _ _).symm

end CanonicalTopology

end Langlands.Plancherel
