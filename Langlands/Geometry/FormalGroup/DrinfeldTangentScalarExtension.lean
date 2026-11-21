import Langlands.Geometry.FormalGroup.DrinfeldTangentBaseChange
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.LinearAlgebra.TensorProduct.Pi

/-! # Scalar extension of the total Drinfeld tangent module and its operators -/

noncomputable section

namespace Langlands.FormalGroup.LocalDivision

open ValuativeRel CentralDivision CentralSimple CategoryTheory ModuleLaw
open scoped TensorProduct ChangeOfRings

universe u v s

section Coordinates

variable {R S : Type v} [CommRing R] [CommRing S] (φ : R →+* S)
variable (I : Type) [Finite I]

/-- Scalar extension of the free coordinate tangent module is coefficient extension. -/
def tangentScalarExtensionIso :
    (ModuleCat.extendScalars φ).obj (ModuleCat.of R (I → R)) ≅ ModuleCat.of S (I → S) := by
  classical
  let : Fintype I := Fintype.ofFinite I
  letI : Algebra R S := φ.toAlgebra
  exact (TensorProduct.piScalarRight R S S I).toModuleIso

/-- The tangent scalar extension comparison applies the coefficient map on pure tensors. -/
theorem tangentScalarExtensionIso_hom_tmul (s : S) (x : I → R) :
    (tangentScalarExtensionIso φ I).hom (s ⊗ₜ[R,φ] x) = s • (fun i => φ (x i)) := by
  classical
  let : Fintype I := Fintype.ofFinite I
  let : Algebra R S := φ.toAlgebra
  change (TensorProduct.piScalarRight R S S I) (s ⊗ₜ[R] x) = _
  rw [TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul]
  funext i
  change x i • s = s * φ (x i)
  exact mul_comm _ _

private theorem tangentScalarExtensionIso_intertwines
    (P : Module.End R (I → R)) (Q : Module.End S (I → S))
    (h : ∀ x, (fun i => φ (P x i)) = Q (fun i => φ (x i))) :
    (ModuleCat.extendScalars φ).map (ModuleCat.ofHom P) ≫ (tangentScalarExtensionIso φ I).hom =
      (tangentScalarExtensionIso φ I).hom ≫ ModuleCat.ofHom Q := by
  apply ModuleCat.ExtendScalars.hom_ext
  intro x
  change (tangentScalarExtensionIso φ I).hom ((ModuleCat.extendScalars φ).map
      (ModuleCat.ofHom P) ((1 : S) ⊗ₜ[R,φ] x)) =
    Q ((tangentScalarExtensionIso φ I).hom ((1 : S) ⊗ₜ[R,φ] x))
  have hgen (y : I → R) :
      (tangentScalarExtensionIso φ I).hom ((1 : S) ⊗ₜ[R,φ] y) = fun i => φ (y i) :=
    (tangentScalarExtensionIso_hom_tmul φ I 1 y).trans (one_smul S _)
  calc
    _ = (tangentScalarExtensionIso φ I).hom ((1 : S) ⊗ₜ[R,φ] (P x)) := rfl
    _ = (fun i => φ (P x i)) := hgen (P x)
    _ = Q (fun i => φ (x i)) := h x
    _ = _ := congrArg Q (hgen x).symm

end Coordinates

variable {K D : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
variable {L : Type s} [Field L] [Algebra K L] (ι : L →ₐ[K] D)

local instance tangentScalarExtensionLocalHom :
    IsLocalHom (algebraMap 𝒪[K] (SubfieldIntegerRing K D ι)) := subfieldIntegerAlgebra_isLocalHom ι

variable {κ : Type u} [Field κ] [Algebra 𝒪[K] κ] [Algebra 𝓀[K] κ]
  [IsScalarTower 𝒪[K] 𝓀[K] κ]
variable (hL : IsUnramifiedSubfieldOfReducedDegree K D ι)
variable (χ : IsLocalRing.ResidueField (SubfieldIntegerRing K D ι) →ₐ[𝓀[K]] κ)
variable {π : 𝒪[K]} {B B' : Nilp.{u, v} 𝒪[K] π} (ψ : κ →ₐ[𝒪[K]] Nilp.Reduction π B.obj)
variable {I : Type} [Finite I] {M : ModuleLaw 𝒪[K] B.obj I}
  (E : OrderAction (IntegerRing K D) M) (f : B ⟶ B')

local notation "d" => CentralSimple.reducedDegree K D
local notation "φ" => CommAlgCat.Hom.hom (InducedCategory.Hom.hom f)
local notation "ψ'" => AlgHom.comp (Nilp.reductionMap φ) ψ
local notation "F" => ModuleCat.extendScalars (AlgHom.toRingHom φ)
local notation "e" => tangentScalarExtensionIso (AlgHom.toRingHom φ) I

/-- The total tangent scalar extension identification intertwines every order element. -/
theorem tangentScalarExtensionIso_order (a : IntegerRing K D) :
    (F).map (ModuleCat.ofHom (E.tangentAction a)) ≫ (e).hom =
      (e).hom ≫ ModuleCat.ofHom ((E.map φ).tangentAction a) :=
  tangentScalarExtensionIso_intertwines (φ).toRingHom I _ _ (E.tangentAction_map_apply φ a)

/-- The same identification intertwines each actual cyclic character projector. -/
theorem tangentScalarExtensionIso_projector (i : Fin d) :
    (F).map (ModuleCat.ofHom (drinfeldTangentProjector ι hL χ ψ E i)) ≫ (e).hom =
      (e).hom ≫ ModuleCat.ofHom (drinfeldTangentProjector ι hL χ ψ' (E.map φ) i) :=
  tangentScalarExtensionIso_intertwines (φ).toRingHom I _ _
    (drinfeldTangentProjector_natural ι hL χ ψ E f i)

end Langlands.FormalGroup.LocalDivision
