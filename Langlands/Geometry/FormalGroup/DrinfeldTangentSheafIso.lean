import Langlands.Geometry.FormalGroup.DeligneStructuralCoherence
import Langlands.Geometry.FormalGroup.DrinfeldTangentComparison
import Langlands.Geometry.FormalGroup.DrinfeldTangentLineSheaf

/-! # Actual comparison of affine Drinfeld tangent sheaves -/

noncomputable section

namespace Langlands.FormalGroup.LocalDivision

open ValuativeRel CentralDivision CentralSimple _root_.CategoryTheory _root_.AlgebraicGeometry
  DeligneFormalSpace ModuleLaw

universe u v s

variable {K D : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
variable {L : Type s} [Field L] [Algebra K L] (ι : L →ₐ[K] D)

local instance tangentSheafIsoLocalHom :
    IsLocalHom (algebraMap 𝒪[K] (SubfieldIntegerRing K D ι)) := subfieldIntegerAlgebra_isLocalHom ι

local instance tangentSheafIsoDegree : NeZero (CentralSimple.reducedDegree K D) :=
  ⟨(reducedDegree_pos K D).ne'⟩

variable {κ : Type u} [Field κ] [Algebra 𝒪[K] κ] [Algebra 𝓀[K] κ]
  [IsScalarTower 𝒪[K] 𝓀[K] κ]
variable (χ : IsLocalRing.ResidueField (SubfieldIntegerRing K D ι) →ₐ[𝓀[K]] κ)
variable {π : 𝒪[K]} {B : Nilp.{u, max u v} 𝒪[K] π}
variable (ψ : κ →ₐ[𝒪[K]] Nilp.Reduction π B.obj) {Y Z : SpecialModule K D ι B.obj}
variable (σ : L ≃ₐ[K] L) (uniformizer : Dˣ)
  (hPow : (uniformizer : D) ^ CentralSimple.reducedDegree K D = algebraMap K D (π : K))
  (hComm : ∀ a : L, (uniformizer : D) * ι a = ι (σ a) * (uniformizer : D))
  (hσ : ∀ a : SubfieldIntegerRing K D ι,
    localReducedNormIntValuation K D (ι (σ (a : L)) - ι ((a : L) ^ Nat.card 𝓀[K])) < 1)

local notation "d" => CentralSimple.reducedDegree K D
local notation "idx" => RingEquiv.symm (ZMod.finEquiv (CentralSimple.reducedDegree K D))
local notation "V" => (Fin d → B.obj)
local notation "R" => CommRingCat.of B.obj
local notation "VM" => ModuleCat.of B.obj V
local notation "G" => (fun (T : SpecialModule K D ι B.obj) =>
  drinfeldTangentGradedPiSheaf ι χ ψ T σ uniformizer hPow hComm hσ)
local notation "J" => (fun (T : SpecialModule K D ι B.obj) =>
  drinfeldTangentComponentSheafIso ι χ ψ T σ uniformizer hPow hComm hσ)
local notation "W" => (fun (T : SpecialModule K D ι B.obj) (i : ZMod d) =>
  drinfeldTangentComponent ι (SpecialModule.unramified T) χ ψ (SpecialModule.order T) (idx i))
local notation "t" => (fun (T : SpecialModule K D ι B.obj) =>
  OrderAction.tangentAction (SpecialModule.order T) (drinfeldIntegralUniformizer uniformizer hPow))

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
theorem drinfeldTangentComponentSheafIso_inclusion (T : SpecialModule K D ι B.obj) (i : ZMod d) :
    (J T i).hom ≫ (G T).componentInclusion i =
      tilde.map (ModuleCat.ofHom (W T i).subtype) :=
  splitRangeIso_hom_inclusion _ _ _

variable (f : SpecialModule.Iso Y Z)

local notation "e" => f.toModuleIso.fiberTangent (RingHom.id B.obj)
local notation "eᵢ" => (fun (i : ZMod d) =>
  drinfeldTangentComponentIso ι Y.unramified χ ψ f (idx i))

private theorem derivative_uniformizer :
    (e).toLinearMap.comp (t Y) = (t Z).comp (e).toLinearMap :=
  OrderAction.Hom.fiberTangent_commutes f.hom (RingHom.id B.obj)
    (drinfeldIntegralUniformizer uniformizer hPow)

private theorem derivative_component (i : ZMod d) :
    (W Z i).subtype.comp (eᵢ i).toLinearMap =
      (e).toLinearMap.comp (W Y i).subtype :=
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1500000 in
/-- Differentiate the actual order-linear formal isomorphism and take its associated graded sheaf. -/
def drinfeldTangentGradedPiSheafIso : G Y ≅ G Z := by
  let F := tilde.functor R
  let E : (G Y).module ≅ (G Z).module := F.mapIso (e).toModuleIso
  let C (i : ZMod d) : (G Y).componentSheaf i ≅ (G Z).componentSheaf i :=
    (J Y i).symm ≪≫ F.mapIso ((eᵢ i).toModuleIso) ≪≫ (J Z i)
  let f₁ : VM ⟶ VM := ModuleCat.ofHom (e).toLinearMap
  let πY : VM ⟶ VM := ModuleCat.ofHom (t Y)
  let πZ : VM ⟶ VM := ModuleCat.ofHom (t Z)
  have hπA : πY ≫ f₁ = f₁ ≫ πZ :=
    ModuleCat.hom_ext (derivative_uniformizer ι uniformizer hPow f)
  have hπS := congrArg (fun g : VM ⟶ VM => F.map g) hπA
  rw [F.map_comp, F.map_comp] at hπS
  refine GradedPiSheaf.isoOfComponents (M := G Y) (N := G Z) E hπS C ?_
  intro i
  apply (cancel_epi (J Y i).hom).mp
  have h := congrArg (fun k : W Y i →ₗ[B.obj] V => F.map (ModuleCat.ofHom k))
    (derivative_component ι χ ψ f i)
  simp only [ModuleCat.ofHom_comp, Functor.map_comp] at h
  simp only [C, Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc]
  exact h

@[simp]
theorem drinfeldTangentGradedPiSheafIso_hom :
    (drinfeldTangentGradedPiSheafIso ι χ ψ σ uniformizer hPow hComm hσ f).hom.val.val =
      (tilde.functor R).map (ModuleCat.ofHom (e).toLinearMap) :=
  rfl

end Langlands.FormalGroup.LocalDivision
