import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesTildePullback
import Langlands.Geometry.FormalGroup.DeligneGradedPiProjectors
import Langlands.Geometry.FormalGroup.DrinfeldTangentScalarExtension
import Langlands.Geometry.FormalGroup.DrinfeldTangentSheafIso

/-! # Coefficient pullback of the actual Drinfeld graded tangent sheaf -/

noncomputable section

namespace Langlands.FormalGroup.LocalDivision

open ValuativeRel CentralDivision CentralSimple _root_.CategoryTheory _root_.AlgebraicGeometry
  DeligneFormalSpace ModuleLaw

universe u v s

variable {K D : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
variable {L : Type s} [Field L] [Algebra K L] (ι : L →ₐ[K] D)

local instance tangentSheafPullbackLocalHom :
    IsLocalHom (algebraMap 𝒪[K] (SubfieldIntegerRing K D ι)) := subfieldIntegerAlgebra_isLocalHom ι

local instance tangentSheafPullbackDegree : NeZero (CentralSimple.reducedDegree K D) :=
  ⟨(reducedDegree_pos K D).ne'⟩

variable {κ : Type u} [Field κ] [Algebra 𝒪[K] κ] [Algebra 𝓀[K] κ]
  [IsScalarTower 𝒪[K] 𝓀[K] κ]
variable (χ : IsLocalRing.ResidueField (SubfieldIntegerRing K D ι) →ₐ[𝓀[K]] κ)
variable {π : 𝒪[K]} {B B' : Nilp.{u, max u v} 𝒪[K] π}
variable (ψ : κ →ₐ[𝒪[K]] Nilp.Reduction π B.obj) (Y : SpecialModule K D ι B.obj)
variable (σ : L ≃ₐ[K] L) (uniformizer : Dˣ)
  (hPow : (uniformizer : D) ^ CentralSimple.reducedDegree K D = algebraMap K D (π : K))
  (hComm : ∀ a : L, (uniformizer : D) * ι a = ι (σ a) * (uniformizer : D))
  (hσ : ∀ a : SubfieldIntegerRing K D ι,
    localReducedNormIntValuation K D (ι (σ (a : L)) - ι ((a : L) ^ Nat.card 𝓀[K])) < 1)

local notation "d" => CentralSimple.reducedDegree K D
local notation "idx" => RingEquiv.symm (ZMod.finEquiv (CentralSimple.reducedDegree K D))
local notation "V" => (Fin d → B.obj)
local notation "V'" => (Fin d → B'.obj)
local notation "R" => CommRingCat.of B.obj
local notation "S" => CommRingCat.of B'.obj
local notation "VM" => ModuleCat.of B.obj V
local notation "VN" => ModuleCat.of B'.obj V'
local notation "G" => drinfeldTangentGradedPiSheaf (B := B) ι χ ψ Y σ uniformizer hPow hComm hσ
local notation "P" => drinfeldTangentProjector ι Y.unramified χ ψ Y.order
local notation "W" => drinfeldTangentComponent ι Y.unramified χ ψ Y.order

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1800000 in
/-- The canonical sheaf projector is the associated map of the given tangent projector. -/
theorem drinfeldTangentGradedPiSheaf_projector (i : ZMod d) :
    (G).componentProjector i = (tilde.functor R).map (ModuleCat.ofHom (P (idx i))) := by
  let F := tilde.functor R
  let C (k : ZMod d) := ModuleCat.of B.obj (W (idx k))
  let j (k : ZMod d) : C k ⟶ VM := ModuleCat.ofHom (W (idx k)).subtype
  let p (k : ZMod d) : VM ⟶ C k := ModuleCat.ofHom (P (idx k)).rangeRestrict
  have split_diag (k : ZMod d) : j k ≫ p k = 𝟙 (C k) := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    obtain ⟨y, hy⟩ := x.property
    change P (idx k) y = x.val at hy
    change P (idx k) x.val = x.val
    rw [← hy]
    exact congrArg (fun a : Module.End B.obj V => a y)
      (drinfeldTangentProjector_mul_same ι Y.unramified χ ψ Y.order (idx k))
  have split_off {k l : ZMod d} (hl : l ≠ k) : j l ≫ p k = 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    obtain ⟨y, hy⟩ := x.property
    change P (idx l) y = x.val at hy
    change P (idx k) x.val = 0
    rw [← hy]
    exact congrArg (fun a : Module.End B.obj V => a y)
      (drinfeldTangentProjector_mul_ne ι Y.unramified χ ψ Y.order ((idx).injective.ne hl.symm))
  let Cₛ (k : ZMod d) := F.obj (C k)
  let jₛ (k : ZMod d) : Cₛ k ⟶ (G).module := F.map (j k)
  let pₛ (k : ZMod d) : (G).module ⟶ Cₛ k := F.map (p k)
  let cj (k : ZMod d) : Cₛ k ≅ (G).componentSheaf k :=
    drinfeldTangentComponentSheafIso ι χ ψ Y σ uniformizer hPow hComm hσ k
  have inclusion (k : ZMod d) : (cj k).hom ≫ (G).componentInclusion k = jₛ k :=
    drinfeldTangentComponentSheafIso_inclusion ι χ ψ σ uniformizer hPow hComm hσ Y k
  have diag (k : ZMod d) : jₛ k ≫ pₛ k = 𝟙 (Cₛ k) :=
    (F.map_comp _ _).symm.trans ((congrArg (fun g => F.map g) (split_diag k)).trans (F.map_id (C k)))
  have off {k l : ZMod d} (hl : l ≠ k) : jₛ l ≫ pₛ k = 0 :=
    (F.map_comp _ _).symm.trans ((congrArg (fun g => F.map g) (split_off hl)).trans tilde.map_zero)
  calc
    _ = pₛ i ≫ jₛ i := (G).componentProjector_of_splitting jₛ pₛ cj inclusion diag (fun h => off h) i
    _ = F.map (p i ≫ j i) := (F.map_comp _ _).symm
    _ = _ := rfl

variable (f : B ⟶ B')

local notation "φ" => CommAlgCat.Hom.hom (InducedCategory.Hom.hom f)
local notation "rmap" => CommRingCat.ofHom (AlgHom.toRingHom φ)
local notation "smap" => Spec.map rmap
local notation "ψ'" => AlgHom.comp (Nilp.reductionMap (π := π) (A := B.obj) (B := B'.obj) φ) ψ
local notation "Y'" => SpecialModule.mapSameUniverse («S» := B'.obj) Y φ
local notation "G'" => drinfeldTangentGradedPiSheaf (B := B') ι χ ψ' Y' σ uniformizer hPow hComm hσ
local notation "a" => Iso.inv (Scheme.ΓSpecIso R) (algebraMap 𝒪[K] B.obj π)
local notation "a'" => Iso.inv (Scheme.ΓSpecIso S) (algebraMap 𝒪[K] B'.obj π)
local notation "Lₛ" => ModuleCat.extendScalars (AlgHom.toRingHom φ)
local notation "Eₛ" => tangentScalarExtensionIso (AlgHom.toRingHom φ) (Fin d)
local notation "Fₛ" => tilde.functor S
local notation "Fᵣ" => tilde.functor R
local notation "Fₚ" => Scheme.Modules.pullback smap

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
private theorem tangentPullback_scalar : (smap).appTop a = a' := by
  have h := ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality (rmap)) (algebraMap 𝒪[K] B.obj π)
  change (Scheme.ΓSpecIso S).inv (φ (algebraMap 𝒪[K] B.obj π)) = (smap).appTop a at h
  rw [AlgHom.commutes] at h
  exact h.symm

/-- The structural pullback with the scalar identified with that of the target test ring. -/
def drinfeldTangentGradedPiSheafPulled :
    GradedPiSheaf d (Spec S).sheaf (schemeScalar (Spec S) a') :=
  ((G).pullback smap).changeScalar (tangentPullback_scalar f)

private def tangentTotalPullbackIso :
    (Fₚ).obj (tilde VM) ≅ tilde VN :=
  tilde.pullbackSpecIso rmap VM ≪≫ (Fₛ).mapIso Eₛ

set_option backward.isDefEq.respectTransparency false in
omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] [FiniteDimensional K D] [Algebra.IsCentral K D] in
private theorem tangentTotalPullbackIso_intertwines (A : VM ⟶ VM) (A' : VN ⟶ VN)
    (h : (Lₛ).map A ≫ (Eₛ).hom = (Eₛ).hom ≫ A') :
    (Fₚ).map ((Fᵣ).map A) ≫ (tangentTotalPullbackIso f).hom =
      (tangentTotalPullbackIso f).hom ≫ (Fₛ).map A' := by
  let t := (tilde.pullbackSpecIso rmap VM).hom
  let c := (Fₛ).map (Eₛ).hom
  change (Fₚ).map ((Fᵣ).map A) ≫ t ≫ c = (t ≫ c) ≫ (Fₛ).map A'
  have hn : (Fₚ).map ((Fᵣ).map A) ≫ t = t ≫ (Fₛ).map ((Lₛ).map A) :=
    tilde.pullbackSpecIso_hom_naturality rmap A
  have h' := congrArg (fun g => (Fₛ).map g) h
  rw [(Fₛ).map_comp, (Fₛ).map_comp] at h'
  calc
    _ = ((Fₚ).map ((Fᵣ).map A) ≫ t) ≫ c := (Category.assoc _ _ _).symm
    _ = (t ≫ (Fₛ).map ((Lₛ).map A)) ≫ c := congrArg (· ≫ c) hn
    _ = t ≫ (Fₛ).map ((Lₛ).map A) ≫ c := Category.assoc _ _ _
    _ = t ≫ c ≫ (Fₛ).map A' := congrArg (t ≫ ·) h'
    _ = _ := (Category.assoc _ _ _).symm

local notation "Gₚ" =>
  drinfeldTangentGradedPiSheafPulled (B := B) (B' := B') ι χ ψ Y σ uniformizer hPow hComm hσ f

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1800000 in
private theorem tangentPullbackIso_pi :
    let e : (Gₚ).module ≅ (G').module := tangentTotalPullbackIso (D := D) f
    (Gₚ).pi ≫ e.hom = e.hom ≫ (G').pi := by
  intro e
  let operator := drinfeldIntegralUniformizer uniformizer hPow
  let A : VM ⟶ VM := ModuleCat.ofHom (Y.order.tangentAction operator)
  let A' : VN ⟶ VN := ModuleCat.ofHom ((Y').order.tangentAction operator)
  have h : (Lₛ).map A ≫ (Eₛ).hom = (Eₛ).hom ≫ A' :=
    tangentScalarExtensionIso_order (B := B) (B' := B') (I := Fin d) Y.order f operator
  have hs : (Gₚ).pi = (Fₚ).map ((Fᵣ).map A) := rfl
  have ht : (G').pi = (Fₛ).map A' := rfl
  rw [hs, ht]
  exact tangentTotalPullbackIso_intertwines.{u,v} (K := K) (D := D) (B := B) (B' := B') f A A' h

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1800000 in
private theorem tangentPullbackIso_projector (i : ZMod d) :
    let e : (Gₚ).module ≅ (G').module := tangentTotalPullbackIso (D := D) f
    (Gₚ).componentProjector i ≫ e.hom = e.hom ≫ (G').componentProjector i := by
  intro e
  let A : VM ⟶ VM := ModuleCat.ofHom (P (idx i))
  let A' : VN ⟶ VN :=
    ModuleCat.ofHom (drinfeldTangentProjector ι Y.unramified χ (B := B') ψ' (Y').order (idx i))
  have hx : (Gₚ).componentProjector i = (Fₚ).map ((Fᵣ).map A) :=
    ((G).componentProjector_pullback smap i).trans
      (congrArg (fun g => (Fₚ).map g)
        (drinfeldTangentGradedPiSheaf_projector ι χ ψ Y σ uniformizer hPow hComm hσ i))
  have hy : (G').componentProjector i = (Fₛ).map A' :=
    drinfeldTangentGradedPiSheaf_projector ι χ (B := B') ψ' Y' σ uniformizer hPow hComm hσ i
  have h : (Lₛ).map A ≫ (Eₛ).hom = (Eₛ).hom ≫ A' :=
    tangentScalarExtensionIso_projector ι Y.unramified χ (B := B) (B' := B') (I := Fin d) ψ Y.order f (idx i)
  rw [hx, hy]
  exact tangentTotalPullbackIso_intertwines.{u,v} (K := K) (D := D) (B := B) (B' := B') f A A' h

set_option maxHeartbeats 1800000 in
/-- The actual graded tangent sheaf commutes with affine coefficient pullback. -/
def drinfeldTangentGradedPiSheafPullbackIso : Gₚ ≅ G' := by
  let e : (Gₚ).module ≅ (G').module := tangentTotalPullbackIso (D := D) f
  let h := tangentPullbackIso_projector.{u,v,s} (B := B) (B' := B') ι χ ψ Y σ uniformizer
    hPow hComm hσ f
  exact GradedPiSheaf.isoOfComponents (M := Gₚ) (N := G') e
    (tangentPullbackIso_pi.{u,v,s} (B := B) (B' := B') ι χ ψ Y σ uniformizer hPow hComm hσ f)
    (fun i => GradedPiSheaf.componentIsoOfProjector e (h i))
    (fun i => GradedPiSheaf.componentIsoOfProjector_hom_inclusion e (h i))

end Langlands.FormalGroup.LocalDivision
