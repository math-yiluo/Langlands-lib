import Langlands.Geometry.FormalGroup.AtlasTangentTests
import Langlands.Geometry.FormalGroup.DrinfeldAtlasTangentProjectors

/-! # Evaluation of the split tangent projectors in a special atlas chart -/

noncomputable section

universe u v w s

namespace Langlands.FormalGroup.ModuleLaw.OrderAction

variable {O : Type u} [CommRing O] {R : Type v} [CommRing R] [Algebra O R]
variable {D : Type w} [Ring D] [Algebra O D] {I : Type} [Finite I]
variable {M : ModuleLaw O R I} (E : OrderAction D M)

/-- Computing the tangent action over the identity coefficient map recovers ordinary differentiation. -/
theorem tangentAction_apply_eq_tangent (a : D) (x : I → R) :
    E.tangentAction a x = E.tangent a x := by
  change ((E.action a).toHom.toCoordinateMap.map (RingHom.id R)).linearPart x =
    (E.action a).toHom.toCoordinateMap.linearPart x
  rw [CoordinateMap.map_ringHom_id]

end Langlands.FormalGroup.ModuleLaw.OrderAction

namespace Langlands.FormalGroup.LocalDivision.SpecialAtlas

open IsLocalRing ValuativeRel CentralDivision CentralSimple _root_.CategoryTheory ModuleLaw
open scoped TensorProduct

attribute [local instance] ModuleLaw.coefficientAlgebra ModuleLaw.coefficientScalarTower

section TensorAction

variable {O R S C : Type*} [CommRing O] [CommRing R] [CommRing S] [CommRing C]
variable [Algebra O R] [Algebra O S] [Algebra O C] [Algebra R S] [IsScalarTower O R S]
variable {M N : Type*} [AddCommGroup M] [Module R M]
variable [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
variable [Module O M] [Module O N] [IsScalarTower O R M] [IsScalarTower O S N]

private theorem tensorLift_intertwines (e : M →ₗ[R] N)
    (F : C →ₐ[O] Module.End R M) (G : C →ₐ[O] Module.End S N)
    (h : ∀ c x, e (F c x) = G c (e x)) (t : R ⊗[O] C) (x : M) :
    e (F.liftEquiv O R C (Module.End R M) t x) =
      G.liftEquiv O S C (Module.End S N)
        (Algebra.TensorProduct.map (IsScalarTower.toAlgHom O R S) (AlgHom.id O C) t) (e x) := by
  let μ := F.liftEquiv O R C (Module.End R M)
  let ν := G.liftEquiv O S C (Module.End S N)
  let φ := IsScalarTower.toAlgHom O R S
  let ext := Algebra.TensorProduct.map φ (AlgHom.id O C)
  change e (μ t x) = ν (ext t) (e x)
  induction t using TensorProduct.inductionOn with
  | tmul r c =>
    have h₁ : μ (r ⊗ₜ[O] c) = r • F c := AlgHom.liftEquiv_tmul F r c
    have h₂ : ν (ext (r ⊗ₜ[O] c)) = φ r • G c := AlgHom.liftEquiv_tmul G (φ r) c
    rw [h₁, h₂]
    change e (r • F c x) = (algebraMap R S r) • G c (e x)
    exact (e.map_smul r (F c x)).trans <|
      (congrArg (fun y : N => r • y) (h c x)).trans (algebraMap_smul S r (G c (e x))).symm
  | add t t' ht ht' => simp only [map_add, LinearMap.add_apply, ht, ht']

private theorem splitTensor_intertwines {J : Type*} (e : M →ₗ[R] N)
    (F : C →ₐ[O] Module.End R M) (G : C →ₐ[O] Module.End S N)
    (δ : R ⊗[O] C ≃ₐ[R] (J → R)) (δ' : S ⊗[O] C ≃ₐ[S] (J → S))
    (hs : ∀ t, (fun j => algebraMap R S (δ t j)) =
      δ' (Algebra.TensorProduct.map (IsScalarTower.toAlgHom O R S) (AlgHom.id O C) t))
    (h : ∀ c x, e (F c x) = G c (e x)) (p : J → R) (x : M) :
    e (((F.liftEquiv O R C (Module.End R M)).comp δ.symm.toAlgHom) p x) =
      ((G.liftEquiv O S C (Module.End S N)).comp δ'.symm.toAlgHom)
        (fun j => algebraMap R S (p j)) (e x) := by
  let μ := F.liftEquiv O R C (Module.End R M)
  let ν := G.liftEquiv O S C (Module.End S N)
  let ext := Algebra.TensorProduct.map (IsScalarTower.toAlgHom O R S) (AlgHom.id O C)
  obtain ⟨t, rfl⟩ := δ.surjective p
  change e (μ (δ.symm (δ t)) x) = ν (δ'.symm (fun j => algebraMap R S (δ t j))) (e x)
  rw [hs, δ.symm_apply_apply, δ'.symm_apply_apply]
  exact tensorLift_intertwines e F G h t x

end TensorAction

variable {K D : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
variable {L : Type s} [Field L] [Algebra K L] {ι : L →ₐ[K] D}

local instance atlasTangentEvaluationLocalHom :
    IsLocalHom (algebraMap 𝒪[K] (SubfieldIntegerRing K D ι)) := subfieldIntegerAlgebra_isLocalHom ι

variable {κ : Type u} [Field κ] [Algebra 𝒪[K] κ] [Algebra 𝓀[K] κ]
  [IsScalarTower 𝒪[K] 𝓀[K] κ]
variable (χ : ResidueField (SubfieldIntegerRing K D ι) →ₐ[𝓀[K]] κ)
variable {π : 𝒪[K]} {B : Nilp.{u,v} 𝒪[K] π} (ψ : κ →ₐ[𝒪[K]] Nilp.Reduction π B.obj)
variable (X : SpecialAtlas K D ι B.obj) (A : CommAlgCat.{v} B.obj)
variable (a : X.atlas.opens) (ha : IsUnit (algebraMap B.obj A a.val))

local notation "d" => CentralSimple.reducedDegree K D
local notation "C" => SubfieldIntegerRing K D ι
local notation "B₀" => CommAlgCat.of B.obj B.obj
local notation "V" => X.atlas.tangentSubmodule B₀
local notation "chartOrder" => SpecialModule.order (X.chartTestModule A a ha)

/-- A chart of the special atlas with a specified affine test algebra in that chart. -/
def tangentChartTest : X.atlas.ChartTest B₀ :=
  ⟨A, CommAlgCat.ofHom (Algebra.ofId B.obj A), a, ha⟩

local notation "test" => tangentChartTest X A a ha

/-- Evaluate the compatible tangent module on a test algebra where this chart is defined. -/
def tangentToChart : V →ₗ[B.obj] (Fin d → A) where
  toFun z := X.atlas.tangentTestEvaluation z test
  map_add' z w := funext fun i => (X.atlas.testFactor test).hom.map_add (z.val a i) (w.val a i)
  map_smul' b z := by
    funext i
    let f : X.atlas.localAlgebra B₀ a →ₐ[B.obj] A := (X.atlas.testFactor test).hom
    exact f.toLinearMap.map_smul b (z.val a i)

/-- The chart evaluation intertwines the full derivative order action. -/
theorem tangentToChart_order (z : V) (g : IntegerRing K D) :
    tangentToChart X A a ha (BasicAtlas.OrderAction.tangentAlgebraAction X.order B₀ g z) =
      (chartOrder).tangentAction g (tangentToChart X A a ha z) :=
  (BasicAtlas.OrderAction.tangentTestEvaluation_action X.atlas X.order z test g).trans
    ((chartOrder).tangentAction_apply_eq_tangent g (tangentToChart X A a ha z)).symm

/-- The chart test is nilpotent for the same scalar as the original base. -/
def tangentChartNilp : Nilp.{u,v} 𝒪[K] π :=
  Nilp.of 𝒪[K] π A (by
    rw [IsScalarTower.algebraMap_apply 𝒪[K] B.obj A]
    exact B.nilpotent.map (algebraMap B.obj A))

local notation "Aₙ" => tangentChartNilp (B := B) A
local notation "φ" => IsScalarTower.toAlgHom 𝒪[K] B.obj A

/-- The chart test has the residue coordinate induced by the structural coefficient map. -/
def tangentChartResidue : κ →ₐ[𝒪[K]] Nilp.Reduction π (Aₙ).obj :=
  (Nilp.reductionMap (φ)).comp ψ

local notation "ψₐ" => tangentChartResidue ψ A
local notation "ev" => tangentToChart X A a ha
variable (ι)
local notation "ρ" => tangentCharacterAction ι χ ψ X
local notation "ρₐ" => drinfeldTangentCharacterAction (B := Aₙ) ι X.unramified χ ψₐ chartOrder

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 850000 in
/-- The actual action of the split coefficient algebra commutes with evaluation in a chart. -/
theorem tangentToChart_character (c : Fin d → B.obj) (z : V) :
    ev (ρ c z) = ρₐ (fun i => algebraMap B.obj A (c i)) (ev z) := by
  let δ : B.obj ⊗[𝒪[K]] C ≃ₐ[B.obj] (Fin d → B.obj) := subfieldCyclicSplitting X.unramified χ ψ
  let δ' : A ⊗[𝒪[K]] C ≃ₐ[A] (Fin d → A) := subfieldCyclicSplitting (B := Aₙ) X.unramified χ ψₐ
  let f : B ⟶ Aₙ := ⟨CommAlgCat.ofHom φ⟩
  let ext := Algebra.TensorProduct.map φ (AlgHom.id 𝒪[K] C)
  let incl := subfieldIntegerInclusion K D ι
  let F : C →ₐ[𝒪[K]] Module.End B.obj V :=
    (BasicAtlas.OrderAction.tangentAlgebraAction X.order B₀).comp incl
  let F' : C →ₐ[𝒪[K]] Module.End A (Fin d → A) := (chartOrder).tangentAction.comp incl
  have hs (t : B.obj ⊗[𝒪[K]] C) : (fun i => algebraMap B.obj A (δ t i)) = δ' (ext t) := funext fun i =>
    (subfieldCyclicSplitting_natural X.unramified χ ψ f t i).symm
  exact splitTensor_intertwines ev F F' δ δ' hs
    (fun q x => tangentToChart_order X A a ha x (incl q)) c z

set_option maxHeartbeats 600000 in
/-- Evaluation sends each actual global projector to the corresponding chart projector. -/
theorem tangentToChart_projector (i : Fin d) (z : V) :
    ev (tangentProjector ι χ ψ X i z) =
      drinfeldTangentProjector (B := Aₙ) ι X.unramified χ ψₐ chartOrder i (ev z) := by
  have h : (fun k => algebraMap B.obj A ((Pi.single i 1 : Fin d → B.obj) k)) =
      (Pi.single i 1 : Fin d → A) := by
    funext k
    by_cases hk : k = i <;> simp [hk]
  have he := tangentToChart_character ι χ ψ X A a ha (Pi.single i 1) z
  exact he.trans (congrArg (fun c : Fin d → A => ρₐ c (ev z)) h)

end Langlands.FormalGroup.LocalDivision.SpecialAtlas
