import Langlands.Geometry.FormalGroup.DrinfeldTangentSheafPullback

/-! # Naturality of the actual affine graded tangent pullback -/

noncomputable section

namespace Langlands.FormalGroup.LocalDivision

open ValuativeRel CentralDivision CentralSimple _root_.CategoryTheory _root_.AlgebraicGeometry
  DeligneFormalSpace ModuleLaw
open scoped TensorProduct ChangeOfRings

universe u v s

variable {K D : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
variable {L : Type s} [Field L] [Algebra K L] (ι : L →ₐ[K] D)

local instance tangentNaturalityLocalHom :
    IsLocalHom (algebraMap 𝒪[K] (SubfieldIntegerRing K D ι)) := subfieldIntegerAlgebra_isLocalHom ι

local instance tangentNaturalityDegree : NeZero (CentralSimple.reducedDegree K D) :=
  ⟨(reducedDegree_pos K D).ne'⟩

variable {κ : Type u} [Field κ] [Algebra 𝒪[K] κ] [Algebra 𝓀[K] κ]
  [IsScalarTower 𝒪[K] 𝓀[K] κ]
variable (χ : IsLocalRing.ResidueField (SubfieldIntegerRing K D ι) →ₐ[𝓀[K]] κ)
variable {π : 𝒪[K]} {B B' : Nilp.{u, max u v} 𝒪[K] π}
variable (ψ : κ →ₐ[𝒪[K]] Nilp.Reduction π B.obj) {Y Z : SpecialModule K D ι B.obj}
variable (σ : L ≃ₐ[K] L) (uniformizer : Dˣ)
  (hPow : (uniformizer : D) ^ CentralSimple.reducedDegree K D = algebraMap K D (π : K))
  (hComm : ∀ a : L, (uniformizer : D) * ι a = ι (σ a) * (uniformizer : D))
  (hσ : ∀ a : SubfieldIntegerRing K D ι,
    localReducedNormIntValuation K D (ι (σ (a : L)) - ι ((a : L) ^ Nat.card 𝓀[K])) < 1)
variable (f : B ⟶ B')

local notation "d" => CentralSimple.reducedDegree K D
local notation "φ" => CommAlgCat.Hom.hom (InducedCategory.Hom.hom f)
local notation "rmap" => CommRingCat.ofHom (AlgHom.toRingHom φ)
local notation "smap" => Spec.map rmap
local notation "R" => CommRingCat.of B.obj
local notation "S" => CommRingCat.of B'.obj
local notation "V" => (Fin d → B.obj)
local notation "V'" => (Fin d → B'.obj)
local notation "VM" => ModuleCat.of B.obj V
local notation "VN" => ModuleCat.of B'.obj V'
local notation "Fᵣ" => tilde.functor R
local notation "Fₛ" => tilde.functor S
local notation "Fₚ" => Scheme.Modules.pullback smap
local notation "Lₛ" => ModuleCat.extendScalars (AlgHom.toRingHom φ)
local notation "Eₛ" => tangentScalarExtensionIso (AlgHom.toRingHom φ) (Fin d)
local notation "ψ'" => AlgHom.comp (Nilp.reductionMap (π := π) (A := B.obj) (B := B'.obj) φ) ψ
local notation "G" => drinfeldTangentGradedPiSheaf (B := B) ι χ ψ
local notation "Gₚ" => fun M => drinfeldTangentGradedPiSheafPulled (B := B) (B' := B')
  ι χ ψ M σ uniformizer hPow hComm hσ f
local notation "T" => drinfeldTangentGradedPiSheafIso (B := B) ι χ ψ (Y := Y) (Z := Z)
  σ uniformizer hPow hComm hσ
local notation "T'" => drinfeldTangentGradedPiSheafIso (B := B') ι χ ψ'
  (Y := Y.mapSameUniverse φ) (Z := Z.mapSameUniverse φ) σ uniformizer hPow hComm hσ
local notation "P" => fun M => drinfeldTangentGradedPiSheafPullbackIso
  (B := B) (B' := B') ι χ ψ M σ uniformizer hPow hComm hσ f

set_option backward.isDefEq.respectTransparency false in
/-- Structural pullback of an actual graded tangent map, with the target scalar identified. -/
def drinfeldTangentGradedPiSheafPulledMap
    (g : G Y σ uniformizer hPow hComm hσ ⟶ G Z σ uniformizer hPow hComm hσ) :
    (Gₚ Y) ⟶ (Gₚ Z) := by
  let m := GradedPiSheaf.pullbackMap smap g
  exact ⟨⟨m.val.val, m.val.comm⟩, m.homogeneous⟩

set_option backward.isDefEq.respectTransparency false in
theorem drinfeldTangentGradedPiSheafPulledMap_total
    (g : G Y σ uniformizer hPow hComm hσ ⟶ G Z σ uniformizer hPow hComm hσ) :
    (drinfeldTangentGradedPiSheafPulledMap ι χ ψ (Y := Y) (Z := Z)
      σ uniformizer hPow hComm hσ f g).val.val = (Fₚ).map g.val.val :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The actual total map of the normalized associated-sheaf pullback comparison. -/
theorem drinfeldTangentGradedPiSheafPullbackIso_hom (M : SpecialModule K D ι B.obj) :
    (P M).hom.val.val = (tilde.pullbackSpecIso rmap VM).hom ≫ (Fₛ).map (Eₛ).hom :=
  rfl

private theorem tangentOfMappedIso (g : SpecialModule.Iso Y Z) (x : V) :
    (fun i => φ (g.hom.val.fiberTangent (RingHom.id B.obj) x i)) =
      (g.mapSameUniverse φ).hom.val.fiberTangent (RingHom.id B'.obj) (fun i => φ (x i)) := by
  funext i
  let A := g.hom.val.toHom.toCoordinateMap
  change φ ((A.map (RingHom.id B.obj)).linearPart x i) =
    ((A.map (AlgHom.toRingHom φ)).map (RingHom.id B'.obj)).linearPart (fun j => φ (x j)) i
  simp only [CoordinateMap.linearPart_apply, CoordinateMap.linearCoeff_map, RingHom.id_apply,
    map_sum, map_mul]
  rfl

private theorem tangentNaturality_scalarExtension (g : SpecialModule.Iso Y Z) :
    (Lₛ).map (ModuleCat.ofHom (g.hom.val.fiberTangent (RingHom.id B.obj))) ≫ (Eₛ).hom =
      (Eₛ).hom ≫ ModuleCat.ofHom ((g.mapSameUniverse φ).hom.val.fiberTangent (RingHom.id B'.obj)) := by
  apply ModuleCat.ExtendScalars.hom_ext
  intro x
  let a := g.hom.val.fiberTangent (RingHom.id B.obj)
  let b := (g.mapSameUniverse φ).hom.val.fiberTangent (RingHom.id B'.obj)
  have hgen (y : V) : (Eₛ).hom ((1 : B'.obj) ⊗ₜ[B.obj,AlgHom.toRingHom φ] y) = fun i => φ (y i) :=
    (tangentScalarExtensionIso_hom_tmul (AlgHom.toRingHom φ) (Fin d) 1 y).trans (one_smul B'.obj _)
  change (Eₛ).hom ((1 : B'.obj) ⊗ₜ[B.obj,AlgHom.toRingHom φ] a x) =
    b ((Eₛ).hom ((1 : B'.obj) ⊗ₜ[B.obj,AlgHom.toRingHom φ] x))
  exact (hgen (a x)).trans
    ((tangentOfMappedIso ι (B := B) (B' := B') (Y := Y) (Z := Z) f g x).trans
      (congrArg b (hgen x).symm))

private theorem gradedSquare_of_total {X : Scheme.{v}} {n : ℕ} [NeZero n] {a : Γ(X, ⊤)}
    {J M N Q : GradedPiSheaf n X.sheaf (schemeScalar X a)}
    (p : J ⟶ M) (q : M ⟶ Q) (r : J ⟶ N) (s : N ⟶ Q)
    (h : p.val.val ≫ q.val.val = r.val.val ≫ s.val.val) : p ≫ q = r ≫ s :=
  GradedPiSheaf.Hom.ext (PiSheaf.Hom.ext h)

set_option backward.isDefEq.respectTransparency false in
omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] [FiniteDimensional K D]
  [Algebra.IsCentral K D] in
private theorem tangentTotalPullbackSquare (A : VM ⟶ VM) (A' : VN ⟶ VN)
    (hmodule : (Lₛ).map A ≫ (Eₛ).hom = (Eₛ).hom ≫ A') :
    (Fₚ).map ((Fᵣ).map A) ≫ ((tilde.pullbackSpecIso rmap VM).hom ≫ (Fₛ).map (Eₛ).hom) =
      ((tilde.pullbackSpecIso rmap VM).hom ≫ (Fₛ).map (Eₛ).hom) ≫ (Fₛ).map A' := by
  let t := (tilde.pullbackSpecIso rmap VM).hom
  let c := (Fₛ).map (Eₛ).hom
  have h₁ : (Fₚ).map ((Fᵣ).map A) ≫ t = t ≫ (Fₛ).map ((Lₛ).map A) :=
    tilde.pullbackSpecIso_hom_naturality rmap A
  have h₂ : (Fₛ).map ((Lₛ).map A) ≫ c = c ≫ (Fₛ).map A' := by
    have h := congrArg (fun k => (Fₛ).map k) hmodule
    rw [(Fₛ).map_comp, (Fₛ).map_comp] at h
    exact h
  change (Fₚ).map ((Fᵣ).map A) ≫ (t ≫ c) = (t ≫ c) ≫ (Fₛ).map A'
  rw [← Category.assoc ((Fₚ).map ((Fᵣ).map A)) t c, h₁,
    Category.assoc t ((Fₛ).map ((Lₛ).map A)) c, h₂, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1800000 in
/-- Differentiating a formal order isomorphism commutes with coefficient pullback. -/
theorem drinfeldTangentGradedPiSheafPullbackIso_natural (g : SpecialModule.Iso Y Z) :
    drinfeldTangentGradedPiSheafPulledMap ι χ ψ (Y := Y) (Z := Z)
        σ uniformizer hPow hComm hσ f (T g).hom ≫ (P Z).hom =
      (P Y).hom ≫
        (T' (g.mapSameUniverse φ)).hom := by
  apply gradedSquare_of_total
  let A : VM ⟶ VM := ModuleCat.ofHom (g.hom.val.fiberTangent (RingHom.id B.obj))
  let A' : VN ⟶ VN := ModuleCat.ofHom ((g.mapSameUniverse φ).hom.val.fiberTangent (RingHom.id B'.obj))
  have hg :=
    drinfeldTangentGradedPiSheafIso_hom ι χ ψ (Y := Y) (Z := Z) σ uniformizer hPow hComm hσ g
  have hg' :=
    drinfeldTangentGradedPiSheafIso_hom (B := B') ι χ ψ'
      (Y := Y.mapSameUniverse φ) (Z := Z.mapSameUniverse φ)
      σ uniformizer hPow hComm hσ (g.mapSameUniverse φ)
  have hpY := drinfeldTangentGradedPiSheafPullbackIso_hom
    (B := B) (B' := B') ι χ ψ σ uniformizer hPow hComm hσ f Y
  have hpZ := drinfeldTangentGradedPiSheafPullbackIso_hom
    (B := B) (B' := B') ι χ ψ σ uniformizer hPow hComm hσ f Z
  have hmap := drinfeldTangentGradedPiSheafPulledMap_total
    (B := B) (B' := B') ι χ ψ (Y := Y) (Z := Z) σ uniformizer hPow hComm hσ f (T g).hom
  have hleft := hmap.trans (congrArg (fun k => (Fₚ).map k) hg)
  have hs := tangentTotalPullbackSquare (K := K) (D := D) (B := B) (B' := B') f A A'
    (tangentNaturality_scalarExtension ι (B := B) (B' := B') (Y := Y) (Z := Z) f g)
  exact (congrArg₂ (· ≫ ·) hleft hpZ).trans (hs.trans (congrArg₂ (· ≫ ·) hpY hg').symm)

end Langlands.FormalGroup.LocalDivision
