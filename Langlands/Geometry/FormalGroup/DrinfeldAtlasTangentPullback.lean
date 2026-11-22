import Langlands.Geometry.FormalGroup.DrinfeldAtlasTangentCharts
import Langlands.Geometry.FormalGroup.DrinfeldTangentSheafPullback
import Langlands.Geometry.FormalGroup.SpecialAtlasChartCoefficientIso

/-! # Pullback of the tangent line datum of an actual special atlas chart -/

noncomputable section

universe u v s

namespace Langlands.FormalGroup.LocalDivision.SpecialAtlas

open ValuativeRel CentralDivision CentralSimple _root_.CategoryTheory _root_.AlgebraicGeometry
  DeligneFormalSpace ModuleLaw

attribute [local instance] ModuleLaw.coefficientAlgebra ModuleLaw.coefficientScalarTower

variable {K D : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
variable {L : Type s} [Field L] [Algebra K L] (ι : L →ₐ[K] D)

local instance atlasTangentPullbackLocalHom :
    IsLocalHom (algebraMap 𝒪[K] (SubfieldIntegerRing K D ι)) := subfieldIntegerAlgebra_isLocalHom ι

local instance atlasTangentPullbackDegree : NeZero (CentralSimple.reducedDegree K D) :=
  ⟨(reducedDegree_pos K D).ne'⟩

variable {κ : Type u} [Field κ] [Algebra 𝒪[K] κ] [Algebra 𝓀[K] κ]
  [IsScalarTower 𝒪[K] 𝓀[K] κ]
variable (χ : IsLocalRing.ResidueField (SubfieldIntegerRing K D ι) →ₐ[𝓀[K]] κ)
variable {π : 𝒪[K]} {B : Nilp.{u, max u v} 𝒪[K] π}
variable (ψ : κ →ₐ[𝒪[K]] Nilp.Reduction π B.obj)
variable (σ : L ≃ₐ[K] L) (uniformizer : Dˣ)
  (hPow : (uniformizer : D) ^ CentralSimple.reducedDegree K D = algebraMap K D (π : K))
  (hComm : ∀ a : L, (uniformizer : D) * ι a = ι (σ a) * (uniformizer : D))
  (hσ : ∀ a : SubfieldIntegerRing K D ι,
    localReducedNormIntValuation K D (ι (σ (a : L)) - ι ((a : L) ^ Nat.card 𝓀[K])) < 1)
variable (X : SpecialAtlas K D ι B.obj)
  {A A' : CommAlgCat.{max u v} B.obj} (f : A ⟶ A')

private def chartNilp (C : CommAlgCat.{max u v} B.obj) : Nilp.{u,max u v} 𝒪[K] π :=
  Nilp.of 𝒪[K] π C (by
    rw [IsScalarTower.algebraMap_apply 𝒪[K] B.obj C]
    exact B.nilpotent.map (algebraMap B.obj C))

private abbrev chartCoeffMap : A →ₐ[𝒪[K]] A' :=
  f.hom.restrictScalars 𝒪[K]

private def chartNilpMap : chartNilp A ⟶ chartNilp A' :=
  ⟨CommAlgCat.ofHom (chartCoeffMap f)⟩

private def chartResidue (C : CommAlgCat.{max u v} B.obj) :
    κ →ₐ[𝒪[K]] Nilp.Reduction π (chartNilp C).obj :=
  (Nilp.reductionMap (IsScalarTower.toAlgHom 𝒪[K] B.obj C)).comp ψ

local notation "B₁" => chartNilp (B := B) A
local notation "B₂" => chartNilp (B := B) A'
local notation "fₙ" => chartNilpMap (B := B) f
local notation "θ" => chartCoeffMap f
local notation "ψ₁" => chartResidue ψ A
local notation "ψ₂" => chartResidue ψ A'
local notation "ψ₂'" => AlgHom.comp
  (Nilp.reductionMap (π := π) (A := CommAlgCat.of 𝒪[K] A) (B := CommAlgCat.of 𝒪[K] A') θ) ψ₁

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 900000 in
omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
private theorem chartResidue_natural : ψ₂' = ψ₂ := by
  let r : B.obj →ₐ[𝒪[K]] A := IsScalarTower.toAlgHom 𝒪[K] B.obj A
  let s : B.obj →ₐ[𝒪[K]] A' := IsScalarTower.toAlgHom 𝒪[K] B.obj A'
  have h : (θ).comp r = s := AlgHom.ext fun a => f.hom.commutes a
  have hred := Nilp.reductionMap_comp (π := π) (A := B.obj)
    (B := CommAlgCat.of 𝒪[K] A) (C := CommAlgCat.of 𝒪[K] A') r θ
  have hcomp := congrArg
    (fun k : Nilp.Reduction π B.obj →ₐ[𝒪[K]] Nilp.Reduction π (CommAlgCat.of 𝒪[K] A') => k.comp ψ)
    hred.symm
  have hbase := congrArg
    (fun k : B.obj →ₐ[𝒪[K]] A' => (Nilp.reductionMap (π := π) (A := B.obj)
      (B := CommAlgCat.of 𝒪[K] A') k).comp ψ) h
  exact hcomp.trans hbase

local notation "Y[" b ", " hb "]" => SpecialAtlas.chartTestModule X A b hb
local notation "Z[" b ", " hb "]" => SpecialAtlas.chartTestModule X A' b hb
local notation "G[" C ", " η ", " M "]" =>
  drinfeldTangentGradedPiSheaf (B := C) ι χ η M σ uniformizer hPow hComm hσ
local notation "H[" b ", " hb "]" => LinePiSheaf.graded
  (chartTangentLinePiSheaf ι χ ψ σ uniformizer hPow hComm hσ X A' b hb)

/-- Pull the tangent sheaf of a test chart to a new algebra and identify its scalar. -/
def chartTangentPulled (b : X.atlas.opens) (hb : IsUnit (algebraMap B.obj A b.val)) :=
  drinfeldTangentGradedPiSheafPulled (B := B₁) (B' := B₂) ι χ ψ₁ Y[b, hb]
    σ uniformizer hPow hComm hσ fₙ

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1200000 in
/-- The actual pullback of a tangent chart is its tangent chart on the new test algebra. -/
def chartTangentPullbackIso (b : X.atlas.opens)
    (hb : IsUnit (algebraMap B.obj A b.val)) (hb' : IsUnit (algebraMap B.obj A' b.val)) :
    chartTangentPulled ι χ ψ σ uniformizer hPow hComm hσ X f b hb ≅ H[b, hb'] := by
  let Y : SpecialModule K D ι A := Y[b, hb]
  let Z : SpecialModule K D ι A' := Z[b, hb']
  let e : SpecialModule.Iso (Y.mapSameUniverse θ) Z :=
    X.chartTestCoefficientIso (A := A) (A' := A') f b hb hb'
  let p := drinfeldTangentGradedPiSheafPullbackIso (B := B₁) (B' := B₂)
    ι χ ψ₁ Y σ uniformizer hPow hComm hσ fₙ
  let q := drinfeldTangentGradedPiSheafIso (B := B₂) ι χ ψ₂'
    (Y := Y.mapSameUniverse θ) (Z := Z)
    σ uniformizer hPow hComm hσ e
  let r : G[B₂, ψ₂', Z] ≅ G[B₂, ψ₂, Z] :=
    eqToIso (congrArg (fun η => G[B₂, η, Z]) (chartResidue_natural (B := B) ψ f))
  exact p ≪≫ q ≪≫ r

end Langlands.FormalGroup.LocalDivision.SpecialAtlas
