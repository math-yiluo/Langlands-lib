import Langlands.Geometry.FormalGroup.AtlasOrderRationalTransition
import Langlands.Geometry.FormalGroup.DrinfeldTangentSheafIso
import Langlands.Geometry.FormalGroup.SpecialAtlas

/-! # Tangent line sheaves and transition maps on special formal atlas charts -/

noncomputable section

universe u v s

namespace Langlands.FormalGroup.LocalDivision

open ValuativeRel CentralDivision CentralSimple _root_.CategoryTheory _root_.AlgebraicGeometry
  DeligneFormalSpace ModuleLaw

attribute [local instance] ModuleLaw.coefficientAlgebra ModuleLaw.coefficientScalarTower

variable {K D : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
variable {L : Type s} [Field L] [Algebra K L] (ι : L →ₐ[K] D)

local instance atlasTangentChartsLocalHom :
    IsLocalHom (algebraMap 𝒪[K] (SubfieldIntegerRing K D ι)) := subfieldIntegerAlgebra_isLocalHom ι

local instance atlasTangentChartsDegree : NeZero (CentralSimple.reducedDegree K D) :=
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

local notation "T" => drinfeldTangentGradedPiSheafIso ι χ ψ σ uniformizer hPow hComm hσ
local notation "F" => tilde.functor (CommRingCat.of B.obj)

private theorem gradedComp_total {S : Scheme.{v}} {d : ℕ} [NeZero d] {a : Γ(S, ⊤)}
    {M N P : GradedPiSheaf d S.sheaf (schemeScalar S a)} (f : M ⟶ N) (g : N ⟶ P) :
    (f ≫ g).val.val = f.val.val ≫ g.val.val :=
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1500000 in
/-- Differentiating the identity order isomorphism gives the identity of graded tangent sheaves. -/
theorem drinfeldTangentGradedPiSheafIso_refl (X : SpecialModule K D ι B.obj) :
    T (SpecialModule.Iso.refl X) = _root_.CategoryTheory.Iso.refl _ := by
  apply _root_.CategoryTheory.Iso.ext
  apply GradedPiSheaf.Hom.ext
  apply PiSheaf.Hom.ext
  rw [drinfeldTangentGradedPiSheafIso_hom]
  change (F).map (ModuleCat.ofHom ((ModuleLaw.Hom.id X.formalModule).fiberTangent
    (RingHom.id B.obj))) = 𝟙 _
  rw [ModuleLaw.Hom.fiberTangent_id]
  exact (F).map_id _

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1500000 in
/-- Differentiation and association of a sheaf preserve composition of order isomorphisms. -/
theorem drinfeldTangentGradedPiSheafIso_trans {X Y Z : SpecialModule K D ι B.obj}
    (f : SpecialModule.Iso X Y) (g : SpecialModule.Iso Y Z) :
    T (SpecialModule.Iso.trans f g) = T f ≪≫ T g := by
  apply _root_.CategoryTheory.Iso.ext
  apply GradedPiSheaf.Hom.ext
  apply PiSheaf.Hom.ext
  rw [_root_.CategoryTheory.Iso.trans_hom, gradedComp_total,
    drinfeldTangentGradedPiSheafIso_hom, drinfeldTangentGradedPiSheafIso_hom,
    drinfeldTangentGradedPiSheafIso_hom]
  change (F).map (ModuleCat.ofHom ((g.hom.val.comp f.hom.val).fiberTangent (RingHom.id B.obj))) =
    (F).map (ModuleCat.ofHom (f.hom.val.fiberTangent (RingHom.id B.obj))) ≫
    (F).map (ModuleCat.ofHom (g.hom.val.fiberTangent (RingHom.id B.obj)))
  rw [ModuleLaw.Hom.fiberTangent_comp]
  exact (F).map_comp (ModuleCat.ofHom (f.hom.val.fiberTangent (RingHom.id B.obj)))
    (ModuleCat.ofHom (g.hom.val.fiberTangent (RingHom.id B.obj)))

namespace SpecialAtlas

variable (X : SpecialAtlas K D ι B.obj) (A : CommAlgCat.{max u v} B.obj)

private def tangentTestBase : Nilp.{u, max u v} 𝒪[K] π :=
  Nilp.of 𝒪[K] π A (by
    rw [IsScalarTower.algebraMap_apply 𝒪[K] B.obj A]
    exact B.nilpotent.map (algebraMap B.obj A))

private def tangentTestResidue :
    κ →ₐ[𝒪[K]] Nilp.Reduction π (CommAlgCat.of 𝒪[K] A) :=
  (Nilp.reductionMap (IsScalarTower.toAlgHom 𝒪[K] B.obj A)).comp ψ

local notation "Bₐ" => tangentTestBase (B := B) A
local notation "ψₐ" => tangentTestResidue ψ A
local notation "J" => Spec (CommRingCat.of A)
local notation "pₐ" => Iso.inv (Scheme.ΓSpecIso (CommRingCat.of A)) (algebraMap 𝒪[K] A π)

/-- The actual affine tangent line sheaf of a chart after extension to a test ring. -/
def chartTangentLinePiSheaf (b : X.atlas.opens) (hb : IsUnit (algebraMap B.obj A b.val)) :
    LinePiSheaf (CentralSimple.reducedDegree K D) J pₐ :=
  drinfeldTangentLinePiSheaf (B := Bₐ) ι χ ψₐ (X.chartTestModule A b hb) σ uniformizer hPow hComm hσ

local notation "M[" b ", " hb "]" =>
  LinePiSheaf.graded (chartTangentLinePiSheaf ι χ ψ σ uniformizer hPow hComm hσ X A b hb)

/-- The derivative of the full-order transition gives the change of tangent chart. -/
def chartTangentTransition (b c : X.atlas.opens)
    (hb : IsUnit (algebraMap B.obj A b.val)) (hc : IsUnit (algebraMap B.obj A c.val)) :
    M[b, hb] ≅ M[c, hc] :=
  drinfeldTangentGradedPiSheafIso (B := Bₐ) ι χ ψₐ σ uniformizer hPow hComm hσ
    (X.order.transitionIso A b c hb hc)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1800000 in
/-- The tangent transition from a chart to itself is the identity. -/
theorem chartTangentTransition_self (b : X.atlas.opens) (hb : IsUnit (algebraMap B.obj A b.val)) :
    chartTangentTransition ι χ ψ σ uniformizer hPow hComm hσ X A b b hb hb =
      _root_.CategoryTheory.Iso.refl _ := by
  have h := congrArg
    (drinfeldTangentGradedPiSheafIso (B := Bₐ) ι χ ψₐ σ uniformizer hPow hComm hσ
      (Y := X.chartTestModule A b hb) (Z := X.chartTestModule A b hb))
    (X.order.transitionIso_self A b hb)
  exact h.trans
    (drinfeldTangentGradedPiSheafIso_refl (B := Bₐ) ι χ ψₐ σ uniformizer hPow hComm hσ _)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1800000 in
/-- The actual tangent transitions satisfy the cocycle on every common test algebra. -/
theorem chartTangentTransition_cocycle (b c e : X.atlas.opens)
    (hb : IsUnit (algebraMap B.obj A b.val)) (hc : IsUnit (algebraMap B.obj A c.val))
    (he : IsUnit (algebraMap B.obj A e.val)) :
    chartTangentTransition ι χ ψ σ uniformizer hPow hComm hσ X A b c hb hc ≪≫
      chartTangentTransition ι χ ψ σ uniformizer hPow hComm hσ X A c e hc he =
    chartTangentTransition ι χ ψ σ uniformizer hPow hComm hσ X A b e hb he := by
  have h := congrArg
    (drinfeldTangentGradedPiSheafIso (B := Bₐ) ι χ ψₐ σ uniformizer hPow hComm hσ
      (Y := X.chartTestModule A b hb) (Z := X.chartTestModule A e he))
    (X.order.transitionIso_cocycle A b c e hb hc he)
  have hcomp := drinfeldTangentGradedPiSheafIso_trans (B := Bₐ) ι χ ψₐ σ uniformizer hPow hComm hσ
    (X := X.chartTestModule A b hb) (Y := X.chartTestModule A c hc)
    (Z := X.chartTestModule A e he) (X.order.transitionIso A b c hb hc)
    (X.order.transitionIso A c e hc he)
  exact hcomp.symm.trans h

end SpecialAtlas

end Langlands.FormalGroup.LocalDivision
