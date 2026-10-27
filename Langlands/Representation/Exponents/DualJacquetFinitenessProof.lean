import Langlands.Representation.Exponents.DualJacquetStatement
import Langlands.Representation.Exponents.FiniteActionSpectrumProof
import Langlands.Representation.Smooth.CentralOperatorExpansionProof
import Langlands.Representation.Parabolic.StandardOppositeJacquetAdmissibilityProof
import Langlands.Representation.Parabolic.OppositeJacquetFiniteGenerationProof
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.RingTheory.Finiteness.Basic

/-!
# Finiteness of full-dual opposite Jacquet exponents

Finite generation and admissibility of the actual opposite Jacquet module
give a finite, locally constant split-center operator span. Transposition
preserves both properties on the full algebraic dual, where the generic
finite-action spectrum theorem supplies all three conclusions.
-/

noncomputable section

namespace Langlands

universe uR uA uV uF

section Transpose

variable {R : Type uR} [CommRing R] {A : Type uA} [CommGroup A]
  {V : Type uV} [AddCommGroup V] [Module R V]

theorem commutativeTranspose_actionSpan_finite (ρ : Representation R A V)
    (hfin : Module.Finite R (Submodule.span R (Set.range ρ))) :
    Module.Finite R
      (Submodule.span R (Set.range (commutativeTranspose ρ))) := by
  let L : Module.End R V →ₗ[R] Module.End R (Module.Dual R V) :=
    Module.Dual.transpose
  have hspan :
      (Submodule.span R (Set.range ρ)).map L =
        Submodule.span R (Set.range (commutativeTranspose ρ)) := by
    rw [Submodule.map_span]
    congr 1
    rw [← Set.range_comp]
    congr 1
    funext a
    ext φ v
    simp [L, Module.Dual.transpose_apply, commutativeTranspose_apply]
  let := hfin
  rw [← hspan]
  infer_instance

theorem commutativeTranspose_action_isLocallyConstant [TopologicalSpace A]
    (ρ : Representation R A V)
    (hρ : IsLocallyConstant (fun a : A => ρ a)) :
    IsLocallyConstant (fun a : A => commutativeTranspose ρ a) := by
  have he : (fun a : A => commutativeTranspose ρ a) =
      (fun a : A => (Module.Dual.transpose (ρ a) :
        Module.End R (Module.Dual R V))) := by
    funext a
    ext φ v
    simp [Module.Dual.transpose_apply, commutativeTranspose_apply]
  rw [he]
  exact hρ.comp (Module.Dual.transpose :
    Module.End R V →ₗ[R] Module.End R (Module.Dual R V))

end Transpose

namespace PadicField.TopologicalData

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) {n : ℕ} (B : GeneralLinear.BlockShape n)

theorem splitCentreDualJacquet_actionFinite
    (A : Rep.{uV} ℂ (GeneralLinear n F.Carrier))
    (hA : letI := T.topology; IsAdmissible A.ρ)
    (hfin : Module.Finite (MonoidAlgebra ℂ (B.Levi F.Carrier))
      (CuspidalJacquetMultiplicity.oppositeJacquet T B A).ρ.asModule) :
    letI := T.topology
    Module.Finite ℂ
      (Submodule.span ℂ (Set.range (T.splitCentreDualJacquet B A).ρ)) ∧
      IsLocallyConstant (fun a => (T.splitCentreDualJacquet B A).ρ a) := by
  let := T.topology
  let := T.moduleTopology
  let : IsTopologicalRing F.Carrier :=
    IsModuleTopology.isTopologicalRing (Padic p) F.Carrier
  let := T.leviTopologicalGroup B
  let J := CuspidalJacquetMultiplicity.oppositeJacquet T B A
  let c : (Fin B.length → F.Carrierˣ) →*
      Subgroup.center (B.Levi F.Carrier) :=
    (B.blockScalarLevi F.Carrier).codRestrict _
      (fun a => B.blockScalarLevi_mem_center F.Carrier a)
  have hc : Continuous c := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    exact (GeneralLinear.scalarContinuous :
      ContinuousMonoidHom F.Carrierˣ
        (GeneralLinear (B.size i) F.Carrier)).continuous.comp (continuous_apply i)
  have hJ : IsAdmissible J.ρ :=
    Parabolic.isAdmissible_standardOppositeJacquet F T B A A.ρ hA
  have hspan : Module.Finite ℂ
      (Submodule.span ℂ (Set.range (T.splitCentreOppositeJacquet B A).ρ)) :=
    centralActionSpan_finite J.ρ c hJ hfin
  have hlocal : IsLocallyConstant
      (fun a => (T.splitCentreOppositeJacquet B A).ρ a) :=
    centralAction_isLocallyConstant J.ρ c hc hJ.1 hfin
  exact ⟨commutativeTranspose_actionSpan_finite _ hspan,
    commutativeTranspose_action_isLocallyConstant _ hlocal⟩

theorem splitCentreDualJacquet_actionFinite_of_irreducible
    (A : Rep.{uV} ℂ (GeneralLinear n F.Carrier))
    (hirr : Representation.IsIrreducible A.ρ)
    (hA : letI := T.topology; IsAdmissible A.ρ) :
    letI := T.topology
    Module.Finite ℂ
      (Submodule.span ℂ (Set.range (T.splitCentreDualJacquet B A).ρ)) ∧
      IsLocallyConstant (fun a => (T.splitCentreDualJacquet B A).ρ a) := by
  let := T.topology
  let := hirr
  have hfin : Module.Finite (MonoidAlgebra ℂ (GeneralLinear n F.Carrier))
      A.ρ.asModule := inferInstance
  exact T.splitCentreDualJacquet_actionFinite B A hA
    (Parabolic.oppositeJacquetFiniteGeneration p F T n B A hA.1 hfin)

end PadicField.TopologicalData

/-- The actual full algebraic dual has finitely many smooth Jacquet exponents,
a finite uniform nilpotence index on each occurring generalized component,
and these generalized components span the full dual. -/
theorem glDualJacquetFiniteness.{uField, uCarrier} :
    GLDualJacquetFinitenessStatement.{uField, uCarrier} := by
  intro p hp F T
  let := T.topology
  intro n _ B A hirr hA
  obtain ⟨hfin, hlocal⟩ :=
    T.splitCentreDualJacquet_actionFinite_of_irreducible B A hirr hA
  exact finiteActionCommutativeSpectrum (Fin B.length → F.Carrierˣ)
    (T.splitCentreDualJacquet B A) (T.splitCentreDualJacquet B A).ρ hfin hlocal

end Langlands
