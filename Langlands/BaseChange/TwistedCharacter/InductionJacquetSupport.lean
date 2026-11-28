import Langlands.Representation.Aubert.QuasicuspidalCutSupport
import Langlands.Representation.Category.UniverseLift
import Langlands.Representation.CuspidalSupport.CuspidalTensorProof
import Langlands.Representation.Classification.SupercuspidalSupport
import Langlands.Representation.Induction.Equivalences

/-! # Exact supercuspidal support of constituents of induction after Jacquet -/

noncomputable section

namespace Langlands.BaseChange

open CategoryTheory GeneralLinear CuspidalSupport PadicField.TopologicalData

universe v z

variable {p : ℕ} [Fact p.Prime] {E : PadicField.{v} p} (T : E.TopologicalData)

/-- An irreducible constituent of normalized induction after normalized
Jacquet of `π` has the exact supercuspidal support of `π`. -/
def InductionJacquetPreservesSupercuspidalSupportStatement : Prop :=
  letI := T.topology
  ∀ (n : ℕ), 0 < n →
    ∀ (C : BlockShape n)
      (π : SmoothRep.{0,v,max v z} ℂ (GeneralLinear n E.Carrier))
      (s : Multiset (CuspidalDatum.{z,v} T)),
        T.IsSupercuspidalSupport π s →
        ∀ D : SmoothRep.{0,v,max v z} ℂ (GeneralLinear n E.Carrier), D.IsIrreducible →
          SmoothRep.IsSubquotient D ((T.normalizedParabolicInductionFunctor C).obj
            ((T.normalizedJacquetFunctor C).obj π)) →
          T.IsSupercuspidalSupport D s

theorem inductionJacquetPreservesSupercuspidalSupport :
    InductionJacquetPreservesSupercuspidalSupportStatement.{v,z} T := by
  let := T.topology
  intro n hn C π s hπ D hD hsub
  obtain ⟨k, ρ, rfl, h, A, hA, _, hπ⟩ := hπ
  let B := T.cuspidalShape ρ h
  let Ξ := FiniteTensor.externalSmoothObject (fun i => (A i).obj)
  have hΞ : Ξ.IsIrreducible ∧ IsLeviCuspidal B Ξ.representation :=
    glCuspidalTensor p E T n hn B A
  let Ξ' := SmoothRep.of (universeLiftRepresentation.{v} Ξ.representation)
    ((isSmooth_universeLift_iff Ξ.representation).mpr Ξ.isSmooth)
  let e := universeLiftEquiv.{v} Ξ.representation
  have hΞ'i : Ξ'.IsIrreducible := (isIrreducible_universeLift_iff Ξ.representation).mpr hΞ.1
  have hΞ'q : IsLeviQuasicuspidal B Ξ'.representation :=
    (isLeviQuasicuspidal_iff_of_equiv B e).mp hΞ.2.2
  let eI : T.cuspidalProductInduced ρ h A ≅ (T.normalizedParabolicInductionFunctor B).obj Ξ' :=
    SmoothRep.mkIso (T.normalizedParabolicInducedEquiv B e)
  have hHom := Aubert.QuasicuspidalCutSupport.inductionJacquet_constituentSupport.{v,z}
    E T B C hn Ξ' (SmoothRep.hasFiniteLength_of_isIrreducible hΞ'i) hΞ'q π (hπ.of_iso_right eI)
  exact ⟨k, ρ, rfl, h, A, hA, hD, (hHom D hD hsub).of_iso_right eI.symm⟩

end Langlands.BaseChange
