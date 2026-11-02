import Langlands.Global.Arithmetic.HarrisSetup

/-!
# CM fields with the two compatible place pairs in Harris's setup

This is an arithmetic existence assertion, with explicit CM composita,
completion diagrams and Galois actions. It introduces no character or
automorphic conclusion. The statement is not proved here.
-/

noncomputable section

universe uF

namespace Langlands.Global

open NumberField LocalFactor.CommonClosure GeneralPosition Harris
open AdelicFunctoriality

/-- The field-and-place existence input of Henniart 2000, Section 3.3, applied
to a finite extension and its normal closure, with the two conjugate-place
pairs used by Harris 1998, Section 4, printed pages 200--201. -/
def HarrisPairedPlaceRealizationStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (F' : Extension F),
    letI := F.canonicalTopology
    letI := (fieldData F F').topology
    letI := (fieldData F (galoisClosure F F')).topology
    ∃ (E E' L : Type) (_ : Field E) (_ : Field E') (_ : Field L)
      (_ : NumberField E) (_ : NumberField E') (_ : NumberField L)
      (_ : IsCMField E) (_ : IsCMField E') (_ : IsCMField L)
      (_ : Algebra E E') (_ : Algebra E L) (_ : Algebra E' L)
      (_ : IsScalarTower E E' L) (_ : IsNormalClosure E E' L)
      (K₀ : IntermediateField ℚ E)
      (P Ps : PlaceDatum F F' E E' L)
      (φ : FiniteCompletion E' P.v' ≃+* F'.field)
      (φs : FiniteCompletion E' Ps.v' ≃+* F'.field)
      (θ : (L ≃ₐ[E] L) ≃*
        ((galoisClosure F F').field ≃ₐ[F.Carrier] (galoisClosure F F').field)),
      IsSplitImaginaryQuadratic p K₀ ∧
      maximalRealSubfield E ⊔ K₀.toSubfield = ⊤ ∧
      maximalRealSubfield E' ⊔ K₀.toSubfield.map (algebraMap E E') = ⊤ ∧
      maximalRealSubfield L ⊔ K₀.toSubfield.map (algebraMap E L) = ⊤ ∧
      Module.finrank E E' = Module.finrank F.Carrier F'.field ∧
      Module.finrank E L = Module.finrank F.Carrier (galoisClosure F F').field ∧
      List.Pairwise (· ≠ ·) [P.v, conjPlace E P.v, Ps.v, conjPlace E Ps.v] ∧
      (∀ v ∈ [P.v, conjPlace E P.v, Ps.v, conjPlace E Ps.v],
        (p : 𝓞 E) ∈ v.asIdeal ∧ HasUniquePlaceAbove L v) ∧
      (∀ Q ∈ [P, Ps],
        Q.IsCompatible ∧
        Continuous Q.iso ∧ Continuous Q.iso.symm ∧
        Continuous Q.isoTilde ∧ Continuous Q.isoTilde.symm ∧
        ∀ (σ : L ≃ₐ[E] L) (x : L),
          θ σ (Q.isoTilde (algebraMap L (FiniteCompletion L Q.vTilde) x)) =
            Q.isoTilde (algebraMap L (FiniteCompletion L Q.vTilde) (σ x))) ∧
      Continuous φ ∧ Continuous φ.symm ∧
      Continuous φs ∧ Continuous φs.symm ∧
      (∀ x : FiniteCompletion E P.v,
        φ (FiniteExtension.completionMap P.v P.v' x) =
          algebraMap F.Carrier F'.field (P.iso x)) ∧
      (∀ y : FiniteCompletion E' P.v',
        ((φ y : F'.field) : AlgebraicClosure F.Carrier) =
          ((P.isoTilde (FiniteExtension.completionMap P.v' P.vTilde y) :
            (galoisClosure F F').field) : AlgebraicClosure F.Carrier)) ∧
      (∀ x : FiniteCompletion E Ps.v,
        φs (FiniteExtension.completionMap Ps.v Ps.v' x) =
          algebraMap F.Carrier F'.field (Ps.iso x)) ∧
      (∀ y : FiniteCompletion E' Ps.v',
        ((φs y : F'.field) : AlgebraicClosure F.Carrier) =
          ((Ps.isoTilde (FiniteExtension.completionMap Ps.v' Ps.vTilde y) :
            (galoisClosure F F').field) : AlgebraicClosure F.Carrier))

end Langlands.Global
