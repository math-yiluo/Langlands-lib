import Langlands.BruhatTits.IntegralModels.DepthZeroReduction
import Langlands.BruhatTits.IntegralModels.UnramifiedParahoricModelStatement
import Langlands.GroupScheme.Descent.FiniteUnramifiedAutomorphismLift
import Langlands.GroupScheme.Torus.FrobeniusConjugate
import Langlands.Galois.Local.SeparableUnramifiedArithmeticProof

/-! # Frobenius descent of the reductive quotient of a twisted-stable unramified model -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj ValuativeRel
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.LocalGalois.Separable

namespace Langlands.BruhatTits.IntegralModels

private instance unramifiedTwistedReductiveQuotientDescentAffineHom {F : Type u} [Field F]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] :
    IsAffineHom (baseChanged F (inertiaFixedField F) G).X.hom := by
  change IsAffineHom
    (CategoryTheory.Limits.pullback.snd G.X.hom (baseMap F (inertiaFixedField F)))
  infer_instance

/-- Let `F` be a nonarchimedean local field, `K` its maximal unramified extension inside the
separable closure, `O` the integers of `K` and `𝓀[F] ⊆ Ω` the residue fields of `F` and `O`.
Let `c` be a cocycle of `Aut(K/F)` in `G(K)` that is trivial on `Aut(K/E)` for a finite
subextension `E`. Let `D` be a relative-component model of `G_K` over `O` whose neutral integral
points `G^0(O)` are stable under every twisted conjugation
`g ↦ c σ * σ(g) * (c σ)⁻¹`, and let `Q` be the reductive quotient of the neutral special fibre.
For every automorphism `φ` of `K` reducing to the arithmetic Frobenius of `Ω`, there is a
connected reductive group `R` over `𝓀[F]` with an isomorphism `R_Ω ≅ Q.quotient` such that
reduction `G^0(O) → R(Ω)` carries the twisted conjugation by `φ` to the canonical Frobenius of
`R(Ω)`. Its existence is not proved here. -/
def UnramifiedTwistedReductiveQuotientDescentStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    (c : (inertiaFixedField F ≃ₐ[F] inertiaFixedField F) →
      rationalPoints (baseChanged F (inertiaFixedField F) G)),
    (∀ σ τ, c (σ * τ) = c σ * rationalConjugate F (inertiaFixedField F) G σ (c τ)) →
    (∃ E : IntermediateField F (inertiaFixedField F), FiniteDimensional F E ∧
      ∀ σ ∈ E.fixingSubgroup, c σ = 1) →
    ∀ (D : RelativeComponentModelData (fixedFieldIntegers F) (inertiaFixedField F)
        (baseChanged F (inertiaFixedField F) G)),
      (∀ (σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F) (g), g ∈ D.neutral.integralPoints →
        c σ * rationalConjugate F (inertiaFixedField F) G σ g * (c σ)⁻¹ ∈
          D.neutral.integralPoints) →
    ∀ (Q : SpecialFibreQuotientData D), Q.IsReductiveQuotient →
      letI : Fintype 𝓀[F] := Fintype.ofFinite _
      letI : Algebra 𝓀[F] (IsLocalRing.ResidueField (fixedFieldIntegers F)) :=
        (residueToFixedField F).toAlgebra
      letI : IsAlgClosure 𝓀[F] (IsLocalRing.ResidueField (fixedFieldIntegers F)) :=
        fixedFieldResidueIsAlgClosure F
      ∀ φ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
        (∀ x : fixedFieldIntegers F,
          IsLocalRing.residue (fixedFieldIntegers F)
              (Langlands.GroupScheme.Descent.FiniteUnramified.fixedFieldIntegerAut
                F φ x) =
            IsLocalRing.residue (fixedFieldIntegers F) x ^ Nat.card 𝓀[F]) →
        ∃ R : GroupScheme (Spec (CommRingCat.of 𝓀[F])), IsConnectedReductive R ∧
          ∃ e : (GroupScheme.baseChange (algebraBaseMap 𝓀[F]
              (IsLocalRing.ResidueField (fixedFieldIntegers F)))).obj R ≅ Q.quotient,
            ∀ (g : D.neutral.integralPoints)
              (hg : c φ * rationalConjugate F (inertiaFixedField F) G φ g * (c φ)⁻¹ ∈
                D.neutral.integralPoints),
              rationalPoints.map e.inv (Q.parahoricReduction ⟨_, hg⟩) =
                descentBasePoint
                  (algebraBaseMap 𝓀[F] (IsLocalRing.ResidueField (fixedFieldIntegers F)))
                  (galoisBaseMap 𝓀[F] (IsLocalRing.ResidueField (fixedFieldIntegers F))
                    (FiniteField.frobeniusAlgEquivOfAlgebraic 𝓀[F]
                      (IsLocalRing.ResidueField (fixedFieldIntegers F))))
                  (galoisBaseMap_over 𝓀[F] (IsLocalRing.ResidueField (fixedFieldIntegers F))
                    (FiniteField.frobeniusAlgEquivOfAlgebraic 𝓀[F]
                      (IsLocalRing.ResidueField (fixedFieldIntegers F))))
                  R (rationalPoints.map e.inv (Q.parahoricReduction g))

end Langlands.BruhatTits.IntegralModels
