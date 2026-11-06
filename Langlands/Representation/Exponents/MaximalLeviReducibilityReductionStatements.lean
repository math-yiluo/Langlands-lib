import Langlands.Representation.Exponents.MaximalLeviSupercuspidalReducibilityStatement
import Langlands.Representation.Category.Twist
import Langlands.Representation.MatrixCoefficient.ModuloCenter
import Langlands.Representation.Twist.ContinuousCharacterProof

/-! # The unitary-central-character reduction of Renard VII.1.3

Renard 2026, VII.1.3 (PDF p.230) begins its proof by twisting `ρ` with an unramified
character of `G` so that the central character becomes unitary (VI.8.5, III.2.11). This
module states the two halves of that reduction for the represented-parabolic interface:
the theorem for inductions with a unitary central character, and the existence of an
unramified twist of `G` making the central character of the induction unitary.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

section Restriction

variable {k : Type u} [Field k] {G P M : GroupScheme (Spec (CommRingCat.of k))}

/-- The restriction `χ_M = χ ∘ (l ≫ p)(F)` of a character of `G(F)` to the Levi points. -/
def leviRestrictedCharacter (p : P ⟶ G) (l : M ⟶ P) (χ : rationalPoints G →* ℂˣ) :
    rationalPoints M →* ℂˣ :=
  χ.comp (rationalPoints.map (l ≫ p))

theorem leviRestrictedCharacter_apply (p : P ⟶ G) (l : M ⟶ P) (χ : rationalPoints G →* ℂˣ)
    (m : rationalPoints M) :
    leviRestrictedCharacter p l χ m = χ (rationalPoints.map (l ≫ p) m) :=
  rfl

variable [TopologicalSpace k] [IsAffineHom G.X.hom]

local instance maximalLeviRestrictionAmbientPointTopology :
    TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

/-- The restriction of a continuous character of `G(F)` has an open kernel for the canonical
topology of `M(F)`, since `M(F)` is a nonarchimedean group. -/
theorem isOpen_ker_leviRestrictedCharacter [NonarchimedeanGroup (rationalPoints G)]
    (p : P ⟶ G) (l : M ⟶ P) (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
    (χ : rationalPoints G →ₜ* ℂˣ) :
    letI := leviPointTopology l hl
    IsOpen ((leviRestrictedCharacter p l χ.toMonoidHom).ker : Set (rationalPoints M)) := by
  let := leviPointTopology l hl
  have := leviPoints_nonarchimedeanGroup p l hp hl
  apply isOpen_ker_of_continuous_complex_character
  have hmap : Continuous fun m : rationalPoints M => rationalPoints.map (l ≫ p) m :=
    continuous_subtype_val.comp (leviPointsEquiv p l hp hl).continuous
  exact χ.continuous_toFun.comp hmap

end Restriction

/-- Renard VII.1.3 in the unitary case: the statement
`MaximalLeviSupercuspidalReducibilityStatement` with the additional premise that the
induced representation `i_P^G ρ` has a smooth unitary central character. -/
def MaximalLeviSupercuspidalReducibilityUnitaryStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (P M U : GroupScheme (Spec (CommRingCat.of k)))
      (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
      (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
      (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
      (hmul : IsIso (subgroupMultiplication l r)),
      ¬ IsIso p →
      (∀ (Q : GroupScheme (Spec (CommRingCat.of k))) (q : Q ⟶ G) (j : P ⟶ Q),
        IsParabolicSubgroup q → j ≫ q = p → IsIso j ∨ IsIso q) →
      haveI := hl.isConnectedReductive.isAffineHom
      letI : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
      haveI : LocallyCompactSpace (rationalPoints M) := leviPoints_locallyCompactSpace p l hp hl
      haveI : NonarchimedeanGroup (rationalPoints M) := leviPoints_nonarchimedeanGroup p l hp hl
      ∀ ρ : SmoothRep.{0, u, v} ℂ (rationalPoints M), ρ.IsIrreducible →
        (∀ (P' M' U' : GroupScheme (Spec (CommRingCat.of k)))
          (p' : P' ⟶ M) (l' : M' ⟶ P') (r' : U' ⟶ P')
          (hp' : IsParabolicSubgroup p') (hl' : IsRationalLeviSubgroup l')
          (hr' : LeviSubgroup.IsGeometricUnipotentRadical r')
          (hmul' : IsIso (subgroupMultiplication l' r')),
          ¬ IsIso p' → Subsingleton ((jacquetFunctor p' l' r' hp' hr' hl' hmul').obj ρ)) →
        ¬ ((leviInductionFunctor p l r hp hr hl hmul).obj ρ).IsIrreducible →
        Nonempty (UnitaryCentralCharacter
          ((leviInductionFunctor p l r hp hr hl hmul).obj ρ).representation) →
        ∃ (g : rationalPoints G) (φ : M ≅ M),
          φ.hom ≫ l ≫ p = l ≫ p ≫ (G.innerIso g).hom ∧ g ∉ pointImage (l ≫ p) ∧
          ∃ ψ : Plancherel.unramifiedCharacters
              (fun χ : rationalCharacters M => (Plancherel.rationalNormCharacters M χ).toMul),
            (∀ m : rationalPoints M, ∃ t : ℝ, 0 < t ∧
              (((ψ : rationalPoints M →ₜ* ℂˣ) m : ℂˣ) : ℂ) = t) ∧
            ∃ T : ρ ≃ₗ[ℂ] ρ, ∀ (m : rationalPoints M) (x : ρ),
              T (ρ.representation m x) =
                (((ψ : rationalPoints M →ₜ* ℂˣ) (rationalPoints.map φ.hom m) : ℂˣ) : ℂ) •
                  ρ.representation (rationalPoints.map φ.hom m) (T x)

/-- The twist step of Renard VI.8.5 used in VII.1.3: for an irreducible supercuspidal
representation `ρ` of the Levi points of an actual rational parabolic, some unramified
character `χ` of `G(F)` makes the induction of `ρ ⊗ χ_M` have a smooth unitary central
character, where `χ_M` is the restriction of `χ` to `M(F)`. -/
def MaximalLeviUnitaryCentralTwistStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (P M U : GroupScheme (Spec (CommRingCat.of k)))
      (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
      (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
      (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
      (hmul : IsIso (subgroupMultiplication l r)),
      haveI := hl.isConnectedReductive.isAffineHom
      letI : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
      haveI : LocallyCompactSpace (rationalPoints M) := leviPoints_locallyCompactSpace p l hp hl
      haveI : NonarchimedeanGroup (rationalPoints M) := leviPoints_nonarchimedeanGroup p l hp hl
      ∀ ρ : SmoothRep.{0, u, v} ℂ (rationalPoints M), ρ.IsIrreducible →
        (∀ (P' M' U' : GroupScheme (Spec (CommRingCat.of k)))
          (p' : P' ⟶ M) (l' : M' ⟶ P') (r' : U' ⟶ P')
          (hp' : IsParabolicSubgroup p') (hl' : IsRationalLeviSubgroup l')
          (hr' : LeviSubgroup.IsGeometricUnipotentRadical r')
          (hmul' : IsIso (subgroupMultiplication l' r')),
          ¬ IsIso p' → Subsingleton ((jacquetFunctor p' l' r' hp' hr' hl' hmul').obj ρ)) →
        ∃ χ : Plancherel.unramifiedCharacters
            (fun χ : rationalCharacters G => (Plancherel.rationalNormCharacters G χ).toMul),
          Nonempty (UnitaryCentralCharacter
            ((leviInductionFunctor p l r hp hr hl hmul).obj
              (ρ.twist (leviRestrictedCharacter p l (χ : rationalPoints G →ₜ* ℂˣ).toMonoidHom)
                (isOpen_ker_leviRestrictedCharacter p l hp hl
                  (χ : rationalPoints G →ₜ* ℂˣ)))).representation)

end Langlands.Aubert.General.RepresentedParabolic
