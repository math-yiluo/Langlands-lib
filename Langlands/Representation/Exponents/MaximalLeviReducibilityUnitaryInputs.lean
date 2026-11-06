import Langlands.Representation.Exponents.MaximalLeviSupercuspidalReducibilityStatement
import Langlands.Representation.Category.Twist
import Langlands.Representation.MatrixCoefficient.ModuloCenter
import Langlands.Representation.Unitary.Basic

/-! # Inputs for the unitary case of Renard VII.1.3

Renard 2026, VII.1.3 (PDF pp.230–232) proves the reducibility criterion for inductions
from irreducible supercuspidal representations of maximal Levis with results of Chapters
III, IV and VI. This module states those results for the represented-parabolic interface,
as propositions that are neither assumed nor proved here:

* an irreducible supercuspidal representation with a unitary central character is
  unitarizable (VI.2.1, IV.3.2);
* normalized induction preserves admissibility (III.2.3), unitarizability (IV.2.3) and
  nonzeroness;
* the hermitian dual of a normalized induction from an admissible unitarizable
  representation twisted by a character `χ` is the induction twisted by `conj(χ)⁻¹`
  (IV.2.1.2), in the form used on admissible unitarizable constituents;
* for a maximal parabolic, the adjunction and the geometric lemma (III.2.5, VI.5.3)
  control the endomorphisms of `i_P^G ρ` and the morphisms `i_P^G τ' → i_P^G τ`;
* for a maximal parabolic and a supercuspidal `ρ` without a unitary central character, a
  reducible `i_P^G ρ` with a unitary central character has an irreducible unitarizable
  subrepresentation or quotient (the Casselman-criterion step of VII.1.3).
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- Renard VI.2.1 and IV.3.2: for a connected reductive group `H` over a nonarchimedean
local field, an irreducible smooth representation of `H(F)` all of whose normalized
Jacquet modules for proper actual parabolics vanish, and whose center acts by a smooth
unitary character, carries an invariant positive definite Hermitian form. -/
def SupercuspidalUnitaryCentralCharacterUnitarizableStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    (H : GroupScheme (Spec (CommRingCat.of k))) (hH : IsConnectedReductive H),
    haveI := hH.isAffineHom
    letI : TopologicalSpace (rationalPoints H) := RationalPointFamily.pointTopology
    ∀ [LocallyCompactSpace (rationalPoints H)] [NonarchimedeanGroup (rationalPoints H)]
      (ρ : SmoothRep.{0, u, v} ℂ (rationalPoints H)), ρ.IsIrreducible →
      (∀ (P' M' U' : GroupScheme (Spec (CommRingCat.of k)))
        (p' : P' ⟶ H) (l' : M' ⟶ P') (r' : U' ⟶ P')
        (hp' : IsParabolicSubgroup p') (hl' : IsRationalLeviSubgroup l')
        (hr' : LeviSubgroup.IsGeometricUnipotentRadical r')
        (hmul' : IsIso (subgroupMultiplication l' r')),
        ¬ IsIso p' → Subsingleton ((jacquetFunctor p' l' r' hp' hr' hl' hmul').obj ρ)) →
      Nonempty (UnitaryCentralCharacter ρ.representation) →
      IsUnitarizable ρ.representation

/-- Renard III.2.3 with VI.1.2: normalized induction from an actual rational parabolic
sends admissible representations of `M(F)` to admissible representations of `G(F)`. -/
def LeviInductionAdmissibleStatement : Prop :=
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
      letI : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
      ∀ σ : SmoothRep.{0, u, v} ℂ (rationalPoints M), σ.IsAdmissible →
        ((leviInductionFunctor p l r hp hr hl hmul).obj σ).IsAdmissible

/-- Renard IV.2.3: normalized induction from an actual rational parabolic sends
unitarizable representations of `M(F)` to unitarizable representations of `G(F)`. -/
def LeviInductionUnitarizableStatement : Prop :=
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
      letI : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
      ∀ σ : SmoothRep.{0, u, v} ℂ (rationalPoints M), IsUnitarizable σ.representation →
        IsUnitarizable ((leviInductionFunctor p l r hp hr hl hmul).obj σ).representation

/-- Normalized induction from an actual rational parabolic sends nonzero representations
of `M(F)` to nonzero representations of `G(F)`. -/
def LeviInductionNontrivialStatement : Prop :=
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
      letI : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
      ∀ σ : SmoothRep.{0, u, v} ℂ (rationalPoints M), Nontrivial σ →
        Nontrivial ((leviInductionFunctor p l r hp hr hl hmul).obj σ)

/-- Renard IV.2.1.2 and IV.2.1, Remark 1: let `σ` be an admissible unitarizable
representation of `M(F)` and `χ, χ'` open-kernel characters of `M(F)` with
`χ'(m) · conj(χ(m)) = 1`, so that the hermitian dual of `i_P^G (σ ⊗ χ)` is
`i_P^G (σ ⊗ χ')`. If a nonzero admissible unitarizable `W` is a subrepresentation of
`i_P^G (σ ⊗ χ)`, there is a nonzero morphism `i_P^G (σ ⊗ χ') → W`; if `W` is a quotient
of `i_P^G (σ ⊗ χ)`, there is a nonzero morphism `W → i_P^G (σ ⊗ χ')`. -/
def LeviInductionHermitianDualityStatement : Prop :=
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
      letI : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
      ∀ σ : SmoothRep.{0, u, v} ℂ (rationalPoints M), σ.IsAdmissible →
        IsUnitarizable σ.representation →
        ∀ (χ χ' : rationalPoints M →* ℂˣ) (hχ : IsOpen (χ.ker : Set (rationalPoints M)))
          (hχ' : IsOpen (χ'.ker : Set (rationalPoints M))),
          (∀ m : rationalPoints M, (χ' m : ℂ) * starRingEnd ℂ (χ m : ℂ) = 1) →
          ∀ W : SmoothRep.{0, u, max u v} ℂ (rationalPoints G), W.IsAdmissible →
            IsUnitarizable W.representation → Nontrivial W →
            ((∃ f : W ⟶ (leviInductionFunctor p l r hp hr hl hmul).obj (σ.twist χ hχ),
                Function.Injective (SmoothRep.hom f)) →
              ∃ f : (leviInductionFunctor p l r hp hr hl hmul).obj (σ.twist χ' hχ') ⟶ W,
                ∃ x, SmoothRep.hom f x ≠ 0) ∧
            ((∃ f : (leviInductionFunctor p l r hp hr hl hmul).obj (σ.twist χ hχ) ⟶ W,
                Function.Surjective (SmoothRep.hom f)) →
              ∃ f : W ⟶ (leviInductionFunctor p l r hp hr hl hmul).obj (σ.twist χ' hχ'),
                ∃ x, SmoothRep.hom f x ≠ 0)

/-- Renard III.2.5 and VI.5.3, as used in VII.1.3: for an actual maximal proper rational
parabolic and an irreducible supercuspidal `ρ` of `M(F)`, every endomorphism of
`i_P^G ρ` is a scalar unless some `g ∈ G(F)` outside the Levi image normalizes the Levi
through an automorphism `φ` with `ρ ∘ φ(F) ≃ ρ`. -/
def MaximalLeviSupercuspidalInductionEndomorphismStatement : Prop :=
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
        ∀ f : (leviInductionFunctor p l r hp hr hl hmul).obj ρ ⟶
            (leviInductionFunctor p l r hp hr hl hmul).obj ρ,
          (∃ c : ℂ, ∀ x, SmoothRep.hom f x = c • x) ∨
          ∃ (g : rationalPoints G) (φ : M ≅ M),
            φ.hom ≫ l ≫ p = l ≫ p ≫ (G.innerIso g).hom ∧ g ∉ pointImage (l ≫ p) ∧
            ∃ T : ρ ≃ₗ[ℂ] ρ, ∀ (m : rationalPoints M) (x : ρ),
              T (ρ.representation m x) = ρ.representation (rationalPoints.map φ.hom m) (T x)

/-- Renard III.2.5 and VI.5.3, as used in VII.1.3: for an actual maximal proper rational
parabolic and irreducible supercuspidal `τ, τ'` of `M(F)`, a nonzero morphism
`i_P^G τ' → i_P^G τ` forces `τ' ≃ τ`, or `τ ≃ τ' ∘ φ(F)` for an automorphism `φ` of `M`
induced by some `g ∈ G(F)` outside the Levi image. -/
def MaximalLeviSupercuspidalInductionHomStatement : Prop :=
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
      ∀ τ τ' : SmoothRep.{0, u, v} ℂ (rationalPoints M), τ.IsIrreducible → τ'.IsIrreducible →
        (∀ (P' M' U' : GroupScheme (Spec (CommRingCat.of k)))
          (p' : P' ⟶ M) (l' : M' ⟶ P') (r' : U' ⟶ P')
          (hp' : IsParabolicSubgroup p') (hl' : IsRationalLeviSubgroup l')
          (hr' : LeviSubgroup.IsGeometricUnipotentRadical r')
          (hmul' : IsIso (subgroupMultiplication l' r')),
          ¬ IsIso p' → Subsingleton ((jacquetFunctor p' l' r' hp' hr' hl' hmul').obj τ)) →
        (∀ (P' M' U' : GroupScheme (Spec (CommRingCat.of k)))
          (p' : P' ⟶ M) (l' : M' ⟶ P') (r' : U' ⟶ P')
          (hp' : IsParabolicSubgroup p') (hl' : IsRationalLeviSubgroup l')
          (hr' : LeviSubgroup.IsGeometricUnipotentRadical r')
          (hmul' : IsIso (subgroupMultiplication l' r')),
          ¬ IsIso p' → Subsingleton ((jacquetFunctor p' l' r' hp' hr' hl' hmul').obj τ')) →
        ∀ f : (leviInductionFunctor p l r hp hr hl hmul).obj τ' ⟶
            (leviInductionFunctor p l r hp hr hl hmul).obj τ,
          (∃ x, SmoothRep.hom f x ≠ 0) →
          Nonempty (τ' ≅ τ) ∨
          ∃ (g : rationalPoints G) (φ : M ≅ M),
            φ.hom ≫ l ≫ p = l ≫ p ≫ (G.innerIso g).hom ∧ g ∉ pointImage (l ≫ p) ∧
            ∃ T : τ ≃ₗ[ℂ] τ', ∀ (m : rationalPoints M) (x : τ),
              T (τ.representation m x) = τ'.representation (rationalPoints.map φ.hom m) (T x)

/-- The Casselman-criterion step of Renard VII.1.3 (with VII.1.2, VI.5.4, IV.3.2): for an
actual maximal proper rational parabolic and an irreducible supercuspidal `ρ` of `M(F)`
whose central character is not unitary, if `i_P^G ρ` is reducible with a unitary central
character, then one of its composition factors is square-integrable modulo the center;
in particular `i_P^G ρ` has an irreducible unitarizable subrepresentation or quotient. -/
def MaximalLeviSupercuspidalUnitarizableConstituentStatement : Prop :=
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
        IsEmpty (UnitaryCentralCharacter ρ.representation) →
        ¬ ((leviInductionFunctor p l r hp hr hl hmul).obj ρ).IsIrreducible →
        Nonempty (UnitaryCentralCharacter
          ((leviInductionFunctor p l r hp hr hl hmul).obj ρ).representation) →
        ∃ W : SmoothRep.{0, u, max u v} ℂ (rationalPoints G),
          W.IsIrreducible ∧ IsUnitarizable W.representation ∧
          ((∃ f : W ⟶ (leviInductionFunctor p l r hp hr hl hmul).obj ρ,
              Function.Injective (SmoothRep.hom f)) ∨
            ∃ f : (leviInductionFunctor p l r hp hr hl hmul).obj ρ ⟶ W,
              Function.Surjective (SmoothRep.hom f))

end Langlands.Aubert.General.RepresentedParabolic
