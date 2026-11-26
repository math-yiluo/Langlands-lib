import Langlands.GroupScheme.Rational.SimplyConnectedHasseAbsolute
import Langlands.GroupScheme.Rational.NumberFieldSimplyConnectedCenterModel
import Langlands.GroupScheme.Rational.NumberFieldInnerTypeAHasseReduction
import Langlands.GroupScheme.Rational.NumberFieldClassicalTypeDHasseReduction
import Langlands.GroupScheme.Rational.NumberFieldTypeCHasse
import Langlands.GroupScheme.Rational.NumberFieldTypeG2Hasse
import Langlands.GroupScheme.SimplyConnected.TypeD4StarOrbits

/-! # The absolutely almost-simple Hasse kernel by Cartan type

This module states the Hasse kernel over number fields for the simply connected
absolutely almost-simple groups of outer type `A`, of type `B`, of trialitarian
type `D_4` and of the types `E_6`, `E_7`, `E_8` and `F_4`. It proves that these
statements, the local-to-global principle for reduced norms and the quaternionic
spin kernel together give the kernel for every absolutely almost-simple simply
connected group. The statements are not proved here.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- The localization kernel for simply connected absolutely almost-simple groups
of outer type `A_n`: the Cartan matrix is of type `A_n` and the full star action
moves some simple vertex. -/
def NumberFieldOuterTypeAHasseStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G) (n : ℕ) (e : d.Vertex ≃ Fin n),
    IsSimplyConnected G → IsAbsolutelyAlmostSimple G →
    (∀ a b, d.cartan a b = CartanMatrix.A n (e a) (e b)) →
    (∃ (σ : SeparableClosure F ≃ₐ[F] SeparableClosure F) (a : d.Vertex), d.star σ a ≠ a) →
    ∀ (L : Type u) [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
      (ξ : Cocycle G (GaloisCocycle.cover F L)), ξ.LocallyTrivial → ξ.IsTrivial

/-- The localization kernel for simply connected absolutely almost-simple groups
of type `B_n` with `n ≥ 3`. -/
def NumberFieldTypeBSimplyConnectedGaloisHasseKernelStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G) (n : ℕ) (e : d.Vertex ≃ Fin n),
    3 ≤ n → IsSimplyConnected G → IsAbsolutelyAlmostSimple G →
    (∀ a b, d.cartan a b = CartanMatrix.B n (e a) (e b)) →
    ∀ (L : Type u) [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
      (ξ : Cocycle G (GaloisCocycle.cover F L)), ξ.LocallyTrivial → ξ.IsTrivial

/-- The localization kernel for simply connected absolutely almost-simple groups
of trialitarian type `D_4`: in the numbering of `CartanMatrix.D 4`, whose vertex `1`
is the centre, no leaf is fixed by the full star action. -/
def NumberFieldTrialitarianTypeDHasseStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G) (e : d.Vertex ≃ Fin 4),
    IsSimplyConnected G → IsAbsolutelyAlmostSimple G →
    (∀ a b, d.cartan a b = CartanMatrix.D 4 (e a) (e b)) →
    (∀ a : d.Vertex, e a ≠ 1 →
      ∃ σ : SeparableClosure F ≃ₐ[F] SeparableClosure F, d.star σ a ≠ a) →
    ∀ (L : Type u) [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
      (ξ : Cocycle G (GaloisCocycle.cover F L)), ξ.LocallyTrivial → ξ.IsTrivial

/-- The localization kernel for simply connected absolutely almost-simple groups
of type `E_6`, inner or outer. -/
def NumberFieldTypeE6HasseStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G) (e : d.Vertex ≃ Fin 6),
    IsSimplyConnected G → IsAbsolutelyAlmostSimple G →
    (∀ a b, d.cartan a b = CartanMatrix.E 6 (e a) (e b)) →
    ∀ (L : Type u) [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
      (ξ : Cocycle G (GaloisCocycle.cover F L)), ξ.LocallyTrivial → ξ.IsTrivial

/-- The localization kernel for simply connected absolutely almost-simple groups
of type `E_7`. -/
def NumberFieldTypeE7HasseStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G) (e : d.Vertex ≃ Fin 7),
    IsSimplyConnected G → IsAbsolutelyAlmostSimple G →
    (∀ a b, d.cartan a b = CartanMatrix.E 7 (e a) (e b)) →
    ∀ (L : Type u) [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
      (ξ : Cocycle G (GaloisCocycle.cover F L)), ξ.LocallyTrivial → ξ.IsTrivial

/-- The localization kernel for simply connected absolutely almost-simple groups
of type `E_8`. -/
def NumberFieldTypeE8HasseStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G) (e : d.Vertex ≃ Fin 8),
    IsSimplyConnected G → IsAbsolutelyAlmostSimple G →
    (∀ a b, d.cartan a b = CartanMatrix.E 8 (e a) (e b)) →
    ∀ (L : Type u) [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
      (ξ : Cocycle G (GaloisCocycle.cover F L)), ξ.LocallyTrivial → ξ.IsTrivial

/-- The localization kernel for simply connected absolutely almost-simple groups
of type `F_4`. -/
def NumberFieldTypeF4HasseStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G) (e : d.Vertex ≃ Fin 4),
    IsSimplyConnected G → IsAbsolutelyAlmostSimple G →
    (∀ a b, d.cartan a b = CartanMatrix.F₄ (e a) (e b)) →
    ∀ (L : Type u) [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
      (ξ : Cocycle G (GaloisCocycle.cover F L)), ξ.LocallyTrivial → ξ.IsTrivial

/-- Exchanging the two vertices of the rank-two type `B` numbering gives the
rank-two type `C` numbering. -/
theorem cartanB_two_swap (i j : Fin 2) :
    CartanMatrix.B 2 i j = CartanMatrix.C 2 (Equiv.swap 0 1 i) (Equiv.swap 0 1 j) := by
  fin_cases i <;> fin_cases j <;> simp [CartanMatrix.B, CartanMatrix.C]

set_option backward.isDefEq.respectTransparency false in
/-- The case analysis over the absolute Cartan type: the reduced-norm principle
gives inner type `A`, the quaternionic spin kernel gives the type `D` groups whose
star action fixes a leaf, and the published type `C` and `G_2` kernels together
with the displayed statements give the remaining types. -/
theorem numberFieldAbsolutelyAlmostSimpleSimplyConnectedGaloisHasseKernel_of_types
    (hnorm : Langlands.CentralSimple.NumberFieldReducedNormLocalityStatement.{u})
    (houter : NumberFieldOuterTypeAHasseStatement.{u})
    (hB : NumberFieldTypeBSimplyConnectedGaloisHasseKernelStatement.{u})
    (hquat : NumberFieldQuaternionicSpinHasseStatement.{u})
    (htri : NumberFieldTrialitarianTypeDHasseStatement.{u})
    (hE6 : NumberFieldTypeE6HasseStatement.{u})
    (hE7 : NumberFieldTypeE7HasseStatement.{u})
    (hE8 : NumberFieldTypeE8HasseStatement.{u})
    (hF4 : NumberFieldTypeF4HasseStatement.{u}) :
    NumberFieldAbsolutelyAlmostSimpleSimplyConnectedGaloisHasseKernelStatement.{u} := by
  intro F _ _ G hsc habs L _ _ _ _ ξ hξ
  let hR := hsc.isSemisimple.isConnectedReductive
  let : IsAffineHom G.X.hom := hR.isAffineHom
  let : Smooth G.X.hom := hR.smooth
  obtain ⟨d⟩ := titsIndexExistence F G hsc.isSemisimple
  rcases absolutelyAlmostSimpleCartanClassification F G d habs with
    ⟨n, hn, e, he⟩ | ⟨n, hn, e, he⟩ | ⟨n, hn, e, he⟩ | ⟨n, hn, e, he⟩ |
    ⟨e, he⟩ | ⟨e, he⟩ | ⟨e, he⟩ | ⟨e, he⟩ | ⟨e, he⟩
  · by_cases hstar : ∀ (σ : SeparableClosure F ≃ₐ[F] SeparableClosure F) (a : d.Vertex),
        d.star σ a = a
    · exact numberFieldInnerTypeASimplyConnectedGaloisHasseKernel_of_reducedNormLocality hnorm
        F G d n hsc habs ⟨hn, ⟨e, he⟩, hstar⟩ L ξ hξ
    · push Not at hstar
      exact houter F G d n e hsc habs he hstar L ξ hξ
  · rcases Nat.lt_or_ge n 3 with h | h
    · obtain rfl : n = 2 := by omega
      exact numberFieldTypeCSimplyConnectedGaloisHasseKernel F G d 2
        (e.trans (Equiv.swap 0 1)) le_rfl hsc habs
        (fun a b => (he a b).trans (cartanB_two_swap (e a) (e b))) L ξ hξ
    · exact hB F G d n e h hsc habs he L ξ hξ
  · exact numberFieldTypeCSimplyConnectedGaloisHasseKernel F G d n e hn hsc habs he L ξ hξ
  · rcases Nat.lt_or_ge n 5 with h | h
    · obtain rfl : n = 4 := by omega
      by_cases hleaf : ∃ a : d.Vertex, e a ≠ 1 ∧
          ∀ σ : SeparableClosure F ≃ₐ[F] SeparableClosure F, d.star σ a = a
      · obtain ⟨a, ha, hfix⟩ := hleaf
        exact numberFieldClassicalTypeDHasse_of_quaternionic hquat F G d 4
          (d.d4NumberingAt e a) le_rfl hsc habs (d.d4NumberingAt_cartan e he a ha)
          (fun γ b hb => d.star_fixes_nonfork_of_D4_fixed_leaf e he a ha hfix γ b hb) L ξ hξ
      · push Not at hleaf
        exact htri F G d e hsc habs he hleaf L ξ hξ
    · exact numberFieldClassicalTypeDHasse_of_quaternionic hquat F G d n e hn hsc habs he
        (fun γ a ha => d.star_fixes_nonfork_of_D h e he γ a ha) L ξ hξ
  · exact hE6 F G d e hsc habs he L ξ hξ
  · exact hE7 F G d e hsc habs he L ξ hξ
  · exact hE8 F G d e hsc habs he L ξ hξ
  · exact hF4 F G d e hsc habs he L ξ hξ
  · exact numberFieldTypeG2Hasse F G d e hsc habs he L ξ hξ

end Langlands.GroupScheme
