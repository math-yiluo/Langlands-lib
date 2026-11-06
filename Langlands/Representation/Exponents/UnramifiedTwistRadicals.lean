import Langlands.Representation.Exponents.ArbitraryParabolic
import Langlands.Representation.Plancherel.RationalCharacterValuation
import Langlands.Representation.Plancherel.UnramifiedCharacters
import Langlands.Representation.Aubert.General.CharacterTwistEquivalences
import Langlands.GroupScheme.Torus.UnipotentHom

/-! # Unramified characters on unipotent radicals

Unramified characters of `H(F)` are trivial on the points of every unipotent group,
because a rational character restricted to a unipotent group scheme is trivial. In
particular an unramified character kills the radical points of every parabolic, which is
the condition under which the published general twist comparisons for normalized
induction and normalized Jacquet modules apply (Renard 2026, III.2.11). As a consequence,
the vanishing of every proper normalized Jacquet module (supercuspidality) is preserved by
unramified twists.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

section Unipotent

variable {k : Type u} [Field k] {G V : GroupScheme (Spec (CommRingCat.of k))}

/-- Every rational character takes the value `1` on the points of a unipotent group:
its restriction is a homomorphism from a unipotent group scheme to the split torus
`𝔾_m`. -/
theorem rationalCharacterEval_map_eq_one_of_isUnipotent (f : V ⟶ G) (hV : IsUnipotent V)
    (c : rationalCharacters G) (y : rationalPoints V) :
    rationalCharacterEval c (rationalPoints.map f y) = 1 := by
  have h : characterRestrict f c = 0 :=
    congrArg Additive.ofMul (hV.hom_eq_zero_of_isSplitTorus isSplitTorus_gm (f ≫ c.toMul))
  rw [← rationalCharacterEval_characterRestrict, h, rationalCharacterEval_zero]

variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/-- The points of a unipotent group map into the common kernel of the rational norm
characters. -/
theorem map_mem_rationalCommonNormKernel_of_isUnipotent (f : V ⟶ G) (hV : IsUnipotent V)
    (y : rationalPoints V) :
    rationalPoints.map f y ∈ Plancherel.rationalCommonNormKernel G := by
  rw [Plancherel.mem_rationalCommonNormKernel]
  intro c
  rw [rationalCharacterEval_map_eq_one_of_isUnipotent f hV c y, map_one]

/-- An unramified character of `G(F)` is trivial on the points of a unipotent group. -/
theorem unramifiedCharacter_map_eq_one_of_isUnipotent [TopologicalSpace (rationalPoints G)]
    (χ : Plancherel.unramifiedCharacters
      (fun c : rationalCharacters G => (Plancherel.rationalNormCharacters G c).toMul))
    (f : V ⟶ G) (hV : IsUnipotent V) (y : rationalPoints V) :
    (χ : rationalPoints G →ₜ* ℂˣ) (rationalPoints.map f y) = 1 :=
  χ.property (map_mem_rationalCommonNormKernel_of_isUnipotent f hV y)

end Unipotent

section Smooth

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] {H P U : GroupScheme (Spec (CommRingCat.of k))}
  [TopologicalSpace (rationalPoints H)] [NonarchimedeanGroup (rationalPoints H)]

/-- An unramified character of `H(F)` as a smooth character. -/
def unramifiedSmoothCharacter
    (χ : Plancherel.unramifiedCharacters
      (fun c : rationalCharacters H => (Plancherel.rationalNormCharacters H c).toMul)) :
    Induction.SmoothCharacter ℂ (rationalPoints H) where
  toMonoidHom := (χ : rationalPoints H →ₜ* ℂˣ).toMonoidHom
  isOpen_ker := Plancherel.unramifiedCharacter_isOpen_ker _ χ

@[simp]
theorem unramifiedSmoothCharacter_apply
    (χ : Plancherel.unramifiedCharacters
      (fun c : rationalCharacters H => (Plancherel.rationalNormCharacters H c).toMul))
    (h : rationalPoints H) :
    (unramifiedSmoothCharacter χ).toMonoidHom h = (χ : rationalPoints H →ₜ* ℂˣ) h :=
  rfl

/-- An unramified character of `H(F)` kills the radical points of every parabolic. -/
theorem pointImage_radical_le_ker_unramifiedSmoothCharacter (p : P ⟶ H) (r : U ⟶ P)
    (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
    (χ : Plancherel.unramifiedCharacters
      (fun c : rationalCharacters H => (Plancherel.rationalNormCharacters H c).toMul)) :
    pointImage (r ≫ p) ≤ (unramifiedSmoothCharacter χ).toMonoidHom.ker := by
  rintro _ ⟨y, rfl⟩
  exact unramifiedCharacter_map_eq_one_of_isUnipotent χ (r ≫ p) hr.1.isUnipotent y

end Smooth

section Jacquet

variable {k : Type u} [Field k] [TopologicalSpace k] [T2Space k]
  {H P' M' U' : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom H.X.hom]

local instance twistJacquetPointTopology : TopologicalSpace (rationalPoints H) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints H)] [NonarchimedeanGroup (rationalPoints H)]

/-- Vanishing of an actual normalized Jacquet module is unchanged by a twist by a smooth
character trivial on the radical points. -/
theorem jacquetFunctor_subsingleton_twist_iff (p' : P' ⟶ H) (l' : M' ⟶ P') (r' : U' ⟶ P')
    (hp' : IsParabolicSubgroup p') (hl' : IsRationalLeviSubgroup l')
    (hr' : LeviSubgroup.IsGeometricUnipotentRadical r')
    (hmul' : IsIso (subgroupMultiplication l' r'))
    (χ : Induction.SmoothCharacter ℂ (rationalPoints H))
    (hχ : pointImage (r' ≫ p') ≤ χ.toMonoidHom.ker) (A : SmoothRep.{0, u, v} ℂ (rationalPoints H)) :
    Subsingleton ((jacquetFunctor p' l' r' hp' hr' hl' hmul').obj
        (A.twist χ.toMonoidHom χ.isOpen_ker)) ↔
      Subsingleton ((jacquetFunctor p' l' r' hp' hr' hl' hmul').obj A) := by
  rw [← SmoothRep.isZero_iff_subsingleton_carrier, ← SmoothRep.isZero_iff_subsingleton_carrier]
  exact normalizedJacquet_isZero_characterTwist_iff _ _ _ _ χ hχ A

variable [ValuativeRel k] [IsNonarchimedeanLocalField k]

/-- Vanishing of an actual normalized Jacquet module is unchanged by an unramified twist. -/
theorem jacquetFunctor_subsingleton_unramifiedTwist_iff (p' : P' ⟶ H) (l' : M' ⟶ P')
    (r' : U' ⟶ P') (hp' : IsParabolicSubgroup p') (hl' : IsRationalLeviSubgroup l')
    (hr' : LeviSubgroup.IsGeometricUnipotentRadical r')
    (hmul' : IsIso (subgroupMultiplication l' r'))
    (ψ : Plancherel.unramifiedCharacters
      (fun c : rationalCharacters H => (Plancherel.rationalNormCharacters H c).toMul))
    (A : SmoothRep.{0, u, v} ℂ (rationalPoints H)) :
    Subsingleton ((jacquetFunctor p' l' r' hp' hr' hl' hmul').obj
        (A.twist (ψ : rationalPoints H →ₜ* ℂˣ).toMonoidHom
          (Plancherel.unramifiedCharacter_isOpen_ker _ ψ))) ↔
      Subsingleton ((jacquetFunctor p' l' r' hp' hr' hl' hmul').obj A) :=
  jacquetFunctor_subsingleton_twist_iff p' l' r' hp' hl' hr' hmul' (unramifiedSmoothCharacter ψ)
    (pointImage_radical_le_ker_unramifiedSmoothCharacter p' r' hr' ψ) A

/-- Supercuspidality, in the form "every normalized Jacquet module for a proper actual
parabolic vanishes", is preserved by an unramified twist. -/
theorem properJacquet_subsingleton_unramifiedTwist
    (ψ : Plancherel.unramifiedCharacters
      (fun c : rationalCharacters H => (Plancherel.rationalNormCharacters H c).toMul))
    (A : SmoothRep.{0, u, v} ℂ (rationalPoints H))
    (hA : ∀ (P' M' U' : GroupScheme (Spec (CommRingCat.of k)))
      (p' : P' ⟶ H) (l' : M' ⟶ P') (r' : U' ⟶ P')
      (hp' : IsParabolicSubgroup p') (hl' : IsRationalLeviSubgroup l')
      (hr' : LeviSubgroup.IsGeometricUnipotentRadical r')
      (hmul' : IsIso (subgroupMultiplication l' r')),
      ¬ IsIso p' → Subsingleton ((jacquetFunctor p' l' r' hp' hr' hl' hmul').obj A)) :
    ∀ (P' M' U' : GroupScheme (Spec (CommRingCat.of k)))
      (p' : P' ⟶ H) (l' : M' ⟶ P') (r' : U' ⟶ P')
      (hp' : IsParabolicSubgroup p') (hl' : IsRationalLeviSubgroup l')
      (hr' : LeviSubgroup.IsGeometricUnipotentRadical r')
      (hmul' : IsIso (subgroupMultiplication l' r')),
      ¬ IsIso p' → Subsingleton ((jacquetFunctor p' l' r' hp' hr' hl' hmul').obj
        (A.twist (ψ : rationalPoints H →ₜ* ℂˣ).toMonoidHom
          (Plancherel.unramifiedCharacter_isOpen_ker _ ψ))) :=
  fun P' M' U' p' l' r' hp' hl' hr' hmul' hproper =>
    (jacquetFunctor_subsingleton_unramifiedTwist_iff p' l' r' hp' hl' hr' hmul' ψ A).mpr
      (hA P' M' U' p' l' r' hp' hl' hr' hmul' hproper)

end Jacquet

end Langlands.Aubert.General.RepresentedParabolic
