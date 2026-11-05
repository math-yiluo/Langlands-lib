import Langlands.Representation.Exponents.ArbitraryParabolic
import Langlands.Representation.Aubert.General.Conjugation
import Langlands.Representation.Filtration.GeneralizedEigencharacterProof
import Langlands.GroupScheme.Rational.ParabolicAmbientTransport
import Langlands.GroupScheme.Rational.ParabolicPointConjugation

/-! # Inner conjugation of arbitrary normalized Jacquet exponents

These are internal transport constructions for the normalized standard
reduction. The actual quotient map is `[v] ↦ [π(g)v]`; the normalization
corresponds by the published conjugation law for the Haar modulus.
-/

noncomputable section

universe u v w

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

section GroupTransport

variable {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [LocallyCompactSpace Γ]
  [NonarchimedeanGroup Γ] {B : Type w} [Group B]
  {N L N' L' : Subgroup Γ}

/-- Translation by `π(g)` identifies the normalized quotient actions restricted
along point maps that correspond under conjugation. -/
def normalizedJacquetRestrictedConjugationEquiv
    (hN : IsClosed (N : Set Γ)) (hLN : L ≤ Subgroup.normalizer (N : Set Γ))
    (hN' : IsClosed (N' : Set Γ)) (hLN' : L' ≤ Subgroup.normalizer (N' : Set Γ))
    (g : Γ) (hNN' : ∀ x : Γ, x ∈ N' ↔ g⁻¹ * x * g ∈ N)
    (hLL' : ∀ x : Γ, x ∈ L' ↔ g⁻¹ * x * g ∈ L)
    (rho : B →* L) (rho' : B →* L')
    (hrho : ∀ t : B, conjugationEquiv g hLL' (rho' t) = rho t)
    (π : SmoothRep.{0, u, v} ℂ Γ) :
    Representation.Equiv
      (((normalizedJacquetFunctor N L hN hLN).obj π).representation.comp rho)
      (((normalizedJacquetFunctor N' L' hN' hLN').obj π).representation.comp rho') :=
  Representation.Equiv.mk (coinvariantsTranslateEquiv g hNN' π.representation)
    (fun t => by
      apply Jacquet.Localization.hom_ext
      ext x
      change coinvariantsTranslate g hNN' π.representation
          (((HaarModulus.closedInverseHalfCharacter N hN L hLN (rho t) : ℂˣ) : ℂ) •
            Jacquet.Localization.mk π.representation N 1 (π.representation (rho t) x)) =
        ((HaarModulus.closedInverseHalfCharacter N' hN' L' hLN' (rho' t) : ℂˣ) : ℂ) •
          Jacquet.Localization.mk π.representation N' 1
            (π.representation (rho' t) (π.representation g x))
      rw [map_smul, coinvariantsTranslate_mk,
        closedInverseHalfCharacter_conj g hNN' hLL' hN hN' hLN hLN' (rho' t),
        hrho t]
      congr 2
      rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
      have ht := congrArg Subtype.val (hrho t)
      change g⁻¹ * (rho' t : Γ) * g = (rho t : Γ) at ht
      rw [← ht]
      congr 2
      group)

/-- The restricted normalized actions have the same uniform generalized
eigencharacters, with the character's domain unchanged. -/
theorem normalizedGeneralizedEigencharacter_conj
    (hN : IsClosed (N : Set Γ)) (hLN : L ≤ Subgroup.normalizer (N : Set Γ))
    (hN' : IsClosed (N' : Set Γ)) (hLN' : L' ≤ Subgroup.normalizer (N' : Set Γ))
    (g : Γ) (hNN' : ∀ x : Γ, x ∈ N' ↔ g⁻¹ * x * g ∈ N)
    (hLL' : ∀ x : Γ, x ∈ L' ↔ g⁻¹ * x * g ∈ L)
    (rho : B →* L) (rho' : B →* L')
    (hrho : ∀ t : B, conjugationEquiv g hLL' (rho' t) = rho t)
    (π : SmoothRep.{0, u, v} ℂ Γ) (χ : B →* ℂˣ) :
    IsGeneralizedEigencharacter
        (((normalizedJacquetFunctor N L hN hLN).obj π).representation.comp rho) χ ↔
      IsGeneralizedEigencharacter
        (((normalizedJacquetFunctor N' L' hN' hLN').obj π).representation.comp rho') χ :=
  isGeneralizedEigencharacter_iff_of_equiv
    (normalizedJacquetRestrictedConjugationEquiv hN hLN hN' hLN'
      g hNN' hLL' rho rho' hrho π) χ

end GroupTransport

section ActualParabolics

open GroupScheme

variable {k : Type u} [Field k]
  {G H P M U : GroupScheme (Spec (CommRingCat.of k))}

/-- Membership in the actual point image of a conjugated subgroup map. -/
theorem mem_pointImage_comp_innerIso (j : H ⟶ G) (g x : rationalPoints G) :
    x ∈ pointImage (j ≫ (G.innerIso g).hom) ↔
      g⁻¹ * x * g ∈ pointImage j := by
  unfold pointImage
  rw [rationalPoints_range_comp_innerIso]
  simp only [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]

variable [TopologicalSpace k] [T2Space k] [IsAffineHom G.X.hom]

local instance conjugationAmbientPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)]
  [NonarchimedeanGroup (rationalPoints G)]
  (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
  (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
  (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
  (hmul : IsIso (subgroupMultiplication l r))
  {A : CommGroupScheme (Spec (CommRingCat.of k))} {a : A.toGrp ⟶ M}

/-- Conjugating the ambient parabolic inclusion preserves every actual
normalized Jacquet exponent. The specified Levi, radical, split component,
character and representation are retained. -/
theorem isNormalizedJacquetExponent_comp_innerIso_iff (ha : IsSplitComponent a)
    (g : rationalPoints G) (π : SmoothRep.{0, u, v} ℂ (rationalPoints G))
    (χ : rationalPoints A.toGrp →* ℂˣ) :
    IsNormalizedJacquetExponent (p ≫ (G.innerIso g).hom) l r
        (hp.comp_iso (G.innerIso g)) hl hr hmul ha π χ ↔
      IsNormalizedJacquetExponent p l r hp hl hr hmul ha π χ := by
  rw [isNormalizedJacquetExponent_iff, isNormalizedJacquetExponent_iff]
  symm
  have hN : ∀ x : rationalPoints G,
      x ∈ pointImage (r ≫ (p ≫ (G.innerIso g).hom)) ↔
        g⁻¹ * x * g ∈ pointImage (r ≫ p) := by
    intro x
    simpa only [Category.assoc] using mem_pointImage_comp_innerIso (r ≫ p) g x
  have hL : ∀ x : rationalPoints G,
      x ∈ pointImage (l ≫ (p ≫ (G.innerIso g).hom)) ↔
        g⁻¹ * x * g ∈ pointImage (l ≫ p) := by
    intro x
    simpa only [Category.assoc] using mem_pointImage_comp_innerIso (l ≫ p) g x
  apply normalizedGeneralizedEigencharacter_conj
    (isClosed_pointImage_comp p r hp.isClosedSubgroup hr.1.isClosedSubgroup)
    (pointImage_le_normalizer p l r hr)
    (isClosed_pointImage_comp (p ≫ (G.innerIso g).hom) r
      (hp.comp_iso (G.innerIso g)).isClosedSubgroup hr.1.isClosedSubgroup)
    (pointImage_le_normalizer (p ≫ (G.innerIso g).hom) l r hr)
    g hN hL _ _ _ π χ
  intro t
  apply Subtype.ext
  change g⁻¹ *
      rationalPoints.map (G.innerIso g).hom
        (rationalPoints.map (l ≫ p) (rationalPoints.map a t)) * g =
    rationalPoints.map (l ≫ p) (rationalPoints.map a t)
  rw [rationalPoints_map_innerIso]
  change g⁻¹ * (g * _ * g⁻¹) * g = _
  group

end ActualParabolics

end Langlands.Aubert.General.RepresentedParabolic
