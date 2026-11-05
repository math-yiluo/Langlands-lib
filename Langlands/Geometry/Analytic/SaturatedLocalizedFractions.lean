import Langlands.Geometry.Analytic.SaturatedQuasiIsoRightFractions
import Langlands.Geometry.Analytic.SaturatedStrongLocalization

/-! # Actual fraction representatives in the saturated atlas localization -/

noncomputable section

universe u v w

namespace Langlands.Analytic.SaturatedAtlasPresentation

open CategoryTheory

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : SaturatedAtlasPresentation.{u, v, w} K}

/-- Interpret an actual source, full quasi-isomorphism denominator and bounded
numerator in the constructed localization. -/
def localizedRightFraction
    (φ : (quasiIsomorphisms (K := K)).RightFraction A B) :
    localizationFunctor.obj A ⟶ localizationFunctor.obj B :=
  (localizedQuasiIso φ.s φ.hs).inv ≫ localizationFunctor.map φ.f

/-- This interpretation is the standard right-fraction map for this localization. -/
theorem localizedRightFraction_eq_map
    (φ : (quasiIsomorphisms (K := K)).RightFraction A B) :
    localizedRightFraction φ =
      φ.map localizationFunctor (Localization.inverts _ (quasiIsomorphisms (K := K))) := rfl

/-- Every arrow between the original objects is represented by an actual
saturated source, a full quasi-isomorphism denominator and a strong numerator. -/
theorem exists_localizedRightFraction
    (f : localizationFunctor.obj A ⟶ localizationFunctor.obj B) :
    ∃ φ : (quasiIsomorphisms (K := K)).RightFraction A B,
      f = localizedRightFraction φ :=
  Localization.exists_rightFraction localizationFunctor (quasiIsomorphisms (K := K)) f

/-- Choose an actual right fraction representing a given localized arrow. -/
def rightFractionRepresentative
    (f : localizationFunctor.obj A ⟶ localizationFunctor.obj B) :
    (quasiIsomorphisms (K := K)).RightFraction A B :=
  Classical.choose (exists_localizedRightFraction f)

@[simp]
theorem localizedRightFraction_representative
    (f : localizationFunctor.obj A ⟶ localizationFunctor.obj B) :
    localizedRightFraction (rightFractionRepresentative f) = f :=
  (Classical.choose_spec (exists_localizedRightFraction f)).symm

/-- A common refinement compares complete strong maps and requires that the
common denominator, rather than each comparison arrow separately, is quasi-isomorphic. -/
def FractionCommonRefinement
    (φ ψ : (quasiIsomorphisms (K := K)).RightFraction A B) : Prop :=
  ∃ (S : SaturatedAtlasPresentation.{u, v, w} K) (a : S ⟶ φ.X') (b : S ⟶ ψ.X'),
    ∃ (_ : a ≫ φ.s = b ≫ ψ.s) (_ : a ≫ φ.f = b ≫ ψ.f), (a ≫ φ.s).IsQuasiIso

/-- Equality in the localization is exactly common-refinement equality of
all bounded pullbacks, not merely equality of underlying continuous maps. -/
theorem localizedRightFraction_eq_iff
    (φ ψ : (quasiIsomorphisms (K := K)).RightFraction A B) :
    localizedRightFraction φ = localizedRightFraction ψ ↔ FractionCommonRefinement φ ψ := by
  exact MorphismProperty.RightFraction.map_eq_iff localizationFunctor
    (quasiIsomorphisms (K := K)) φ ψ

/-- The proved right calculus makes common refinement an equivalence relation. -/
def rightFractionSetoid (A B : SaturatedAtlasPresentation.{u, v, w} K) :
    Setoid ((quasiIsomorphisms (K := K)).RightFraction A B) where
  r := FractionCommonRefinement
  iseqv := MorphismProperty.equivalenceRightFractionRel A B

/-- Descend actual fraction interpretation to its common-refinement quotient. -/
def rightFractionQuotientMap : Quotient (rightFractionSetoid A B) →
    (localizationFunctor.obj A ⟶ localizationFunctor.obj B) :=
  Quotient.lift localizedRightFraction fun φ ψ h => (localizedRightFraction_eq_iff φ ψ).2 h

theorem rightFractionQuotientMap_bijective :
    Function.Bijective (rightFractionQuotientMap (A := A) (B := B)) := by
  constructor
  · intro x y
    refine Quotient.inductionOn₂ x y ?_
    intro φ ψ h
    exact Quotient.sound ((localizedRightFraction_eq_iff φ ψ).1 h)
  · intro f
    obtain ⟨φ, hφ⟩ := exists_localizedRightFraction f
    exact ⟨Quotient.mk _ φ, hφ.symm⟩

/-- The actual common-refinement quotient computes the hom set of the
previously constructed path-and-relations localization. -/
def rightFractionHomEquiv : Quotient (rightFractionSetoid A B) ≃
    (localizationFunctor.obj A ⟶ localizationFunctor.obj B) :=
  Equiv.ofBijective rightFractionQuotientMap rightFractionQuotientMap_bijective

@[simp]
theorem rightFractionHomEquiv_mk
    (φ : (quasiIsomorphisms (K := K)).RightFraction A B) :
    rightFractionHomEquiv (Quotient.mk _ φ) = localizedRightFraction φ := rfl

/-- For original arrows, localization equality means equality after an actual
full quasi-isomorphism source refinement. -/
theorem localizationFunctor_map_eq_iff (f g : A ⟶ B) :
    localizationFunctor.map f = localizationFunctor.map g ↔
      ∃ (S : SaturatedAtlasPresentation.{u, v, w} K) (s : S ⟶ A)
        (_ : s.IsQuasiIso), s ≫ f = s ≫ g :=
  MorphismProperty.map_eq_iff_precomp localizationFunctor (quasiIsomorphisms (K := K)) f g

/-- A fraction acts on the original spaces by the inverse denominator
homeomorphism followed by its actual numerator continuous map. -/
theorem localizedSpaceFunctor_map_rightFraction
    (φ : (quasiIsomorphisms (K := K)).RightFraction A B) :
    localizedSpaceFunctor.map (localizedRightFraction φ) =
      TopCat.ofHom (φ.f.baseMap.comp φ.hs.inverseBaseMap) := by
  exact (Functor.map_comp localizedSpaceFunctor _ _).trans
    (congrArg₂ (fun (a : A.presentation.space ⟶ φ.X'.presentation.space)
      (b : φ.X'.presentation.space ⟶ B.presentation.space) => a ≫ b)
        (localizedSpaceFunctor_map_quasiIso_inv φ.s φ.hs)
        (localizedSpaceFunctor_map φ.f))

/-- The chosen representative computes the underlying map of every localized arrow. -/
theorem localizedSpaceFunctor_map_representative
    (f : localizationFunctor.obj A ⟶ localizationFunctor.obj B) :
    localizedSpaceFunctor.map f =
      TopCat.ofHom ((rightFractionRepresentative f).f.baseMap.comp
        (rightFractionRepresentative f).hs.inverseBaseMap) := by
  rw [← localizedSpaceFunctor_map_rightFraction, localizedRightFraction_representative]

end Langlands.Analytic.SaturatedAtlasPresentation
