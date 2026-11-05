import Langlands.Representation.Category.UniverseLift
import Langlands.Representation.Classification.Essential
import Langlands.Representation.Exponents.ScalarCentralExponents
import Langlands.Representation.Aubert.General.RationalSquareIntegrabilityStatement
import Langlands.Representation.Jacquet.LocalizationTransport

/-! # Arbitrary carrier universes in the strict Jacquet criterion -/

noncomputable section

universe u v w

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General

section Equivalence

variable {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [LocallyCompactSpace Γ]
  [NonarchimedeanGroup Γ]

/-- A representation equivalence, even between different carrier universes,
induces an equivalence of the actual normalized Jacquet representations. -/
def normalizedJacquetRepresentationEquiv
    (U M : Subgroup Γ) (hU : IsClosed (U : Set Γ))
    (hMU : M ≤ Subgroup.normalizer (U : Set Γ))
    (π : SmoothRep.{0, u, v} ℂ Γ) (σ : SmoothRep.{0, u, w} ℂ Γ)
    (e : π.representation.Equiv σ.representation) :
    ((normalizedJacquetFunctor U M hU hMU).obj π).representation.Equiv
      ((normalizedJacquetFunctor U M hU hMU).obj σ).representation :=
  Representation.Equiv.mk (Jacquet.Localization.representationEquiv U 1 e) (fun m => by
    ext x
    obtain ⟨v, rfl⟩ := Jacquet.Localization.mk_surjective π.representation U 1 x
    change (Jacquet.Localization.representationEquiv U 1 e)
      (((HaarModulus.closedInverseHalfCharacter U hU M hMU m : ℂˣ) : ℂ) •
        Jacquet.Localization.mk π.representation U 1 (π.representation m v)) =
      ((HaarModulus.closedInverseHalfCharacter U hU M hMU m : ℂˣ) : ℂ) •
        Jacquet.Localization.mk σ.representation U 1 (σ.representation m (e v))
    rw [map_smul, Jacquet.Localization.representationEquiv_mk]
    apply congrArg (fun w =>
      ((HaarModulus.closedInverseHalfCharacter U hU M hMU m : ℂˣ) : ℂ) •
        Jacquet.Localization.mk σ.representation U 1 w)
    exact Representation.IntertwiningMap.isIntertwining
      π.representation σ.representation e.toIntertwiningMap m v)

/-- The actual normalized Jacquet full-center exponent predicate is
invariant under cross-universe representation equivalences. -/
theorem isCentralExponent_normalizedJacquet_equiv_iff
    (U M : Subgroup Γ) (hU : IsClosed (U : Set Γ))
    (hMU : M ≤ Subgroup.normalizer (U : Set Γ))
    (π : SmoothRep.{0, u, v} ℂ Γ) (σ : SmoothRep.{0, u, w} ℂ Γ)
    (e : π.representation.Equiv σ.representation)
    (χ : Subgroup.center M →* ℂˣ) :
    IsCentralExponent ((normalizedJacquetFunctor U M hU hMU).obj π).representation χ ↔
      IsCentralExponent ((normalizedJacquetFunctor U M hU hMU).obj σ).representation χ :=
  isCentralExponent_equiv_iff (normalizedJacquetRepresentationEquiv U M hU hMU π σ e) χ

end Equivalence

namespace RationalPointFamily

open GroupScheme

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]
  (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]
  (hG : IsConnectedReductive G)

local instance carrierAmbientTopology : TopologicalSpace (rationalPoints G) := pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  [T2Space (rationalPoints G)]

/-- The published strict Jacquet sufficiency statement applies to smooth
representations in an arbitrary carrier universe, by lifting the carrier
and transporting both the Jacquet exponents and the coefficient conclusion. -/
theorem strictJacquetSquareIntegrability_arbitraryCarrier
    (hsq : RationalStrictJacquetSquareIntegrabilityStatement.{u, v})
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G)
    (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice T)
    (hν : IsGenericCocharacter i ν) (hStandard : StandardCocharacterStatement.{u})
    (hU : ∀ I : Finset (SimpleRoot i ν),
      IsClosed (unipotent i ν I : Set (rationalPoints G)))
    (π : SmoothRep.{0, u, v} ℂ (rationalPoints G))
    (hπ : π.IsAdmissible) (hc : Nonempty (UnitaryCentralCharacter π.representation))
    (hstrict : ∀ (I : Finset (SimpleRoot i ν))
      (χ : Subgroup.center (levi i ν I) →* ℂˣ),
      IsCentralExponent ((jacquetFunctor
        (isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν I)
        (hU I)).obj π).representation χ →
      ∀ (t : rationalPoints T.toGrp) (z : Subgroup.center (levi i ν I)),
        ((z : levi i ν I) : rationalPoints G) = rationalPoints.map i t →
        IsNoncentralNegativeTorusPoint i ν t → ‖(χ z : ℂ)‖ < 1)
    [MeasurableSpace (rationalPoints G ⧸ Subgroup.center (rationalPoints G))]
    [BorelSpace (rationalPoints G ⧸ Subgroup.center (rationalPoints G))]
    (haar : MeasureTheory.Measure (rationalPoints G ⧸ Subgroup.center (rationalPoints G)))
    [haar.IsHaarMeasure] :
    IsSquareIntegrableModCenter π.representation haar := by
  let σ : SmoothRep.{0, u, max (u + 1) v} ℂ (rationalPoints G) :=
    SmoothRep.universeLift.{u + 1} π
  let e := SmoothRep.universeLiftEquiv.{u + 1} π
  have hσ : σ.IsAdmissible := (SmoothRep.isAdmissible_universeLift_iff π).mpr hπ
  obtain ⟨c⟩ := hc
  have hcσ : Nonempty (UnitaryCentralCharacter σ.representation) := ⟨c.ofEquiv e⟩
  have hsσ : HasStrictNormalizedJacquetExponents i ν
      (isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν)
      hU σ := by
    intro I χ hχ t z hz ht
    apply hstrict I χ ?_ t z hz ht
    exact (isCentralExponent_normalizedJacquet_equiv_iff _ _ (hU I)
      (isSemidirectDecomposition_of_standardCocharacterStatement
        i ν hStandard hG hi hν I).levi_le_normalizer π σ e χ).mpr hχ
  have hL2 := hsq k G hG T i hi ν hν hStandard hU σ hσ hcσ hsσ haar
  exact isSquareIntegrableModCenter_of_equiv e.symm haar hL2

end RationalPointFamily

end Langlands.Aubert.General
