import Langlands.GroupScheme.Rational.SplitTorusCharacterBoundedness
import Langlands.Representation.Plancherel.TorusNormKernelCompactnessProof
import Langlands.Galois.Local.SpectralDefinitions

/-! # Torus norm kernels in algebraic extensions of complete valued fields -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.LocalGalois

variable {F K E : Type u} [NontriviallyNormedField F] [IsUltrametricDist F]
  [CompleteSpace F] [Field K] [Field E] [Algebra F K] [Algebra F E] [Algebra K E]
  [IsScalarTower F K E] [Algebra.IsAlgebraic F K] [Algebra.IsAlgebraic F E]
  [FiniteDimensional K E] [IsGalois K E]

/-- The spectral valuation in an algebraic tower turns the relative Galois norm
into the corresponding power, even when the intermediate field is not complete. -/
theorem spectralValuation_pow_card_relativeNorm (x : E) :
    spectralValuation F E x ^ Fintype.card (E ≃ₐ[K] E) =
      spectralValuation F K (Algebra.norm K x) := by
  classical
  apply NNReal.eq
  change spectralNorm F E x ^ Fintype.card (E ≃ₐ[K] E) =
    spectralNorm F K (Algebra.norm K x)
  calc
    spectralNorm F E x ^ Fintype.card (E ≃ₐ[K] E) =
        ∏ σ : E ≃ₐ[K] E, spectralMulAlgNorm F E (σ x) := by
      have hσ (σ : E ≃ₐ[K] E) : spectralNorm F E (σ x) = spectralNorm F E x :=
        (spectralNorm_eq_of_equiv (σ.restrictScalars F) x).symm
      simp only [spectralMulAlgNorm_def, hσ, Finset.prod_const, Finset.card_univ]
    _ = spectralMulAlgNorm F E (∏ σ : E ≃ₐ[K] E, σ x) := (map_prod _ _ _).symm
    _ = spectralNorm F K (Algebra.norm K x) := by
      rw [← Algebra.norm_eq_prod_automorphisms, spectralMulAlgNorm_def,
        ← spectralNorm.eq_of_tower]

/-- A relative norm with spectral valuation one already has spectral-unit input. -/
theorem spectralValuation_eq_one_of_relativeNorm {x : E}
    (hx : spectralValuation F K (Algebra.norm K x) = 1) :
    spectralValuation F E x = 1 := by
  apply (pow_eq_one_iff_of_nonneg (show 0 ≤ spectralValuation F E x from zero_le)
    (Fintype.card_ne_zero (α := E ≃ₐ[K] E))).mp
  rw [spectralValuation_pow_card_relativeNorm, hx]

end Langlands.LocalGalois

namespace Langlands.GroupScheme

open Langlands.LocalGalois
open Langlands.Plancherel.TorusNormKernel

variable (F K : Type u) [NontriviallyNormedField F] [IsUltrametricDist F]
  [CompleteSpace F] [Field K] [Algebra F K] [Algebra.IsAlgebraic F K]

/-- Rational points on which every actual rational character is a spectral unit. -/
def spectralCharacterUnitLocus (T : GroupScheme (Spec (CommRingCat.of K))) :
    Set (rationalPoints T) :=
  {p | ∀ χ : rationalCharacters T,
    spectralValuation F K (rationalCharacterEval χ p : K) = 1}

variable {F K}

/-- Every geometric character over a finite Galois extension is a spectral unit
on the common rational-character unit locus. -/
theorem spectralCharacterUnitLocus_characterEval_eq_one
    (E : Type u) [Field E] [Algebra F E] [Algebra K E] [IsScalarTower F K E]
    [Algebra.IsAlgebraic F E] [FiniteDimensional K E] [IsGalois K E]
    (T : GroupScheme (Spec (CommRingCat.of K))) [IsAffine T.X.left]
    (p : rationalPoints T) (hp : p ∈ spectralCharacterUnitLocus F K T)
    (χ : rationalCharacters (GaloisPointComparison.baseChanged K E T)) :
    spectralValuation F E (rationalCharacterEval χ
      (GaloisPointComparison.rationalExtend K E T p) : E) = 1 := by
  apply spectralValuation_eq_one_of_relativeNorm (K := K)
  rw [← normCharacter_eval]
  exact hp (normCharacter χ)

/-- The common spectral-unit locus of an actual torus is algebraically bounded.
Only the original field `F` is assumed complete. -/
theorem isAlgebraicallyBounded_spectralCharacterUnitLocus
    (T : GroupScheme (Spec (CommRingCat.of K))) [IsAffine T.X.left]
    (hT : IsTorus T) :
    letI : ValuativeRel K := ValuativeRel.ofValuation (spectralValuation F K)
    IsAlgebraicallyBounded K T.X (spectralCharacterUnitLocus F K T) := by
  classical
  let : ValuativeRel K := ValuativeRel.ofValuation (spectralValuation F K)
  obtain ⟨E, _, _, _, _, hsplit⟩ := torusFiniteGaloisSplitting K T hT
  let : Algebra F E := ((algebraMap K E).comp (algebraMap F K)).toAlgebra
  let : IsScalarTower F K E := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra.IsAlgebraic F E := Algebra.IsAlgebraic.trans F K E
  let : ValuativeRel E := ValuativeRel.ofValuation (spectralValuation F E)
  have : (spectralValuation F E).Compatible := Valuation.Compatible.ofValuation _
  obtain ⟨I, _, ⟨e⟩⟩ := hsplit
  let := Fintype.ofFinite I
  let TE := GaloisPointComparison.baseChanged K E T
  let : IsAffine TE.X.left := by
    change IsAffine (Limits.pullback T.X.hom (GaloisPointComparison.baseMap K E))
    infer_instance
  let : IsAffineHom (splitTorus (Spec (CommRingCat.of E)) I).X.hom :=
    isAffineHom_splitTorus _ _
  let : IsAffine (splitTorus (Spec (CommRingCat.of E)) I).X.left :=
    isAffine_of_isAffineHom (splitTorus (Spec (CommRingCat.of E)) I).X.hom
  let B : Set (rationalPoints TE) :=
    GaloisPointComparison.rationalExtend K E T '' spectralCharacterUnitLocus F K T
  have hB : IsAlgebraicallyBounded E TE.X B := by
    have : IsIso e.hom.hom.hom.left :=
      inferInstanceAs (IsIso ((Over.forget _).map ((Grp.forget _).map e.hom)))
    apply isAlgebraicallyBounded_of_closedImmersion E e.hom.hom.hom B
    apply splitTorus.isAlgebraicallyBounded_of_unitCoordinates
    rintro _ ⟨s, ⟨p, hp, rfl⟩, rfl⟩ i
    have hunit := spectralCharacterUnitLocus_characterEval_eq_one E T p hp
      (splitCharacter e i)
    apply (ValuativeRel.isEquiv (spectralValuation F E)
      (ValuativeRel.valuation E)).eq_one_iff_eq_one.mp
    convert hunit using 1
    change spectralValuation F E
      (Gm.affinePointsEquiv (𝟙 _) ((GaloisPointComparison.rationalExtend K E T p ≫
        e.hom.hom.hom) ≫
          (Limits.Pi.π (fun _ : I => (Gm (Spec (CommRingCat.of E))).toGrp) i).hom.hom) : E) = _
    rw [Category.assoc]
    rfl
  intro f
  obtain ⟨c, _, hc⟩ := hB
    ((Limits.pullback.fst T.X.hom (GaloisPointComparison.baseMap K E)).appTop.hom f)
  obtain ⟨b, hb⟩ := NormedField.exists_lt_norm F (spectralNorm F E c)
  have hb0 : b ≠ 0 := by
    intro h
    rw [h, norm_zero] at hb
    exact (not_lt_of_ge (spectralNorm_nonneg c)) hb
  refine ⟨algebraMap F K b, (map_ne_zero (algebraMap F K)).mpr hb0, fun p hp => ?_⟩
  have h := hc _ ⟨p, hp, rfl⟩
  rw [rationalPointAlgebraHom_rationalExtend] at h
  change spectralValuation F E (algebraMap K E (rationalPointAlgebraHom K T.X p f)) ≤
    spectralValuation F E c at h
  change spectralValuation F K (rationalPointAlgebraHom K T.X p f) ≤
    spectralValuation F K (algebraMap F K b)
  apply NNReal.coe_le_coe.mp
  change spectralNorm F K (rationalPointAlgebraHom K T.X p f) ≤
    spectralNorm F K (algebraMap F K b)
  rw [spectralNorm_extends]
  have h' := NNReal.coe_le_coe.mpr h
  change spectralNorm F E (algebraMap K E (rationalPointAlgebraHom K T.X p f)) ≤
    spectralNorm F E c at h'
  rw [← spectralNorm.eq_of_tower] at h'
  exact h'.trans hb.le

end Langlands.GroupScheme
