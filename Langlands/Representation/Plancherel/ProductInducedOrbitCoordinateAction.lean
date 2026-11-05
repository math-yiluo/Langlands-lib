import Langlands.Representation.Plancherel.ProductInducedOrbitCoefficients
import Langlands.Representation.Plancherel.ProductInducedOrbitFormCoordinates

/-! # Coordinate comparisons for the full actual orbit representation -/

noncomputable section

set_option maxHeartbeats 800000
set_option maxRecDepth 4096

open CategoryTheory MeasureTheory
open scoped NNReal

namespace Langlands.Plancherel

open Aubert.General HarishChandraSchwartz
open HarmonicAnalysis.TorusFourier

universe uG uI uV uJ uJ' uL

variable {J : Type uJ} {J' : Type uJ'} [Fintype J] [Fintype J']
  {L : Type uL} [AddCommGroup L] [Module ℤ L]
  (b : Module.Basis J ℤ L) (c : Module.Basis J' ℤ L)

private theorem torusCharacter_basis_reconstruction (l : L) (z : J → Circle) :
    Circle.coeHom ((b.constr ℤ (fun j => Additive.ofMul (z j)) l).toMul) =
      torusCharacter (fun j => b.repr l j) z := by
  rw [Module.Basis.constr_apply_fintype]
  simp only [Module.Basis.equivFun_apply, toMul_sum, toMul_zsmul, map_prod]
  rfl

/-- Laurent exponents rebase by expressing the same lattice element in the
new integer basis. -/
theorem torusCharacter_comp_basisChange (n : J → ℤ) (z : J' → Circle) :
    torusCharacter n (finiteTorusBasisChange c b z) =
      torusCharacter
        (fun k => c.repr (b.repr.symm (Finsupp.equivFunOnFinite.symm n)) k) z := by
  let l := b.repr.symm (Finsupp.equivFunOnFinite.symm n)
  have hn : (fun j => b.repr l j) = n := by
    funext j
    simp [l]
  calc
    _ = Circle.coeHom
        ((b.constr ℤ (fun j => Additive.ofMul
          (finiteTorusBasisChange c b z j)) l).toMul) := by
      rw [torusCharacter_basis_reconstruction, hn]
    _ = Circle.coeHom ((c.constr ℤ (fun k => Additive.ofMul (z k)) l).toMul) := by
      rw [finiteTorusBasisChange_constr]
    _ = _ := torusCharacter_basis_reconstruction c l z

variable {H : Type uG} [Group H] [TopologicalSpace H]
  {I : Type uI} (νH : I → (H →* ℝ≥0ˣ))
  (eH : unitaryUnramifiedCharacters νH ≃* (J → Circle))

/-- The algebraic Laurent coordinate condition survives integer rebasing;
no new smoothness or continuity assumption is required. -/
theorem hasLaurentUnitaryCoordinates_rebase
    (he : HasLaurentUnitaryCoordinates νH eH) :
    HasLaurentUnitaryCoordinates νH
      (eH.trans (finiteTorusBasisChangeMulEquiv b c)) := by
  intro m
  obtain ⟨n, hn⟩ := he m
  refine ⟨fun k => c.repr (b.repr.symm (Finsupp.equivFunOnFinite.symm n)) k,
    fun z => ?_⟩
  change ((eH.symm (finiteTorusBasisChange c b z)).val m : ℂ) = _
  rw [hn]
  exact torusCharacter_comp_basisChange b c n z

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G] {P M U : Subgroup G}
  (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
  (ν : I → (M →* ℝ≥0ˣ))
  (π : IrreducibleAdmissibleRep.{0, uG, uV} (k := ℂ) (G := M))
  (K : OpenSubgroup G) (hP : IsClosed (P : Set G)) (hK : IsCompact (K : Set G))
  (hν : ∀ i, Continuous (ν i)) (hr : Continuous h.projection)
  (hPK : ∀ g : G, ∃ p : P, ∃ k : K, g = (p : G) * (k : G))
  (e : unitaryUnramifiedCharacters ν ≃* (J → Circle))

/-- The published identity on actual fibers intertwines the full product
actions, with the rebased Laurent premise proved from the original one. -/
theorem productInducedSmoothOrbitRebaseEquiv_action
    (he : HasLaurentUnitaryCoordinates ν e) (x : G × G)
    (q : productInducedSmoothOrbitSections ν π (rebaseUnitaryTorusCoordinates ν e b c)
      h hU K hP hK hν hr hPK) :
    productInducedSmoothOrbitRebaseEquiv ν π e b c h hU K hP hK hν hr hPK
        (productInducedSmoothOrbitRepresentation h hU ν π K hP hK hν hr hPK
          (rebaseUnitaryTorusCoordinates ν e b c)
          (hasLaurentUnitaryCoordinates_rebase b c ν e he) x q) =
      productInducedSmoothOrbitRepresentation h hU ν π K hP hK hν hr hPK e he x
        (productInducedSmoothOrbitRebaseEquiv ν π e b c h hU K hP hK hν hr hPK q) :=
  Subtype.ext rfl

/-- Coordinate rebasing as an equivalence of the actual full representations. -/
def productInducedSmoothOrbitRebaseRepresentationEquiv
    (he : HasLaurentUnitaryCoordinates ν e) :
    Representation.Equiv
      (productInducedSmoothOrbitRepresentation h hU ν π K hP hK hν hr hPK
        (rebaseUnitaryTorusCoordinates ν e b c)
        (hasLaurentUnitaryCoordinates_rebase b c ν e he))
      (productInducedSmoothOrbitRepresentation h hU ν π K hP hK hν hr hPK e he) :=
  Representation.Equiv.mk
    (productInducedSmoothOrbitRebaseEquiv ν π e b c h hU K hP hK hν hr hPK)
    (fun x => LinearMap.ext
      (productInducedSmoothOrbitRebaseEquiv_action b c h hU ν π K hP hK hν hr hPK e he x))

/-- The coordinate comparison in the canonical smooth representation category. -/
def productInducedSmoothOrbitRebaseIso
    (he : HasLaurentUnitaryCoordinates ν e) :
    productInducedSmoothOrbitObject h hU ν π K hP hK hν hr hPK
        (rebaseUnitaryTorusCoordinates ν e b c)
        (hasLaurentUnitaryCoordinates_rebase b c ν e he) ≅
      productInducedSmoothOrbitObject h hU ν π K hP hK hν hr hPK e he :=
  SmoothRep.mkIso
    (productInducedSmoothOrbitRebaseRepresentationEquiv
      b c h hU ν π K hP hK hν hr hPK e he)

@[simp]
theorem productInducedSmoothOrbitRebaseIso_hom_apply
    (he : HasLaurentUnitaryCoordinates ν e)
    (q : productInducedSmoothOrbitSections ν π (rebaseUnitaryTorusCoordinates ν e b c)
      h hU K hP hK hν hr hPK) :
    SmoothRep.hom
        (productInducedSmoothOrbitRebaseIso b c h hU ν π K hP hK hν hr hPK e he).hom q =
      productInducedSmoothOrbitRebaseEquiv ν π e b c h hU K hP hK hν hr hPK q := rfl

section Coefficients

variable [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  [LocallyCompactSpace P]
  (hG : ∀ g : G, Measure.modularCharacter g = 1)
  (hδ : ∀ p : P, Measure.modularCharacter p =
    (HaarModulus.closedRestrictCharacter U hU P h.le_normalizer p : ℝ≥0))
  (C : Subgroup M) [C.Normal] (hC : C ≤ Subgroup.center M)
  [MeasurableSpace (M ⧸ C)]
  (μ : Measure (M ⧸ C)) [μ.IsHaarMeasure]
  (hsq : IsSquareIntegrableModCentralSubgroup C hC π.obj.representation μ)

/-- Rebasing leaves the entire actual orbit coefficient function unchanged,
with the same compact Haar probability and inducing representative. -/
theorem unitaryOrbitCoefficientMap_rebase
    (q : productInducedSmoothOrbitSections ν π (rebaseUnitaryTorusCoordinates ν e b c)
      h hU K hP hK hν hr hPK) :
    unitaryOrbitCoefficientMap h hU hP K hK hPK hG hδ ν π hν hr C hC μ hsq e
        (productInducedSmoothOrbitRebaseEquiv ν π e b c h hU K hP hK hν hr hPK q) =
      unitaryOrbitCoefficientMap h hU hP K hK hPK hG hδ ν π hν hr C hC μ hsq
        (rebaseUnitaryTorusCoordinates ν e b c) q := rfl

end Coefficients

section OrbitForm

variable [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  [LocallyCompactSpace P]
  (hG : ∀ g : G, Measure.modularCharacter g = 1)
  (hδ : ∀ p : P, Measure.modularCharacter p =
    (HaarModulus.closedRestrictCharacter U hU P h.le_normalizer p : ℝ≥0))
  (hcof : CompactOpenCofinal M)
  (C : Subgroup M) [C.Normal] (hC : C ≤ Subgroup.center M)
  [MeasurableSpace (M ⧸ C)] [BorelSpace (M ⧸ C)]
  (μ : Measure (M ⧸ C)) [μ.IsHaarMeasure] [μ.IsInvInvariant]
  (hsq : IsSquareIntegrableModCentralSubgroup C hC π.obj.representation μ)
  [Finite (M ⧸ (commonNormKernel ν ⊔ C))]

/-- The categorical comparison preserves the whole original full invariant
form, through the already proved comparison of the entire orbit cores. -/
theorem productInducedSmoothOrbitRebaseForm_inner
    (hLaurent : HasLaurentUnitaryCoordinates ν e) (he : Continuous e)
    (η : Measure (unitaryUnramifiedCharacters ν))
    [IsFiniteMeasure η] [η.IsOpenPosMeasure]
    (q r : productInducedSmoothOrbitSections ν π (rebaseUnitaryTorusCoordinates ν e b c)
      h hU K hP hK hν hr hPK) :
    (productInducedSmoothOrbitForm
      h hU ν π K hP hK hν hr hPK e hG hδ hcof C hC μ hsq hLaurent he η).inner
        (productInducedSmoothOrbitRebaseEquiv ν π e b c h hU K hP hK hν hr hPK q)
        (productInducedSmoothOrbitRebaseEquiv ν π e b c h hU K hP hK hν hr hPK r) =
      (productInducedSmoothOrbitForm h hU ν π K hP hK hν hr hPK
        (rebaseUnitaryTorusCoordinates ν e b c) hG hδ hcof C hC μ hsq
        (hasLaurentUnitaryCoordinates_rebase b c ν e hLaurent)
        (continuous_rebaseUnitaryTorusCoordinates ν e b c he) η).inner q r :=
  productInducedSmoothOrbitRebaseEquiv_inner
    ν e b c h hU hP K hK hPK hG hδ π hcof C hC μ hsq hν hr he η q r

/-- The existing isometry for the actual orbit-integral norms also
intertwines the full product actions; its underlying map is unchanged. -/
theorem productInducedSmoothOrbitRebaseIsometry_action
    (hLaurent : HasLaurentUnitaryCoordinates ν e) (he : Continuous e)
    (η : Measure (unitaryUnramifiedCharacters ν))
    [IsFiniteMeasure η] [η.IsOpenPosMeasure] (x : G × G)
    (q : productInducedSmoothOrbitSections ν π (rebaseUnitaryTorusCoordinates ν e b c)
      h hU K hP hK hν hr hPK) :
    productInducedSmoothOrbitRebaseIsometry
        ν e b c h hU hP K hK hPK hG hδ π hcof C hC μ hsq hν hr he η
        (productInducedSmoothOrbitRepresentation h hU ν π K hP hK hν hr hPK
          (rebaseUnitaryTorusCoordinates ν e b c)
          (hasLaurentUnitaryCoordinates_rebase b c ν e hLaurent) x q) =
      productInducedSmoothOrbitRepresentation h hU ν π K hP hK hν hr hPK e hLaurent x
        (productInducedSmoothOrbitRebaseIsometry
          ν e b c h hU hP K hK hPK hG hδ π hcof C hC μ hsq hν hr he η q) :=
  productInducedSmoothOrbitRebaseEquiv_action b c h hU ν π K hP hK hν hr hPK e hLaurent x q

end OrbitForm

end Langlands.Plancherel
