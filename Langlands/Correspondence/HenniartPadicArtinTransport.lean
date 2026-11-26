import Langlands.Correspondence.HenniartNumericalStatement

/-!
# Transport of p-adic Artin conductor witnesses

On a fixed finite Galois subextension, the two spectral constructions give
the same valuation ring and restrict Weil inertia by the same field action.
Hence Henniart's Artin relation `Numerical.HasArtinConductor`, defined with the
general presentations, is computed by the p-adic presentations.
-/

noncomputable section

namespace Langlands.Henniart

universe uK uW

open Ramification.Local

private theorem spectralNorm_le_one_iff_coeff_zero
    {K L : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    [Field L] [Algebra K L] [Algebra.IsAlgebraic K L] (x : L) :
    spectralNorm K L x ≤ 1 ↔ ‖(minpoly K x).coeff 0‖ ≤ 1 := by
  rw [spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow]
  let e : ℝ := 1 / (minpoly K x).natDegree
  have hd : 0 < (minpoly K x).natDegree :=
    minpoly.natDegree_pos (Algebra.IsIntegral.isIntegral x)
  have he : 0 < e := by dsimp [e]; positivity
  have h := Real.rpow_le_rpow_iff (norm_nonneg ((minpoly K x).coeff 0))
    zero_le_one he
  rwa [Real.one_rpow] at h

section Quotient

variable {K₀ K₁ K L : Type*} [Field K₀] [ValuativeRel K₀] [TopologicalSpace K₀]
    [Field K₁] [ValuativeRel K₁] [TopologicalSpace K₁]
    [Field K] [Algebra K₀ K] [Algebra K₁ K]
    [Field L] [Algebra K₀ L] [Algebra K₁ L] [Algebra K L]
    [IsScalarTower K₀ K L] [IsScalarTower K₁ K L]
    [FiniteDimensional K₀ L] [FiniteDimensional K₁ L]
    {J V : Type*} [Group J] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

private abbrev hasQuotientArtin (T : LocalField.TopologicalData K₀ L)
    (π : J →* inertia T K) (ρ : Representation ℂ J V) (a : ℚ) : Prop :=
  ∃ (hs : Function.Surjective π) (hc : π.ker ≤ ρ.ker),
    artinConductorOfQuotient T K π hs ρ hc = a

private theorem quotientArtin_exists_iff_of_same_valuation
    (T₀ : LocalField.TopologicalData K₀ L) (T₁ : LocalField.TopologicalData K₁ L)
    (hT : T₀.valuativeRel = T₁.valuativeRel)
    (π₀ : J →* inertia T₀ K) (π₁ : J →* inertia T₁ K)
    (hπ : ∀ j, (π₀ j : Gal(L/K)) = (π₁ j : Gal(L/K)))
    (ρ : Representation ℂ J V) (a : ℚ) :
    hasQuotientArtin T₀ π₀ ρ a ↔ hasQuotientArtin T₁ π₁ ρ a := by
  rcases T₀ with @⟨top₀, val₀, ext₀, mod₀, loc₀⟩
  rcases T₁ with @⟨top₁, val₁, ext₁, mod₁, loc₁⟩
  change val₀ = val₁ at hT
  subst val₁
  have h : π₀ = π₁ := MonoidHom.ext fun j => Subtype.ext (hπ j)
  subst π₁
  rfl

end Quotient

private theorem exists_presentation_at_iff
    {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]
    {c s : FiniteGaloisIntermediateField K Ω → Prop}
    (q : ∀ L, c L → s L → Prop) (L : FiniteGaloisIntermediateField K Ω) :
    (∃ (P : FiniteInertiaPresentationData c) (hs : s P.extension),
      P.extension = L ∧ q P.extension P.kernel_le hs) ↔
    (∃ (hs : s L) (hc : c L), q L hc hs) := by
  constructor
  · rintro ⟨⟨M, hc⟩, hs, h, hq⟩
    cases h
    exact ⟨hs, hc, hq⟩
  · rintro ⟨hs, hc, hq⟩
    exact ⟨⟨L, hc⟩, hs, rfl, hq⟩

namespace PadicArtinTransport

open Ramification.Padic Weil.Local
variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uK} p)

local instance : CharZero F.Carrier := Algebra.charZero_of_charZero (Padic p) F.Carrier
local instance : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance : IsNonarchimedeanLocalField F.Carrier := F.canonicalTopologicalData.localField

variable (L : FiniteGaloisIntermediateField F.Carrier (AlgebraicClosure F.Carrier))

local instance : FiniteDimensional (Padic p) L :=
  FiniteDimensional.trans (Padic p) F.Carrier L

private theorem spectralValuation_isEquiv :
    letI := LocalGalois.localNormedField F.Carrier
    letI := LocalGalois.localNormedField_ultrametric F.Carrier
    letI := LocalGalois.localNormedField_complete F.Carrier
    (LocalField.canonicalValuation (Padic p) L).IsEquiv
      (LocalField.canonicalValuation F.Carrier L) := by
  let := LocalGalois.localNormedField F.Carrier
  let := LocalGalois.localNormedField_ultrametric F.Carrier
  let := LocalGalois.localNormedField_complete F.Carrier
  apply Valuation.isEquiv_of_val_le_one
  intro x
  change spectralNorm (Padic p) L x ≤ 1 ↔ spectralNorm F.Carrier L x ≤ 1
  rw [spectralNorm_le_one_iff_coeff_zero (K := F.Carrier)]
  let c := (minpoly F.Carrier x).coeff 0
  change spectralNorm (Padic p) L x ≤ 1 ↔ ‖c‖ ≤ 1
  have hc : ‖c‖ ≤ 1 ↔ spectralNorm (Padic p) F.Carrier c ≤ 1 := by
    have h := (LocalGalois.localNormedField_le F.Carrier c 1).trans
      (Valuation.Compatible.vle_iff_le (v := ValuativeRel.valuation F.Carrier) c 1).symm
    rw [norm_one] at h
    change ‖c‖ ≤ 1 ↔
      spectralNorm (Padic p) F.Carrier c ≤ spectralNorm (Padic p) F.Carrier 1 at h
    simpa only [spectralNorm_one] using h
  rw [hc]
  let := F.canonicalNormedField
  let : IsUltrametricDist F.Carrier :=
    IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm
      (isNonarchimedean_spectralNorm (K := Padic p) (L := F.Carrier))
  let : CompleteSpace F.Carrier := spectralNorm.completeSpace (Padic p) F.Carrier
  have ht := spectralNorm_unique_field_norm_ext
    (f := MulRingNorm.toAbsoluteValue (spectralMulAlgNorm (Padic p) L).toMulRingNorm)
    (fun y : F.Carrier => (spectralNorm.eq_of_tower (K := Padic p) (L := L) y).symm) x
  change spectralNorm (Padic p) L x = spectralNorm F.Carrier L x at ht
  rw [ht]
  exact spectralNorm_le_one_iff_coeff_zero (K := F.Carrier) x

private theorem finiteValuativeRel_eq :
    (absoluteFiniteExtension F L).canonicalTopologicalData.toLocalData.valuativeRel =
      (Ramification.Local.SepClosed.finiteTopologicalData
        F.Carrier (AlgebraicClosure F.Carrier) L).valuativeRel := by
  ext x y
  exact spectralValuation_isEquiv F L x y

private theorem finiteRestriction_agree (w : localInertia F) :
    (Ramification.Padic.weilInertiaRestriction F L w : Gal(L/F.Carrier)) =
      (Ramification.Local.SepClosed.weilInertiaRestriction F.Carrier
        (AlgebraicClosure F.Carrier) L w : Gal(L/F.Carrier)) := by
  rw [Ramification.Padic.weilInertiaRestriction_coe]
  rfl

variable (A : FiniteRepresentation.{0, uK, uW} ℂ (localWeilGroup F))

private abbrev hasPadicQuotientArtin (a : ℚ) : Prop :=
  hasQuotientArtin (absoluteFiniteExtension F L).canonicalTopologicalData.toLocalData
    (Ramification.Padic.weilInertiaRestriction F L).toMonoidHom
    (Ramification.Padic.localInertiaRepresentation F A) a

private abbrev hasLocalQuotientArtin (a : ℚ) : Prop :=
  hasQuotientArtin
    (Ramification.Local.SepClosed.finiteTopologicalData
      F.Carrier (AlgebraicClosure F.Carrier) L)
    (Ramification.Local.SepClosed.weilInertiaRestriction F.Carrier
      (AlgebraicClosure F.Carrier) L).toMonoidHom
    (Ramification.Padic.localInertiaRepresentation F A) a

private theorem exists_padic_presentation_at_iff (a : ℚ) :
    (∃ (P : Ramification.Padic.FiniteInertiaPresentation F A)
      (hP : Function.Surjective (Ramification.Padic.weilInertiaRestriction F P.extension)),
      P.extension = L ∧ P.artinConductor hP = a) ↔ hasPadicQuotientArtin F L A a :=
  exists_presentation_at_iff (fun M hc hs =>
    artinConductorOfQuotient
      (absoluteFiniteExtension F M).canonicalTopologicalData.toLocalData F.Carrier
      (Ramification.Padic.weilInertiaRestriction F M).toMonoidHom hs
      (Ramification.Padic.localInertiaRepresentation F A) hc = a) L

private theorem exists_local_presentation_at_iff (a : ℚ) :
    (∃ (P : Ramification.Local.SepClosed.FiniteInertiaPresentation
      F.Carrier (AlgebraicClosure F.Carrier) A)
      (hP : Function.Surjective (Ramification.Local.SepClosed.weilInertiaRestriction
        F.Carrier (AlgebraicClosure F.Carrier) P.extension)),
      P.extension = L ∧ P.artinConductor hP = a) ↔ hasLocalQuotientArtin F L A a :=
  exists_presentation_at_iff (fun M hc hs =>
    artinConductorOfQuotient
      (Ramification.Local.SepClosed.finiteTopologicalData
        F.Carrier (AlgebraicClosure F.Carrier) M) F.Carrier
      (Ramification.Local.SepClosed.weilInertiaRestriction F.Carrier
        (AlgebraicClosure F.Carrier) M).toMonoidHom hs
      (Ramification.Padic.localInertiaRepresentation F A) hc = a) L

private theorem quotientArtin_exists_iff (a : ℚ) :
    hasPadicQuotientArtin F L A a ↔ hasLocalQuotientArtin F L A a :=
  quotientArtin_exists_iff_of_same_valuation
    (K := F.Carrier) (absoluteFiniteExtension F L).canonicalTopologicalData.toLocalData
    (Ramification.Local.SepClosed.finiteTopologicalData F.Carrier
      (AlgebraicClosure F.Carrier) L)
    (finiteValuativeRel_eq F L)
    (Ramification.Padic.weilInertiaRestriction F L).toMonoidHom
    (Ramification.Local.SepClosed.weilInertiaRestriction F.Carrier
      (AlgebraicClosure F.Carrier) L).toMonoidHom
    (finiteRestriction_agree F L) (Ramification.Padic.localInertiaRepresentation F A) a

/-- The p-adic and general presentations compute the same Artin conductor
on the same actual finite Galois subextension. -/
theorem existsArtinPresentationAt_iff (a : ℚ) :
    (∃ (P : Ramification.Padic.FiniteInertiaPresentation F A)
      (hP : Function.Surjective (Ramification.Padic.weilInertiaRestriction F P.extension)),
      P.extension = L ∧ P.artinConductor hP = a) ↔
    (∃ (P : Ramification.Local.SepClosed.FiniteInertiaPresentation
      F.Carrier (AlgebraicClosure F.Carrier) A)
      (hP : Function.Surjective (Ramification.Local.SepClosed.weilInertiaRestriction
        F.Carrier (AlgebraicClosure F.Carrier) P.extension)),
      P.extension = L ∧ P.artinConductor hP = a) :=
  (exists_padic_presentation_at_iff F L A a).trans
    ((quotientArtin_exists_iff F L A a).trans (exists_local_presentation_at_iff F L A a).symm)

end PadicArtinTransport

namespace Numerical

open Correspondence

variable {p : ℕ} [Fact p.Prime] (K : PadicField.{uK} p)

/-- `HasArtinConductor K σ a` holds exactly when some representative of `σ` has a
p-adic finite inertia presentation, with surjective inertia restriction, whose Artin
expression is `a`. -/
theorem hasArtinConductor_iff_exists_padicPresentation {k : ℕ}
    (σ : IrreducibleWeilClass.{uK, uW} K k.succPNat) (a : ℕ) :
    HasArtinConductor K σ a ↔
      ∃ (A : FiniteRepresentation.{0, uK, uW} ℂ (Weil.Local.localWeilGroup K))
        (P : Ramification.Padic.FiniteInertiaPresentation K A)
        (hsurj : Function.Surjective
          (Ramification.Padic.weilInertiaRestriction K P.extension)),
        FiniteRepresentation.classOf A = weilClassForget K σ ∧
          P.artinConductor hsurj = (a : ℚ) := by
  constructor
  · rintro ⟨A, P, hP, hA, ha⟩
    obtain ⟨Q, hQ, -, hq⟩ :=
      (PadicArtinTransport.existsArtinPresentationAt_iff K P.extension A a).mpr
        ⟨P, hP, rfl, ha⟩
    exact ⟨A, Q, hQ, hA, hq⟩
  · rintro ⟨A, P, hP, hA, ha⟩
    obtain ⟨Q, hQ, -, hq⟩ :=
      (PadicArtinTransport.existsArtinPresentationAt_iff K P.extension A a).mp
        ⟨P, hP, rfl, ha⟩
    exact ⟨A, Q, hQ, hA, hq⟩

end Numerical
end Langlands.Henniart
