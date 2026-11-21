import Langlands.Geometry.FormalGroup.CentralOrderSectionGluing
import Langlands.Geometry.FormalGroup.ScalarRamificationHeight

/-! # Order-linear local quasi-isogenies over the central field -/

noncomputable section

universe u v w c

namespace Langlands.FormalGroup.ModuleLaw

open CategoryTheory Opposite TopologicalSpace RationalSection

attribute [local instance] coefficientAlgebra coefficientScalarTower

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {D : Type w} [Ring D] [Algebra O D]
variable {C : Type c} [CommRing C] [Algebra C D] [Algebra C R]
variable {F K : Type v} [Field F] [Algebra O F] [Field K] [Algebra C K]
variable {σ τ : Type} [Finite σ] [Finite τ]
variable {M : ModuleLaw O R σ} {N : ModuleLaw O R τ}
variable {E : OrderAction D M} {G : OrderAction D N}
variable {hs : ∀ (a : C) (x : σ → R),
  E.fiberTangent (RingHom.id R) (algebraMap C D a) x = algebraMap C R a • x}
variable {ht : ∀ (a : C) (x : τ → R),
  G.fiberTangent (RingHom.id R) (algebraMap C D a) x = algebraMap C R a • x}
variable {U : Opens (PrimeSpectrum R)} {p : ℕ} {π : C} {e : ℕ} {a : Cˣ}

namespace RationalSection.OrderScalarPresentation

variable {z : RationalSection F M N U}
variable (P : OrderScalarPresentation p E G z)

/-- A central numerator section is linear for the actual division order. -/
theorem centralSection_orderLinear :
    IsOrderLinear (E.centralOrder hs) (G.centralOrder ht) (P.centralSection (K := K)) := by
  intro b
  rw [centralSection, smul_comp, comp_smul]
  apply congrArg (((p : K) ^ P.exponent)⁻¹ • ·)
  let A := (coefficientStructurePresheaf R).obj (op U)
  let f := P.centralNumerator (hs := hs) (ht := ht)
  change RationalSection.comp (ofIntegral U f.val)
      (ofIntegral U (((E.centralOrder hs).overAlgebra A).action b)) =
    RationalSection.comp (ofIntegral U (((G.centralOrder ht).overAlgebra A).action b)) (ofIntegral U f.val)
  rw [comp_ofIntegral, comp_ofIntegral, f.commutes]

/-- A unit multiple of a central uniformizer power clears the original denominator. -/
theorem centralSection_isLocallyScalarIsogeny (hp : (p : K) ≠ 0)
    (hcal : (p : C) = (↑a : C) * π ^ e) :
    IsLocallyScalarIsogeny π (P.centralSection (K := K) (hs := hs) (ht := ht)) := by
  let A := (coefficientStructurePresheaf R).obj (op U)
  let f := P.centralNumerator (hs := hs) (ht := ht)
  let n := P.exponent
  let b : Cˣ := (a ^ n)⁻¹
  have hf : f.val.IsIsogeny :=
    P.numerator.centralScalarsOverAlgebra_isIsogeny (hs := hs) (ht := ht) A P.isIsogeny
  let hIso := ((G.centralModule ht).overAlgebra A).scalarUnitIso b
  have hg : ((b : C) • f.val).IsIsogeny := by
    have hh := hIso.isIsogeny.comp_of_finiteKernelComposition
      (Hom.finiteKernelCompositionStatement _ _ _) hf
    simpa only [hIso, scalarUnitIso, scalarHom, Hom.smul_comp, Hom.id_comp] using hh
  intro x hx
  refine ⟨U, hx, 𝟙 U, e * n, (b : C) • f.val, hg, ?_⟩
  rw [restrict_id, centralSection, smul_smul, ofIntegral_smul]
  let c := algebraMap C K π
  have hpEq : (p : K) ^ n = algebraMap C K (↑(a ^ n) : C) * c ^ (e * n) := by
    rw [← map_natCast (algebraMap C K), ← map_pow, hcal, mul_pow,
      ← pow_mul, map_mul, map_pow (algebraMap C K) π]
    rfl
  have hh := congrArg (fun x : K => algebraMap C K (↑b : C) * x) hpEq
  change algebraMap C K (↑b : C) * (p : K) ^ n =
    algebraMap C K (↑b : C) * (algebraMap C K (↑(a ^ n) : C) * c ^ (e * n)) at hh
  rw [← mul_assoc, ← map_mul, show (↑b : C) * ↑(a ^ n) = 1 from Units.inv_mul _, map_one, one_mul] at hh
  have hc : c ^ (e * n) * ((p : K) ^ n)⁻¹ = algebraMap C K (↑b : C) := by
    rw [← hh, mul_assoc, mul_inv_cancel₀ (pow_ne_zero n hp), mul_one]
  exact congrArg (· • (ofIntegral U f.val : RationalSection K _ _ U)) hc

end RationalSection.OrderScalarPresentation

variable [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O F]

namespace LocalQuasiIsogeny

variable (z : LocalQuasiIsogeny F (p : O) M N U) (hz : IsOrderLinear E G z.val)
variable (hπ : Irreducible (p : O)) (hp : (p : K) ≠ 0)

/-- Change an actual local quasi-isogeny to the central scalar law. A ramification
identity converts the original p-denominators to central uniformizer denominators. -/
def centralScalarChange (hcal : (p : C) = (↑a : C) * π ^ e) (hπK : algebraMap C K π ≠ 0)
    (hS : (E.centralModule hs).IsPiDivisible π) (hT : (G.centralModule ht).IsPiDivisible π) :
    LocalQuasiIsogeny K π (E.centralModule hs) (G.centralModule ht) U where
  scalar_ne_zero := hπK
  source_divisible := hS
  target_divisible := hT
  val := RationalSection.centralScalarSection z hz hπ hp
  isLocal := by
    intro x hx
    obtain ⟨V, hxV, i, ⟨P⟩⟩ := exists_orderScalarPresentation z hz hπ ⟨x, hx⟩
    have h := P.centralSection_isLocallyScalarIsogeny (hs := hs) (ht := ht) hp hcal
    obtain ⟨W, hxW, j, n, f, hf, he⟩ := h x hxV
    refine ⟨W, hxW, j ≫ i, n, f, hf, ?_⟩
    rw [RationalSection.restrict_comp, centralScalarSection_isCentralScalarChange z hz hπ hp V i P]
    exact he

/-- The central section remains order-linear after gluing. -/
theorem centralScalarSection_orderLinear :
    IsOrderLinear (E.centralOrder hs) (G.centralOrder ht)
      (centralScalarSection (hs := hs) (ht := ht) z hz hπ hp) := by
  intro b
  choose V hx i ho using fun x : U => exists_orderScalarPresentation z hz hπ x
  let P (x : U) := Classical.choice (ho x)
  have hc : U ≤ iSup V := fun x h => (le_iSup V ⟨x, h⟩) (hx ⟨x, h⟩)
  apply (rationalHomTypeSheaf K (E.centralModule hs) (G.centralModule ht)).eq_of_locally_eq' V U i hc
  intro x
  change RationalSection.restrict (i x) (RationalSection.comp (centralScalarSection z hz hπ hp)
      (ofHom ((E.centralOrder hs).action b) U)) =
    RationalSection.restrict (i x) (RationalSection.comp (ofHom ((G.centralOrder ht).action b) U)
      (centralScalarSection z hz hπ hp))
  rw [RationalSection.restrict_comp_hom, RationalSection.restrict_comp_hom, restrict_ofHom, restrict_ofHom,
    centralScalarSection_isCentralScalarChange z hz hπ hp (V x) (i x) (P x)]
  exact (P x).centralSection_orderLinear b

end LocalQuasiIsogeny

end Langlands.FormalGroup.ModuleLaw
