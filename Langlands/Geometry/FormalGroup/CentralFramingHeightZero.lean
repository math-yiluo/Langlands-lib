import Langlands.Geometry.FormalGroup.CentralLocalQuasiIsogeny
import Langlands.Geometry.FormalGroup.RationalHeight

/-! # Preservation of zero rank height under change to central scalars -/

noncomputable section

universe u v w c

namespace Langlands.FormalGroup.ModuleLaw.RationalSection

open CategoryTheory Opposite TopologicalSpace

attribute [local instance] coefficientAlgebra coefficientScalarTower

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

variable {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {D : Type w} [Ring D] [Algebra O D]
variable {C : Type c} [CommRing C] [Algebra C D] [Algebra C R]
variable {F K : Type v} [Field F] [Algebra O F] [IsFractionRing O F] [Field K] [Algebra C K]
variable {σ τ : Type} [Finite σ] [Finite τ]
variable {M : ModuleLaw O R σ} {N : ModuleLaw O R τ}
variable {E : OrderAction D M} {G : OrderAction D N}
variable {hs : ∀ (a : C) (x : σ → R),
  E.fiberTangent (RingHom.id R) (algebraMap C D a) x = algebraMap C R a • x}
variable {ht : ∀ (a : C) (x : τ → R),
  G.fiberTangent (RingHom.id R) (algebraMap C D a) x = algebraMap C R a • x}
variable {U V : Opens (PrimeSpectrum R)} {p q H e : ℕ} {π : C} {u : Cˣ}

namespace OrderScalarPresentation

variable {z : RationalSection F M N V} (P : OrderScalarPresentation p E G z)

/-- The integral numerator after replacing its prime-power denominator by a uniformizer power. -/
def uniformizerNumerator (u : Cˣ) : OpenIntegralHom (E.centralModule hs) (G.centralModule ht) V :=
  (↑((u ^ P.exponent)⁻¹) : C) • (P.centralNumerator (hs := hs) (ht := ht)).val

omit [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O F] in
/-- The unit correction gives exactly the new uniformizer denominator. -/
theorem represents_uniformizer (hp : (p : K) ≠ 0) (hcal : (p : C) = (u : C) * π ^ e) :
    (algebraMap C K π) ^ (e * P.exponent) • (P.centralSection (K := K) (hs := hs) (ht := ht)) =
      ofIntegral V (P.uniformizerNumerator u) := by
  rw [centralSection, smul_smul, uniformizerNumerator, ofIntegral_smul]
  let n := P.exponent
  have h : (p : K) ^ n = algebraMap C K (↑(u ^ n) : C) * (algebraMap C K π) ^ (e * n) := by
    rw [← map_natCast (algebraMap C K), ← map_pow, hcal, mul_pow, ← pow_mul,
      map_mul, map_pow (algebraMap C K) π]
    rfl
  have hinv : algebraMap C K (↑((u ^ n)⁻¹) : C) * (p : K) ^ n = (algebraMap C K π) ^ (e * n) := by
    rw [h, ← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]
  have hcoef : (algebraMap C K π) ^ (e * n) * ((p : K) ^ n)⁻¹ =
      algebraMap C K (↑((u ^ n)⁻¹) : C) := by
    rw [← hinv, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hp), mul_one]
  exact congrArg (· • (ofIntegral V (P.centralNumerator (hs := hs) (ht := ht)).val :
    RationalSection K (E.centralModule hs) (G.centralModule ht) V)) hcoef

end OrderScalarPresentation

namespace HeightPresentation

variable {z : RationalSection F M N U} {i : V ⟶ U}
variable (P : HeightPresentation (p : O) p (RationalSection.restrict i z))
variable (hz : IsOrderLinear E G z) (hπ : Irreducible (p : O)) (hM : M.IsPiDivisible (p : O))

/-- A rank presentation of an order-linear section has an actual order-linear numerator. -/
def orderNumerator : OrderScalarPresentation p E G (RationalSection.restrict i z) :=
  let he : (p : F) ^ P.exponent • RationalSection.restrict i z = ofIntegral V P.representative :=
    by simpa only [map_natCast] using P.represents
  ⟨P.exponent, integralOrderHomOfScalar hπ hM hz i _ P.representative he, P.numerator.1, he⟩

/-- An actual prime-normalized zero-height presentation gives an actual central
uniformizer-normalized zero-height presentation with the same numerator kernel rank. -/
def centralZero (hzero : P.index = 0) (hp : (p : K) ≠ 0)
    (hcal : (p : C) = (u : C) * π ^ e) (hC : (E.centralModule hs).HasPiHeight π q H) :
    HeightPresentation π q ((P.orderNumerator hz hπ hM).centralSection (K := K) (hs := hs) (ht := ht)) := by
  let S := (coefficientStructurePresheaf R).obj (op V)
  let n := P.exponent
  let m := e * n
  let L := (E.centralModule hs).overAlgebra S
  let J := (G.centralModule ht).overAlgebra S
  let Q := P.orderNumerator hz hπ hM
  let f := (Q.centralNumerator (hs := hs) (ht := ht)).val
  let g := Q.uniformizerNumerator (hs := hs) (ht := ht) u
  let a := L.scalarHom (π ^ m)
  have hL : L.HasPiHeight π q H := hC.map (IsScalarTower.toAlgHom C R S)
  have ha : a.HasHeight q (m * H) := ⟨hL.piDivisible.scalarPower_isIsogeny m, hL.scalarPower_rank m⟩
  let b := (M.overAlgebra S).scalarHom ((p : O) ^ n)
  have hkernel : b.kernelSetFunctor ≅ a.kernelSetFunctor := by
    let hS := OrderAction.centralTangent_overAlgebra (E := E) (hs := hs) S
    refine ((E.overAlgebra S).centralModule_scalarPowerKernelIso hS p n).trans ?_
    have hh : (p : C) ^ n = (↑(u ^ n) : C) * π ^ m := by
      rw [hcal, mul_pow, ← pow_mul]
      rfl
    change (L.scalarHom ((p : C) ^ n)).kernelSetFunctor ≅ (L.scalarHom (π ^ m)).kernelSetFunctor
    rw [hh]
    exact (L.scalarKernelIso_unit_mul (u ^ n) (π ^ m)).symm
  have hb : b.HasKernelRank (q ^ (m * H)) := by
    obtain ⟨K, hK⟩ := ha.2
    exact ⟨{
      coordinateAlgebra := K.coordinateAlgebra
      finite := K.finite
      projective := K.projective
      represents := K.represents.ofIso hkernel.symm }, hK⟩
  have heq : P.numeratorHeight = P.denominatorHeight := by
    unfold HeightPresentation.index at hzero
    omega
  have hf : f.HasHeight q (m * H) := by
    obtain ⟨KN, hKN⟩ := P.numerator.2
    obtain ⟨KD, hKD⟩ := P.denominator.2
    have hrank : ∀ x, KN.rank x = q ^ (m * H) := by
      intro x
      rw [hKN x, heq, ← hKD x]
      exact (Hom.hasKernelRank_iff b KD _).mp hb x
    refine ⟨Q.numerator.centralScalarsOverAlgebra_isIsogeny (hs := hs) (ht := ht) S Q.isIsogeny, ?_⟩
    let er : P.representative.kernelSetFunctor ≅ f.kernelSetFunctor :=
      Q.numerator.centralScalarsKernelIso (hs := OrderAction.centralTangent_overAlgebra (hs := hs) S)
        (ht := OrderAction.centralTangent_overAlgebra (hs := ht) S)
    exact ⟨{
      coordinateAlgebra := KN.coordinateAlgebra
      finite := KN.finite
      projective := KN.projective
      represents := KN.represents.ofIso er }, hrank⟩
  let v := (u ^ n)⁻¹
  have hg : g.HasHeight q (m * H) := by
    apply Hom.hasHeight_of_isoSquare f g (Iso.refl L) (J.scalarUnitIso v) _ hf
    change ((v : C) • f).comp (Hom.id L) = ((v : C) • Hom.id J).comp f
    rw [Hom.comp_id, Hom.smul_comp, Hom.id_comp]
  exact ⟨m, g, m * H, m * H, hg, ha, Q.represents_uniformizer hp hcal⟩

@[simp]
theorem centralZero_index (hzero : P.index = 0) (hp : (p : K) ≠ 0)
    (hcal : (p : C) = (u : C) * π ^ e) (hC : (E.centralModule hs).HasPiHeight π q H) :
    (P.centralZero (ht := ht) hz hπ hM hzero hp hcal hC).index = 0 := by
  change ((e * P.exponent * H : ℕ) : ℤ) - (e * P.exponent * H : ℕ) = 0
  exact sub_self _

end HeightPresentation

/-- Actual zero height is preserved by the central scalar change of a local quasi-isogeny. -/
theorem HasHeightFunction.centralScalarSection_zero (z : LocalQuasiIsogeny F (p : O) M N U)
    (hz : IsOrderLinear E G z.val) (hπ : Irreducible (p : O)) (hp : (p : K) ≠ 0)
    (hh : HasHeightFunction (p : O) p z.val (fun _ => 0))
    (hcal : (p : C) = (u : C) * π ^ e) (hC : (E.centralModule hs).HasPiHeight π q H) :
    HasHeightFunction π q (centralScalarSection (hs := hs) (ht := ht) z hz hπ hp) (fun _ => 0) := by
  intro x
  obtain ⟨V, hx, i, P, hP⟩ := hh x
  have hzero : P.index = 0 := (hP ⟨x, hx⟩).symm
  let Q := P.orderNumerator hz hπ z.source_divisible
  have h := centralScalarSection_isCentralScalarChange (hs := hs) (ht := ht) z hz hπ hp V i Q
  refine ⟨V, hx, i, h.symm ▸ P.centralZero hz hπ z.source_divisible hzero hp hcal hC, ?_⟩
  intro y
  rw [HeightPresentation.index_cast, HeightPresentation.centralZero_index]

end Langlands.FormalGroup.ModuleLaw.RationalSection
