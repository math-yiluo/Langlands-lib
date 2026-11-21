import Langlands.Geometry.FormalGroup.CentralOrderIntegralMap
import Langlands.Geometry.FormalGroup.CentralScalarKernel
import Langlands.Geometry.FormalGroup.OrderLinearIntegralSection
import Langlands.Geometry.FormalGroup.LocalQuasiIsogenyInverseAssembly

/-! # Central scalar changes of local rational numerator presentations -/

noncomputable section

universe u v w c

namespace Langlands.FormalGroup.ModuleLaw.RationalSection

open CategoryTheory Opposite TopologicalSpace

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
variable {U V W : Opens (PrimeSpectrum R)} {p : ℕ}

/-- An actual order-linear integral isogeny representing a scalar multiple of a section. -/
structure OrderScalarPresentation (p : ℕ) (E : OrderAction D M) (G : OrderAction D N)
    {U : Opens (PrimeSpectrum R)} (z : RationalSection F M N U) where
  exponent : ℕ
  numerator : OrderAction.Hom (E.overAlgebra ((coefficientStructurePresheaf R).obj (op U)))
    (G.overAlgebra ((coefficientStructurePresheaf R).obj (op U)))
  isIsogeny : numerator.val.IsIsogeny
  represents : (p : F) ^ exponent • z = ofIntegral U numerator.val

namespace OrderScalarPresentation

variable {z : RationalSection F M N U} {w : RationalSection F M N V}

/-- The order-linear numerator with the central formal module laws. -/
def centralNumerator (P : OrderScalarPresentation p E G z) :
    OrderAction.Hom ((E.centralOrder hs).overAlgebra ((coefficientStructurePresheaf R).obj (op U)))
      ((G.centralOrder ht).overAlgebra ((coefficientStructurePresheaf R).obj (op U))) :=
  P.numerator.centralScalarsOverAlgebra _

/-- Divide the actual numerator by the original scalar power in the new fraction field. -/
def centralSection (P : OrderScalarPresentation p E G z) :
    RationalSection K (E.centralModule hs) (G.centralModule ht) U :=
  ((p : K) ^ P.exponent)⁻¹ • ofIntegral U (P.centralNumerator (hs := hs) (ht := ht)).val

private theorem scalarPower_restrict_coordinates
    {A B : CommAlgCat.{v} R} (φ : A ⟶ B)
    (g : OrderAction.Hom (E.overAlgebra A) (G.overAlgebra A)) (p n : ℕ) :
    (((p : C) ^ n) • Hom.algebraMapLinear φ
      (g.centralScalarsOverAlgebra (hs := hs) (ht := ht) A).val).toHom.toCoordinateMap =
    (((p : O) ^ n) • Hom.algebraMapLinear φ g.val).toHom.toCoordinateMap := by
  simp only [Hom.smul_toHom, CommLaw.Hom.comp_toCoordinateMap, Hom.algebraMapLinear_coordinates,
    OrderAction.Hom.centralScalarsOverAlgebra_coordinates]
  have h := (G.overAlgebra B).centralModule_scalarPower_toHom
    (OrderAction.centralTangent_overAlgebra (E := G) (hs := ht) B) p n
  simp only [scalarHom, Hom.smul_toHom, Hom.id_toHom, CommLaw.Hom.comp_id] at h
  exact congrArg (fun a => a.toCoordinateMap.comp (g.val.toHom.toCoordinateMap.map φ.hom.toRingHom)) h

variable [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O F]

/-- The rational section computed with the central scalars agrees on overlaps of
any two integral isogeny presentations of the same original section. -/
theorem centralSection_restrict_eq (P : OrderScalarPresentation p E G z)
    (Q : OrderScalarPresentation p E G w) (i : W ⟶ U) (j : W ⟶ V)
    (hp : (p : K) ≠ 0) (hπ : Irreducible (p : O)) (hM : M.IsPiDivisible (p : O))
    (hz : restrict i z = restrict j w) :
    restrict i (P.centralSection (K := K) (hs := hs) (ht := ht)) =
      restrict j (Q.centralSection (K := K) (hs := hs) (ht := ht)) := by
  let φ := (coefficientStructurePresheaf R).map i.op
  let ψ := (coefficientStructurePresheaf R).map j.op
  have hP : (p : F) ^ P.exponent • restrict i z =
      ofIntegral W (Hom.algebraMapLinear φ P.numerator.val) := by
    simpa only [map_smul, restrict_ofIntegral] using congrArg (restrict i) P.represents
  have hQ : (p : F) ^ Q.exponent • restrict j w =
      ofIntegral W (Hom.algebraMapLinear ψ Q.numerator.val) := by
    simpa only [map_smul, restrict_ofIntegral] using congrArg (restrict j) Q.represents
  have hcross : ((p : O) ^ Q.exponent) • Hom.algebraMapLinear φ P.numerator.val =
      ((p : O) ^ P.exponent) • Hom.algebraMapLinear ψ Q.numerator.val := by
    apply ofIntegral_injective_of_isPiDivisible (F := F) hπ hM
    simp only [ofIntegral_smul, map_pow, map_natCast, ← hP, ← hQ, hz, smul_smul]
    rw [mul_comm]
  let f := Hom.algebraMapLinear φ (P.centralNumerator (hs := hs) (ht := ht)).val
  let g := Hom.algebraMapLinear ψ (Q.centralNumerator (hs := hs) (ht := ht)).val
  have hc : ((p : C) ^ Q.exponent) • f = ((p : C) ^ P.exponent) • g := by
    apply Hom.ext
    apply CommLaw.Hom.ext
    exact (scalarPower_restrict_coordinates (hs := hs) (ht := ht) φ P.numerator p Q.exponent).trans
      ((congrArg (fun h : OpenIntegralHom M N W => h.toHom.toCoordinateMap) hcross).trans
        (scalarPower_restrict_coordinates (hs := hs) (ht := ht) ψ Q.numerator p P.exponent).symm)
  let l : K := (p : K) ^ P.exponent
  let r : K := (p : K) ^ Q.exponent
  have hcr : r • (ofIntegral W f : RationalSection K (E.centralModule hs) (G.centralModule ht) W) =
      l • ofIntegral W g := by
    simpa only [ofIntegral_smul, map_pow, map_natCast] using
      congrArg (ofIntegral (F := K) (M := E.centralModule hs) (N := G.centralModule ht) W) hc
  have hl : l ≠ 0 := pow_ne_zero _ hp
  have hr : r ≠ 0 := pow_ne_zero _ hp
  have h₁ : (l * r)⁻¹ * r = l⁻¹ := by field_simp
  have h₂ : (l * r)⁻¹ * l = r⁻¹ := by field_simp
  simp only [centralSection, map_smul, restrict_ofIntegral]
  change l⁻¹ • (ofIntegral W f : RationalSection K (E.centralModule hs) (G.centralModule ht) W) =
    r⁻¹ • ofIntegral W g
  simpa only [smul_smul, h₁, h₂] using
    congrArg ((l * r)⁻¹ • ·) hcr

end OrderScalarPresentation

end Langlands.FormalGroup.ModuleLaw.RationalSection
