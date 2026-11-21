import Langlands.Geometry.FormalGroup.CentralOrderSectionGluing

/-! # A global integral numerator computes the centralized rational section -/

noncomputable section

universe u v w c

namespace Langlands.FormalGroup.ModuleLaw.RationalSection

open CategoryTheory Opposite TopologicalSpace

attribute [local instance] coefficientAlgebra coefficientScalarTower

set_option maxHeartbeats 1700000
set_option backward.isDefEq.respectTransparency false

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
variable {U : Opens (PrimeSpectrum R)} {p n : ℕ}

/-- An integral global numerator gives a section after replacing its scalar action
by the central one and dividing by the original denominator. -/
def centralOfGlobalNumerator (p n : ℕ) (f : OrderAction.Hom E G) (U : Opens (PrimeSpectrum R)) :
    RationalSection K (E.centralModule hs) (G.centralModule ht) U :=
  ((p : K) ^ n)⁻¹ • ofHom (f.centralScalars (h := hs) (h' := ht)).val U

private theorem centralOverAlgebra_natPow_toHom (B : CommAlgCat.{v} R)
    (g : OrderAction.Hom (E.overAlgebra B) (G.overAlgebra B)) (p m : ℕ) :
    (((p : C) ^ m) • (g.centralScalarsOverAlgebra (hs := hs) (ht := ht) B).val).toHom =
      (((p : O) ^ m) • g.val).toHom := by
  have h := (G.overAlgebra B).centralModule_scalarPower_toHom
    (OrderAction.centralTangent_overAlgebra (hs := ht) B) p m
  simp only [scalarHom, Hom.smul_toHom, Hom.id_toHom, CommLaw.Hom.comp_id] at h
  change (((G.centralModule ht).overAlgebra B).action ((p : C) ^ m)).comp g.val.toHom =
    ((N.overAlgebra B).action ((p : O) ^ m)).comp g.val.toHom
  exact congrArg (·.comp g.val.toHom) h

variable [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O F]

/-- The same global numerator computes the centralized local quasi-isogeny even when
its unstabilized integral map is only known to present a rational section. -/
theorem centralScalarSection_ofGlobalNumerator (z : LocalQuasiIsogeny F (p : O) M N U)
    (hz : IsOrderLinear E G z.val) (hπ : Irreducible (p : O)) (hp : (p : K) ≠ 0)
    (f : OrderAction.Hom E G) (hf : (p : F) ^ n • z.val = ofHom f.val U) :
    centralScalarSection (hs := hs) (ht := ht) z hz hπ hp = centralOfGlobalNumerator p n f U := by
  choose V hx i hex using fun x : U => exists_orderScalarPresentation z hz hπ x
  let P (x : U) := Classical.choice (hex x)
  have hcover : U ≤ iSup V := fun x h => (le_iSup V ⟨x, h⟩) (hx ⟨x, h⟩)
  apply (rationalHomTypeSheaf K (E.centralModule hs) (G.centralModule ht)).eq_of_locally_eq' V U i hcover
  intro x
  change restrict (i x) (centralScalarSection (hs := hs) (ht := ht) z hz hπ hp) =
    restrict (i x) (centralOfGlobalNumerator p n f U)
  rw [centralScalarSection_isCentralScalarChange z hz hπ hp (V x) (i x) (P x),
    centralOfGlobalNumerator, map_smul, restrict_ofHom]
  let B := (coefficientStructurePresheaf R).obj (op (V x))
  let fB := f.map (IsScalarTower.toAlgHom O R B)
  let fc := (fB.centralScalarsOverAlgebra (hs := hs) (ht := ht) B).val
  let g := (P x).numerator
  let gc := ((P x).centralNumerator (hs := hs) (ht := ht)).val
  let m := (P x).exponent
  have hfB : (p : F) ^ n • restrict (i x) z.val = ofIntegral (V x) fB.val := by
    have h := congrArg (restrict (i x)) hf
    rw [map_smul, restrict_ofHom] at h
    exact h
  have hgB : (p : F) ^ m • restrict (i x) z.val = ofIntegral (V x) g.val := (P x).represents
  have hcross : ((p : O) ^ n) • g.val = ((p : O) ^ m) • fB.val := by
    apply ofIntegral_injective_of_isPiDivisible (F := F) hπ z.source_divisible
    have hl := ofIntegral_smul (F := F) (M := M) (N := N) (U := V x) ((p : O) ^ n) g.val
    have hr := ofIntegral_smul (F := F) (M := M) (N := N) (U := V x) ((p : O) ^ m) fB.val
    rw [map_pow, map_natCast] at hl hr
    have h : (p : F) ^ n • (ofIntegral (V x) g.val : RationalSection F M N (V x)) =
        (p : F) ^ m • ofIntegral (V x) fB.val := by
      rw [← hgB, ← hfB, smul_smul, smul_smul, mul_comm]
    exact hl.trans (h.trans hr.symm)
  have hcrossC : ((p : C) ^ n) • gc = ((p : C) ^ m) • fc := by
    apply Hom.ext
    exact (centralOverAlgebra_natPow_toHom (hs := hs) (ht := ht) B g p n).trans
      ((congrArg (fun f : OpenIntegralHom M N (V x) => f.toHom) hcross).trans
        (centralOverAlgebra_natPow_toHom (hs := hs) (ht := ht) B fB p m).symm)
  have hsection : (p : K) ^ n • (ofIntegral (V x) gc : RationalSection K _ _ (V x)) =
      (p : K) ^ m • ofIntegral (V x) fc := by
    have hl := ofIntegral_smul (F := K) (M := E.centralModule hs) (N := G.centralModule ht)
      (U := V x) ((p : C) ^ n) gc
    have hr := ofIntegral_smul (F := K) (M := E.centralModule hs) (N := G.centralModule ht)
      (U := V x) ((p : C) ^ m) fc
    rw [map_pow, map_natCast] at hl hr
    have h := congrArg (ofIntegral (F := K) (M := E.centralModule hs) (N := G.centralModule ht) (V x)) hcrossC
    exact hl.symm.trans (h.trans hr)
  let l := (p : K) ^ m
  let r := (p : K) ^ n
  have hl : l ≠ 0 := pow_ne_zero _ hp
  have hr : r ≠ 0 := pow_ne_zero _ hp
  have h₁ : (l * r)⁻¹ * r = l⁻¹ := by field_simp
  have h₂ : (l * r)⁻¹ * l = r⁻¹ := by field_simp
  change l⁻¹ • (ofIntegral (V x) gc : RationalSection K _ _ (V x)) = r⁻¹ • ofIntegral (V x) _
  have hc : (f.centralScalars (h := hs) (h' := ht)).val.map (IsScalarTower.toAlgHom C R B) = fc := by
    apply Hom.ext
    rfl
  rw [hc]
  have hh := congrArg ((l * r)⁻¹ • ·) hsection
  change (l * r)⁻¹ • (r • (ofIntegral (V x) gc : RationalSection K _ _ (V x))) =
    (l * r)⁻¹ • (l • ofIntegral (V x) fc) at hh
  simpa only [smul_smul, h₁, h₂] using hh

end Langlands.FormalGroup.ModuleLaw.RationalSection
