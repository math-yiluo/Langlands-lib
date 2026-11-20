import Langlands.Geometry.FormalGroup.NilpotentOpenBaseChange
import Langlands.Geometry.FormalGroup.RationalSectionBaseChangeCalculus

/-! # Injectivity on arbitrary rational Hom sections across a nilpotent thickening -/

noncomputable section

universe u v

namespace Langlands.FormalGroup.ModuleLaw

open CategoryTheory Opposite TopologicalSpace

attribute [local instance] coefficientAlgebra coefficientScalarTower

variable {O : Type u} [CommRing O]
variable {R S : Type v} [CommRing R] [CommRing S] [Algebra O R] [Algebra O S]
variable {F : Type v} [Field F] [Algebra O F] [Module.Flat O F]
variable {σ τ : Type} [Finite σ] [Finite τ]
variable {M : ModuleLaw O R σ} {N : ModuleLaw O R τ} {π : O}

namespace RationalSection

set_option maxHeartbeats 400000 in
/-- Rational Hom sections are determined by their pullback across a nilpotent
coefficient thickening. -/
theorem baseChange_injective_of_nilpotent (φ : R →ₐ[O] S)
    (hφ : Function.Surjective φ) (hI : IsNilpotent (RingHom.ker φ.toRingHom))
    (hspec : Function.Surjective (coefficientSpectrumMap φ))
    (hM : M.IsPiDivisible π) (hN : N.IsPiDivisible π) (U : Opens (PrimeSpectrum R)) :
    Function.Injective (baseChange (F := F) (M := M) (N := N) φ U) := by
  classical
  apply (injective_iff_map_eq_zero (baseChange (F := F) (M := M) (N := N) φ U)).2
  intro z hz
  have hlocal : ∀ x ∈ U, ∃ (B : Opens (PrimeSpectrum R)) (i : B ⟶ U),
      x ∈ B ∧ restrict i z = 0 := by
    intro x hx
    obtain ⟨V, i, ⟨a, ha⟩, hxV⟩ :=
      (Presheaf.imageSieve_mem (Opens.grothendieckTopology _)
        (rationalHomTypeUnit F M N) z) x hx
    change ofRational V a = restrict i z at ha
    let V' := (coefficientOpenMap φ).obj V
    have he : ofRational V' (RationalHom.openBaseChange φ V a) =
        ofRational (F := F) V' 0 := by
      rw [← baseChange_ofRational, ha, ← restrict_baseChange, hz, map_zero, map_zero]
    obtain ⟨y, rfl⟩ := hspec x
    have hyV : y ∈ V' := hxV
    let a' := RationalHom.openBaseChange φ V a
    let e := Presheaf.equalizerSieve (F := rationalHomTypePresheaf F (M.map φ) (N.map φ))
      (X := op V') a' 0
    obtain ⟨W, j, hj, hyW⟩ :=
      (Presheaf.equalizerSieve_mem (Opens.grothendieckTopology _)
        (rationalHomTypeUnit F (M.map φ) (N.map φ)) a' 0 he) y hyV
    obtain ⟨r, hyB, hBW⟩ := exists_basicOpen_preimage_le φ hφ hyW
    let B := PrimeSpectrum.basicOpen r
    let k : B ⟶ V := homOfLE (coefficientOpenMap_le_of_le φ hspec (hBW.trans j.le))
    let l : (coefficientOpenMap φ).obj B ⟶ W := homOfLE hBW
    have hr := e.downward_closed hj l
    rw [show l ≫ j = (coefficientOpenMap φ).map k from Subsingleton.elim _ _] at hr
    change (rationalHomPresheaf F (M.map φ) (N.map φ)).map
      ((coefficientOpenMap φ).map k).op (RationalHom.openBaseChange φ V a) =
        ((rationalHomPresheaf F (M.map φ) (N.map φ)).map
          ((coefficientOpenMap φ).map k).op).hom 0 at hr
    rw [map_zero, ← RationalHom.openBaseChange_naturality, ←
      (RationalHom.openBaseChange φ B).map_zero] at hr
    have haB := RationalHom.openBaseChange_injective_basicOpen φ hφ hI hM hN r hr
    refine ⟨B, k ≫ i, hyB, ?_⟩
    rw [restrict_comp, ← ha, restrict_ofRational, haB, map_zero]
  choose B i hxB hzB using fun x : U => hlocal x.val x.property
  have hcover : U ≤ iSup B := fun x hx => (le_iSup B ⟨x, hx⟩) (hxB ⟨x, hx⟩)
  apply (rationalHomTypeSheaf F M N).eq_of_locally_eq' B U i hcover
  intro x
  change restrict (i x) z = restrict (i x) 0
  rw [hzB, map_zero]

end RationalSection

end Langlands.FormalGroup.ModuleLaw
