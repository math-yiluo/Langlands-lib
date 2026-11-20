import Langlands.Geometry.FormalGroup.NilpotentFormalHom
import Langlands.Geometry.FormalGroup.RationalSectionBaseChange
import Mathlib.RingTheory.Localization.Algebra
import Mathlib.RingTheory.Flat.Basic

/-! # Coefficient pullback on basic opens of a nilpotent thickening -/

noncomputable section

universe u v

namespace Langlands.FormalGroup.ModuleLaw

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

attribute [local instance] coefficientAlgebra coefficientScalarTower

variable {O : Type u} [CommRing O]
variable {R S : Type v} [CommRing R] [CommRing S] [Algebra O R] [Algebra O S]
variable {F : Type v} [Field F] [Algebra O F]
variable {σ τ : Type} [Finite σ] [Finite τ]
variable {M : ModuleLaw O R σ} {N : ModuleLaw O R τ} {π : O}

/-- Pullback takes a basic open to the basic open of the image. -/
theorem coefficientOpenMap_basicOpen (φ : R →ₐ[O] S) (r : R) :
    (coefficientOpenMap φ).obj (PrimeSpectrum.basicOpen r) =
      PrimeSpectrum.basicOpen (φ r) :=
  PrimeSpectrum.comap_basicOpen φ.toRingHom r

/-- Inverse images of opens reflect inclusion along a surjective spectrum map. -/
theorem coefficientOpenMap_le_of_le (φ : R →ₐ[O] S)
    (hspec : Function.Surjective (coefficientSpectrumMap φ))
    {V U : Opens (PrimeSpectrum R)}
    (h : (coefficientOpenMap φ).obj V ≤ (coefficientOpenMap φ).obj U) : V ≤ U := by
  intro x hx
  obtain ⟨y, rfl⟩ := hspec x
  exact h (show y ∈ (coefficientOpenMap φ).obj V from hx)

/-- For a surjective coefficient map, inverse images of basic opens form a basis
of the target spectrum. -/
theorem exists_basicOpen_preimage_le (φ : R →ₐ[O] S) (hφ : Function.Surjective φ)
    {W : Opens (PrimeSpectrum S)} {y : PrimeSpectrum S} (hy : y ∈ W) :
    ∃ r : R, y ∈ (coefficientOpenMap φ).obj (PrimeSpectrum.basicOpen r) ∧
      (coefficientOpenMap φ).obj (PrimeSpectrum.basicOpen r) ≤ W := by
  obtain ⟨_, ⟨_, ⟨s, rfl⟩, rfl⟩, hys, hsW⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hy W.2
  obtain ⟨r, rfl⟩ := hφ s
  exact ⟨r, by rw [coefficientOpenMap_basicOpen]; exact hys,
    by rw [coefficientOpenMap_basicOpen]; exact hsW⟩

set_option maxHeartbeats 400000 in
/-- On a basic open, a surjective coefficient map with nilpotent kernel induces
a surjective section ring map with nilpotent kernel. -/
theorem coefficientSectionMap_basicOpen_nilpotent (φ : R →ₐ[O] S)
    (hφ : Function.Surjective φ) (hI : IsNilpotent (RingHom.ker φ.toRingHom)) (r : R) :
    Function.Surjective (coefficientSectionMap φ (PrimeSpectrum.basicOpen r)) ∧
      IsNilpotent (RingHom.ker (coefficientSectionMap φ (PrimeSpectrum.basicOpen r)).toRingHom) := by
  let U := PrimeSpectrum.basicOpen r
  let V := (coefficientOpenMap φ).obj U
  let A := (coefficientStructurePresheaf R).obj (op U)
  let B := (coefficientStructurePresheaf S).obj (op V)
  let β : A →ₐ[O] B := coefficientSectionMap φ U
  have : IsLocalization.Away r A := StructureSheaf.IsLocalization.to_basicOpen R r
  have : IsLocalization.Away (φ r) B := by
    change IsLocalization.Away (φ r) ((coefficientStructurePresheaf S).obj (op V))
    rw [show V = PrimeSpectrum.basicOpen (φ r) from coefficientOpenMap_basicOpen φ r]
    exact StructureSheaf.IsLocalization.to_basicOpen S (φ r)
  let hS : Submonoid.map φ.toRingHom (Submonoid.powers r) = Submonoid.powers (φ r) :=
    Submonoid.map_powers _ _
  have he : β = IsLocalization.Away.mapₐ A B φ r := by
    apply AlgHom.coe_ringHom_injective
    apply IsLocalization.ringHom_ext (Submonoid.powers r)
    apply RingHom.ext
    intro x
    have h := DFunLike.congr_fun (coefficientSectionMap_structural φ U) x
    let hm : Submonoid.powers r ≤ (Submonoid.powers (φ r)).comap φ.toRingHom :=
      hS.symm ▸ (Submonoid.powers r).le_comap_map
    exact h.trans (IsLocalization.map_eq (S := A) (Q := B) (g := φ.toRingHom) hm x).symm
  change Function.Surjective β ∧ IsNilpotent (RingHom.ker β.toRingHom)
  rw [he]
  refine ⟨IsLocalization.Away.mapₐ_surjective_of_surjective r hφ, ?_⟩
  change IsNilpotent (RingHom.ker (IsLocalization.map B φ.toRingHom (hS.symm ▸
    (Submonoid.powers r).le_comap_map) : A →+* B))
  rw [IsLocalization.ker_map B φ.toRingHom hS]
  obtain ⟨d, hd⟩ := hI
  refine ⟨d, ?_⟩
  change _ = ⊥
  rw [← Ideal.map_pow, show RingHom.ker φ.toRingHom ^ d = ⊥ from hd, Ideal.map_bot]

namespace Hom

/-- On a basic open, integral Hom pullback is injective across a nilpotent
coefficient thickening of scalar-divisible laws. -/
theorem openBaseChange_injective_basicOpen (φ : R →ₐ[O] S)
    (hφ : Function.Surjective φ) (hI : IsNilpotent (RingHom.ker φ.toRingHom))
    (hM : M.IsPiDivisible π) (hN : N.IsPiDivisible π) (r : R) :
    Function.Injective (openBaseChange (M := M) (N := N) φ (PrimeSpectrum.basicOpen r)) := by
  let U := PrimeSpectrum.basicOpen r
  let A := (coefficientStructurePresheaf R).obj (op U)
  let α := IsScalarTower.toAlgHom O R A
  let β := coefficientSectionMap φ U
  obtain ⟨hβ, hker⟩ := coefficientSectionMap_basicOpen_nilpotent φ hφ hI r
  intro f g he
  apply map_injective_of_nilpotent β hβ hker (hM.map α) (hN.map α).torsion
  apply Hom.ext
  apply CommLaw.Hom.ext
  change f.toHom.toCoordinateMap.map (coefficientSectionMap φ U).toRingHom =
    g.toHom.toCoordinateMap.map (coefficientSectionMap φ U).toRingHom
  rw [← openBaseChange_coordinates φ U f, ← openBaseChange_coordinates φ U g, he]

end Hom

/-- Flat extension of scalars preserves the injectivity on basic opens. -/
theorem RationalHom.openBaseChange_injective_basicOpen [Module.Flat O F]
    (φ : R →ₐ[O] S) (hφ : Function.Surjective φ)
    (hI : IsNilpotent (RingHom.ker φ.toRingHom))
    (hM : M.IsPiDivisible π) (hN : N.IsPiDivisible π) (r : R) :
    Function.Injective (openBaseChange (F := F) (M := M) (N := N) φ (PrimeSpectrum.basicOpen r)) :=
  Module.Flat.lTensor_preserves_injective_linearMap _
    (Hom.openBaseChange_injective_basicOpen φ hφ hI hM hN r)

end Langlands.FormalGroup.ModuleLaw
