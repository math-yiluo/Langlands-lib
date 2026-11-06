import Langlands.GroupScheme.Torus.KernelCocharacters
import Langlands.GroupScheme.Torus.WeilRestrictionNormOneCharacters
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # Actual character pullback and the annihilator of its cocharacter kernel -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.characterLattice

variable {k : Type u} [Field k]
    {T Q : CommGroupScheme (Spec (CommRingCat.of k))}

/-- Actual characters of `T` annihilating every cocharacter killed by `f`. -/
def cocharacterKernelAnnihilator (f : T ⟶ Q) :
    Submodule ℤ (characterLattice T) :=
  (CommGroupScheme.postcompose f (Gm (Spec (CommRingCat.of k)))).toIntLinearMap.ker
    |>.dualAnnihilator.comap (latticePairing T)

@[simp]
theorem mem_cocharacterKernelAnnihilator (f : T ⟶ Q) (χ : characterLattice T) :
    χ ∈ cocharacterKernelAnnihilator f ↔
      ∀ ν : cocharacterLattice T, ν ≫ f = 0 → latticePairing T χ ν = 0 := by
  simp only [cocharacterKernelAnnihilator, Submodule.mem_comap,
    Submodule.mem_dualAnnihilator, LinearMap.mem_ker]
  rfl

/-- Pullback of characters is adjoint to actual cocharacter postcomposition. -/
theorem pairing_precompose (f : T ⟶ Q) (χ : characterLattice Q)
    (ν : cocharacterLattice T) :
    latticePairing T (precompose f χ) ν = latticePairing Q χ (ν ≫ f) := by
  simp only [latticePairing_apply]
  exact congrArg (gmEndEquiv k) (Category.assoc ν f χ).symm

/-- Surjectivity on integral cocharacters makes actual character pullback injective. -/
theorem precompose_injective_of_cocharacter_surjective (f : T ⟶ Q)
    [(latticePairing Q).IsPerfPair]
    (hf : Function.Surjective (fun ν : cocharacterLattice T => ν ≫ f)) :
    Function.Injective (precompose f) := by
  intro χ ψ h
  apply (LinearMap.IsPerfPair.bijective_left (latticePairing Q)).injective
  apply LinearMap.ext
  intro νQ
  obtain ⟨ν, rfl⟩ := hf νQ
  rw [← pairing_precompose, ← pairing_precompose, h]

/-- For perfect actual lattice pairings, the character image is exactly the
annihilator of the kernel of a surjective integral cocharacter map. -/
theorem mem_range_precompose_iff (f : T ⟶ Q)
    [(latticePairing T).IsPerfPair] [(latticePairing Q).IsPerfPair]
    (hf : Function.Surjective (fun ν : cocharacterLattice T => ν ≫ f))
    (χ : characterLattice T) :
    χ ∈ (precompose f).toIntLinearMap.range ↔
      χ ∈ cocharacterKernelAnnihilator f := by
  let g := (CommGroupScheme.postcompose f (Gm (Spec (CommRingCat.of k)))).toIntLinearMap
  constructor
  · rintro ⟨ψ, rfl⟩
    rw [mem_cocharacterKernelAnnihilator]
    intro ν hν
    change latticePairing T (precompose f ψ) ν = 0
    rw [pairing_precompose, hν, map_zero]
  · intro hχ
    have hχ' : latticePairing T χ ∈ g.ker.dualAnnihilator := hχ
    rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker_of_surjective g hf] at hχ'
    obtain ⟨F, hF⟩ := hχ'
    obtain ⟨ψ, hψ⟩ :=
      (LinearMap.IsPerfPair.bijective_left (latticePairing Q)).surjective F
    refine ⟨ψ, ?_⟩
    apply (LinearMap.IsPerfPair.bijective_left (latticePairing T)).injective
    apply LinearMap.ext
    intro ν
    change latticePairing T (precompose f ψ) ν = latticePairing T χ ν
    rw [pairing_precompose]
    calc
      latticePairing Q ψ (ν ≫ f) = F (g ν) := LinearMap.congr_fun hψ (g ν)
      _ = latticePairing T χ ν := LinearMap.congr_fun hF ν

/-- The actual character lattice of the quotient is identified with the
annihilator of the full integral cocharacter kernel. -/
def cocharacterKernelAnnihilatorEquiv (f : T ⟶ Q)
    [(latticePairing T).IsPerfPair] [(latticePairing Q).IsPerfPair]
    (hf : Function.Surjective (fun ν : cocharacterLattice T => ν ≫ f)) :
    characterLattice Q ≃ₗ[ℤ] cocharacterKernelAnnihilator f :=
  LinearEquiv.ofBijective
    ((precompose f).toIntLinearMap.codRestrict (cocharacterKernelAnnihilator f)
      (fun χ => (mem_range_precompose_iff f hf _).mp ⟨χ, rfl⟩))
    ⟨fun χ ψ h =>
      precompose_injective_of_cocharacter_surjective f hf (congrArg Subtype.val h),
      fun χ => by
        obtain ⟨ψ, hψ⟩ := (mem_range_precompose_iff f hf χ.val).mpr χ.property
        exact ⟨ψ, Subtype.ext hψ⟩⟩

@[simp]
theorem cocharacterKernelAnnihilatorEquiv_val (f : T ⟶ Q)
    [(latticePairing T).IsPerfPair] [(latticePairing Q).IsPerfPair]
    (hf : Function.Surjective (fun ν : cocharacterLattice T => ν ≫ f))
    (χ : characterLattice Q) :
    (cocharacterKernelAnnihilatorEquiv f hf χ).val = f ≫ χ :=
  rfl

/-- A family which spans the cocharacter kernel up to nonzero integer
multiples cuts out the same character image. Integral generation is unnecessary. -/
theorem mem_range_precompose_iff_of_saturated_span (f : T ⟶ Q)
    [(latticePairing T).IsPerfPair] [(latticePairing Q).IsPerfPair]
    (hf : Function.Surjective (fun ν : cocharacterLattice T => ν ≫ f))
    {I : Type v} (c : I → cocharacterLattice T)
    (hc : ∀ i, c i ≫ f = 0)
    (hspan : ∀ ν : cocharacterLattice T, ν ≫ f = 0 →
      ∃ m : ℤ, m ≠ 0 ∧ m • ν ∈ Submodule.span ℤ (Set.range c))
    (χ : characterLattice T) :
    χ ∈ (precompose f).toIntLinearMap.range ↔
      ∀ i, latticePairing T χ (c i) = 0 := by
  rw [mem_range_precompose_iff f hf, mem_cocharacterKernelAnnihilator]
  constructor
  · exact fun h i => h (c i) (hc i)
  · intro h ν hν
    obtain ⟨m, hm, hmem⟩ := hspan ν hν
    have hle : Submodule.span ℤ (Set.range c) ≤ (latticePairing T χ).ker := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact h i
    have hz := hle hmem
    change latticePairing T χ (m • ν) = 0 at hz
    rw [map_smul, smul_eq_mul] at hz
    exact (mul_eq_zero.mp hz).resolve_left hm

end Langlands.GroupScheme.characterLattice
