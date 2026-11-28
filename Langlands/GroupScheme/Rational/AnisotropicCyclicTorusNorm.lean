import Langlands.GroupScheme.Absolute.CocharacterDescentLattice
import Langlands.GroupScheme.Rational.NontrivialCocharacterRank
import Langlands.GroupScheme.Rational.SplitRankTransport
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Subgroup

/-! # The cocharacter norm of a torus in an anisotropic group -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 650000

variable {F K : Type u} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [IsGalois F K]
  {H : GroupScheme (Spec (CommRingCat.of F))}
  {T : CommGroupScheme (Spec (CommRingCat.of F))} [IsAffineHom T.X.hom]
  {t : T.toGrp ⟶ H}

local notation "TK" => Functor.obj (CommGroupScheme.baseChange (algebraBaseMap F K)) T

omit [IsAffineHom T.X.hom] in
/-- The three powers of a generator enumerate the automorphisms of a cubic Galois extension. -/
theorem cubic_aut_pow_bijective (hdeg : Module.finrank F K = 3)
    (σ : K ≃ₐ[F] K) (hσ : orderOf σ = 3) :
    Function.Bijective (fun j : Fin 3 => σ ^ (j : ℕ)) := by
  apply (Nat.bijective_iff_injective_and_card _).mpr
  refine ⟨?_, by rw [Nat.card_fin, IsGalois.card_aut_eq_finrank F K, hdeg]⟩
  intro a b h
  apply Fin.ext
  exact pow_injOn_Iio_orderOf (x := σ) (by simp [hσ]) (by simp [hσ]) h

omit [IsAffineHom T.X.hom] in
/-- A cubic Galois extension has a coefficient automorphism of order three. -/
theorem exists_cubic_galois_generator (hdeg : Module.finrank F K = 3) :
    ∃ σ : K ≃ₐ[F] K, orderOf σ = 3 := by
  have hcard : Nat.card (K ≃ₐ[F] K) = 3 := (IsGalois.card_aut_eq_finrank F K).trans hdeg
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  let : IsCyclic (K ≃ₐ[F] K) := isCyclic_of_prime_card hcard
  obtain ⟨σ, hσ⟩ := IsCyclic.exists_generator (α := K ≃ₐ[F] K)
  exact ⟨σ, (orderOf_eq_card_of_forall_mem_zpowers hσ).trans hcard⟩

/-- The norm of a cocharacter of a torus in an anisotropic group vanishes,
because its descended cocharacter is trivial. -/
theorem IsAnisotropic.galoisOrbitSum_eq_zero [Fintype (K ≃ₐ[F] K)]
    (hH : IsAnisotropic H) (ht : IsClosedSubgroup t) (ν : cocharacterLattice (TK)) :
    CocharacterAveraging.galoisOrbitSum F K T ν = 0 := by
  have hT : IsAnisotropic T.toGrp := by
    change splitRank T.toGrp = 0
    have h := splitRank_le_of_isClosedSubgroup t ht
    rw [show splitRank H = 0 from hH] at h
    exact le_antisymm h zero_le
  let ν₀ := CocharacterAveraging.descendedOrbitSum F K T ν
  have hν₀ : ν₀ = 0 :=
    congrArg Additive.ofMul (hT.cocharacter_eq_zero (CommGroupScheme.groupHom ν₀))
  rw [← CocharacterAveraging.baseChange_descendedOrbitSum F K T ν]
  change cocharacterLattice.baseChange (algebraBaseMap F K) T ν₀ = 0
  rw [hν₀, map_zero]

/-- For a cubic Galois extension the cocharacter and its two successive
translates under a generator add to zero. -/
theorem IsAnisotropic.cocharacter_cyclic_norm_eq_zero
    (hH : IsAnisotropic H) (ht : IsClosedSubgroup t) (hdeg : Module.finrank F K = 3)
    (σ : K ≃ₐ[F] K) (hσ : orderOf σ = 3) (ν : cocharacterLattice (TK)) :
    ν + cocharacterLattice.galoisRepresentation F K T σ ν +
      cocharacterLattice.galoisRepresentation F K T (σ ^ 2) ν = 0 := by
  classical
  let : Fintype (K ≃ₐ[F] K) := Fintype.ofFinite _
  let g : Fin 3 → (K ≃ₐ[F] K) := fun j => σ ^ (j : ℕ)
  have hbij : Function.Bijective g := cubic_aut_pow_bijective hdeg σ hσ
  let e := Equiv.ofBijective g hbij
  have hsum := hH.galoisOrbitSum_eq_zero ht ν
  have he := e.sum_comp (fun τ : K ≃ₐ[F] K => cocharacterLattice.galoisRepresentation F K T τ ν)
  rw [CocharacterAveraging.galoisOrbitSum, CocharacterAveraging.orbitSum, ← he] at hsum
  simpa only [Fin.sum_univ_three, e, Equiv.ofBijective_apply, g, Fin.val_zero, Fin.val_one,
    Fin.val_two, pow_zero, pow_one, map_one, Module.End.one_apply, add_assoc] using hsum

end Langlands.GroupScheme
