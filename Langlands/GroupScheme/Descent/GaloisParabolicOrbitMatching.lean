import Langlands.GroupScheme.Descent.GaloisStandardParabolicIntersections

/-! # Galois orbit matching for a commonly transported standard family -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace SubgroupFunctor

variable {F L : Type u} [Field F] [Field L] [Algebra F L]
  (G : GroupScheme (Spec (CommRingCat.of F)))

/-- The actual all-test intersection of every Galois translate of a subgroup
functor of the pulled-back ground-field group. -/
def galoisOrbitIntersection
    (P : SubgroupFunctor ((GroupScheme.baseChange (algebraBaseMap F L)).obj G)) :
    SubgroupFunctor ((GroupScheme.baseChange (algebraBaseMap F L)).obj G) :=
  intersection (fun σ : L ≃ₐ[F] L => galoisTransport F L G σ P)

/-- The full orbit intersection is invariant by the transport group law and
bijective left multiplication of the Galois index. -/
theorem galoisTransport_galoisOrbitIntersection
    (P : SubgroupFunctor ((GroupScheme.baseChange (algebraBaseMap F L)).obj G))
    (σ : L ≃ₐ[F] L) :
    galoisTransport F L G σ (galoisOrbitIntersection G P) = galoisOrbitIntersection G P := by
  apply galoisTransport_intersection_eq_of_permutes G σ _ (Equiv.mulLeft σ)
  intro τ
  exact congrFun (map_mul (galoisTransport F L G) σ τ).symm P

/-- Matching every inverse-indexed member to the identity-indexed member forces
all members to be the actual Galois translates of that one subgroup functor. -/
theorem galoisTransport_eq_of_inverse_orbit_matching
    (P : (L ≃ₐ[F] L) →
      SubgroupFunctor ((GroupScheme.baseChange (algebraBaseMap F L)).obj G))
    (hmatch : ∀ σ : L ≃ₐ[F] L,
      galoisTransport F L G σ (P σ⁻¹) = P 1) (σ : L ≃ₐ[F] L) :
    galoisTransport F L G σ (P 1) = P σ := by
  have hσ : galoisTransport F L G σ⁻¹ (P σ) = P 1 := by
    simpa only [inv_inv] using hmatch σ⁻¹
  calc
    galoisTransport F L G σ (P 1) =
        galoisTransport F L G σ (galoisTransport F L G σ⁻¹ (P σ)) := by rw [hσ]
    _ = galoisTransport F L G (σ * σ⁻¹) (P σ) := by rw [map_mul]; rfl
    _ = P σ := by rw [mul_inv_cancel, map_one]; rfl

/-- Inverse-orbit matching identifies the supplied family intersection with
the actual invariant orbit intersection of its identity-indexed member. -/
theorem intersection_eq_galoisOrbitIntersection_of_inverse_orbit_matching
    (P : (L ≃ₐ[F] L) →
      SubgroupFunctor ((GroupScheme.baseChange (algebraBaseMap F L)).obj G))
    (hmatch : ∀ σ : L ≃ₐ[F] L,
      galoisTransport F L G σ (P σ⁻¹) = P 1) :
    intersection P = galoisOrbitIntersection G (P 1) := by
  unfold galoisOrbitIntersection
  congr 1
  funext σ
  exact (galoisTransport_eq_of_inverse_orbit_matching G P hmatch σ).symm

/-- One-member inverse-orbit matching supplies the full left-regular
Galois permutation of the family. -/
theorem galoisTransport_family_eq_of_inverse_orbit_matching
    (P : (L ≃ₐ[F] L) →
      SubgroupFunctor ((GroupScheme.baseChange (algebraBaseMap F L)).obj G))
    (hmatch : ∀ σ : L ≃ₐ[F] L,
      galoisTransport F L G σ (P σ⁻¹) = P 1) (σ τ : L ≃ₐ[F] L) :
    galoisTransport F L G σ (P τ) = P (σ * τ) := by
  rw [← galoisTransport_eq_of_inverse_orbit_matching G P hmatch τ,
    ← galoisTransport_eq_of_inverse_orbit_matching G P hmatch (σ * τ), map_mul]
  rfl

/-- The inverse-orbit matching criterion makes the actual all-test
intersection Galois-invariant. -/
theorem galoisTransport_intersection_eq_of_inverse_orbit_matching
    (P : (L ≃ₐ[F] L) →
      SubgroupFunctor ((GroupScheme.baseChange (algebraBaseMap F L)).obj G))
    (hmatch : ∀ σ : L ≃ₐ[F] L,
      galoisTransport F L G σ (P σ⁻¹) = P 1) (σ : L ≃ₐ[F] L) :
    galoisTransport F L G σ (intersection P) = intersection P := by
  apply galoisTransport_intersection_eq_of_permutes G σ P (Equiv.mulLeft σ)
  exact galoisTransport_family_eq_of_inverse_orbit_matching G P hmatch σ

end SubgroupFunctor

section Parabolic

variable {F L : Type u} [Field F] [Field L] [Algebra F L]
  [FiniteDimensional F L] [IsGalois F L]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  {S : CommGroupScheme (Spec (CommRingCat.of F))} {s : S.toGrp ⟶ G}
  {T : CommGroupScheme (Spec (CommRingCat.of L))}
  [IsAffineHom ((GroupScheme.baseChange (algebraBaseMap F L)).obj G).X.hom]
  (i : T.toGrp ⟶ (GroupScheme.baseChange (algebraBaseMap F L)).obj G)
  (ν : cocharacterLattice T)

/-- Inverse-orbit matching cannot hold for a proper member of a commonly
transported standard family when a ground-field maximal split torus is central. -/
theorem IsMaximalSplitTorus.eq_simpleRelativeRoots_of_inverse_orbit_matching
    (hs : IsMaximalSplitTorus s) (hc : IsCentral s)
    (hG : IsConnectedReductive G)
    (hGL : IsConnectedReductive ((GroupScheme.baseChange (algebraBaseMap F L)).obj G))
    (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
    (J : (L ≃ₐ[F] L) → Set (characterLattice T))
    (hJ : ∀ σ, J σ ⊆ simpleRelativeRoots i ν)
    (e : (GroupScheme.baseChange (algebraBaseMap F L)).obj G ≅
      (GroupScheme.baseChange (algebraBaseMap F L)).obj G)
    (hmatch : ∀ σ : L ≃ₐ[F] L,
      SubgroupFunctor.range
        (radicalGaloisHom (Standard.parabolicHom i ν (J σ⁻¹) ≫ e.hom) σ) =
      SubgroupFunctor.range (Standard.parabolicHom i ν (J 1) ≫ e.hom)) :
    ∀ σ, J σ = simpleRelativeRoots i ν := by
  classical
  let : Fintype (L ≃ₐ[F] L) := Fintype.ofFinite _
  let P := fun σ : L ≃ₐ[F] L =>
    SubgroupFunctor.range (Standard.parabolicHom i ν (J σ) ≫ e.hom)
  have hm : ∀ σ : L ≃ₐ[F] L,
      SubgroupFunctor.galoisTransport F L G σ (P σ⁻¹) = P 1 := by
    intro σ
    change SubgroupFunctor.descentTransport (algebraBaseMap F L)
      (galoisBaseMap F L σ) (galoisBaseMap_over F L σ) G
        (SubgroupFunctor.range (Standard.parabolicHom i ν (J σ⁻¹) ≫ e.hom)) = _
    rw [SubgroupFunctor.descentTransport_range]
    exact hmatch σ
  apply hs.eq_simpleRelativeRoots_of_galoisPermuted i ν hc hG hGL hi hν J hJ e
  intro σ
  refine ⟨Equiv.mulLeft σ, ?_⟩
  intro τ
  have h := SubgroupFunctor.galoisTransport_family_eq_of_inverse_orbit_matching G P hm σ τ
  change SubgroupFunctor.descentTransport (algebraBaseMap F L)
    (galoisBaseMap F L σ) (galoisBaseMap_over F L σ) G
      (SubgroupFunctor.range (Standard.parabolicHom i ν (J τ) ≫ e.hom)) = _ at h
  rw [SubgroupFunctor.descentTransport_range] at h
  exact h

end Parabolic

end Langlands.GroupScheme
