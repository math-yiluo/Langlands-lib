import Langlands.Geometry.Building.IntegerValuationBoundedNormalizerOrbit
import Langlands.Geometry.Building.IntegerValuationNormalizerSharpReduction
import Langlands.Geometry.Building.IntegerValuationCommonApartments
import Langlands.Geometry.Building.ApartmentQuotientFactorization
import Langlands.Geometry.Building.GenericVertexApartmentRigidity
import Langlands.Geometry.Building.IntegerValuationBoundedGeometry
import Langlands.Geometry.Building.AffineFacetCentroids

/-! # Maximal boundedness from finite apartment orbits -/

noncomputable section

universe u uV uA

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Geometry.Building

namespace AffineRootSystem

/-- In a locally finite arrangement, the hyperplanes through a vertex
determine that vertex on the original affine torsor. -/
theorem eq_of_isVertex_of_vanishingRoots_torsor
    {V : Type uV} {A : Type uA}
    [AddCommGroup V] [Module ℝ V] [AddTorsor V A]
    {Ψ : Set (A →ᵃ[ℝ] ℝ)}
    (hΨ : IsLocallyFiniteReflectionArrangement Ψ) {x y : A}
    (hx : IsVertex Ψ x) (hy : ∀ ψ ∈ vanishingRoots Ψ x, ψ y = 0) :
    y = x := by
  obtain ⟨ε, hε, hsign⟩ :=
    GalleryGeometry.exists_pos_of_eventually
      (GalleryGeometry.eventually_sign_smul_vadd hΨ x (y -ᵥ x))
  have hf : ε • (y -ᵥ x) +ᵥ x ∈ facet Ψ x := by
    intro ψ hψ
    by_cases hzero : ψ x = 0
    · have hd : ψ.linear (y -ᵥ x) = 0 := by
        simpa only [vsub_eq_sub, hzero, hy ψ ⟨hψ, hzero⟩, sub_self]
          using ψ.linearMap_vsub y x
      rw [GalleryGeometry.apply_smul_vadd, hd, hzero]
      simp
    · exact (hsign ψ hψ hzero).symm
  rw [hx, Set.mem_singleton_iff] at hf
  have hz : ε • (y -ᵥ x) = 0 := by
    simpa only [vadd_vsub, vsub_self] using congrArg (fun z => z -ᵥ x) hf
  exact vsub_eq_zero_iff_eq.mp ((smul_eq_zero.mp hz).resolve_left hε.ne')

end AffineRootSystem

namespace IntegerValuationBuildingData

variable {k : Type u} [Field k] [ValuativeRel k]
    {v : Valuation k (WithZero (Multiplicative ℤ))} [v.Compatible]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (B : IntegerValuationBuildingData v G)

private instance vertexMaximalBoundedAffine : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom

/-- The finite orbit of the normalizer part of a bounded subgroup has an
affine centroid fixed by that entire normalizer part. -/
theorem exists_normalizer_fixed_of_isAlgebraicallyBounded
    (H : Subgroup (rationalPoints G))
    (hH : IsAlgebraicallyBounded k G.X (H : Set (rationalPoints G)))
    (x : B.Apartment) :
    ∃ z : B.Apartment, ∀ n : normalizerPoints B.i,
      (n : rationalPoints G) ∈ H → n • z = z := by
  classical
  let X : Set (normalizerPoints B.i) := {n | (n : rationalPoints G) ∈ H}
  have hX : IsAlgebraicallyBounded k G.X
      ((fun n : normalizerPoints B.i => (n : rationalPoints G)) '' X) :=
    hH.mono (by rintro _ ⟨n, hn, rfl⟩; exact hn)
  have hfin := B.finite_normalizer_orbit_of_isAlgebraicallyBounded X hX x
  let s : Finset B.Apartment := hfin.toFinset
  have hs : s.Nonempty := by
    refine ⟨x, hfin.mem_toFinset.mpr ?_⟩
    exact ⟨1, H.one_mem, one_smul _ _⟩
  refine ⟨s.centroid ℝ id, fun n hn => ?_⟩
  let e : B.Apartment ≃ᵃ[ℝ] B.Apartment := B.apartment.normalizerAffineEquiv n
  have hperm : s.map e.toEquiv.toEmbedding = s := by
    ext y
    constructor
    · intro hy
      obtain ⟨z, hz, rfl⟩ := Finset.mem_map.mp hy
      obtain ⟨m, hm, rfl⟩ := hfin.mem_toFinset.mp hz
      apply hfin.mem_toFinset.mpr
      refine ⟨n * m, H.mul_mem hn hm, ?_⟩
      exact mul_smul n m x
    · intro hy
      obtain ⟨m, hm, rfl⟩ := hfin.mem_toFinset.mp hy
      apply Finset.mem_map.mpr
      refine ⟨n⁻¹ • (m • x), hfin.mem_toFinset.mpr ?_, ?_⟩
      · exact ⟨n⁻¹ * m, H.mul_mem (H.inv_mem hn) hm, mul_smul _ _ _⟩
      · exact smul_inv_smul n (m • x)
  change e (s.centroid ℝ id) = s.centroid ℝ id
  rw [AffineRootSystem.affineEquiv_centroid_map e s hs, hperm]

/-- A bounded subgroup containing the vertex one-stabilizer has normalizer
part fixing that same apartment vertex. -/
theorem normalizer_fixes_vertex_of_isAlgebraicallyBounded
    (H : Subgroup (rationalPoints G))
    (hH : IsAlgebraicallyBounded k G.X (H : Set (rationalPoints G)))
    {x : B.Apartment} (hx : AffineRootSystem.IsVertex B.affineRoots x)
    (hle : B.oneStabilizer (B.apartmentMap x) ≤ H) :
    ∀ n : normalizerPoints B.i, (n : rationalPoints G) ∈ H → n • x = x := by
  obtain ⟨z, hz⟩ := B.exists_normalizer_fixed_of_isAlgebraicallyBounded H hH x
  have hzx : z = x := by
    apply AffineRootSystem.eq_of_isVertex_of_vanishingRoots_torsor
      (B.isLocallyFiniteReflectionArrangement_of_hasOppositeFactorPairs
        B.hasOppositeFactorPairs) hx
    intro ψ hψ
    obtain ⟨w, hw⟩ := B.exists_isCoroot_affineRoots hψ.1
    obtain ⟨m, hm, hme⟩ := B.exists_sharpFixer_normalizer_eq_affineReflection hψ.1
      (Ω := {x}) (fun y hy => by simpa only [Set.mem_singleton_iff.mp hy] using hψ.2) hw
    have hmH := hle (B.sharpFixer_le_oneStabilizer x hm)
    have hmz := hz m hmH
    change B.apartment.normalizerAffineEquiv m z = z at hmz
    rw [hme] at hmz
    have hval := congrArg ψ hmz
    rw [AffineRootSystem.apply_affineReflection] at hval
    linarith
  simpa only [hzx] using hz

/-- Common-apartment factorization upgrades normalizer rigidity to containment
of a bounded overgroup in the original apartment vertex one-stabilizer. -/
theorem le_oneStabilizer_apartment_vertex_of_isAlgebraicallyBounded
    (hcommon : B.apartment.HasCommonApartments)
    (H : Subgroup (rationalPoints G))
    (hH : IsAlgebraicallyBounded k G.X (H : Set (rationalPoints G)))
    {x : B.Apartment} (hx : AffineRootSystem.IsVertex B.affineRoots x)
    (hle : B.oneStabilizer (B.apartmentMap x) ≤ H) :
    H ≤ B.oneStabilizer (B.apartmentMap x) := by
  have hkernel :=
    IntegerValuation.subgroup_le_characterValuationKernel_of_isAlgebraicallyBounded v G H hH
  intro g hg
  obtain ⟨p, hp, n, q, hq, heq⟩ :=
    (ApartmentQuotient.hasCommonTranslatedApartment_iff_factorization
      B.apartment.sharpFixerFamily).mp hcommon x x g
  have hpK := B.sharpFixer_le_oneStabilizer x hp
  have hqK := B.sharpFixer_le_oneStabilizer x hq
  have hnH : (n : rationalPoints G) ∈ H := by
    have hn : (n : rationalPoints G) = p⁻¹ * g * q⁻¹ := by
      rw [heq]
      group
    rw [hn]
    exact H.mul_mem (H.mul_mem (H.inv_mem (hle hpK)) hg) (H.inv_mem (hle hqK))
  have hnx := B.normalizer_fixes_vertex_of_isAlgebraicallyBounded H hH hx hle n hnH
  refine B.mem_oneStabilizer.mpr ⟨hkernel hg, ?_⟩
  rw [heq, mul_smul, mul_smul, (B.mem_oneStabilizer.mp hqK).2,
    B.normalizer_smul_apartmentMap, hnx, (B.mem_oneStabilizer.mp hpK).2]

/-- Bounded overgroups of arbitrary vertex one-stabilizers are contained in
that one-stabilizer, by conjugating to the original apartment. -/
theorem le_oneStabilizer_vertex_of_isAlgebraicallyBounded
    (hcommon : B.apartment.HasCommonApartments)
    (H : Subgroup (rationalPoints G))
    (hH : IsAlgebraicallyBounded k G.X (H : Set (rationalPoints G)))
    {y : B.ReducedBuilding} (hy : B.IsVertex y)
    (hle : B.oneStabilizer y ≤ H) :
    H ≤ B.oneStabilizer y := by
  let : Smooth G.X.hom := B.isConnectedReductive.smooth
  obtain ⟨g, x, rfl, hx⟩ := hy
  let H' : Subgroup (rationalPoints G) := H.comap (MulAut.conj g).toMonoidHom
  have memH' (h : rationalPoints G) : h ∈ H' ↔ g * h * g⁻¹ ∈ H := by
    simp only [H', Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  have hH' : IsAlgebraicallyBounded k G.X (H' : Set (rationalPoints G)) := by
    refine (isAlgebraicallyBounded_conj_of_finiteType hH g⁻¹).mono ?_
    intro h hh
    have hhg := (memH' h).mp hh
    refine ⟨g⁻¹ * (g * h * g⁻¹), ⟨g⁻¹, rfl, g * h * g⁻¹, hhg, rfl⟩,
      (g⁻¹)⁻¹, rfl, ?_⟩
    group
  have hle' : B.oneStabilizer (B.apartmentMap x) ≤ H' := by
    intro h hh
    exact (memH' h).mpr (hle (B.conj_mem_oneStabilizer g hh))
  have hsub := B.le_oneStabilizer_apartment_vertex_of_isAlgebraicallyBounded
    hcommon H' hH' hx hle'
  intro h hh
  have hh' : g⁻¹ * h * g ∈ H' := by
    apply (memH' _).mpr
    have heq : g * (g⁻¹ * h * g) * g⁻¹ = h := by group
    rwa [heq]
  have hconj := B.conj_mem_oneStabilizer g (hsub hh')
  have heq : g * (g⁻¹ * h * g) * g⁻¹ = h := by group
  rwa [heq] at hconj

/-- Boundedness of the vertex one-stabilizer combines with the overgroup
containment theorem to give maximal boundedness. -/
theorem maximal_oneStabilizer_vertex_of_isAlgebraicallyBounded
    (hcommon : B.apartment.HasCommonApartments)
    {y : B.ReducedBuilding} (hy : B.IsVertex y)
    (hbounded : IsAlgebraicallyBounded k G.X
      (B.oneStabilizer y : Set (rationalPoints G))) :
    Maximal (fun H : Subgroup (rationalPoints G) =>
      IsAlgebraicallyBounded k G.X (H : Set (rationalPoints G)))
      (B.oneStabilizer y) := by
  exact ⟨hbounded, fun H hH hle =>
    B.le_oneStabilizer_vertex_of_isAlgebraicallyBounded hcommon H hH hy hle⟩

end IntegerValuationBuildingData

namespace IntegerValuation

/-- The overgroup-containment half of vertex maximal boundedness, over an
arbitrary compatible integer-valued field with common apartments. -/
def VertexBoundedOvergroupStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k]
    (v : Valuation k (WithZero (Multiplicative ℤ))) [v.Compatible]
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]
    (B : IntegerValuationBuildingData v G),
    B.apartment.HasCommonApartments →
    ∀ (H : Subgroup (rationalPoints G)) (y : B.ReducedBuilding),
      IsAlgebraicallyBounded k G.X (H : Set (rationalPoints G)) →
      B.IsVertex y → B.oneStabilizer y ≤ H → H ≤ B.oneStabilizer y

/-- Finite normalizer orbits, affine reflections and common-apartment
factorization prove the exact overgroup-containment proposition. -/
theorem vertexBoundedOvergroup : VertexBoundedOvergroupStatement.{u} := by
  intro k _ _ v _ G _ B hcommon H y hH hy hle
  exact B.le_oneStabilizer_vertex_of_isAlgebraicallyBounded hcommon H hH hy hle

end IntegerValuation
end Langlands.Geometry.Building
