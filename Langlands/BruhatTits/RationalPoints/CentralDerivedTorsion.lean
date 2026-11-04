import Langlands.GroupScheme.Derived.RepresentabilityProof
import Langlands.GroupScheme.Derived.CentralIntersectionProof
import Langlands.GroupScheme.CentralIsogeny.KernelTorsion
import Mathlib.Basic.Real.Basic

/-! # Uniform torsion in the full central derived intersection -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))}

/-- A positive exponent kills every point in the intersection of the full
scheme-theoretic centre and derived subgroup, on every test scheme. -/
theorem IsConnectedReductive.exists_pow_eq_one_of_mem_center_derived
    (hG : IsConnectedReductive G) :
    ∃ N : ℕ, 0 < N ∧
      ∀ (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ G.X),
        x ∈ (center G).carrier T → x ∈ (derivedSubgroup G).carrier T → x ^ N = 1 := by
  let := hG.isAffineHom
  let := hG.smooth
  obtain ⟨D, d, _, _, hd⟩ := derivedSubgroupRepresentability k G
  obtain ⟨C, c, hc, hr, hfin⟩ :=
    derivedCentralIntersectionFiniteness k G D d hG hd
  let : IsClosedImmersion d.hom.hom.left := hd.1
  let : IsClosedImmersion c.hom.hom.left := hc
  let : Mono d.hom.hom := Over.mono_of_mono_left _
  let : Mono c.hom.hom := Over.mono_of_mono_left _
  have hcentral : IsCentral (c ≫ d) := by
    intro T x
    have hx : x ≫ c.hom.hom ∈ (SubgroupFunctor.range c).carrier T :=
      SubgroupFunctor.mem_range.mpr ⟨x, rfl⟩
    rw [hr, SubgroupFunctor.mem_comap] at hx
    simpa only [Grp.comp_hom_hom, Category.assoc] using hx
  let : Mono (c ≫ d).hom.hom := by
    rw [Grp.comp_hom_hom]
    infer_instance
  let : IsCommMonObj C.X := hcentral.isCommMonObj
  let : IsFinite C.X.hom := hfin
  obtain ⟨N, hN, hpow⟩ := exists_pow_eq_one_of_isFinite C
  refine ⟨N, hN, fun T x hxcent hxder => ?_⟩
  rw [← hd.2, SubgroupFunctor.mem_range] at hxder
  obtain ⟨y, hy⟩ := hxder
  have hyc : y ∈ (SubgroupFunctor.range c).carrier T := by
    rw [hr, SubgroupFunctor.mem_comap, hy]
    exact hxcent
  obtain ⟨z, hz⟩ := SubgroupFunctor.mem_range.mp hyc
  rw [← hy, ← hz, ← MonObj.pow_comp, ← MonObj.pow_comp, hpow T z,
    MonObj.one_comp, MonObj.one_comp]

end Langlands.GroupScheme

namespace Langlands.BruhatTits.RationalPoints

open Langlands.GroupScheme

variable {k : Type u} [CommRing k]

/-- Actual rational points belonging to both the full scheme-theoretic centre
and the scheme-theoretic derived subgroup. -/
def centralDerivedPoints (G : GroupScheme (Spec (CommRingCat.of k))) :
    Subgroup (rationalPoints G) :=
  (center G).carrier (Over.mk (𝟙 _)) ⊓ (derivedSubgroup G).carrier (Over.mk (𝟙 _))

@[simp] theorem mem_centralDerivedPoints
    {G : GroupScheme (Spec (CommRingCat.of k))} {x : rationalPoints G} :
    x ∈ centralDerivedPoints G ↔
      x ∈ (center G).carrier (Over.mk (𝟙 _)) ∧
        x ∈ (derivedSubgroup G).carrier (Over.mk (𝟙 _)) := Iff.rfl

section Field

variable {K : Type u} [Field K]
    {G H : GroupScheme (Spec (CommRingCat.of K))}

/-- The full central derived rational subgroup has a uniform positive exponent. -/
theorem exists_pow_eq_one_centralDerivedPoints (hG : IsConnectedReductive G) :
    ∃ N : ℕ, 0 < N ∧ ∀ x ∈ centralDerivedPoints G, x ^ N = 1 := by
  obtain ⟨N, hN, hpow⟩ := hG.exists_pow_eq_one_of_mem_center_derived
  exact ⟨N, hN, fun x hx => hpow _ x hx.1 hx.2⟩

/-- Every ambient real homomorphism kills all actual central derived points;
no openness or continuity hypothesis is needed. -/
theorem centralDerivedPoints_le_ker (hG : IsConnectedReductive G)
    (f : rationalPoints G →* Multiplicative ℝ) :
    centralDerivedPoints G ≤ f.ker := by
  obtain ⟨N, hN, hpow⟩ := exists_pow_eq_one_centralDerivedPoints hG
  intro x hx
  apply toAdd_eq_zero.mp
  have hf := congrArg (fun y => (f y).toAdd) (hpow x hx)
  simp only [map_pow, toAdd_pow, map_one, toAdd_one, nsmul_eq_mul] at hf
  exact (mul_eq_zero.mp hf).resolve_left (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN))

/-- If an actual central homomorphism has full range in the derived subgroup,
all its rational images are killed by every ambient real homomorphism. -/
theorem map_eq_one_of_isCentral_range_le_derived (hG : IsConnectedReductive G)
    (f : rationalPoints G →* Multiplicative ℝ) (i : H ⟶ G)
    (hi : IsCentral i) (hider : SubgroupFunctor.range i ≤ derivedSubgroup G)
    (x : rationalPoints H) :
    f (rationalPoints.map i x) = 1 := by
  apply centralDerivedPoints_le_ker hG f
  exact ⟨hi _ x, hider _ (SubgroupFunctor.mem_range.mpr ⟨x, rfl⟩)⟩

end Field

end Langlands.BruhatTits.RationalPoints
