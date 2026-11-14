import Langlands.GroupScheme.Reductive.RootDatum
import Langlands.LinearAlgebra.RootDatumIsogeny
import Langlands.GroupScheme.Rational.RootSubgroupTorusRestriction
import Langlands.GroupScheme.Rational.RootSubgroupConjugation
import Langlands.GroupScheme.Rational.WeightSupportCongruence
import Langlands.GroupScheme.Rational.RootPointOutsideMultiples

/-! # Root functors under a compatible root-datum isogeny -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false

private theorem index_eq_of_pos_nsmul_root_eq
    {J X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
    (P : RootDatum J X Y) [P.IsReduced] {i j : J} {m n : ℕ}
    (hm : 0 < m) (hn : 0 < n) (h : m • P.root i = n • P.root j) : i = j := by
  have hdep : ¬ LinearIndependent ℤ ![P.root i, P.root j] := by
    rw [LinearIndependent.pair_iff]
    intro hind
    have hz : (m : ℤ) • P.root i + (-(n : ℤ)) • P.root j = 0 := by
      simpa only [natCast_zsmul, neg_smul, add_neg_eq_zero] using h
    have hm0 := (hind (m : ℤ) (-(n : ℤ)) hz).1
    omega
  rcases RootPairing.IsReduced.eq_or_eq_neg (P := P) i j hdep with heq | hneg
  · exact P.root.injective heq
  · have hp := congrArg (P.toLinearMap.flip (P.coroot j)) h
    rw [hneg] at hp
    simp only [map_nsmul, map_neg, LinearMap.flip_apply,
      P.root_coroot_two, nsmul_eq_mul] at hp
    omega

namespace RelativeRoot

section Comparison

variable {k : Type u} [Field k]
    {T T' : CommGroupScheme (Spec (CommRingCat.of k))}
    {J J' : Type u} [Finite J] [Finite J']
    [Module.Finite ℤ (characterLattice T)] [Module.Finite ℤ (cocharacterLattice T)]
    [Module.Finite ℤ (characterLattice T')] [Module.Finite ℤ (cocharacterLattice T')]
    (P : RootDatum J (characterLattice T) (cocharacterLattice T))
    (P' : RootDatum J' (characterLattice T') (cocharacterLattice T'))
    [P.IsReduced] [P'.IsReduced]

omit [Finite J] [Module.Finite ℤ (characterLattice T)]
  [Module.Finite ℤ (cocharacterLattice T)] in
/-- A root in a reduced integral root datum lies in another root's positive
cyclic tail precisely when their indices agree. -/
theorem root_mem_cyclicTail_iff (l j : J) :
    P.root l ∈ cyclicTail (P.root j) 1 ↔ l = j := by
  constructor
  · rintro ⟨n, _, hn, heq⟩
    exact (index_eq_of_pos_nsmul_root_eq P (m := n) (n := 1) hn (by omega)
      (by simpa using heq)).symm
  · rintro rfl
    exact ⟨1, le_rfl, by omega, one_nsmul _⟩

/-- A root of the larger torus restricts to a positive multiple of the
corresponding source root precisely at the supplied index. -/
theorem root_mem_characterSemigroupPreimage_iff
    {p : ℕ} (f : Langlands.LinearAlgebra.RootDatumIsogeny p P' P)
    (t : T ⟶ T') (hweight : ∀ χ, f.weightMap χ = t ≫ χ)
    (l j' : J') :
    P'.root l ∈ characterSemigroupPreimage t
      (cyclicTail (P.root (f.indexEquiv j')) 1) ↔ l = j' := by
  constructor
  · intro hl
    change t ≫ P'.root l ∈ cyclicTail (P.root (f.indexEquiv j')) 1 at hl
    obtain ⟨n, _, hn, heq⟩ := hl
    have hr : f.rootFactor l • P.root (f.indexEquiv l) =
        n • P.root (f.indexEquiv j') := by
      simpa only [← hweight, f.root_weightMap, natCast_zsmul] using heq.symm
    exact f.indexEquiv.injective
      (index_eq_of_pos_nsmul_root_eq P (f.rootFactor_pos l) hn hr)
  · intro hl
    subst l
    change t ≫ P'.root j' ∈ cyclicTail (P.root (f.indexEquiv j')) 1
    refine ⟨f.rootFactor j', by have := f.rootFactor_pos j'; omega,
      f.rootFactor_pos j', ?_⟩
    simp only [← hweight, f.root_weightMap, natCast_zsmul]

variable {G' : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G'.X.hom] [Smooth G'.X.hom]

omit [Finite J'] [Module.Finite ℤ (characterLattice T')]
  [Module.Finite ℤ (cocharacterLattice T')] in
/-- Distinct roots of an actual reduced root datum give incomparable whole
root subgroup functors, over arbitrary fields. -/
theorem subgroup_le_subgroup_iff_of_isRootDatumOf
    (hT' : IsSplitTorus T'.toGrp) (i' : T'.toGrp ⟶ G')
    (hP' : IsRootDatumOf i' P') (l j' : J') :
    subgroup i' (P'.root l) ≤ subgroup i' (P'.root j') ↔ l = j' := by
  constructor
  · intro hle
    by_contra hne
    have hl : P'.root l ∈ relativeRoots i' := by
      change P'.root l ∈ roots i'
      rw [← hP'.2.1]
      exact Set.mem_range_self l
    exact subgroup_not_le_of_not_mem_cyclicTail hT' i' hl (P'.ne_zero _)
      (by rwa [root_mem_cyclicTail_iff P']) hle
  · rintro rfl
    exact le_rfl

/-- Under the supplied compatible lattice isogeny, restricting the target
full-torus action selects exactly the same intrinsic root subgroup. -/
theorem subgroup_comp_torusHom_eq_of_rootDatumIsogeny
    (hT : IsSplitTorus T.toGrp) (hT' : IsSplitTorus T'.toGrp)
    (i' : T'.toGrp ⟶ G') (hP' : IsRootDatumOf i' P')
    {p : ℕ} (f : Langlands.LinearAlgebra.RootDatumIsogeny p P' P)
    (t : T ⟶ T') (hweight : ∀ χ, f.weightMap χ = t ≫ χ)
    (j' : J') :
    subgroup (CommGroupScheme.groupHom t ≫ i') (P.root (f.indexEquiv j')) =
      subgroup i' (P'.root j') := by
  rw [subgroup_comp_torusHom_eq_semigroupSubgroup hT hT' t i' _ (P.ne_zero _),
    ← cyclicRootFunctorComparison k G' inferInstance inferInstance T' hT' i'
      (P'.root j') (P'.ne_zero j')]
  change semigroupSubgroup _ _ = semigroupSubgroup _ _
  apply semigroupSubgroup_eq_of_weightSupport
  intro χ hχ
  by_cases hz : χ = 0
  · subst χ
    constructor
    · rintro ⟨n, _, hn, heq⟩
      have heq0 : n • P.root (f.indexEquiv j') = 0 := by
        simpa only [← hweight, map_zero] using heq
      exact False.elim (hT.nsmul_ne_zero (P.ne_zero _) (by omega) heq0)
    · rintro ⟨n, _, hn, heq⟩
      exact False.elim (hT'.nsmul_ne_zero (P'.ne_zero _) (by omega) heq)
  · have hw : weightSpace i' χ ≠ ⊥ := by
      simpa only [actionWeightSpace_conjugation] using
        (mem_actionWeightSupport_top_iff _ χ).mp hχ
    obtain ⟨l, rfl⟩ := hP'.2.1.symm ▸ (show χ ∈ roots i' from ⟨hz, hw⟩)
    rw [root_mem_characterSemigroupPreimage_iff P P' f t hweight,
      root_mem_cyclicTail_iff P']

/-- The identity on ambient points identifies the root subgroup for the restricted
source torus with the corresponding root subgroup for the full target torus. -/
def rootPointsEquivOfRootDatumIsogeny
    (hT : IsSplitTorus T.toGrp) (hT' : IsSplitTorus T'.toGrp)
    (i' : T'.toGrp ⟶ G') (hP' : IsRootDatumOf i' P')
    {p : ℕ} (f : Langlands.LinearAlgebra.RootDatumIsogeny p P' P)
    (t : T ⟶ T') (hweight : ∀ χ, f.weightMap χ = t ≫ χ)
    (j' : J') (Z : Over (Spec (CommRingCat.of k))) :
    (subgroup (CommGroupScheme.groupHom t ≫ i')
      (P.root (f.indexEquiv j'))).carrier Z ≃*
        (subgroup i' (P'.root j')).carrier Z :=
  MulEquiv.subgroupCongr (congrArg (fun F : SubgroupFunctor G' => F.carrier Z)
    (subgroup_comp_torusHom_eq_of_rootDatumIsogeny P P' hT hT' i' hP' f t hweight j'))

@[simp] theorem rootPointsEquivOfRootDatumIsogeny_coe
    (hT : IsSplitTorus T.toGrp) (hT' : IsSplitTorus T'.toGrp)
    (i' : T'.toGrp ⟶ G') (hP' : IsRootDatumOf i' P')
    {p : ℕ} (f : Langlands.LinearAlgebra.RootDatumIsogeny p P' P)
    (t : T ⟶ T') (hweight : ∀ χ, f.weightMap χ = t ≫ χ)
    (j' : J') (Z : Over (Spec (CommRingCat.of k)))
    (g : (subgroup (CommGroupScheme.groupHom t ≫ i')
      (P.root (f.indexEquiv j'))).carrier Z) :
    (rootPointsEquivOfRootDatumIsogeny P P' hT hT' i' hP' f t hweight j' Z g).val =
      g.val := rfl

variable {G : GroupScheme (Spec (CommRingCat.of k))}

/-- A homomorphism compatible with the torus square sends corresponding
source-root points into the target root subgroup on every scheme test. -/
theorem comp_mem_subgroup_of_rootDatumIsogeny
    (hT : IsSplitTorus T.toGrp) (hT' : IsSplitTorus T'.toGrp)
    (i : T.toGrp ⟶ G) (i' : T'.toGrp ⟶ G') (hP' : IsRootDatumOf i' P')
    (φ : G ⟶ G') (t : T ⟶ T')
    (hsquare : i ≫ φ = CommGroupScheme.groupHom t ≫ i')
    {p : ℕ} (f : Langlands.LinearAlgebra.RootDatumIsogeny p P' P)
    (hweight : ∀ χ, f.weightMap χ = t ≫ χ)
    (j' : J') {Z : Over (Spec (CommRingCat.of k))} {g : Z ⟶ G.X}
    (hg : g ∈ (subgroup i (P.root (f.indexEquiv j'))).carrier Z) :
    g ≫ φ.hom.hom ∈ (subgroup i' (P'.root j')).carrier Z := by
  have h := comp_mem_subgroup i (P.root (f.indexEquiv j')) φ hg
  rwa [hsquare,
    subgroup_comp_torusHom_eq_of_rootDatumIsogeny P P' hT hT' i' hP' f t hweight j'] at h

end Comparison

end RelativeRoot
end Langlands.GroupScheme
