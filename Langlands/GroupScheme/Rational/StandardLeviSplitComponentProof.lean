import Langlands.GroupScheme.Rational.StandardLeviSplitComponentStatement
import Langlands.GroupScheme.Rational.LeviSplitComponentProof
import Langlands.GroupScheme.Rational.SplitComponentProof
import Langlands.GroupScheme.Rational.RelativeRootSignsProof
import Langlands.GroupScheme.Rational.RootSupportFiniteness

/-! # Split components of the actual standard Levi representatives -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace StandardLeviSplitComponent

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

/-- For a split torus in a connected reductive group, containment of the zero sets on actual
relative roots gives containment of the dynamic centralizers on every test scheme. -/
theorem dynamicCentralizer_le_of_zero_imp (hG : IsConnectedReductive G)
    (hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G) {zeta eta : cocharacterLattice T}
    (h : ∀ α ∈ relativeRoots i, latticePairing T α zeta = 0 → latticePairing T α eta = 0) :
    Dynamic.centralizer (CommGroupScheme.groupHom zeta ≫ i) ≤
      Dynamic.centralizer (CommGroupScheme.groupHom eta ≫ i) := by
  rw [(RelativeRoot.dynamicSemigroupComparison k G hG.smooth hG.isAffineHom
      hG.connectedSpace T hT i zeta).2.1,
    (RelativeRoot.dynamicSemigroupComparison k G hG.smooth hG.isAffineHom
      hG.connectedSpace T hT i eta).2.1]
  apply RelativeRoot.semigroupSubgroup_mono_on_weightSupport
  exact (RelativeRoot.rootSupport_imp_iff_actionWeightSupport_imp i
    (fun χ => χ ∈ RelativeRoot.zeroSemigroup zeta)
    (fun χ => χ ∈ RelativeRoot.zeroSemigroup eta)
    (fun _ => show latticePairing T 0 eta = 0 by simp)).mp h

/-- A nonnegative multiple of a standard cocharacter plus another standard cocharacter for the
same face is again standard for that face. -/
theorem isStandardCocharacter_nsmul_add (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
    {J : Set (characterLattice T)} {zeta eta : cocharacterLattice T}
    (hzeta : IsStandardCocharacter i ν J zeta) (heta : IsStandardCocharacter i ν J eta)
    (m : ℕ) : IsStandardCocharacter i ν J (m • zeta + eta) := by
  refine ⟨hzeta.1, fun α hα => ?_, fun α hα hαJ => ?_⟩
  · rw [map_add, map_nsmul, hzeta.2.1 α hα, heta.2.1 α hα, smul_zero, add_zero]
  · rw [map_add, map_nsmul, nsmul_eq_mul]
    exact add_pos_of_nonneg_of_pos
      (mul_nonneg (Int.natCast_nonneg m) (hzeta.2.2 α hα hαJ).le) (heta.2.2 α hα hαJ)

/-- A nonzero integer multiplied by `M + 1` cannot be cancelled by an integer of absolute value
at most `M`. -/
theorem natCast_succ_mul_add_ne_zero {M : ℕ} {p q : ℤ} (hp : p ≠ 0) (hq : q.natAbs ≤ M) :
    ((M + 1 : ℕ) : ℤ) * p + q ≠ 0 := by
  intro h
  have hp' : 1 ≤ |p| := Int.one_le_abs hp
  have hq' : |q| ≤ M := by
    rw [Int.abs_eq_natAbs]
    exact_mod_cast hq
  have hqe : |q| = (M + 1) * |p| := by
    rw [show q = -(((M + 1 : ℕ) : ℤ) * p) by linarith, abs_neg, abs_mul]
    push_cast
    rw [abs_of_nonneg (by positivity : (0 : ℤ) ≤ M + 1)]
  have hM : (0 : ℤ) ≤ M := by positivity
  nlinarith

/-- If the actual relative roots are finite and some standard cocharacter exists, then some
standard cocharacter vanishes only on roots that vanish on every standard cocharacter. -/
theorem exists_isStandardCocharacter_zero_minimal (i : T.toGrp ⟶ G)
    (ν : cocharacterLattice T) {J : Set (characterLattice T)} (hR : (relativeRoots i).Finite)
    {eta : cocharacterLattice T} (heta : IsStandardCocharacter i ν J eta) :
    ∃ zeta, IsStandardCocharacter i ν J zeta ∧
      ∀ eta, IsStandardCocharacter i ν J eta →
        ∀ α ∈ relativeRoots i, latticePairing T α zeta = 0 → latticePairing T α eta = 0 := by
  classical
  have hZ : ∀ zeta : cocharacterLattice T,
      {α | α ∈ relativeRoots i ∧ latticePairing T α zeta = 0}.Finite :=
    fun _ => hR.subset fun _ hα => hα.1
  have hex : ∃ n, ∃ zeta, IsStandardCocharacter i ν J zeta ∧
      {α | α ∈ relativeRoots i ∧ latticePairing T α zeta = 0}.ncard = n :=
    ⟨_, eta, heta, rfl⟩
  obtain ⟨zeta, hzeta, hzn⟩ := Nat.find_spec hex
  refine ⟨zeta, hzeta, fun eta heta α hα hαzeta => ?_⟩
  by_contra hαeta
  obtain ⟨M, hM⟩ : ∃ M : ℕ, ∀ β ∈ relativeRoots i, (latticePairing T β eta).natAbs ≤ M :=
    ⟨∑ β ∈ hR.toFinset, (latticePairing T β eta).natAbs, fun β hβ =>
      Finset.single_le_sum (f := fun β => (latticePairing T β eta).natAbs)
        (fun _ _ => Nat.zero_le _) (hR.mem_toFinset.mpr hβ)⟩
  have hxi := isStandardCocharacter_nsmul_add i ν hzeta heta (M + 1)
  have hsub : {β | β ∈ relativeRoots i ∧ latticePairing T β ((M + 1) • zeta + eta) = 0} ⊂
      {β | β ∈ relativeRoots i ∧ latticePairing T β zeta = 0} := by
    refine ssubset_of_subset_not_superset (fun β hβ => ?_) fun hle => ?_
    · rw [Set.mem_ofPred_eq] at hβ ⊢
      refine ⟨hβ.1, ?_⟩
      by_contra hβzeta
      have h0 := hβ.2
      rw [map_add, map_nsmul, nsmul_eq_mul] at h0
      exact natCast_succ_mul_add_ne_zero hβzeta (hM β hβ.1) h0
    · have h0 := (Set.mem_ofPred.mp (hle (Set.mem_ofPred.mpr ⟨hα, hαzeta⟩))).2
      rw [map_add, map_nsmul, hαzeta, smul_zero, zero_add] at h0
      exact hαeta h0
  have hlt := Set.ncard_lt_ncard hsub (hZ zeta)
  have hmin := Nat.find_min' hex ⟨_, hxi, rfl⟩
  omega

/-- For a split torus in a connected reductive group, the choice-free standard Levi functor is
the dynamic centralizer of one cocharacter of the same torus. When the face has no standard
cocharacter, the zero cocharacter is used. -/
theorem exists_standardLevi_eq_dynamicCentralizer (hG : IsConnectedReductive G)
    (hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
    (J : Set (characterLattice T)) :
    ∃ zeta : cocharacterLattice T,
      standardLevi i ν J = Dynamic.centralizer (CommGroupScheme.groupHom zeta ≫ i) := by
  by_cases hJ : ∃ eta, IsStandardCocharacter i ν J eta
  · obtain ⟨eta, heta⟩ := hJ
    have : Smooth G.X.hom := hG.smooth
    obtain ⟨zeta, hzeta, hmin⟩ :=
      exists_isStandardCocharacter_zero_minimal i ν (hT.finite_relativeRoots i) heta
    refine ⟨zeta, le_antisymm (standardLevi_le_dynamicCentralizer i ν hzeta) ?_⟩
    intro U g hg
    rw [mem_standardLevi]
    intro eta heta
    exact dynamicCentralizer_le_of_zero_imp hG hT i (hmin eta heta) U hg
  · refine ⟨0, SubgroupFunctor.ext fun U => Subgroup.ext fun g => ?_⟩
    rw [mem_standardLevi, Dynamic.mem_centralizer]
    refine iff_of_true (fun eta heta => (hJ ⟨eta, heta⟩).elim) ?_
    have h1 : CartesianMonoidalCategory.snd U (Gm (Spec (CommRingCat.of k))).X ≫
        (CommGroupScheme.groupHom (0 : cocharacterLattice T) ≫ i).hom.hom = 1 := by
      rw [Grp.comp_hom_hom, ← Category.assoc, comp_groupHom_zero, MonObj.one_comp]
    rw [Dynamic.orbit, h1, one_mul, inv_one, mul_one]

end StandardLeviSplitComponent

open StandardLeviSplitComponent in
/-- Every actual standard Levi representative of a connected reductive group over a field is
connected reductive and has a split component whose inclusion into the ambient group factors
through the same maximal split torus. -/
theorem standardLeviSplitComponentStatement : StandardLeviSplitComponentStatement.{u} := by
  intro k _ G hG T i hi
  have := hG.isAffineHom
  have := hi.isSplitSubtorus.mono
  intro ν _ J _
  obtain ⟨zeta, hzeta⟩ :=
    exists_standardLevi_eq_dynamicCentralizer hG hi.isSplitSubtorus.1 i ν J
  have hrep : (Dynamic.centralizer (CommGroupScheme.groupHom zeta ≫ i)).IsRepresentedBy
      (Standard.leviHom i ν J) := by
    rw [← hzeta]
    exact Standard.isRepresentedBy_leviHom i ν J
  obtain ⟨hM, hA⟩ := leviSplitComponentStatement k G hG T i hi zeta
    (Standard.leviScheme i ν J) (Standard.leviHom i ν J)
    (Standard.isClosedSubgroup_leviHom i ν J) hrep
  obtain ⟨⟨A_G, iG, hiG⟩, _⟩ := splitComponentStatement k G hG
  obtain ⟨A, a, _, g, ha, _, hg, _⟩ := hA A_G iG hiG
  exact ⟨hM, A, a, g, ha, hg⟩

example : StandardLeviSplitComponentStatement.{u} := @standardLeviSplitComponentStatement.{u}

end Langlands.GroupScheme
