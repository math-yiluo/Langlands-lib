import Langlands.Geometry.Building.IntegerOrdinaryRootQuotients
import Langlands.Geometry.Building.ValuationDerivativeAffineRoots
import Langlands.GroupScheme.Rational.VectorRationalPointUnboundedness

/-! # Ordinary derivative roots from algebraically bounded filtrations -/

noncomputable section
universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Geometry.Building.IntegerValuationBuildingData

private instance boundedDerivativeAffine {k : Type u} [Field k]
    {H : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom H.X.hom] :
    IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom

variable {k : Type u} [Field k] [ValuativeRel k]
    {v : Valuation k (WithZero (Multiplicative ℤ))}
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (B : IntegerValuationBuildingData v G)

/-- Each actual relative root has an algebraically bounded filtration at some
apartment point and some depth. -/
def HasBoundedRootFiltrations : Prop :=
  ∀ a : relativeRoots B.i, ∃ (x : B.Apartment) (r : ℝ),
    IsAlgebraicallyBounded k G.X (B.filtration x a r : Set (rationalPoints G))

/-- A missing multipliable ordinary direction would make every rational point of
its positive-dimensional vector quotient the image of a bounded filtration. -/
theorem not_hasNoOrdinaryRootDirection_of_bounded {a : relativeRoots B.i}
    (h2a : 2 • (a : characterLattice B.S) ∈ relativeRoots B.i)
    (x : B.Apartment) (s : ℝ)
    (hbounded : IsAlgebraicallyBounded k G.X
      (B.filtration x a s : Set (rationalPoints G)))
    (hlarge : ∃ t : k, (1 : k) <ᵥ t) :
    ¬ B.HasNoOrdinaryRootDirection a := by
  classical
  intro hno
  let : Smooth G.X.hom := B.isConnectedReductive.smooth
  have hS : IsSplitTorus B.S.toGrp := B.isMaximalSplitTorus.1.1
  have ha0 : (a : characterLattice B.S) ≠ 0 := (mem_relativeRoots.mp a.property).1
  have hhigh : ∀ n : ℕ, 3 ≤ n →
      n • (a : characterLattice B.S) ∉ relativeRoots B.i := by
    intro n hn hmem
    have := B.hasOppositeFactorPairs.eq_one_or_two_of_nsmul_mem B.i hS hmem
    omega
  obtain ⟨U, j, hj, hjc, -, -, -, -, -, -⟩ :=
    RelativeRoot.rootSubgroupRealization k G B.isConnectedReductive B.S B.i
      B.isMaximalSplitTorus a a.property
  obtain ⟨U₂, j₂, hj₂, -, -, -, -, -, -, -⟩ :=
    RelativeRoot.rootSubgroupRealization k G B.isConnectedReductive B.S B.i
      B.isMaximalSplitTorus (2 • (a : characterLattice B.S)) h2a
  let : IsAffineHom U.X.hom := hjc.isAffineHom
  let : IsClosedImmersion j.hom.hom.left := hjc
  obtain ⟨C⟩ := RelativeRoot.nonempty_doubleRootCommutatorPairing hS B.i ha0 hhigh hj hj₂
  obtain ⟨N⟩ := RelativeRoot.nonempty_heisenbergNormalForm C hS ha0 hhigh
  obtain ⟨d, e, he⟩ := C.weightVectorStructure.1
  let : IsAffineHom C.V.X.hom := RelativeRoot.IsVectorGroupOfDimension.isAffineHom ⟨e, he.1⟩
  have hker (T : Over (Spec (CommRingCat.of k))) (p : T ⟶ U.X) :
      p ≫ C.q.hom.hom = 1 ↔ p ≫ j.hom.hom ∈
        (RelativeRoot.subgroup B.i (2 • (a : characterLattice B.S))).carrier T := by
    rw [← SubgroupFunctor.mem_comap, ← C.isFppfQuotient.2.2.2]
    exact (mem_range_kernelι_iff C.q p).symm
  have hd : 0 < d := by
    obtain ⟨g, hg, hg2⟩ := RelativeRoot.exists_mem_rootGroupPoints_not_mem_two_smul
      B.isConnectedReductive B.isMaximalSplitTorus a.property h2a hhigh
    have hgU : g ∈ (SubgroupFunctor.range j).carrier (Over.mk (𝟙 _)) := by
      rw [hj.2]
      exact hg
    obtain ⟨g₀, hg₀⟩ := hgU
    rcases Nat.eq_zero_or_pos d with hzero | hd
    · subst d
      exfalso
      apply hg2
      rw [← hg₀]
      apply (hker _ g₀).mp
      apply (e _).injective
      exact Subsingleton.elim _ _
    · exact hd
  let A : Set (rationalPoints U) :=
    {p | rationalPoints.map j p ∈ B.filtration x a s}
  have hA : IsAlgebraicallyBounded k U.X A := by
    apply isAlgebraicallyBounded_of_closedImmersion k j.hom.hom A
    apply hbounded.mono
    rintro _ ⟨p, hp, rfl⟩
    exact hp
  have hsurj : rationalPoints.map C.q '' A = Set.univ := by
    apply Set.eq_univ_of_forall
    intro p
    let u₀ : rationalPoints U := p ≫ N.sec
    have hu : rationalPoints.map j u₀ ∈ B.rootGroup a := by
      change u₀ ≫ j.hom.hom ∈ (RelativeRoot.subgroup B.i a).carrier _
      rw [← hj.2]
      exact ⟨u₀, rfl⟩
    obtain ⟨r, hr⟩ : ∃ r : ℝ, rationalPoints.map j u₀ ∈ B.filtration x a r := by
      induction hval : x.val a (rationalPoints.map j u₀) using WithTop.recTopCoe with
      | top => exact ⟨0, KPApartmentData.mem_filtration.mpr ⟨hu, by rw [hval]; exact le_top⟩⟩
      | coe r => exact ⟨r, KPApartmentData.mem_filtration.mpr ⟨hu, by rw [hval]⟩⟩
    obtain ⟨v, hv, hdeep⟩ :=
      B.exists_mul_inv_mem_filtration_of_forall_not_mem_affineRoots h2a hno x hr s
    have hv2 : v ∈ (RelativeRoot.subgroup B.i
        (2 • (a : characterLattice B.S))).carrier (Over.mk (𝟙 _)) :=
      B.filtration_le_rootGroup x _ _ hv
    have hvU : v ∈ (SubgroupFunctor.range j).carrier (Over.mk (𝟙 _)) := by
      rw [hj.2]
      exact RelativeRoot.double_subgroup_le B.i a (Over.mk (𝟙 _)) hv2
    obtain ⟨v₀, hv₀⟩ : ∃ v₀ : rationalPoints U, rationalPoints.map j v₀ = v := hvU
    have hvq : rationalPoints.map C.q v₀ = 1 := by
      apply (hker _ v₀).mpr
      change rationalPoints.map j v₀ ∈ _
      rw [hv₀]
      exact hv2
    refine ⟨u₀ * v₀⁻¹, ?_, ?_⟩
    · change rationalPoints.map j (u₀ * v₀⁻¹) ∈ B.filtration x a s
      rw [map_mul, map_inv, hv₀]
      exact hdeep
    · rw [map_mul, map_inv, hvq, inv_one, mul_one]
      change (p ≫ N.sec) ≫ C.q.hom.hom = p
      rw [Category.assoc, N.sec_comp, Category.comp_id]
  have hV := hA.image_rationalPointsMap C.q
  rw [hsurj] at hV
  exact RelativeRoot.not_isAlgebraicallyBounded_univ_of_naturalVectorCoordinates
    e he.1 hd hlarge hV

/-- Algebraic boundedness at one depth for each root suffices for full ordinary
derivative equality, with no topological or completeness hypothesis. -/
theorem derivativeRoots_affineRoots_of_bounded
    (hbounded : B.HasBoundedRootFiltrations)
    (hlarge : ∃ t : k, (1 : k) <ᵥ t) :
    AffineRootSystem.derivativeRoots B.affineRoots = Set.range (rootForm B.i) := by
  apply Set.Subset.antisymm
  · rintro f ⟨ψ, ⟨a, hlin, _⟩, rfl⟩
    exact ⟨a, hlin.symm⟩
  · rintro _ ⟨a, rfl⟩
    by_contra hnot
    have hno : B.HasNoOrdinaryRootDirection a :=
      fun ψ hψ h => hnot ⟨ψ, hψ, h⟩
    by_cases h2a : 2 • (a : characterLattice B.S) ∈ relativeRoots B.i
    · obtain ⟨x, s, hB⟩ := hbounded a
      exact B.not_hasNoOrdinaryRootDirection_of_bounded h2a x s hB hlarge hno
    · let x : B.Apartment := Classical.arbitrary B.Apartment
      obtain ⟨g, hg, hgtop⟩ := x.isValuation.exists_ne_top a.property
      have hg1 : g ≠ 1 := by
        rintro rfl
        exact hgtop (B.val_apply_one a x)
      have hlin := B.reflectionFunctional_linear a g
      have hjump : B.apartment.affineRootGroupPlus a (B.reflectionFunctional a g) ≠
          B.apartment.affineRootGroup a (B.reflectionFunctional a g) := by
        intro heq
        have hmem : g ∈ B.apartment.affineRootGroup a (B.reflectionFunctional a g) :=
          (KPApartmentData.mem_affineRootGroup_iff hlin x).2
            ⟨hg, (B.coe_reflectionFunctional_apply hg hg1 x).le⟩
        rw [← heq, KPApartmentData.mem_affineRootGroupPlus_iff hlin x,
          ← B.coe_reflectionFunctional_apply hg hg1 x] at hmem
        exact lt_irrefl _ hmem.2
      exact hno _ (B.apartment.mem_affineRoots_of_not_double_root h2a hlin hjump) hlin

end Langlands.Geometry.Building.IntegerValuationBuildingData
