import Langlands.GroupScheme.Rational.RootSubgroupRealizationProof
import Langlands.GroupScheme.Rational.RootHeisenbergNormalForm
import Langlands.GroupScheme.CentralIsogeny.Basic
import Langlands.GroupScheme.Torus.WeightDecomposition
import Langlands.Geometry.Building.KPFiltrationTopology
import Langlands.Geometry.Building.ValuationAffineRootSystems

/-! # The derivative of the affine roots under V 7 -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

variable {k : Type u} [Field k] {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}

/-- A Lie vector of weight `a` that lies in the span of the weight spaces of the positive
multiples of `2a` is zero. -/
theorem eq_zero_of_mem_weightSpace_of_mem_positiveWeightSpan_two_smul
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (hS : IsSplitTorus S.toGrp) (i : S.toGrp ⟶ G) {a : characterLattice S} (ha : a ≠ 0)
    {X : Additive (lieKernel G k)} (hX : X ∈ weightSpace i a)
    (hX2 : X ∈ positiveWeightSpan i (2 • a)) : X = 0 := by
  classical
  have hind := (isInternal_weightSpace_of_isSplitTorus k G S hS i).submodule_iSupIndep
  have hle : positiveWeightSpan i (2 • a) ≤ ⨆ (χ) (_ : χ ≠ a), weightSpace i χ := by
    refine iSup_le fun n => le_iSup₂_of_le (n.val • 2 • a) ?_ le_rfl
    intro h
    have hn := n.property
    have h' : (2 * n.val - 1) • a + a = 0 + a := by
      rw [← succ_nsmul, zero_add, smul_smul] at *
      rw [show 2 * n.val - 1 + 1 = n.val * 2 by omega]
      exact h
    exact hS.nsmul_ne_zero ha (by omega) (add_right_cancel h')
  exact (Submodule.disjoint_def.1 (hind a)) X hX (hle hX2)

/-- **A multipliable root group is larger than its doubled root group on rational points.**
For a multipliable relative root `a` of a maximal split torus, some rational point of `U_a`
does not lie in `U_{2a}`. -/
theorem exists_mem_rootGroupPoints_not_mem_two_smul [IsAffineHom G.X.hom] [Smooth G.X.hom]
    (hG : IsConnectedReductive G) {i : S.toGrp ⟶ G} (hi : IsMaximalSplitTorus i)
    {a : characterLattice S} (ha : a ∈ relativeRoots i) (h2a : 2 • a ∈ relativeRoots i)
    (hhigh : ∀ n : ℕ, 3 ≤ n → n • a ∉ relativeRoots i) :
    ∃ g ∈ (subgroup i a).carrier (Over.mk (𝟙 _)),
      g ∉ (subgroup i (2 • a)).carrier (Over.mk (𝟙 _)) := by
  have ha0 : a ≠ 0 := (mem_relativeRoots.mp ha).1
  have hS : IsSplitTorus S.toGrp := hi.1.1
  obtain ⟨U, j, hj, hjc, -, -, -, -, -, hLie⟩ := rootSubgroupRealization k G hG S i hi a ha
  obtain ⟨U₂, j₂, hj₂, -, -, -, -, -, -, hLie₂⟩ :=
    rootSubgroupRealization k G hG S i hi (2 • a) h2a
  let : IsAffineHom U.X.hom := hjc.isAffineHom
  obtain ⟨C⟩ := nonempty_doubleRootCommutatorPairing hS i ha0 hhigh hj hj₂
  obtain ⟨N⟩ := nonempty_heisenbergNormalForm C hS ha0 hhigh
  have hker : ∀ (T : Over (Spec (CommRingCat.of k))) (h : T ⟶ U.X),
      h ≫ C.q.hom.hom = 1 → h ≫ j.hom.hom ∈ (subgroup i (2 • a)).carrier T := by
    intro T h hh
    have hmem : h ∈ (SubgroupFunctor.range (kernelι C.q)).carrier T :=
      (mem_range_kernelι_iff C.q h).2 hh
    rw [C.isFppfQuotient.2.2.2] at hmem
    exact SubgroupFunctor.mem_comap.1 hmem
  -- A nonzero Lie vector of weight `a` has a nontrivial image in the quotient `V`.
  obtain ⟨X, hX, hX0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (mem_relativeRoots.mp ha).2
  have hXpos : X ∈ positiveWeightSpan i a := by
    have hle := le_iSup (fun n : {n : ℕ // 0 < n} => weightSpace i (n.val • a)) ⟨1, one_pos⟩
    exact hle (by simpa only [one_smul] using hX)
  have hXU : X.toMul.val ∈ (SubgroupFunctor.range j).carrier _ := by
    rw [hj.2]
    exact (hLie X).2 hXpos
  obtain ⟨h, hh⟩ := hXU
  have hq : h ≫ C.q.hom.hom ≠ 1 := by
    intro hq
    apply hX0
    refine eq_zero_of_mem_weightSpace_of_mem_positiveWeightSpan_two_smul hS i ha0 hX
      ((hLie₂ X).1 ?_)
    rw [← hh]
    exact hker _ h hq
  -- So `V` has positive dimension, and it has a nontrivial rational point.
  obtain ⟨⟨d, e, -⟩, -⟩ := C.weightVectorStructure
  have hd : 0 < d := by
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · exfalso
      apply hq
      apply (e _).injective
      rw [map_one]
      exact Subsingleton.elim _ _
    · exact hd
  let T₀ : Over (Spec (CommRingCat.of k)) := Over.mk (𝟙 _)
  have h10 : (1 : Γ(T₀.left, ⊤)) ≠ 0 := by
    intro h10
    have := congrArg (Scheme.ΓSpecIso (CommRingCat.of k)).hom h10
    rw [map_one, map_zero] at this
    exact one_ne_zero this
  let x : T₀ ⟶ C.V.X := (e T₀).symm (Multiplicative.ofAdd (Pi.single ⟨0, hd⟩ 1))
  have hx : x ≠ 1 := by
    intro hx
    have := congrArg (fun y => (e T₀ y).toAdd ⟨0, hd⟩) hx
    simp only [x, MulEquiv.apply_symm_apply, toAdd_ofAdd, Pi.single_eq_same, map_one,
      toAdd_one, Pi.zero_apply] at this
    exact h10 this
  refine ⟨(x ≫ N.sec) ≫ j.hom.hom, ?_, fun hmem => hx ?_⟩
  · rw [← hj.2]
    exact ⟨_, rfl⟩
  · have hmem' : x ≫ N.sec ∈ (SubgroupFunctor.range (kernelι C.q)).carrier T₀ := by
      rw [C.isFppfQuotient.2.2.2]
      exact SubgroupFunctor.mem_comap.2 hmem
    have := (mem_range_kernelι_iff C.q _).1 hmem'
    rwa [Category.assoc, N.sec_comp, Category.comp_id] at this

end Langlands.GroupScheme.RelativeRoot

namespace Langlands.Geometry.Building.ValuationBuildingData

open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    (B : ValuationBuildingData G)

/-- V 4: `U_{2a,x,2r} ⊆ U_{a,x,r}`. -/
theorem filtration_two_smul_le {a : relativeRoots B.i}
    (h2a : 2 • (a : characterLattice B.S) ∈ relativeRoots B.i) (x : B.Apartment) (r : ℝ) :
    B.filtration x (2 • (a : characterLattice B.S)) (2 * r) ≤ B.filtration x a r := by
  intro v hv
  rw [KPApartmentData.mem_filtration] at hv ⊢
  refine ⟨RelativeRoot.double_subgroup_le B.i a (Over.mk (𝟙 _)) hv.1, ?_⟩
  have hd := hv.2
  rw [x.isValuation.double a a.property h2a v hv.1, two_nsmul] at hd
  induction hval : x.val a v using WithTop.recTopCoe with
  | top => exact le_top
  | coe t =>
    rw [hval, ← WithTop.coe_add, WithTop.coe_le_coe] at hd
    rw [WithTop.coe_le_coe]
    linarith

/-- One step of KP Lemma 6.3.9. If no affine root has derivative `a`, then every
`u ∈ U_a(F) ∖ {1}` is a product `u' w` with `x_a(u') > x_a(u)` and `w ∈ U_{2a,x,2x_a(u)}`. -/
theorem exists_mul_of_forall_not_mem_affineRoots {a : relativeRoots B.i}
    (h2a : 2 • (a : characterLattice B.S) ∈ relativeRoots B.i)
    (hno : ∀ ψ ∈ B.affineRoots, ψ.linear ≠ rootForm B.i a)
    {u : rationalPoints G} (hu : u ∈ B.rootGroup a) (hu1 : u ≠ 1) (x : B.Apartment) :
    ∃ u' w : rationalPoints G, u' * w = u ∧ u' ∈ B.rootGroup a ∧
      ((B.reflectionFunctional a u x : ℝ) : WithTop ℝ) < x.val a u' ∧
      w ∈ B.filtration x (2 • (a : characterLattice B.S))
        (2 * B.reflectionFunctional a u x) := by
  have hlin : (B.reflectionFunctional a u).linear = rootForm B.i a :=
    B.reflectionFunctional_linear a u
  have hψ : B.reflectionFunctional a u ∉ B.affineRoots := fun h => hno _ h hlin
  have huψ : u ∈ B.apartment.affineRootGroup a (B.reflectionFunctional a u) :=
    (KPApartmentData.mem_affineRootGroup_iff hlin x).2
      ⟨hu, (B.coe_reflectionFunctional_apply hu hu1 x).le⟩
  obtain ⟨u', hu', w, hw, huw⟩ :=
    B.apartment.affineRootGroup_subset_mul_double_of_not_mem_affineRoots h2a hlin hψ huψ
  have hlin2 : ((2 : ℝ) • B.reflectionFunctional a u).linear =
      rootForm B.i ⟨2 • (a : characterLattice B.S), h2a⟩ := by
    rw [AffineMap.smul_linear, hlin, rootForm_nsmul a.property 2 h2a]
    norm_num
  have hu'' := (KPApartmentData.mem_affineRootGroupPlus_iff hlin x).1 hu'
  have hw' := (KPApartmentData.mem_affineRootGroup_iff hlin2 x).1 hw
  refine ⟨u', w, huw, hu''.1, hu''.2, hw'.1, ?_⟩
  simpa only [AffineMap.coe_smul, Pi.smul_apply, smul_eq_mul] using hw'.2

/-- If no affine root has derivative `a`, then every `u ∈ U_{a,x,r}` can be moved into
`U_{a,x,s}`, for every `s`, by right multiplication with an element of `U_{2a,x,2r}`. This is
the iteration in the proof of KP Lemma 6.3.9; it terminates by the discreteness of the jumps
(KP Proposition 6.3.7). -/
theorem exists_mul_inv_mem_filtration_of_forall_not_mem_affineRoots {a : relativeRoots B.i}
    (h2a : 2 • (a : characterLattice B.S) ∈ relativeRoots B.i)
    (hno : ∀ ψ ∈ B.affineRoots, ψ.linear ≠ rootForm B.i a)
    (x : B.Apartment) {r : ℝ} {u : rationalPoints G} (hu : u ∈ B.filtration x a r) (s : ℝ) :
    ∃ v ∈ B.filtration x (2 • (a : characterLattice B.S)) (2 * r),
      u * v⁻¹ ∈ B.filtration x a s := by
  by_contra hcon
  push Not at hcon
  set K := B.filtration x (2 • (a : characterLattice B.S)) (2 * r) with hKdef
  have hK : ∀ v ∈ K, u * v⁻¹ ∈ B.filtration x a r := fun v hv =>
    (B.filtration x a r).mul_mem hu
      ((B.filtration x a r).inv_mem (B.filtration_two_smul_le h2a x r hv))
  have hne : ∀ v ∈ K, u * v⁻¹ ≠ 1 := fun v hv h1 =>
    hcon v hv (h1 ▸ (B.filtration x a s).one_mem)
  have hmemU : ∀ v ∈ K, u * v⁻¹ ∈ B.rootGroup a := fun v hv =>
    B.filtration_le_rootGroup x a r (hK v hv)
  -- the value of `u v⁻¹` lies in `[r, s)`
  have hval : ∀ v ∈ K, r ≤ B.reflectionFunctional a (u * v⁻¹) x ∧
      B.reflectionFunctional a (u * v⁻¹) x < s := by
    intro v hv
    have he := B.coe_reflectionFunctional_apply (hmemU v hv) (hne v hv) x
    constructor
    · have h := (KPApartmentData.mem_filtration.1 (hK v hv)).2
      rw [← he] at h
      exact_mod_cast h
    · by_contra hge
      push Not at hge
      apply hcon v hv
      refine KPApartmentData.mem_filtration.2 ⟨hmemU v hv, ?_⟩
      rw [← he]
      exact_mod_cast hge
  let T : Set ℝ := {t | ∃ v ∈ K, B.reflectionFunctional a (u * v⁻¹) x = t}
  have hTfin : T.Finite := by
    refine ((B.finite_bounded_reflectionFunctionals_of_oppositePairs B.hasOppositeFactorPairs a
      x (|r| + |s|)).image fun ψ => ψ x).subset ?_
    rintro t ⟨v, hv, rfl⟩
    refine ⟨_, ⟨u * v⁻¹, hmemU v hv, hne v hv, rfl, ?_⟩, rfl⟩
    obtain ⟨h1, h2⟩ := hval v hv
    rw [abs_le]
    constructor <;> linarith [neg_abs_le r, le_abs_self s, abs_nonneg r, abs_nonneg s]
  have hTne : T.Nonempty := ⟨_, 1, K.one_mem, rfl⟩
  obtain ⟨t, ⟨v, hv, rfl⟩, hmax⟩ := Set.exists_max_image T id hTfin hTne
  obtain ⟨u', w, huw, hu', hlt, hw⟩ :=
    B.exists_mul_of_forall_not_mem_affineRoots h2a hno (hmemU v hv) (hne v hv) x
  have hwK : w * v ∈ K := by
    refine K.mul_mem ?_ hv
    refine KPApartmentData.filtration_antitone x _ ?_ hw
    have := (hval v hv).1
    linarith
  have heq : u * (w * v)⁻¹ = u' := by
    rw [mul_inv_rev, ← mul_assoc, ← huw, mul_inv_cancel_right]
  have hT' : B.reflectionFunctional a u' x ∈ T := ⟨w * v, hwK, by rw [heq]⟩
  have hle : B.reflectionFunctional a u' x ≤ B.reflectionFunctional a (u * v⁻¹) x :=
    hmax _ hT'
  have hu'1 : u' ≠ 1 := heq ▸ hne _ hwK
  have he := B.coe_reflectionFunctional_apply hu' hu'1 x
  rw [← he] at hlt
  have hlt' : B.reflectionFunctional a (u * v⁻¹) x < B.reflectionFunctional a u' x := by
    exact_mod_cast hlt
  linarith

section Topology

local instance valuationDerivativeAmbientAffine : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom
local instance valuationDerivativeAmbientTopology : TopologicalSpace (rationalPoints G) :=
  rationalPointTopology F G.X

variable {B} (hB : B.apartment.IsTopologyCompatible)

include hB

/-- V 7 neighbourhood base, read in `G(F)`: every neighbourhood of `1` in `G(F)` contains some
`U_{a,x,s}`. -/
theorem exists_filtration_subset_of_mem_nhds (x : B.Apartment) (a : relativeRoots B.i)
    {N : Set (rationalPoints G)} (hN : N ∈ nhds (1 : rationalPoints G)) :
    ∃ s : ℝ, (B.filtration x a s : Set (rationalPoints G)) ⊆ N := by
  have hN' : ((↑) : B.rootGroup a → rationalPoints G) ⁻¹' N ∈ nhds (1 : B.rootGroup a) :=
    continuous_subtype_val.continuousAt.preimage_mem_nhds hN
  obtain ⟨s, -, hs⟩ := ((hB x.val x.mem a a.property).1).mem_iff.1 hN'
  exact ⟨s, fun g hg => hs (show (⟨g, B.filtration_le_rootGroup x a s hg⟩ : B.rootGroup a) ∈
    ((↑) : B.rootGroup a → rationalPoints G) ⁻¹' rootFiltration B.i x.val a s from hg)⟩

/-- KP Lemma 6.3.9 under V 7: if no affine root has derivative `a`, then
`U_a(F) ⊆ U_{2a}(F)`. An element `u ∈ U_a(F) ∖ {1}` lies in the closure of `U_{2a,x,2r}`
(V 7 neighbourhood base and the iteration above), and `U_{2a,x,2r}` is closed. -/
theorem mem_rootGroup_two_smul_of_forall_not_mem_affineRoots {a : relativeRoots B.i}
    (h2a : 2 • (a : characterLattice B.S) ∈ relativeRoots B.i)
    (hno : ∀ ψ ∈ B.affineRoots, ψ.linear ≠ rootForm B.i a)
    {u : rationalPoints G} (hu : u ∈ B.rootGroup a) :
    u ∈ B.rootGroup (2 • (a : characterLattice B.S)) := by
  by_cases hu1 : u = 1
  · rw [hu1]
    exact (B.rootGroup _).one_mem
  let : Smooth G.X.hom := B.isConnectedReductive.smooth
  let : IsTopologicalGroup (rationalPoints G) := rationalPoint_isTopologicalGroup F G
  let x : B.Apartment := Classical.arbitrary B.Apartment
  have hur : u ∈ B.filtration x a (B.reflectionFunctional a u x) :=
    KPApartmentData.mem_filtration.2 ⟨hu, (B.coe_reflectionFunctional_apply hu hu1 x).le⟩
  have hKc : IsClosed (B.filtration x (2 • (a : characterLattice B.S))
      (2 * B.reflectionFunctional a u x) : Set (rationalPoints G)) :=
    B.isClosed_filtration hB x ⟨2 • (a : characterLattice B.S), h2a⟩ _
  have hcl : u ∈ closure (B.filtration x (2 • (a : characterLattice B.S))
      (2 * B.reflectionFunctional a u x) : Set (rationalPoints G)) := by
    rw [mem_closure_iff_nhds_one]
    intro N hN
    obtain ⟨s, hs⟩ := exists_filtration_subset_of_mem_nhds hB x a hN
    obtain ⟨v, hv, huv⟩ :=
      B.exists_mul_inv_mem_filtration_of_forall_not_mem_affineRoots h2a hno x hur s
    refine ⟨v, hv, hs ?_⟩
    have hvu := (B.filtration x a s).inv_mem huv
    rw [mul_inv_rev, inv_inv, ← div_eq_mul_inv] at hvu
    exact hvu
  rw [hKc.closure_eq] at hcl
  exact B.filtration_le_rootGroup x _ _ hcl

/-- AS 3, derivative part, under V 7 (KP Proposition 6.3.8): `∇Ψ = Φ`. -/
theorem derivativeRoots_affineRoots_of_isTopologyCompatible :
    AffineRootSystem.derivativeRoots B.affineRoots = Set.range (rootForm B.i) := by
  apply Set.Subset.antisymm
  · rintro f ⟨ψ, ⟨a, hlin, _⟩, rfl⟩
    exact ⟨a, hlin.symm⟩
  · rintro _ ⟨a, rfl⟩
    by_contra hnot
    have hno : ∀ ψ ∈ B.affineRoots, ψ.linear ≠ rootForm B.i a :=
      fun ψ hψ h => hnot ⟨ψ, hψ, h⟩
    let : Smooth G.X.hom := B.isConnectedReductive.smooth
    have hS := B.isMaximalSplitTorus.isSplitSubtorus.1
    by_cases h2a : 2 • (a : characterLattice B.S) ∈ relativeRoots B.i
    · have hhigh : ∀ n : ℕ, 3 ≤ n → n • (a : characterLattice B.S) ∉ relativeRoots B.i := by
        intro n hn hmem
        have := B.hasOppositeFactorPairs.eq_one_or_two_of_nsmul_mem B.i hS hmem
        omega
      obtain ⟨g, hg, hg2⟩ := RelativeRoot.exists_mem_rootGroupPoints_not_mem_two_smul
        B.isConnectedReductive B.isMaximalSplitTorus a.property h2a hhigh
      exact hg2 (mem_rootGroup_two_smul_of_forall_not_mem_affineRoots hB h2a hno hg)
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

end Topology

end Langlands.Geometry.Building.ValuationBuildingData

namespace Langlands.Geometry.Building

/-- Under V 7, the derivative of the affine roots `Ψ` of every `B : ValuationBuildingData G` is
the relative root system `Φ` (the derivative part of AS 3; KP Proposition 6.3.8 and
Proposition 6.3.13). -/
def ValuationBuildingDerivativeAffineRootsStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    (B : ValuationBuildingData G), B.apartment.IsTopologyCompatible →
      AffineRootSystem.derivativeRoots B.affineRoots = Set.range (rootForm B.i)

/-- Proof of `ValuationBuildingDerivativeAffineRootsStatement`. -/
theorem valuationBuildingDerivativeAffineRoots :
    ValuationBuildingDerivativeAffineRootsStatement.{u} :=
  fun _ _ _ _ _ _ _ _ hB =>
    ValuationBuildingData.derivativeRoots_affineRoots_of_isTopologyCompatible hB

end Langlands.Geometry.Building
