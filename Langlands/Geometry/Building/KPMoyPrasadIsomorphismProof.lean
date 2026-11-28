import Langlands.Geometry.Building.KPMoyPrasadIsomorphismStatement
import Langlands.Geometry.Building.MoyPrasadQuotientAssembly
import Langlands.Geometry.Building.MoyPrasadCommutatorGenerators
import Langlands.Geometry.Building.MoyPrasadProductCoordinates
import Langlands.Geometry.Building.MoyPrasadOrderedEmbedding
import Langlands.Geometry.Building.MoyPrasadBlockExchange
import Langlands.Geometry.Building.ChamberPositiveCollection
import Langlands.Geometry.Building.ApartmentRootRays
import Langlands.GroupScheme.Torus.WeightDecomposition
import Langlands.GroupScheme.Lie.TorusCentralizer
import Langlands.GroupScheme.Lie.KernelTargetMaps
import Langlands.GroupScheme.Rational.GenericCocharacter
import Langlands.GroupScheme.Rational.RootSupportFiniteness

/-!
# Proof of the supplied-data Moy–Prasad isomorphism (KP Theorem 13.5.1 (1))

The theorem `moyPrasadIsomorphismStatement` proves `MoyPrasadIsomorphismStatement`. Let `K` be
the product of the root blocks `U_{a,x,r} U_{2a,x,r}` of the non-divisible roots `a` and of
`Z(F)_r`. Ordered multiplication maps `K` onto `P_{x,r} / P_{x,s}`, which is abelian because
`⁅P_{x,r}, P_{x,r}⁆ ≤ P_{x,s}`. The supplied component isomorphisms, followed by the inclusions
into `𝔤_{x,r} / 𝔤_{x,s}`, map `K` onto `𝔤_{x,r} / 𝔤_{x,s}`. The second map uses the
independence of the grouped weight spaces of the maximal split torus. Both kernels consist of
the tuples of depth `s`, which gives the isomorphism.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped ValuativeRel CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.Geometry.Building

namespace MoyPrasadIsomorphism

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {P : ParahoricBuildingData G}

/-! ### Weight spaces -/

theorem nsmul_ne_zero_of_isGeneric {ν : cocharacterLattice P.S}
    (hν : IsGenericCocharacter P.i ν) {a : characterLattice P.S} (ha : a ∈ relativeRoots P.i)
    {m : ℕ} (hm : 0 < m) : m • a ≠ 0 := by
  intro h0
  apply hν a ha
  have h := congrArg (fun χ => latticePairing P.S χ ν) h0
  simp only [map_nsmul, LinearMap.smul_apply, map_zero, LinearMap.zero_apply,
    nsmul_eq_mul] at h
  rcases mul_eq_zero.1 h with h | h
  · exact absurd (by exact_mod_cast h) hm.ne'
  · exact h

/-- Under the apartment axioms, the positive multiples of a multiple `m • a` of a relative root
`a` that carry a nonzero weight space are `a` and `2a`. -/
theorem positiveWeightSpan_nsmul_le (hP : P.SatisfiesApartmentAxioms)
    {ν : cocharacterLattice P.S} (hν : IsGenericCocharacter P.i ν)
    {a : characterLattice P.S} (ha : a ∈ relativeRoots P.i) {m : ℕ} (hm : 0 < m) :
    RelativeRoot.positiveWeightSpan P.i (m • a) ≤
      ⨆ χ ∈ ({a, 2 • a} : Set (characterLattice P.S)), weightSpace P.i χ := by
  refine iSup_le fun n => ?_
  have e : (n : ℕ) • m • a = ((n : ℕ) * m) • a := (mul_nsmul' a _ _).symm
  rw [e]
  have hnm : 0 < n.1 * m := Nat.mul_pos n.2 hm
  by_cases hroot : (n.1 * m) • a ∈ relativeRoots P.i
  · rcases P.apartment.root_multiple_eq_one_or_two hP.isAffineRootSystem_extendedAffineRoots
      hP.derivativeRoots_extendedAffineRoots ha hnm hroot with h | h
    · rw [h, one_nsmul]
      exact le_biSup (fun χ => weightSpace P.i χ) (Set.mem_insert a _)
    · rw [h]
      exact le_biSup (fun χ => weightSpace P.i χ)
        (Set.mem_insert_of_mem a (Set.mem_singleton ((2 : ℕ) • a)))
  · have hbot : weightSpace P.i ((n.1 * m) • a) = ⊥ := by
      by_contra hb
      exact hroot (mem_relativeRoots.2 ⟨nsmul_ne_zero_of_isGeneric hν ha hnm, hb⟩)
    rw [hbot]
    exact bot_le

theorem rootBlockLie_mem_pairWeightSpace (hP : P.SatisfiesApartmentAxioms)
    {ν : cocharacterLattice P.S} (hν : IsGenericCocharacter P.i ν)
    (L : P.LieFiltrationData) (x : P.Apartment) {a : characterLattice P.S}
    (ha : a ∈ relativeRoots P.i) (t : NNReal) {X : GenericLie 𝒪[F] G}
    (hX : X ∈ L.rootBlockLie x ⟨a, ha⟩ t) :
    GenericLie.equiv 𝒪[F] G X ∈
      ⨆ χ ∈ ({a, 2 • a} : Set (characterLattice P.S)), weightSpace P.i χ := by
  let W := ⨆ χ ∈ ({a, 2 • a} : Set (characterLattice P.S)), weightSpace P.i χ
  let WO := (W.comap (GenericLie.equiv 𝒪[F] G).toLinearMap).restrictScalars 𝒪[F]
  have h1 : ∀ (β : relativeRoots P.i) (m : ℕ), 0 < m → β.1 = m • a → L.rootLie x β t ≤ WO := by
    intro β m hm hβ Y hY
    have hY' := L.rootLie_le_rootLieSpace x β t hY
    change GenericLie.equiv 𝒪[F] G Y ∈ W
    rw [ParahoricBuildingData.mem_rootLieSpace, hβ] at hY'
    exact positiveWeightSpan_nsmul_le hP hν ha hm hY'
  have hle : L.rootBlockLie x ⟨a, ha⟩ t ≤ WO :=
    sup_le (h1 _ 1 one_pos (one_smul _ _).symm) (iSup₂_le fun β hβ => h1 β 2 two_pos hβ)
  exact hle hX

theorem equiv_map_centralizer_mem_weightSpace_zero
    (Y : GenericLie 𝒪[F] P.centralizer.Z) :
    GenericLie.equiv 𝒪[F] G (GenericLie.map 𝒪[F] P.centralizer.j Y) ∈ weightSpace P.i 0 := by
  rw [GenericLie.map_apply, LinearEquiv.apply_symm_apply]
  apply Lie.mem_weightSpace_zero_of_mem_torusCentralizer
  rw [← P.centralizer.isRepresentedBy.2]
  exact SubgroupFunctor.mem_range.2 ⟨(GenericLie.equiv 𝒪[F] P.centralizer.Z Y).toMul.val, rfl⟩

theorem genericLie_map_centralizer_injective :
    Function.Injective (GenericLie.map 𝒪[F] P.centralizer.j) := by
  have : Mono P.centralizer.j.hom.hom := P.centralizer.isRepresentedBy.1
  intro Y Y' h
  rw [GenericLie.map_apply, GenericLie.map_apply] at h
  exact (GenericLie.equiv 𝒪[F] _).injective
    (Lie.targetMapLinear_injective P.centralizer.j F ((GenericLie.equiv 𝒪[F] G).symm.injective h))

/-! ### Independence of the root-pair weight spaces -/

/-- A sum of a vector in each `𝔤_a + 𝔤_{2a}` for the negative indivisible roots `a`, a vector of
weight `0`, and a vector in each `𝔤_a + 𝔤_{2a}` for the positive indivisible roots `a` vanishes
only if every summand does. -/
theorem eq_zero_of_sum_pairWeightSpace_eq_zero (hP : P.SatisfiesApartmentAxioms)
    {ν : cocharacterLattice P.S} (hν : IsGenericCocharacter P.i ν)
    {nneg npos : ℕ} {aneg : Fin nneg → characterLattice P.S}
    {apos : Fin npos → characterLattice P.S} (haneg : Function.Injective aneg)
    (hrneg : Set.range aneg = RelativeRoot.indivisiblePositiveRoots P.i (-ν))
    (hapos : Function.Injective apos)
    (hrpos : Set.range apos = RelativeRoot.indivisiblePositiveRoots P.i ν)
    {wn : Fin nneg → Additive (lieKernel G F)} {z : Additive (lieKernel G F)}
    {wp : Fin npos → Additive (lieKernel G F)}
    (hwn : ∀ j, wn j ∈
      ⨆ χ ∈ ({aneg j, 2 • aneg j} : Set (characterLattice P.S)), weightSpace P.i χ)
    (hz : z ∈ weightSpace P.i 0)
    (hwp : ∀ j, wp j ∈
      ⨆ χ ∈ ({apos j, 2 • apos j} : Set (characterLattice P.S)), weightSpace P.i χ)
    (hsum : ∑ j, wn j + z + ∑ j, wp j = 0) :
    (∀ j, wn j = 0) ∧ z = 0 ∧ ∀ j, wp j = 0 := by
  classical
  let : Smooth G.X.hom := P.isConnectedReductive.smooth
  have hT : IsSplitTorus P.S.toGrp := P.isMaximalSplitTorus.isSplitSubtorus.1
  have hn : ∀ j, aneg j ∈ RelativeRoot.indivisiblePositiveRoots P.i (-ν) :=
    fun j => hrneg ▸ Set.mem_range_self j
  have hp : ∀ j, apos j ∈ RelativeRoot.indivisiblePositiveRoots P.i ν :=
    fun j => hrpos ▸ Set.mem_range_self j
  let root : Fin nneg ⊕ Fin npos → characterLattice P.S := Sum.elim aneg apos
  have hind : ∀ l, root l ∈ RelativeRoot.indivisibleRoots P.i := by
    rintro (j | j)
    · exact (hn j).1
    · exact (hp j).1
  have hinj : Function.Injective root := by
    refine haneg.sumElim hapos fun j j' h => ?_
    have h1 := (hn j).2
    have h2 := (hp j').2
    rw [h, map_neg] at h1
    omega
  have hne : ∀ l, (0 : characterLattice P.S) ≠ root l ∧ (0 : characterLattice P.S) ≠ 2 • root l :=
    fun l => ⟨((mem_relativeRoots.1 (hind l).1).1).symm,
      (nsmul_ne_zero_of_isGeneric hν (hind l).1 two_pos).symm⟩
  have hndiv : ∀ l l', root l ≠ 2 • root l' := fun l l' h =>
    (hind l).2 (root l') (hind l').1 2 one_lt_two h.symm
  let T : Option (Fin nneg ⊕ Fin npos) → Set (characterLattice P.S) :=
    fun k => k.elim {0} fun l => {root l, 2 • root l}
  have hTd : Pairwise (Function.onFun Disjoint T) := by
    rintro (_ | l) (_ | l') hkk
    · exact absurd rfl hkk
    · refine Set.disjoint_left.2 fun χ h1 h2 => ?_
      change χ ∈ ({0} : Set (characterLattice P.S)) at h1
      change χ ∈ ({root l', 2 • root l'} : Set (characterLattice P.S)) at h2
      rw [Set.mem_singleton_iff] at h1
      rw [Set.mem_insert_iff, Set.mem_singleton_iff, h1] at h2
      rcases h2 with h2 | h2
      · exact (hne l').1 h2
      · exact (hne l').2 h2
    · refine Set.disjoint_left.2 fun χ h1 h2 => ?_
      change χ ∈ ({0} : Set (characterLattice P.S)) at h2
      change χ ∈ ({root l, 2 • root l} : Set (characterLattice P.S)) at h1
      rw [Set.mem_singleton_iff] at h2
      rw [Set.mem_insert_iff, Set.mem_singleton_iff, h2] at h1
      rcases h1 with h1 | h1
      · exact (hne l).1 h1
      · exact (hne l).2 h1
    · refine Set.disjoint_left.2 fun χ h1 h2 => hkk ?_
      change χ ∈ ({root l, 2 • root l} : Set (characterLattice P.S)) at h1
      change χ ∈ ({root l', 2 • root l'} : Set (characterLattice P.S)) at h2
      rw [Set.mem_insert_iff, Set.mem_singleton_iff] at h1 h2
      refine congrArg some (hinj ?_)
      rcases h1 with rfl | rfl <;> rcases h2 with h2 | h2
      · exact h2
      · exact absurd h2 (hndiv l l')
      · exact absurd h2.symm (hndiv l' l)
      · rcases P.apartment.root_eq_or_twice_of_common_positive_multiple P.centralizer hP hT
          (hind l).1 (hind l').1 two_pos two_pos h2 with h | h | h
        · exact h
        · exact absurd h (hndiv l l')
        · exact absurd h (hndiv l' l)
  have hI := iSupIndep_biSup_of_pairwise_disjoint
    (isInternal_weightSpace_of_isSplitTorus F G P.S hT P.i).submodule_iSupIndep T hTd
  rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero] at hI
  let v : Option (Fin nneg ⊕ Fin npos) → Additive (lieKernel G F) :=
    fun k => k.elim z fun l => Sum.elim wn wp l
  have hv : ∀ k ∈ (Finset.univ : Finset (Option (Fin nneg ⊕ Fin npos))),
      v k ∈ ⨆ χ ∈ T k, weightSpace P.i χ := by
    rintro (_ | j | j) -
    · exact le_biSup (fun χ => weightSpace P.i χ) (Set.mem_singleton (0 : characterLattice P.S)) hz
    · exact hwn j
    · exact hwp j
  have hv0 : ∑ k, v k = 0 := by
    rw [Fintype.sum_option, Fintype.sum_sum_type, ← hsum]
    change z + (∑ j, wn j + ∑ j, wp j) = _
    abel
  have h0 := hI Finset.univ v hv hv0
  exact ⟨fun j => h0 (some (Sum.inl j)) (Finset.mem_univ _), h0 none (Finset.mem_univ _),
    fun j => h0 (some (Sum.inr j)) (Finset.mem_univ _)⟩

/-- Every relative root is `a` or `2a` for an indivisible root `a` that is positive on `-ν` or
on `ν`. -/
theorem exists_eq_or_double_of_mem_relativeRoots (hP : P.SatisfiesApartmentAxioms)
    {ν : cocharacterLattice P.S} (hν : IsGenericCocharacter P.i ν)
    {nneg npos : ℕ} {aneg : Fin nneg → characterLattice P.S}
    {apos : Fin npos → characterLattice P.S}
    (hrneg : Set.range aneg = RelativeRoot.indivisiblePositiveRoots P.i (-ν))
    (hrpos : Set.range apos = RelativeRoot.indivisiblePositiveRoots P.i ν)
    {b : characterLattice P.S} (hb : b ∈ relativeRoots P.i) :
    (∃ j, b = aneg j ∨ b = 2 • aneg j) ∨ ∃ j, b = apos j ∨ b = 2 • apos j := by
  rcases lt_or_gt_of_ne (hν b hb) with hlt | hgt
  · have hb' : b ∈ positiveRelativeRoots P.i (-ν) := ⟨hb, by rw [map_neg]; omega⟩
    obtain ⟨a, ha, hba⟩ := P.apartment.exists_indivisiblePositiveRoot_eq_or_double
      hP.isAffineRootSystem_extendedAffineRoots hP.derivativeRoots_extendedAffineRoots (-ν) hb'
    rw [← hrneg] at ha
    obtain ⟨j, rfl⟩ := ha
    exact Or.inl ⟨j, hba⟩
  · obtain ⟨a, ha, hba⟩ := P.apartment.exists_indivisiblePositiveRoot_eq_or_double
      hP.isAffineRootSystem_extendedAffineRoots hP.derivativeRoots_extendedAffineRoots ν ⟨hb, hgt⟩
    rw [← hrpos] at ha
    obtain ⟨j, rfl⟩ := ha
    exact Or.inr ⟨j, hba⟩

/-! ### Root blocks in the Lie filtration -/

theorem rootLie_le_rootBlockLie (L : P.LieFiltrationData) (x : P.Apartment)
    {α β : relativeRoots P.i} (h : α.1 = β.1 ∨ α.1 = 2 • β.1) (t : NNReal) :
    L.rootLie x α t ≤ L.rootBlockLie x β t := by
  rcases h with h | h
  · rw [Subtype.ext h]
    exact le_sup_left
  · exact le_sup_of_le_right (le_iSup₂_of_le α h le_rfl)

theorem rootBlockLie_le_lieFiltration (L : P.LieFiltrationData) (x : P.Apartment)
    (α : relativeRoots P.i) (t : NNReal) :
    L.rootBlockLie x α t ≤ L.lieFiltration x t :=
  sup_le (L.rootLie_le_lieFiltration x α t)
    (iSup₂_le fun β _ => L.rootLie_le_lieFiltration x β t)

/-- Every element of `𝔤_{x,t}` is a sum of elements of the negative root blocks at depth `t`,
the image of an element of `z_t`, and elements of the positive root blocks at depth `t`. -/
theorem exists_sum_eq_of_mem_lieFiltration (L : P.LieFiltrationData) (x : P.Apartment)
    {nneg npos : ℕ} {aneg : Fin nneg → characterLattice P.S}
    {apos : Fin npos → characterLattice P.S}
    (hn : ∀ j, aneg j ∈ relativeRoots P.i) (hp : ∀ j, apos j ∈ relativeRoots P.i)
    (hcover : ∀ b ∈ relativeRoots P.i,
      (∃ j, b = aneg j ∨ b = 2 • aneg j) ∨ ∃ j, b = apos j ∨ b = 2 • apos j)
    (t : NNReal) {X : GenericLie 𝒪[F] G} (hX : X ∈ L.lieFiltration x t) :
    ∃ (wn : Fin nneg → GenericLie 𝒪[F] G) (y : GenericLie 𝒪[F] P.centralizer.Z)
      (wp : Fin npos → GenericLie 𝒪[F] G),
      (∀ j, wn j ∈ L.rootBlockLie x ⟨aneg j, hn j⟩ t) ∧ y ∈ L.centralizerLie t ∧
      (∀ j, wp j ∈ L.rootBlockLie x ⟨apos j, hp j⟩ t) ∧
      ∑ j, wn j + GenericLie.map 𝒪[F] P.centralizer.j y + ∑ j, wp j = X := by
  classical
  rw [L.lieFiltration_eq_sup_rootLie, Submodule.mem_sup] at hX
  obtain ⟨Y, hY, W, hW, rfl⟩ := hX
  obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hY
  let C : GenericLie 𝒪[F] G → Prop := fun W =>
    ∃ (wn : Fin nneg → GenericLie 𝒪[F] G) (wp : Fin npos → GenericLie 𝒪[F] G),
      (∀ j, wn j ∈ L.rootBlockLie x ⟨aneg j, hn j⟩ t) ∧
      (∀ j, wp j ∈ L.rootBlockLie x ⟨apos j, hp j⟩ t) ∧ ∑ j, wn j + ∑ j, wp j = W
  have hC : C W := by
    refine Submodule.iSup_induction _ (motive := C) hW ?_ ?_ ?_
    · intro α W hW
      rcases hcover α.1 α.2 with ⟨j, hj⟩ | ⟨j, hj⟩
      · refine ⟨Pi.single j W, 0, fun j' => ?_, fun _ => zero_mem _, ?_⟩
        · by_cases hjj : j' = j
          · subst hjj
            rw [Pi.single_eq_same]
            exact rootLie_le_rootBlockLie L x hj t hW
          · rw [Pi.single_eq_of_ne hjj]
            exact zero_mem _
        · simp only [Finset.sum_pi_single', Finset.mem_univ, ite_true, Pi.zero_apply,
            Finset.sum_const_zero, add_zero]
      · refine ⟨0, Pi.single j W, fun _ => zero_mem _, fun j' => ?_, ?_⟩
        · by_cases hjj : j' = j
          · subst hjj
            rw [Pi.single_eq_same]
            exact rootLie_le_rootBlockLie L x hj t hW
          · rw [Pi.single_eq_of_ne hjj]
            exact zero_mem _
        · simp only [Finset.sum_pi_single', Finset.mem_univ, ite_true, Pi.zero_apply,
            Finset.sum_const_zero, zero_add]
    · exact ⟨0, 0, fun _ => zero_mem _, fun _ => zero_mem _, by
        simp only [Pi.zero_apply, Finset.sum_const_zero, add_zero]⟩
    · rintro W₁ W₂ ⟨wn₁, wp₁, h1n, h1p, rfl⟩ ⟨wn₂, wp₂, h2n, h2p, rfl⟩
      refine ⟨wn₁ + wn₂, wp₁ + wp₂, fun j => add_mem (h1n j) (h2n j),
        fun j => add_mem (h1p j) (h2p j), ?_⟩
      simp only [Pi.add_apply, Finset.sum_add_distrib]
      abel
  obtain ⟨wn, wp, hwn, hwp, rfl⟩ := hC
  exact ⟨wn, y, wp, hwn, hy, hwp, by abel⟩

/-! ### The Lie quotients -/

/-- The map `(u_{a,x,r} + u_{2a,x,r}) / (u_{a,x,s} + u_{2a,x,s}) → 𝔤_{x,r} / 𝔤_{x,s}` induced by
the inclusion of the root block in the Lie filtration. -/
def rootBlockQuotientMap (L : P.LieFiltrationData) (x : P.Apartment) (α : relativeRoots P.i)
    (r s : NNReal) :
    (L.rootBlockLie x α r).toAddSubgroup ⧸
        (L.rootBlockLie x α s).toAddSubgroup.addSubgroupOf (L.rootBlockLie x α r).toAddSubgroup →+
      (L.lieFiltration x r).toAddSubgroup ⧸
        (L.lieFiltration x s).toAddSubgroup.addSubgroupOf (L.lieFiltration x r).toAddSubgroup :=
  addSubgroupQuotientMap (AddMonoidHom.id _)
    (fun _ hX => rootBlockLie_le_lieFiltration L x α r hX)
    (fun _ hX => rootBlockLie_le_lieFiltration L x α s hX)

/-- The map `z_r / z_s → 𝔤_{x,r} / 𝔤_{x,s}` induced by the differential of `Z → G`. -/
def centralizerQuotientMap (L : P.LieFiltrationData) (x : P.Apartment) (r s : NNReal) :
    (L.centralizerLie r).toAddSubgroup ⧸
        (L.centralizerLie s).toAddSubgroup.addSubgroupOf (L.centralizerLie r).toAddSubgroup →+
      (L.lieFiltration x r).toAddSubgroup ⧸
        (L.lieFiltration x s).toAddSubgroup.addSubgroupOf (L.lieFiltration x r).toAddSubgroup :=
  addSubgroupQuotientMap (GenericLie.map 𝒪[F] P.centralizer.j).toAddMonoidHom
    (fun _ hY => L.centralizerLieImage_le_lieFiltration x r (Submodule.mem_map_of_mem hY))
    (fun _ hY => L.centralizerLieImage_le_lieFiltration x s (Submodule.mem_map_of_mem hY))

theorem sum_quotientMap_mk (L : P.LieFiltrationData) (x : P.Apartment) (r s : NNReal)
    {nneg npos : ℕ} {aneg : Fin nneg → characterLattice P.S}
    {apos : Fin npos → characterLattice P.S}
    (hn : ∀ j, aneg j ∈ relativeRoots P.i) (hp : ∀ j, apos j ∈ relativeRoots P.i)
    (Xn : ∀ j, (L.rootBlockLie x ⟨aneg j, hn j⟩ r).toAddSubgroup)
    (Y : (L.centralizerLie r).toAddSubgroup)
    (Xp : ∀ j, (L.rootBlockLie x ⟨apos j, hp j⟩ r).toAddSubgroup)
    (hV : ∑ j, (Xn j : GenericLie 𝒪[F] G) + GenericLie.map 𝒪[F] P.centralizer.j Y +
      ∑ j, (Xp j : GenericLie 𝒪[F] G) ∈ (L.lieFiltration x r).toAddSubgroup) :
    ∑ j, rootBlockQuotientMap L x ⟨aneg j, hn j⟩ r s (Xn j) +
        centralizerQuotientMap L x r s Y +
        ∑ j, rootBlockQuotientMap L x ⟨apos j, hp j⟩ r s (Xp j) =
      ((⟨_, hV⟩ : (L.lieFiltration x r).toAddSubgroup) :
        (L.lieFiltration x r).toAddSubgroup ⧸
          (L.lieFiltration x s).toAddSubgroup.addSubgroupOf (L.lieFiltration x r).toAddSubgroup) := by
  simp only [rootBlockQuotientMap, centralizerQuotientMap, addSubgroupQuotientMap_mk,
    ← QuotientAddGroup.mk_sum, ← QuotientAddGroup.mk_add]
  congr 1
  apply Subtype.ext
  simp only [AddSubgroup.coe_add, AddSubmonoidClass.coe_finsetSum, AddMonoidHom.id_apply,
    LinearMap.toAddMonoidHom_coe]

/-- A sum of images of the root-block quotients and of `z_r / z_s` in `𝔤_{x,r} / 𝔤_{x,s}`
vanishes only if every summand does. -/
theorem eq_zero_of_sum_quotientMap_eq_zero (hP : P.SatisfiesApartmentAxioms)
    {ν : cocharacterLattice P.S} (hν : IsGenericCocharacter P.i ν)
    (L : P.LieFiltrationData) (x : P.Apartment) (r s : NNReal)
    {nneg npos : ℕ} {aneg : Fin nneg → characterLattice P.S}
    {apos : Fin npos → characterLattice P.S} (haneg : Function.Injective aneg)
    (hrneg : Set.range aneg = RelativeRoot.indivisiblePositiveRoots P.i (-ν))
    (hapos : Function.Injective apos)
    (hrpos : Set.range apos = RelativeRoot.indivisiblePositiveRoots P.i ν)
    (hn : ∀ j, aneg j ∈ relativeRoots P.i) (hp : ∀ j, apos j ∈ relativeRoots P.i)
    (qn : ∀ j, (L.rootBlockLie x ⟨aneg j, hn j⟩ r).toAddSubgroup ⧸
      (L.rootBlockLie x ⟨aneg j, hn j⟩ s).toAddSubgroup.addSubgroupOf
        (L.rootBlockLie x ⟨aneg j, hn j⟩ r).toAddSubgroup)
    (qz : (L.centralizerLie r).toAddSubgroup ⧸
      (L.centralizerLie s).toAddSubgroup.addSubgroupOf (L.centralizerLie r).toAddSubgroup)
    (qp : ∀ j, (L.rootBlockLie x ⟨apos j, hp j⟩ r).toAddSubgroup ⧸
      (L.rootBlockLie x ⟨apos j, hp j⟩ s).toAddSubgroup.addSubgroupOf
        (L.rootBlockLie x ⟨apos j, hp j⟩ r).toAddSubgroup)
    (h : ∑ j, rootBlockQuotientMap L x ⟨aneg j, hn j⟩ r s (qn j) +
        centralizerQuotientMap L x r s qz +
        ∑ j, rootBlockQuotientMap L x ⟨apos j, hp j⟩ r s (qp j) = 0) :
    (∀ j, qn j = 0) ∧ qz = 0 ∧ ∀ j, qp j = 0 := by
  classical
  choose Xn hXn using fun j => QuotientAddGroup.mk_surjective (qn j)
  choose Xp hXp using fun j => QuotientAddGroup.mk_surjective (qp j)
  obtain ⟨Y, rfl⟩ := QuotientAddGroup.mk_surjective qz
  obtain rfl : qn = fun j => (Xn j : _ ⧸ _) := funext fun j => (hXn j).symm
  obtain rfl : qp = fun j => (Xp j : _ ⧸ _) := funext fun j => (hXp j).symm
  have hV : ∑ j, (Xn j : GenericLie 𝒪[F] G) + GenericLie.map 𝒪[F] P.centralizer.j Y +
      ∑ j, (Xp j : GenericLie 𝒪[F] G) ∈ (L.lieFiltration x r).toAddSubgroup :=
    add_mem (add_mem (sum_mem fun j _ => rootBlockLie_le_lieFiltration L x _ r (Xn j).2)
      (L.centralizerLieImage_le_lieFiltration x r (Submodule.mem_map_of_mem Y.2)))
      (sum_mem fun j _ => rootBlockLie_le_lieFiltration L x _ r (Xp j).2)
  rw [sum_quotientMap_mk L x r s hn hp Xn Y Xp hV, QuotientAddGroup.eq_zero_iff,
    AddSubgroup.mem_addSubgroupOf] at h
  have hcover : ∀ b ∈ relativeRoots P.i,
      (∃ j, b = aneg j ∨ b = 2 • aneg j) ∨ ∃ j, b = apos j ∨ b = 2 • apos j :=
    fun b hb => exists_eq_or_double_of_mem_relativeRoots hP hν hrneg hrpos hb
  obtain ⟨wn, y, wp, hwn, hy, hwp, hsum⟩ :=
    exists_sum_eq_of_mem_lieFiltration L x hn hp hcover s h
  let E := GenericLie.equiv 𝒪[F] G
  have hI := eq_zero_of_sum_pairWeightSpace_eq_zero hP hν haneg hrneg hapos hrpos
    (wn := fun j => E ((Xn j : GenericLie 𝒪[F] G) - wn j))
    (z := E (GenericLie.map 𝒪[F] P.centralizer.j ((Y : GenericLie 𝒪[F] P.centralizer.Z) - y)))
    (wp := fun j => E ((Xp j : GenericLie 𝒪[F] G) - wp j))
    (fun j => by
      rw [map_sub]
      exact sub_mem (rootBlockLie_mem_pairWeightSpace hP hν L x (hn j) r (Xn j).2)
        (rootBlockLie_mem_pairWeightSpace hP hν L x (hn j) s (hwn j)))
    (equiv_map_centralizer_mem_weightSpace_zero _)
    (fun j => by
      rw [map_sub]
      exact sub_mem (rootBlockLie_mem_pairWeightSpace hP hν L x (hp j) r (Xp j).2)
        (rootBlockLie_mem_pairWeightSpace hP hν L x (hp j) s (hwp j)))
    (by
      have key : E (∑ j, (Xn j : GenericLie 𝒪[F] G) + GenericLie.map 𝒪[F] P.centralizer.j Y +
          ∑ j, (Xp j : GenericLie 𝒪[F] G)) -
          E (∑ j, wn j + GenericLie.map 𝒪[F] P.centralizer.j y + ∑ j, wp j) = 0 := by
        rw [hsum, sub_self]
      rw [← key]
      simp only [map_sub, map_add, map_sum, Finset.sum_sub_distrib]
      abel)
  obtain ⟨h1, h2, h3⟩ := hI
  refine ⟨fun j => ?_, ?_, fun j => ?_⟩
  · rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
    have := h1 j
    rw [LinearEquiv.map_eq_zero_iff, sub_eq_zero] at this
    change (Xn j : GenericLie 𝒪[F] G) ∈ L.rootBlockLie x ⟨aneg j, hn j⟩ s
    rw [this]
    exact hwn j
  · rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
    have h2' : GenericLie.map 𝒪[F] P.centralizer.j ((Y : GenericLie 𝒪[F] P.centralizer.Z) - y) =
        GenericLie.map 𝒪[F] P.centralizer.j 0 := by
      rw [map_zero]
      exact (LinearEquiv.map_eq_zero_iff E).1 h2
    have := genericLie_map_centralizer_injective h2'
    rw [sub_eq_zero] at this
    change (Y : GenericLie 𝒪[F] P.centralizer.Z) ∈ L.centralizerLie s
    rw [this]
    exact hy
  · rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
    have := h3 j
    rw [LinearEquiv.map_eq_zero_iff, sub_eq_zero] at this
    change (Xp j : GenericLie 𝒪[F] G) ∈ L.rootBlockLie x ⟨apos j, hp j⟩ s
    rw [this]
    exact hwp j

/-- Every element of `𝔤_{x,r} / 𝔤_{x,s}` is a sum of images of the root-block quotients and of
`z_r / z_s`. -/
theorem exists_sum_quotientMap_eq (hP : P.SatisfiesApartmentAxioms)
    {ν : cocharacterLattice P.S} (hν : IsGenericCocharacter P.i ν)
    (L : P.LieFiltrationData) (x : P.Apartment) (r s : NNReal)
    {nneg npos : ℕ} {aneg : Fin nneg → characterLattice P.S}
    {apos : Fin npos → characterLattice P.S}
    (hrneg : Set.range aneg = RelativeRoot.indivisiblePositiveRoots P.i (-ν))
    (hrpos : Set.range apos = RelativeRoot.indivisiblePositiveRoots P.i ν)
    (hn : ∀ j, aneg j ∈ relativeRoots P.i) (hp : ∀ j, apos j ∈ relativeRoots P.i)
    (q : (L.lieFiltration x r).toAddSubgroup ⧸
      (L.lieFiltration x s).toAddSubgroup.addSubgroupOf (L.lieFiltration x r).toAddSubgroup) :
    ∃ (qn : ∀ j, (L.rootBlockLie x ⟨aneg j, hn j⟩ r).toAddSubgroup ⧸
        (L.rootBlockLie x ⟨aneg j, hn j⟩ s).toAddSubgroup.addSubgroupOf
          (L.rootBlockLie x ⟨aneg j, hn j⟩ r).toAddSubgroup)
      (qz : (L.centralizerLie r).toAddSubgroup ⧸
        (L.centralizerLie s).toAddSubgroup.addSubgroupOf (L.centralizerLie r).toAddSubgroup)
      (qp : ∀ j, (L.rootBlockLie x ⟨apos j, hp j⟩ r).toAddSubgroup ⧸
        (L.rootBlockLie x ⟨apos j, hp j⟩ s).toAddSubgroup.addSubgroupOf
          (L.rootBlockLie x ⟨apos j, hp j⟩ r).toAddSubgroup),
      ∑ j, rootBlockQuotientMap L x ⟨aneg j, hn j⟩ r s (qn j) +
        centralizerQuotientMap L x r s qz +
        ∑ j, rootBlockQuotientMap L x ⟨apos j, hp j⟩ r s (qp j) = q := by
  classical
  obtain ⟨⟨X, hX⟩, rfl⟩ := QuotientAddGroup.mk_surjective q
  have hcover : ∀ b ∈ relativeRoots P.i,
      (∃ j, b = aneg j ∨ b = 2 • aneg j) ∨ ∃ j, b = apos j ∨ b = 2 • apos j :=
    fun b hb => exists_eq_or_double_of_mem_relativeRoots hP hν hrneg hrpos hb
  obtain ⟨wn, y, wp, hwn, hy, hwp, hsum⟩ :=
    exists_sum_eq_of_mem_lieFiltration L x hn hp hcover r hX
  let Xn : ∀ j, (L.rootBlockLie x ⟨aneg j, hn j⟩ r).toAddSubgroup := fun j => ⟨wn j, hwn j⟩
  let Xp : ∀ j, (L.rootBlockLie x ⟨apos j, hp j⟩ r).toAddSubgroup := fun j => ⟨wp j, hwp j⟩
  let Y : (L.centralizerLie r).toAddSubgroup := ⟨y, hy⟩
  have hV : ∑ j, (Xn j : GenericLie 𝒪[F] G) + GenericLie.map 𝒪[F] P.centralizer.j Y +
      ∑ j, (Xp j : GenericLie 𝒪[F] G) ∈ (L.lieFiltration x r).toAddSubgroup := by
    change ∑ j, wn j + GenericLie.map 𝒪[F] P.centralizer.j y + ∑ j, wp j ∈ _
    rw [hsum]
    exact hX
  refine ⟨fun j => (Xn j : _ ⧸ _), (Y : _ ⧸ _), fun j => (Xp j : _ ⧸ _), ?_⟩
  rw [sum_quotientMap_mk L x r s hn hp Xn Y Xp hV]
  congr 1
  exact Subtype.ext hsum

/-- The Lie side: from surjections of groups `An j`, `Az`, `Ap j` onto the root-block quotients
and onto `z_r / z_s`, the sum of their images in `𝔤_{x,r} / 𝔤_{x,s}` is a surjective
homomorphism from the product, whose kernel is the product of the kernels. -/
theorem exists_lieQuotient_hom (hP : P.SatisfiesApartmentAxioms)
    {ν : cocharacterLattice P.S} (hν : IsGenericCocharacter P.i ν)
    (L : P.LieFiltrationData) (x : P.Apartment) (r s : NNReal)
    {nneg npos : ℕ} {aneg : Fin nneg → characterLattice P.S}
    {apos : Fin npos → characterLattice P.S} (haneg : Function.Injective aneg)
    (hrneg : Set.range aneg = RelativeRoot.indivisiblePositiveRoots P.i (-ν))
    (hapos : Function.Injective apos)
    (hrpos : Set.range apos = RelativeRoot.indivisiblePositiveRoots P.i ν)
    (hn : ∀ j, aneg j ∈ relativeRoots P.i) (hp : ∀ j, apos j ∈ relativeRoots P.i)
    {An : Fin nneg → Type*} [∀ j, Group (An j)] {Az : Type*} [Group Az]
    {Ap : Fin npos → Type*} [∀ j, Group (Ap j)]
    (φN : ∀ j, An j →* Multiplicative ((L.rootBlockLie x ⟨aneg j, hn j⟩ r).toAddSubgroup ⧸
      (L.rootBlockLie x ⟨aneg j, hn j⟩ s).toAddSubgroup.addSubgroupOf
        (L.rootBlockLie x ⟨aneg j, hn j⟩ r).toAddSubgroup))
    (hφN : ∀ j, Function.Surjective (φN j))
    (φZ : Az →* Multiplicative ((L.centralizerLie r).toAddSubgroup ⧸
      (L.centralizerLie s).toAddSubgroup.addSubgroupOf (L.centralizerLie r).toAddSubgroup))
    (hφZ : Function.Surjective φZ)
    (φP : ∀ j, Ap j →* Multiplicative ((L.rootBlockLie x ⟨apos j, hp j⟩ r).toAddSubgroup ⧸
      (L.rootBlockLie x ⟨apos j, hp j⟩ s).toAddSubgroup.addSubgroupOf
        (L.rootBlockLie x ⟨apos j, hp j⟩ r).toAddSubgroup))
    (hφP : ∀ j, Function.Surjective (φP j)) :
    ∃ Λ : (∀ j, An j) × Az × (∀ j, Ap j) →* Multiplicative
        ((L.lieFiltration x r).toAddSubgroup ⧸
          (L.lieFiltration x s).toAddSubgroup.addSubgroupOf (L.lieFiltration x r).toAddSubgroup),
      Function.Surjective Λ ∧ ∀ p, Λ p = 1 ↔
        (∀ j, φN j (p.1 j) = 1) ∧ φZ p.2.1 = 1 ∧ ∀ j, φP j (p.2.2 j) = 1 := by
  classical
  let Λf : (∀ j, An j) × Az × (∀ j, Ap j) → Multiplicative
      ((L.lieFiltration x r).toAddSubgroup ⧸
        (L.lieFiltration x s).toAddSubgroup.addSubgroupOf (L.lieFiltration x r).toAddSubgroup) :=
    fun p => Multiplicative.ofAdd
      (∑ j, rootBlockQuotientMap L x ⟨aneg j, hn j⟩ r s (Multiplicative.toAdd (φN j (p.1 j))) +
        centralizerQuotientMap L x r s (Multiplicative.toAdd (φZ p.2.1)) +
        ∑ j, rootBlockQuotientMap L x ⟨apos j, hp j⟩ r s
          (Multiplicative.toAdd (φP j (p.2.2 j))))
  let Λ := MonoidHom.mk' Λf (by
    intro p q
    simp only [Λf, Prod.fst_mul, Prod.snd_mul, Pi.mul_apply, map_mul, toAdd_mul, map_add,
      Finset.sum_add_distrib, ← ofAdd_add]
    congr 1
    abel)
  refine ⟨Λ, fun m => ?_, fun p => ?_⟩
  · obtain ⟨qn, qz, qp, hq⟩ := exists_sum_quotientMap_eq hP hν L x r s hrneg hrpos hn hp
      (Multiplicative.toAdd m)
    choose pn hpn using fun j => hφN j (Multiplicative.ofAdd (qn j))
    choose pp hpp using fun j => hφP j (Multiplicative.ofAdd (qp j))
    obtain ⟨pz, hpz⟩ := hφZ (Multiplicative.ofAdd qz)
    refine ⟨(pn, pz, pp), ?_⟩
    change Λf (pn, pz, pp) = m
    simp only [Λf, hpn, hpz, hpp, toAdd_ofAdd, hq, ofAdd_toAdd]
  · change Λf p = 1 ↔ _
    simp only [Λf, ofAdd_eq_one]
    constructor
    · intro h
      obtain ⟨h1, h2, h3⟩ :=
        eq_zero_of_sum_quotientMap_eq_zero hP hν L x r s haneg hrneg hapos hrpos hn hp _ _ _ h
      exact ⟨fun j => toAdd_eq_zero.1 (h1 j), toAdd_eq_zero.1 h2,
        fun j => toAdd_eq_zero.1 (h3 j)⟩
    · rintro ⟨h1, h2, h3⟩
      simp only [h1, h2, h3, toAdd_one, map_zero, Finset.sum_const_zero, add_zero]

/-! ### The group side -/

theorem closure_filtrationBlock_eq (hP : P.SatisfiesApartmentAxioms) (x : P.Apartment) (t : ℝ)
    {a : characterLattice P.S} (ha : a ∈ relativeRoots P.i) :
    Subgroup.closure (P.apartment.filtrationBlock x (fun _ => t) a) =
      P.filtrationBlockSubgroup hP x t ha :=
  Subgroup.closure_eq (P.filtrationBlockSubgroup hP x t ha)

theorem filtrationBlockSubgroup_le_moyPrasad (hP : P.SatisfiesApartmentAxioms)
    (Zf : P.CentralizerFiltration) (x : P.Apartment) {a : characterLattice P.S}
    (ha : a ∈ relativeRoots P.i) (t : NNReal) :
    P.filtrationBlockSubgroup hP x (t : ℝ) ha ≤ Zf.moyPrasad x t := by
  rintro g ⟨v, hv, w, hw, rfl⟩
  refine (Zf.moyPrasad x t).mul_mem (Zf.filtration_le_moyPrasad x ⟨a, ha⟩ t hv) ?_
  by_cases h2a : 2 • a ∈ relativeRoots P.i
  · have hw' : w ∈ P.apartment.doubleFiltration x a (t : ℝ) := hw
    rw [P.apartment.doubleFiltration_of_mem x a _ h2a] at hw'
    exact Zf.filtration_le_moyPrasad x ⟨2 • a, h2a⟩ t hw'
  · have hw' : w ∈ P.apartment.doubleFiltration x a (t : ℝ) := hw
    rw [P.apartment.doubleFiltration_of_not_mem x a _ h2a, Subgroup.mem_bot] at hw'
    rw [hw']
    exact (Zf.moyPrasad x t).one_mem

/-- The group side: when `⁅P_{x,r}, P_{x,r}⁆ ≤ P_{x,s}`, the product of the images of the root
blocks and of `Z(F)_r` in `P_{x,r} / P_{x,s}` is a surjective homomorphism from the product of
the root blocks and `Z(F)_r` (in the ordered coordinates of KP Proposition 13.2.5(3)), whose
kernel consists of the tuples all of whose coordinates have depth `s`. -/
theorem exists_moyPrasadQuotient_hom (hP : P.SatisfiesApartmentAxioms)
    (Zf : P.CentralizerFiltration) (hZ : Zf.IsCommutatorFriendly) (x : P.Apartment)
    {r s : NNReal} (hr : 0 < r) (hrs : r ≤ s)
    (hcomm : ⁅Zf.moyPrasad x r, Zf.moyPrasad x r⁆ ≤ Zf.moyPrasad x s)
    [((Zf.moyPrasad x s).subgroupOf (Zf.moyPrasad x r)).Normal]
    {ν : cocharacterLattice P.S} (hν : IsGenericCocharacter P.i ν)
    {nneg npos : ℕ} {aneg : Fin nneg → characterLattice P.S}
    {apos : Fin npos → characterLattice P.S} (haneg : Function.Injective aneg)
    (hrneg : Set.range aneg = RelativeRoot.indivisiblePositiveRoots P.i (-ν))
    (hapos : Function.Injective apos)
    (hrpos : Set.range apos = RelativeRoot.indivisiblePositiveRoots P.i ν)
    (hn : ∀ j, aneg j ∈ relativeRoots P.i) (hp : ∀ j, apos j ∈ relativeRoots P.i) :
    ∃ Θ : (∀ j, P.filtrationBlockSubgroup hP x (r : ℝ) (hn j)) × Zf.filtration r ×
        (∀ j, P.filtrationBlockSubgroup hP x (r : ℝ) (hp j)) →*
        Zf.moyPrasad x r ⧸ (Zf.moyPrasad x s).subgroupOf (Zf.moyPrasad x r),
      Function.Surjective Θ ∧ ∀ p, Θ p = 1 ↔
        (∀ j, (p.1 j : rationalPoints G) ∈ P.filtrationBlockSubgroup hP x (s : ℝ) (hn j)) ∧
          (p.2.1 : rationalPoints P.centralizer.Z) ∈ Zf.filtration s ∧
          ∀ j, (p.2.2 j : rationalPoints G) ∈ P.filtrationBlockSubgroup hP x (s : ℝ) (hp j) := by
  classical
  let := quotientCommGroupOfCommutatorLE hcomm
  have hs : 0 < s := lt_of_lt_of_le hr hrs
  let π := QuotientGroup.mk' ((Zf.moyPrasad x s).subgroupOf (Zf.moyPrasad x r))
  let incN : ∀ j, P.filtrationBlockSubgroup hP x (r : ℝ) (hn j) →* Zf.moyPrasad x r :=
    fun j => Subgroup.inclusion (filtrationBlockSubgroup_le_moyPrasad hP Zf x (hn j) r)
  let incP : ∀ j, P.filtrationBlockSubgroup hP x (r : ℝ) (hp j) →* Zf.moyPrasad x r :=
    fun j => Subgroup.inclusion (filtrationBlockSubgroup_le_moyPrasad hP Zf x (hp j) r)
  let incZ : Zf.filtration r →* Zf.moyPrasad x r :=
    ((rationalPoints.map P.centralizer.j).comp (Zf.filtration r).subtype).codRestrict _
      (fun z => Zf.image_le_moyPrasad x r (Subgroup.mem_map_of_mem _ z.2))
  let Θf : (∀ j, P.filtrationBlockSubgroup hP x (r : ℝ) (hn j)) × Zf.filtration r ×
      (∀ j, P.filtrationBlockSubgroup hP x (r : ℝ) (hp j)) →
      Zf.moyPrasad x r ⧸ (Zf.moyPrasad x s).subgroupOf (Zf.moyPrasad x r) :=
    fun p => (∏ j, π (incN j (p.1 j))) * π (incZ p.2.1) * ∏ j, π (incP j (p.2.2 j))
  let Θ := MonoidHom.mk' Θf (by
    intro p q
    simp only [Θf, Prod.fst_mul, Prod.snd_mul, Pi.mul_apply, map_mul, Finset.prod_mul_distrib]
    ac_rfl)
  let toCoord : (∀ j, P.filtrationBlockSubgroup hP x (r : ℝ) (hn j)) × Zf.filtration r ×
      (∀ j, P.filtrationBlockSubgroup hP x (r : ℝ) (hp j)) →
      (∀ j, P.apartment.filtrationBlock x (fun _ => (r : ℝ)) (aneg j)) × Zf.filtration r ×
        (∀ j, P.apartment.filtrationBlock x (fun _ => (r : ℝ)) (apos j)) :=
    fun p => (fun j => ⟨(p.1 j : rationalPoints G), (p.1 j).2⟩, p.2.1,
      fun j => ⟨(p.2.2 j : rationalPoints G), (p.2.2 j).2⟩)
  have hmem : ∀ p, Zf.orderedMoyPrasadProduct x r aneg apos (toCoord p) ∈ Zf.moyPrasad x r := by
    intro p
    rw [← SetLike.mem_coe,
      ← Zf.range_orderedMoyPrasadProduct_eq hP hZ x r hr ν hν aneg apos hrneg hrpos]
    exact Set.mem_range_self _
  have hΘ : ∀ p, Θ p = π ⟨_, hmem p⟩ := by
    intro p
    have h : (⟨_, hmem p⟩ : Zf.moyPrasad x r) =
        (List.ofFn fun j => incN j (p.1 j)).prod * incZ p.2.1 *
          (List.ofFn fun j => incP j (p.2.2 j)).prod := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, SubmonoidClass.coe_list_prod, List.map_ofFn]
      rfl
    rw [h, map_mul, map_mul, map_list_prod, map_list_prod, List.map_ofFn, List.map_ofFn,
      List.prod_ofFn, List.prod_ofFn]
    rfl
  refine ⟨Θ, fun q => ?_, fun p => ?_⟩
  · obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective _ q
    obtain ⟨c, hc⟩ : (g : rationalPoints G) ∈
        Set.range (Zf.orderedMoyPrasadProduct x r aneg apos) := by
      rw [Zf.range_orderedMoyPrasadProduct_eq hP hZ x r hr ν hν aneg apos hrneg hrpos]
      exact g.2
    refine ⟨(fun j => ⟨(c.1 j : rationalPoints G), (c.1 j).2⟩, c.2.1,
      fun j => ⟨(c.2.2 j : rationalPoints G), (c.2.2 j).2⟩), ?_⟩
    rw [hΘ]
    congr 1
    exact Subtype.ext hc
  · rw [hΘ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    change Zf.orderedMoyPrasadProduct x r aneg apos (toCoord p) ∈ Zf.moyPrasad x s ↔ _
    constructor
    · intro h
      obtain ⟨c, hc⟩ : _ ∈ Set.range (Zf.orderedMoyPrasadProduct x s aneg apos) := by
        rw [Zf.range_orderedMoyPrasadProduct_eq hP hZ x s hs ν hν aneg apos hrneg hrpos]
        exact h
      let c' : (∀ j, P.apartment.filtrationBlock x (fun _ => (r : ℝ)) (aneg j)) ×
          Zf.filtration r × (∀ j, P.apartment.filtrationBlock x (fun _ => (r : ℝ)) (apos j)) :=
        (fun j => ⟨(c.1 j : rationalPoints G), P.apartment.filtrationBlock_antitone x (aneg j)
            (NNReal.coe_le_coe.2 hrs) (c.1 j).2⟩,
          ⟨(c.2.1 : rationalPoints P.centralizer.Z), Zf.antitone hrs c.2.1.2⟩,
          fun j => ⟨(c.2.2 j : rationalPoints G), P.apartment.filtrationBlock_antitone x (apos j)
            (NNReal.coe_le_coe.2 hrs) (c.2.2 j).2⟩)
      have hcc : Zf.orderedMoyPrasadProduct x r aneg apos c' =
          Zf.orderedMoyPrasadProduct x s aneg apos c := rfl
      have heq := Zf.orderedMoyPrasadProduct_injective x r ν aneg apos haneg hrneg hapos hrpos
        (hcc.trans hc)
      refine ⟨fun j => ?_, ?_, fun j => ?_⟩
      · have hj : (c.1 j : rationalPoints G) = (p.1 j : rationalPoints G) :=
          congrArg (fun q => ((q.1 j : rationalPoints G))) heq
        change (p.1 j : rationalPoints G) ∈ P.apartment.filtrationBlock x (fun _ => (s : ℝ)) _
        rw [← hj]
        exact (c.1 j).2
      · have hz : (c.2.1 : rationalPoints P.centralizer.Z) = (p.2.1 : rationalPoints _) :=
          congrArg (fun q => ((q.2.1 : rationalPoints P.centralizer.Z))) heq
        rw [← hz]
        exact c.2.1.2
      · have hj : (c.2.2 j : rationalPoints G) = (p.2.2 j : rationalPoints G) :=
          congrArg (fun q => ((q.2.2 j : rationalPoints G))) heq
        change (p.2.2 j : rationalPoints G) ∈ P.apartment.filtrationBlock x (fun _ => (s : ℝ)) _
        rw [← hj]
        exact (c.2.2 j).2
    · rintro ⟨h1, h2, h3⟩
      let c : (∀ j, P.apartment.filtrationBlock x (fun _ => (s : ℝ)) (aneg j)) ×
          Zf.filtration s × (∀ j, P.apartment.filtrationBlock x (fun _ => (s : ℝ)) (apos j)) :=
        (fun j => ⟨(p.1 j : rationalPoints G), h1 j⟩, ⟨(p.2.1 : rationalPoints _), h2⟩,
          fun j => ⟨(p.2.2 j : rationalPoints G), h3 j⟩)
      have hcc : Zf.orderedMoyPrasadProduct x s aneg apos c =
          Zf.orderedMoyPrasadProduct x r aneg apos (toCoord p) := rfl
      rw [← hcc, ← SetLike.mem_coe,
        ← Zf.range_orderedMoyPrasadProduct_eq hP hZ x s hs ν hν aneg apos hrneg hrpos]
      exact Set.mem_range_self c

omit [IsAffineHom G.X.hom] in
/-- Each of the three alternatives of KP §13.5 gives `s ≤ r + r`. -/
theorem le_add_self_of_moyPrasadAlternative {r s : NNReal} (halt : MoyPrasadAlternative F G r s) :
    s ≤ r + r := by
  rcases halt with ⟨-, h⟩ | ⟨r₀, n, -, -, hreq, h⟩ | ⟨h, -⟩
  · rwa [two_mul] at h
  · rw [← NNReal.coe_le_coe] at h ⊢
    rw [hreq]
    push_cast at h ⊢
    linarith [r₀.coe_nonneg]
  · rwa [two_mul] at h

end MoyPrasadIsomorphism

open MoyPrasadIsomorphism in
/-- KP Theorem 13.5.1 (1) on supplied data: under the apartment axioms, the filtration axioms
and the double-root commutator condition, for `0 < r ≤ s` satisfying one of the alternatives of
KP §13.5, the isomorphisms `Z(F)_r / Z(F)_s ≅ z_r / z_s` and, for every non-divisible relative
root, of the root blocks, give `P_{x,r} / P_{x,s} ≅ 𝔤_{x,r} / 𝔤_{x,s}`. -/
theorem moyPrasadIsomorphismStatement : MoyPrasadIsomorphismStatement.{u} := by
  intro F _ _ _ _ G _ P Zf L hP hZ hZ2 x r s hr hrs halt hZiso hroot
  classical
  have : Smooth G.X.hom := P.isConnectedReductive.smooth
  have hfin (v : cocharacterLattice P.S) :
      (RelativeRoot.indivisiblePositiveRoots P.i v).Finite :=
    (P.isMaximalSplitTorus.1.1.finite_relativeRoots P.i).subset (fun _ ha => ha.1.1)
  obtain ⟨ν, hν⟩ := P.isMaximalSplitTorus.isSplitSubtorus.1.exists_genericCocharacter P.i
  obtain ⟨nneg, eneg, hrneg⟩ := (hfin (-ν)).fin_embedding
  obtain ⟨npos, epos, hrpos⟩ := (hfin ν).fin_embedding
  have hn' (j : Fin nneg) : eneg j ∈ RelativeRoot.indivisiblePositiveRoots P.i (-ν) :=
    hrneg ▸ Set.mem_range_self j
  have hp' (j : Fin npos) : epos j ∈ RelativeRoot.indivisiblePositiveRoots P.i ν :=
    hrpos ▸ Set.mem_range_self j
  have hn (j : Fin nneg) : eneg j ∈ relativeRoots P.i := (hn' j).1.1
  have hp (j : Fin npos) : epos j ∈ relativeRoots P.i := (hp' j).1.1
  have hcomm : ⁅Zf.moyPrasad x r, Zf.moyPrasad x r⁆ ≤ Zf.moyPrasad x s :=
    (Zf.commutator_moyPrasad_le hP hZ hZ2 x r r).trans
      (Zf.moyPrasad_antitone x (le_add_self_of_moyPrasadAlternative halt))
  have := subgroupOf_normal_of_commutator_le hcomm
  obtain ⟨Θ, hΘs, hΘk⟩ := exists_moyPrasadQuotient_hom hP Zf hZ.1 x hr hrs hcomm hν
    eneg.injective hrneg epos.injective hrpos hn hp
  obtain ⟨φZ, hφZs, hφZk⟩ := hZiso
  have hblock {a : characterLattice P.S} (ha : a ∈ RelativeRoot.indivisibleRoots P.i) :
      HasMoyPrasadQuotientIso (P.filtrationBlockSubgroup hP x (r : ℝ) ha.1)
        (P.filtrationBlockSubgroup hP x (s : ℝ) ha.1)
        (L.rootBlockLie x ⟨a, ha.1⟩ r).toAddSubgroup
        (L.rootBlockLie x ⟨a, ha.1⟩ s).toAddSubgroup := by
    have h : HasMoyPrasadQuotientIso
        (Subgroup.closure (P.apartment.filtrationBlock x (fun _ => (r : ℝ)) a))
        (Subgroup.closure (P.apartment.filtrationBlock x (fun _ => (s : ℝ)) a))
        (L.rootBlockLie x ⟨a, ha.1⟩ r).toAddSubgroup
        (L.rootBlockLie x ⟨a, ha.1⟩ s).toAddSubgroup :=
      hroot ⟨a, ha.1⟩ fun β hβ => ha.2 β.1 β.2 2 one_lt_two hβ.symm
    rwa [closure_filtrationBlock_eq hP x (r : ℝ) ha.1,
      closure_filtrationBlock_eq hP x (s : ℝ) ha.1] at h
  choose φN hφNs hφNk using fun j => hblock (hn' j).1
  choose φP hφPs hφPk using fun j => hblock (hp' j).1
  obtain ⟨Λ, hΛs, hΛk⟩ := exists_lieQuotient_hom hP hν L x r s eneg.injective hrneg
    epos.injective hrpos hn hp φN hφNs φZ hφZs φP hφPs
  refine hasMoyPrasadQuotientIso_of_ker_eq Θ hΘs Λ hΛs ?_
  ext p
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker, hΘk, hΛk]
  refine and_congr (forall_congr' fun j => ?_) (and_congr ?_ (forall_congr' fun j => ?_))
  · rw [← MonoidHom.mem_ker, hφNk j, Subgroup.mem_subgroupOf]
  · rw [← MonoidHom.mem_ker, hφZk, Subgroup.mem_subgroupOf]
  · rw [← MonoidHom.mem_ker, hφPk j, Subgroup.mem_subgroupOf]

end Langlands.Geometry.Building
