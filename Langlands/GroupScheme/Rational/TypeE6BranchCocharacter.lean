import Langlands.GroupScheme.Reductive.TitsIndexStarProof
import Langlands.GroupScheme.Reductive.TitsIndexExistenceProof
import Langlands.GroupScheme.Rational.RelativeRootSystemProof
import Langlands.GroupScheme.Rational.IndependentStandardCocharacter
import Langlands.GroupScheme.SimplyConnected.LocalRankOneTitsIndexNormalization
import Langlands.GroupScheme.SimplyConnected.TypeDVectorQuotient
import Langlands.GroupScheme.Derived.SplitTorusCommutators
import Langlands.LinearAlgebra.CartanE6Root
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex

/-! # The split cocharacter through the branch vertex in type E6 -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.LinearAlgebra.RationalSpan
open scoped BigOperators CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace TitsIndexData

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G)
  (e : d.Vertex ≃ Fin 6)
  (hCartan : ∀ a b, d.cartan a b = CartanMatrix.E 6 (e a) (e b))

include hCartan

/-- Both possible star permutations of E6 fix the short-arm end, vertex 1. -/
theorem star_eq_typeE6Branch (σ : SeparableClosure k ≃ₐ[k] SeparableClosure k) :
    d.star σ (e.symm 1) = e.symm 1 := by
  apply e.injective
  rcases d.star_cases_of_cartan e Langlands.CartanE6Root.symmetry hCartan
    Langlands.CartanE6Root.eq_id_or_symmetry_of_preserves σ with h | h
  · exact h (e.symm 1)
  · rw [h, Equiv.apply_symm_apply]
    rfl

/-- If the short-arm end of E6 is distinguished, the actual maximal split torus
has an integral cocharacter with positive pairing at that vertex and zero pairing
at the other five absolute simple roots. -/
theorem exists_scaled_typeE6BranchCocharacter
    (hmark : e.symm 1 ∈ d.distinguishedVertices) :
    ∃ m : ℤ, 0 < m ∧ ∃ ν : cocharacterLattice d.splitTorus,
      ∀ a : d.Vertex, latticePairing d.splitTorus (d.rootRestriction a.val) ν =
        if e a = 1 then m else 0 := by
  classical
  let a₀ := e.symm 1
  let hT := d.maximalSplit.1.1
  let : Mono d.splitInclusion.hom.hom.left := d.maximalSplit.1.2.mono
  let hRoots := relativeRootSystem k G d.isSemisimple.isConnectedReductive _ _ d.maximalSplit
  let α (b : simpleRelativeRoots d.splitInclusion d.positiveCocharacter) :=
    (b : characterLattice d.splitTorus)
  obtain ⟨hOrbit, E, hE⟩ := titsIndexRelativeSimpleRoots k G d
  let b₀ := E (d.orbitClass ⟨a₀, hmark⟩)
  obtain ⟨m, hm, ν, hν⟩ := hT.exists_scaled_pairings α
    (hRoots.linearIndependent_simpleRelativeRoots d.splitInclusion d.positiveCocharacter hT d.generic)
    (fun b => if b = b₀ then 1 else 0)
  refine ⟨m, hm, ν, fun a => ?_⟩
  by_cases ha : a ∈ d.distinguishedVertices
  · let b := E (d.orbitClass ⟨a, ha⟩)
    have hab : b = b₀ ↔ a = a₀ := by
      constructor
      · intro h
        have heq : d.rootRestriction a.val = d.rootRestriction a₀.val := by
          rw [← hE ⟨a, ha⟩, ← hE ⟨a₀, hmark⟩]
          exact congrArg Subtype.val h
        obtain ⟨σ, hσ⟩ := (hOrbit ⟨a₀, hmark⟩ ⟨a, ha⟩).mp heq.symm
        exact hσ.symm.trans (d.star_eq_typeE6Branch e hCartan σ)
      · rintro rfl
        rfl
    have heq : α b = d.rootRestriction a.val := hE ⟨a, ha⟩
    have heqa : a = a₀ ↔ e a = 1 := e.eq_symm_apply
    simpa only [heq, hab, heqa, mul_ite, mul_one, mul_zero] using hν b
  · have hz : d.rootRestriction a.val = 0 := by
      simpa only [distinguishedVertices, zeroVertices, Set.mem_compl_iff, Set.mem_ofPred_eq,
        not_ne_iff] using ha
    have hne : e a ≠ 1 := fun h => ha ((e.eq_symm_apply.mpr h).symm ▸ hmark)
    simp only [hz, map_zero, LinearMap.zero_apply, ite_eq_right hne]

local notation "b" => algebraBaseMap k (SeparableClosure k)

/-- The integral fundamental coweight of the short-arm vertex, expressed in the
simple coroots of the actual E6 datum. -/
def typeE6BranchCoweight :
    cocharacterLattice ((CommGroupScheme.baseChange b).obj d.pinning.torus) :=
  ∑ i : Fin 6, Langlands.CartanE6Root.coefficients i •
    d.pinning.rootDatum.coroot (e.symm i).val

theorem typeE6BranchCoweight_pairing (a : d.Vertex) :
    d.pinning.rootDatum.root' a.val (d.typeE6BranchCoweight e) =
      if e a = 1 then 1 else 0 := by
  have hcalc : ∀ j : Fin 6,
    (∑ i : Fin 6, Langlands.CartanE6Root.coefficients i * CartanMatrix.E 6 j i) =
      if j = 1 then 1 else 0 := by decide
  change d.pinning.rootDatum.toLinearMap (d.pinning.rootDatum.root a.val) _ = _
  simp only [typeE6BranchCoweight, map_sum, map_zsmul,
    d.pinning.rootDatum.root_coroot_eq_pairing, zsmul_eq_mul]
  change (∑ i : Fin 6, Langlands.CartanE6Root.coefficients i * d.cartan a (e.symm i)) = _
  simp only [hCartan, Equiv.apply_symm_apply, hcalc]

private theorem typeE6_simple_pairing_injective (hsc : IsSimplyConnected G)
    {x y : cocharacterLattice ((CommGroupScheme.baseChange b).obj d.pinning.torus)}
    (h : ∀ a : d.Vertex, d.pinning.rootDatum.root' a.val x =
      d.pinning.rootDatum.root' a.val y) : x = y := by
  classical
  let P := d.pinning.rootDatum
  let B := (Langlands.RootDatum.simpleCorootBasis P d.pinning.base
    (d.pinning_corootSpan_eq_top hsc)).reindex e
  let c (i : Fin 6) : ℤ := B.repr (x - y) i
  have hB (i : Fin 6) : B i = P.coroot (e.symm i).val := by
    simp only [B, Module.Basis.reindex_apply, Langlands.RootDatum.simpleCorootBasis_apply]
  have hxy : (∑ i : Fin 6, c i • P.coroot (e.symm i).val) = x - y := by
    simpa only [← hB] using B.sum_repr (x - y)
  have heq (j : Fin 6) : (∑ i : Fin 6, c i * CartanMatrix.E 6 j i) = 0 := by
    have h0 := congrArg (P.root' (e.symm j).val) hxy
    have hx : P.root' (e.symm j).val x = P.root' (e.symm j).val y := h (e.symm j)
    simp only [map_sum, map_zsmul, map_sub, hx, sub_self, zsmul_eq_mul] at h0
    change (∑ i : Fin 6, c i * P.toLinearMap (P.root (e.symm j).val)
      (P.coroot (e.symm i).val)) = 0 at h0
    simp only [P.root_coroot_eq_pairing] at h0
    change (∑ i : Fin 6, c i * d.cartan (e.symm j) (e.symm i)) = 0 at h0
    simpa only [hCartan, Equiv.apply_symm_apply] using h0
  have hrow (j : Fin 6) :
      c 0 * CartanMatrix.E 6 j 0 + c 1 * CartanMatrix.E 6 j 1 +
      c 2 * CartanMatrix.E 6 j 2 + c 3 * CartanMatrix.E 6 j 3 +
      c 4 * CartanMatrix.E 6 j 4 + c 5 * CartanMatrix.E 6 j 5 = 0 := by
    have hj := heq j
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hj
    simp only [add_assoc]
    exact hj
  have h0 := hrow 0
  have h1 := hrow 1
  have h2 := hrow 2
  have h3 := hrow 3
  have h4 := hrow 4
  have h5 := hrow 5
  have hc : ∀ i, c i = 0 := by
    norm_num [CartanMatrix.E_six_eq] at h0 h1 h2 h3 h4 h5
    intro i
    fin_cases i
    · change c 0 = 0
      omega
    · change c 1 = 0
      omega
    · change c 2 = 0
      omega
    · change c 3 = 0
      omega
    · change c 4 = 0
      omega
    · change c 5 = 0
      omega
  apply sub_eq_zero.mp
  simpa only [hc, zero_smul, Finset.sum_const_zero] using hxy.symm

set_option backward.isDefEq.respectTransparency false in
/-- The branch coweight descends to a primitive split cocharacter. Its
absolute representatives have the same simple-root pairings across forms. -/
theorem exists_typeE6BranchCocharacter (hsc : IsSimplyConnected G)
    (hmark : e.symm 1 ∈ d.distinguishedVertices) :
    ∃ ν : cocharacterLattice d.splitTorus,
      IsClosedSubgroup (CommGroupScheme.groupHom ν ≫ d.splitInclusion) ∧
      cocharacterLattice.baseChange b d.pinning.torus (ν ≫ d.torusMap) =
        d.typeE6BranchCoweight e := by
  obtain ⟨m, hm, mu, hmu⟩ := d.exists_scaled_typeE6BranchCocharacter e hCartan hmark
  let S' := (CommGroupScheme.baseChange b).obj d.splitTorus
  let T' := (CommGroupScheme.baseChange b).obj d.pinning.torus
  let i := (CommGroupScheme.baseChange b).map d.torusMap
  let mu' := cocharacterLattice.baseChange b d.splitTorus mu
  let lambda' := d.typeE6BranchCoweight e
  have hmu' : mu' ≫ i = m • lambda' := by
    apply d.typeE6_simple_pairing_injective e hCartan hsc
    intro a
    change d.pinning.rootDatum.toLinearMap (d.pinning.rootDatum.root a.val) (mu' ≫ i) =
      d.pinning.rootDatum.root' a.val (m • lambda')
    rw [d.pinning.isRootDatum.1, ← TitsIndexExistence.latticePairing_restriction
      d.maximalSplit.1.1 d.torusMap _ mu]
    change latticePairing d.splitTorus (d.rootRestriction a.val) mu =
      d.pinning.rootDatum.root' a.val (m • d.typeE6BranchCoweight e)
    rw [hmu, map_zsmul, d.typeE6BranchCoweight_pairing e hCartan a, zsmul_eq_mul,
      mul_ite, mul_one, mul_zero, Int.cast_id]
  have hi₀ : IsClosedSubgroup (CommGroupScheme.groupHom d.torusMap) :=
    IsClosedSubgroup.of_comp d.maximalTorus.2.1 (d.square.symm ▸ d.maximalSplit.1.2)
  have hi : IsClosedSubgroup (CommGroupScheme.groupHom i) := hi₀.baseChange b
  let : Mono (CommGroupScheme.groupHom i).hom.hom.left := hi.mono
  let : Mono (CommGroupScheme.groupHom i).hom.hom := Over.mono_of_mono_left _
  have hrep : (SubgroupFunctor.range (CommGroupScheme.groupHom i)).IsRepresentedBy
      (CommGroupScheme.groupHom i) := ⟨inferInstance, rfl⟩
  have hland : m • lambda' ∈ cocharactersLandingIn (𝟙 T'.toGrp)
      (SubgroupFunctor.range (CommGroupScheme.groupHom i)) := by
    intro U t
    apply SubgroupFunctor.mem_range.mpr
    refine ⟨t ≫ (CommGroupScheme.groupHom mu').hom.hom, ?_⟩
    change (t ≫ (CommGroupScheme.groupHom mu').hom.hom) ≫
      (CommGroupScheme.groupHom i).hom.hom =
      t ≫ (CommGroupScheme.groupHom (m • lambda') ≫ 𝟙 T'.toGrp).hom.hom
    rw [Category.comp_id]
    rw [← hmu', comp_groupHom_comp]
  have hlambda' := mem_cocharactersLandingIn_of_zsmul_mem (𝟙 T'.toGrp) hi hm.ne' hland
  have hrange : SubgroupFunctor.range (CommGroupScheme.groupHom lambda') ≤
      SubgroupFunctor.range (CommGroupScheme.groupHom i) := by
    intro U t ht
    obtain ⟨w, rfl⟩ := SubgroupFunctor.mem_range.mp ht
    simpa using hlambda' U w
  let l : (Gm (Spec (CommRingCat.of (SeparableClosure k)))).toGrp ⟶ S'.toGrp :=
    hrep.factorHom (CommGroupScheme.groupHom lambda') hrange
  let E := cocharacterLattice.baseChangeEquiv b d.splitTorus d.maximalSplit.1.1
  let ν := E.symm (Additive.ofMul l)
  have hν' : cocharacterLattice.baseChange b d.splitTorus ν ≫ i = lambda' := by
    rw [← cocharacterLattice.baseChangeEquiv_apply b d.splitTorus d.maximalSplit.1.1]
    change E (E.symm (Additive.ofMul l)) ≫ i = lambda'
    rw [E.apply_symm_apply]
    exact congrArg Additive.ofMul (hrep.factorHom_comp (CommGroupScheme.groupHom lambda') hrange)
  refine ⟨ν, ?_, by rwa [cocharacterLattice.baseChange_comp]⟩
  let χ := d.rootRestriction (e.symm 1).val
  have hχν : latticePairing d.splitTorus χ ν = 1 := by
    change latticePairing d.splitTorus
      ((characterLattice.baseChangeEquiv b d.splitTorus d.maximalSplit.1.1).symm
        (i ≫ d.pinning.rootDatum.root (e.symm 1).val)) ν = 1
    rw [TitsIndexExistence.latticePairing_restriction d.maximalSplit.1.1 d.torusMap _ ν,
      hν', ← d.pinning.isRootDatum.1]
    exact (d.typeE6BranchCoweight_pairing e hCartan (e.symm 1)).trans (by simp)
  have hretract : ν ≫ χ = 𝟙 (Gm (Spec (CommRingCat.of k))) := by
    apply (gmEndEquiv k).injective
    rw [← latticePairing_apply, hχν]
    simp
  have hclosed : IsClosedSubgroup (CommGroupScheme.groupHom ν) := by
    let f := (CommGroupScheme.groupHom ν).hom.hom.left
    let g := (CommGroupScheme.groupHom χ).hom.hom.left
    have hfg : f ≫ g = 𝟙 (Gm (Spec (CommRingCat.of k))).X.left :=
      congrArg (fun p => (CommGroupScheme.groupHom p).hom.hom.left) hretract
    let : IsAffineHom d.splitTorus.X.hom := d.maximalSplit.1.1.isAffineHom
    let : IsAffineHom (Gm (Spec (CommRingCat.of k))).X.hom := isSplitTorus_gm.isAffineHom
    let : IsAffine d.splitTorus.X.left := isAffine_of_isAffineHom d.splitTorus.X.hom
    let : IsAffine (Gm (Spec (CommRingCat.of k))).X.left :=
      isAffine_of_isAffineHom (Gm (Spec (CommRingCat.of k))).X.hom
    let : IsAffineHom g := inferInstance
    let : IsClosedImmersion (f ≫ g) := hfg.symm ▸ inferInstance
    exact IsClosedImmersion.of_comp f g
  exact hclosed.comp d.maximalSplit.1.2

end TitsIndexData

/-- Bourbaki's short-arm vertex α₂ is distinguished in an actual E6 index over a
number field without real places. -/
def NumberFieldTotallyComplexTypeE6BranchDistinguishedStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F], NumberField.IsTotallyComplex F →
    ∀ (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
      [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G) (e : d.Vertex ≃ Fin 6),
      IsSimplyConnected G → IsAbsolutelyAlmostSimple G →
      (∀ a b, d.cartan a b = CartanMatrix.E 6 (e a) (e b)) →
      e.symm 1 ∈ d.distinguishedVertices

end Langlands.GroupScheme
