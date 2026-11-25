/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.SupportDimension
public import WeilConjectures.AlgebraicGeometry.Sites.TorsionCohomologicalDimension
public import WeilConjectures.AlgebraicGeometry.Sites.CohomologyFilteredColimit
public import WeilConjectures.AlgebraicGeometry.Sites.CohomologyClopen
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import WeilConjectures.SixFunctors.OpenClosed.Conservative

/-!
# Cohomology of sheaves supported in low dimension

Let `B` be an affine scheme of finite type over a field `K` and `N` a torsion abelian étale
sheaf on `B` whose geometric stalks vanish at every point `y` with `trdeg_K κ(y) > a`. If every
closed subscheme `Z` of `B` of dimension at most `a` satisfies `cd_tor(Z) ≤ a`, then
`Hᵖ(B, N) = 0` for `p > a`
(`AlgebraicGeometry.Etale.subsingleton_H_of_isZero_upperStar_of_lt_residueFieldTrdeg`).

Indeed `N` is the directed union of its subsheaves `N_Z` of sections supported in closed subsets
`Z` of dimension at most `a` (`AlgebraicGeometry.Etale.exists_covering_supportedIn`), étale
cohomology of the quasi-compact quasi-separated `B`
commutes with directed unions (`AlgebraicGeometry.Scheme.H_map_of_directed_of_locally`), and
`N_Z = i_* i^* N_Z` for the closed immersion `i` of the reduced closed subscheme on `Z`, whose
cohomology is that of `i^* N_Z` on `Z` (`AlgebraicGeometry.Etale.bijective_edgeMap_of_isFinite`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

/-- The union of two closed subsets of dimension at most `n` of a quasi-sober `T₀` space has
dimension at most `n`. -/
theorem topologicalKrullDim_union_le {X : Type*} [TopologicalSpace X] [QuasiSober X]
    [T0Space X] {Z₁ Z₂ : Set X} (h₁ : IsClosed Z₁) (h₂ : IsClosed Z₂)
    {n : WithBot ℕ∞}
    (hZ₁ : topologicalKrullDim Z₁ ≤ n) (hZ₂ : topologicalKrullDim Z₂ ≤ n) :
    topologicalKrullDim (Z₁ ∪ Z₂ : Set X) ≤ n := by
  have key {Z : Set X} (hZ : IsClosed Z) (hn : topologicalKrullDim Z ≤ n) (z : X)
      (hz : z ∈ Z) : topologicalKrullDim (closure ({z} : Set X)) ≤ n :=
    ((Topology.IsEmbedding.inclusion (hZ.closure_subset_iff.2
      (Set.singleton_subset_iff.2 hz))).isInducing.topologicalKrullDim_le).trans hn
  refine topologicalKrullDim_le_of_forall_exists_specializes (h₁.union h₂) n fun z hz ↦
    ⟨z, specializes_rfl, ?_⟩
  rcases hz with hz | hz
  · exact key h₁ hZ₁ z hz
  · exact key h₂ hZ₂ z hz

namespace CategoryTheory.Sheaf

/-- A subsheaf of a torsion sheaf of abelian groups is torsion. -/
lemma IsTorsion.of_mono {C : Type*} [Category* C] {J : GrothendieckTopology C}
    {F G : Sheaf J AddCommGrpCat.{u}} (m : G ⟶ F) [Mono m] (hF : F.IsTorsion) :
    G.IsTorsion := by
  intro U s
  obtain ⟨S, hS, h⟩ := hF (m.hom.app U s)
  refine ⟨S, hS, fun V f hf ↦ ?_⟩
  have hinj : Function.Injective (m.hom.app (Opposite.op V)) := by
    have : Mono m.hom := (sheafToPresheaf J _).map_mono m
    have : Mono (m.hom.app (Opposite.op V)) := inferInstance
    exact (AddCommGrpCat.mono_iff_injective _).1 this
  have := h hf
  rw [← NatTrans.naturality_apply] at this
  obtain ⟨k, hk, hk'⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.1 this
  refine isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨k, hk, hinj ?_⟩
  rw [map_nsmul, hk', map_zero]

end CategoryTheory.Sheaf

namespace AlgebraicGeometry.Etale

open Scheme

variable {B : Scheme.{u}}

/-- For an open `U` with inclusion `j`, a morphism `f : G ⟶ N` is killed by the unit
`N ⟶ j_* j^* N` if and only if `j^* f = 0`. -/
lemma comp_unit_app_eq_zero_iff (U : B.Opens)
    {G N : Sheaf B.smallEtaleTopology AddCommGrpCat.{u + 1}} (f : G ⟶ N) :
    f ≫ (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} U.ι).unit.app N = 0 ↔
      (U.ι)^*[AddCommGrpCat.{u + 1}].map f = 0 := by
  set adj := upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} U.ι
  have h : f ≫ adj.unit.app N = adj.homEquiv _ _ ((U.ι)^*[AddCommGrpCat.{u + 1}].map f) := by
    rw [Adjunction.homEquiv_unit]
    exact adj.unit.naturality f
  have h0 : adj.homEquiv G ((U.ι)^*[AddCommGrpCat.{u + 1}].obj N) 0 = 0 := by
    rw [Adjunction.homEquiv_unit, Functor.map_zero, comp_zero]
  rw [h, ← h0]
  exact (adj.homEquiv _ _).injective.eq_iff

/-- The subsheaves `N_Z` grow with `Z`: if `U' ≤ U`, a morphism killed by the unit for `U` is
killed by the unit for `U'`. -/
lemma comp_unit_app_eq_zero_of_le {U U' : B.Opens} (hU : U' ≤ U)
    {G N : Sheaf B.smallEtaleTopology AddCommGrpCat.{u + 1}} (f : G ⟶ N)
    (hf : f ≫ (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} U.ι).unit.app N = 0) :
    f ≫ (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} U'.ι).unit.app N = 0 := by
  rw [comp_unit_app_eq_zero_iff] at hf ⊢
  let e := upperStarComp AddCommGrpCat.{u + 1} (B.homOfLE hU) U.ι U'.ι (B.homOfLE_ι hU).symm
  have := e.hom.naturality f
  rw [Functor.comp_map, hf, Functor.map_zero, comp_zero] at this
  rwa [← cancel_mono (e.hom.app N), zero_comp]

/-- The inclusion `N_Z ⟶ N_{Z'}` for `Z ⊆ Z'`, i.e. for opens `U' ≤ U`. -/
noncomputable def supportedInMap (N : Sheaf B.smallEtaleTopology AddCommGrpCat.{u + 1})
    {U U' : B.Opens} (hU : U' ≤ U) : supportedIn N U ⟶ supportedIn N U' :=
  kernel.lift _ (supportedInι N U) (comp_unit_app_eq_zero_of_le hU _ (kernel.condition _))

@[reassoc (attr := simp)]
lemma supportedInMap_ι (N : Sheaf B.smallEtaleTopology AddCommGrpCat.{u + 1})
    {U U' : B.Opens} (hU : U' ≤ U) :
    supportedInMap N hU ≫ supportedInι N U' = supportedInι N U :=
  kernel.lift_ι _ _ _

instance (N : Sheaf B.smallEtaleTopology AddCommGrpCat.{u + 1}) (U : B.Opens) :
    Mono (supportedInι N U) :=
  inferInstanceAs (Mono (kernel.ι _))

/-- The restriction of `N_Z` to the complement `U` of `Z` vanishes. -/
lemma isZero_upperStar_supportedIn (N : Sheaf B.smallEtaleTopology AddCommGrpCat.{u + 1})
    (U : B.Opens) : IsZero ((U.ι)^*[AddCommGrpCat.{u + 1}].obj (supportedIn N U)) :=
  IsZero.of_mono_eq_zero ((U.ι)^*[AddCommGrpCat.{u + 1}].map (supportedInι N U))
    ((comp_unit_app_eq_zero_iff U _).1 (kernel.condition _))

/-- `N_Z = i_* i^* N_Z` for the closed immersion `i` of the closed complement `Z` of `U`. -/
instance isIso_unit_app_supportedIn (N : Sheaf B.smallEtaleTopology AddCommGrpCat.{u + 1})
    (U : B.Opens) :
    IsIso ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
      (Opens.closedComplement U)).unit.app (supportedIn N U)) := by
  set i := Opens.closedComplement U
  have hij : Set.range i.base = (Set.range U.ι.base)ᶜ := by
    rw [Opens.range_closedComplement]
    exact congrArg _ U.range_ι.symm
  refine isIso_of_isIso_upperStar_map AddCommGrpCat.{u + 1} U.ι i hij _ ?_ inferInstance
  have h₁ := isZero_upperStar_supportedIn N U
  have h₂ := isZero_upperStar_lowerStar_of_disjoint_range AddCommGrpCat.{u + 1} U.ι i
    (disjoint_range_of_range_eq_compl _ _ hij)
    ((i)^*[AddCommGrpCat.{u + 1}].obj (supportedIn N U))
  exact ⟨⟨(h₁.iso h₂).inv, h₁.eq_of_src _ _, h₂.eq_of_src _ _⟩⟩

/-- **Cohomology of a sheaf supported in low dimension.** Let `B` be an affine scheme of finite
type over a field `K` (structure morphism `b`), `a ≥ 0`, and suppose that every closed
subscheme of `B` of dimension at most `a` has torsion cohomological dimension at most `a`. Let
`N` be a torsion abelian étale sheaf on `B` whose geometric stalks vanish at every point `y`
with `trdeg_K κ(y) > a`. Then `Hᵖ(B, N) = 0` for every `p > a`. -/
theorem subsingleton_H_of_isZero_upperStar_of_lt_residueFieldTrdeg {K : Type u} [Field K]
    {B : Scheme.{u}} (b : B ⟶ Spec (.of K)) [LocallyOfFiniteType b] [IsAffine B] (a : ℕ)
    (hZ : ∀ (Z : Scheme.{u}) (i : Z ⟶ B), IsClosedImmersion i →
      topologicalKrullDim Z ≤ (a : WithBot ℕ∞) → Z.HasTorsionCohomologicalDimensionLE a)
    (N : Sheaf B.smallEtaleTopology AddCommGrpCat.{u + 1}) (hN : N.IsTorsion)
    (hstalk : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ B),
      (a : Cardinal.{u}) < Scheme.residueFieldTrdeg b (s (IsLocalRing.closedPoint Ω)) →
        IsZero ((s)^*[AddCommGrpCat.{u + 1}].obj N))
    (p : ℕ) (hp : a < p) : Subsingleton (Sheaf.H N p) := by
  have : QuasiCompact b := inferInstance
  let ι := {U : B.Opens // topologicalKrullDim ((U : Set B)ᶜ : Set B) ≤ a}
  have : Nonempty ι := ⟨⟨⊤, by
    have : IsEmpty (TopologicalSpace.IrreducibleCloseds
        ((((⊤ : B.Opens) : Set B)ᶜ : Set B))) :=
      ⟨fun s ↦ s.isIrreducible.nonempty.elim fun x _ ↦ x.2 trivial⟩
    rw [topologicalKrullDim, Order.krullDim_eq_bot]
    exact bot_le⟩⟩
  have hdir (U U' : ι) : ∃ (U'' : ι) (φ : supportedIn N U.1 ⟶ supportedIn N U''.1)
      (φ' : supportedIn N U'.1 ⟶ supportedIn N U''.1),
      φ ≫ supportedInι N U''.1 = supportedInι N U.1 ∧
        φ' ≫ supportedInι N U''.1 = supportedInι N U'.1 := by
    refine ⟨⟨U.1 ⊓ U'.1, ?_⟩, supportedInMap N inf_le_left, supportedInMap N inf_le_right,
      by simp, by simp⟩
    rw [TopologicalSpace.Opens.coe_inf, Set.compl_inter]
    exact topologicalKrullDim_union_le U.1.isOpen.isClosed_compl U'.1.isOpen.isClosed_compl
      U.2 U'.2
  obtain ⟨hsurj, -⟩ := Scheme.H_map_of_directed_of_locally B (ι := ι)
    (fun U ↦ supportedInι N U.1) hdir (fun V s ↦ by
      obtain ⟨R, hR, h⟩ := exists_covering_supportedIn b a N hN hstalk V s
      exact ⟨R, hR, fun W g hg ↦ by
        obtain ⟨U, hU, t, ht⟩ := h g hg
        exact ⟨⟨U, hU⟩, t, ht⟩⟩) p
  refine subsingleton_of_forall_eq 0 fun x ↦ ?_
  obtain ⟨⟨U, hU⟩, y, rfl⟩ := hsurj x
  suffices Subsingleton (Sheaf.H (supportedIn N U) p) by
    rw [Subsingleton.elim y 0, map_zero]
  let i := Opens.closedComplement U
  let G := supportedIn N U
  have hG : G.IsTorsion := Sheaf.IsTorsion.of_mono (supportedInι N U) hN
  have hdim : topologicalKrullDim
      (IdealSheafData.vanishingIdeal ⟨(U : Set B)ᶜ, U.isOpen.isClosed_compl⟩).subscheme ≤
        (a : WithBot ℕ∞) := by
    rw [i.isClosedEmbedding.isEmbedding.topologicalKrullDim_eq_range,
      Opens.range_closedComplement]
    exact hU
  have hZ' := hZ _ i inferInstance hdim _ (isTorsion_upperStar i hG) p hp
  have h₁ := (bijective_edgeMap_of_isFinite i ((i)^*[AddCommGrpCat.{u + 1}].obj G) p).injective
  have h₂ : Function.Injective (Sheaf.H.map
      ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} i).unit.app G) p) := by
    intro x y hxy
    have := congrArg (Sheaf.H.map (inv
      ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} i).unit.app G)) p) hxy
    simpa only [← Sheaf.H.map_comp_apply, IsIso.hom_inv_id, Sheaf.H.map_id_apply] using this
  have : Subsingleton (Sheaf.H ((𝟭 _).obj ((i)^*[AddCommGrpCat.{u + 1}].obj G)) p) := hZ'
  exact (h₁.comp h₂).subsingleton

end AlgebraicGeometry.Etale
