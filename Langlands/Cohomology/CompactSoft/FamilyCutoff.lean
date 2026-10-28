import Langlands.Sheaf.CompactSoft
import Langlands.Sheaf.Equivariant.SmoothPart

/-!
# Compact smooth cutoffs in indexed-family sheaves
-/

noncomputable section

attribute [local instance] Classical.propDecidable

namespace Langlands.Cohomology.CompactSoft

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Langlands.Sheaf.Equivariant Langlands.Sheaf.CompactSoft

universe u

variable {R : Type u} [CommRing R]
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {X : Type u} [TopologicalSpace X] [MulAction G X] [ContinuousConstSMul G X]
variable [HasStableNeighbourhoods G X]

omit [IsTopologicalGroup G] [ContinuousConstSMul G X] in
/-- A compact set has a relatively compact open neighbourhood stabilized by an
open subgroup, with closure in any prescribed open neighbourhood. -/
theorem exists_compact_stable_neighbourhood [T2Space X] [LocallyCompactSpace X]
    {K : Set X} (hK : IsCompact K) (U : Opens X) (hKU : K ⊆ U) :
    ∃ (V : Opens X) (H : OpenSubgroup G),
      K ⊆ V ∧ closure (V : Set X) ⊆ U ∧ IsCompact (closure (V : Set X)) ∧
      ∀ h ∈ H, ∀ y ∈ V, h • y ∈ V := by
  classical
  obtain ⟨W, hW, hKW, hWU, hWc⟩ :=
    exists_open_between_and_isCompact_closure hK U.isOpen hKU
  choose H V hV hxV hVW hHV using
    fun x : K => HasStableNeighbourhoods.exists_stable (G := G) x.1 W hW (hKW x.2)
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover V hV (fun x hx =>
    Set.mem_iUnion.2 ⟨⟨x, hx⟩, hxV ⟨x, hx⟩⟩)
  let O : Opens X := ⟨⋃ i ∈ s, V i, isOpen_biUnion fun i _ => hV i⟩
  let J : OpenSubgroup G := OpenSubgroup.iInfOfFinite (fun i : s => H i.1)
  have hOW : (O : Set X) ⊆ W := by
    intro y hy
    obtain ⟨i, _, hi⟩ := Set.mem_iUnion₂.1 hy
    exact hVW i hi
  refine ⟨O, J, hs, (closure_mono hOW).trans hWU,
    hWc.of_isClosed_subset isClosed_closure (closure_mono hOW), ?_⟩
  intro h hh y hy
  obtain ⟨i, hi, hyi⟩ := Set.mem_iUnion₂.1 hy
  exact Set.mem_iUnion₂.2 ⟨i, hi,
    hHV i h (OpenSubgroup.iInfOfFinite_le (fun i : s => H i.1) ⟨i, hi⟩ hh) y hyi⟩

/-- The coordinate type for a coinduced sheaf of arbitrary coefficient families. -/
abbrev FamilySections (A : X → ModuleCat.{u} R) (U : ActionOpens G X) :=
  ∀ (g : G) (y : {y : X // g • y ∈ U.openSet}), A y.1

section Coordinates

variable (A : X → ModuleCat.{u} R) (F : TopologicalSheaf G X (ModuleCat.{u} R))
variable (read : ∀ U : ActionOpens G X, F.obj.obj (op U) ≃ₗ[R] FamilySections A U)
variable (read_map : ∀ {U V : ActionOpens G X} (f : U ⟶ V)
  (s : F.obj.obj (op V)) (g : G) (y : X) (hy : g • y ∈ U.openSet),
  read U ((F.obj.map f.op).hom s) g ⟨y, hy⟩ =
    read V s (f.label * g) ⟨y, by simpa only [mul_smul] using f.mapsTo (g • y) hy⟩)

include read_map

/-- Restriction forgets the entries outside the smaller open. -/
theorem read_restrict {U V : ActionOpens G X} (hVU : V.openSet ≤ U.openSet)
    (s : F.obj.obj (op U)) (g : G) (y : X) (hy : g • y ∈ V.openSet) :
    read V ((F.obj.map (ActionOpens.inclusionHom hVU).op).hom s) g ⟨y, hy⟩ =
      read U s g ⟨y, hVU hy⟩ := by
  have e := read_map (ActionOpens.inclusionHom hVU) s g y hy
  have heval : ∀ (g' : G) (hg : g' = g) (hy' : g' • y ∈ U.openSet),
      read U s g' ⟨y, hy'⟩ = read U s g ⟨y, hVU hy⟩ := by
    intro g' hg hy'
    subst g'
    rfl
  exact e.trans (heval _ (one_mul g) _)

/-- A subgroup action changes the group index by left multiplication. -/
theorem read_invariant {U : ActionOpens G X} (H : Subgroup G)
    (hU : ∀ h : H, ∀ y ∈ U.openSet, (h : G) • y ∈ U.openSet)
    (s : F.obj.obj (op U)) (h : H) (g : G) (y : X) (hy : g • y ∈ U.openSet) :
    read U ((F.obj.map (ActionOpens.invariantArrow H U hU h).op).hom s) g ⟨y, hy⟩ =
      read U s ((h : G)⁻¹ * g) ⟨y, by simpa only [mul_smul, Subgroup.coe_inv] using hU h⁻¹ _ hy⟩ := by
  exact read_map (ActionOpens.invariantArrow H U hU h) s g y hy

omit read_map in
/-- Keep the coordinates over `V` and put zero at all other coordinates. -/
def familyCutoff {U : ActionOpens G X} (V : Opens X) (hVU : V ≤ U.openSet)
    (s : F.obj.obj (op U)) : F.obj.obj (op (⟨⊤⟩ : ActionOpens G X)) :=
  (read (⟨⊤⟩ : ActionOpens G X)).symm (fun g y =>
    if hv : g • y.1 ∈ V then read U s g ⟨y.1, hVU hv⟩ else 0)

omit read_map in
/-- Coordinates of the cutoff. -/
theorem read_familyCutoff {U : ActionOpens G X} (V : Opens X) (hVU : V ≤ U.openSet)
    (s : F.obj.obj (op U)) (g : G) (y : X) (hy : g • y ∈ (⊤ : Opens X)) :
    read (⟨⊤⟩ : ActionOpens G X) (familyCutoff A F read V hVU s) g ⟨y, hy⟩ =
      if hv : g • y ∈ V then read U s g ⟨y, hVU hv⟩ else 0 := by
  simp only [familyCutoff, LinearEquiv.apply_symm_apply]

/-- The cutoff agrees with the original section on its selected open. -/
theorem familyCutoff_restrict {U : ActionOpens G X} (V : Opens X) (hVU : V ≤ U.openSet)
    (s : F.obj.obj (op U)) :
    (F.obj.map (ActionOpens.inclusionHom (U := ⟨V⟩) (V := (⟨⊤⟩ : ActionOpens G X))
        (show V ≤ ⊤ from le_top)).op).hom
        (familyCutoff A F read V hVU s) =
      (F.obj.map (ActionOpens.inclusionHom hVU).op).hom s := by
  apply (read (⟨V⟩ : ActionOpens G X)).injective
  funext g ⟨y, hy⟩
  rw [read_restrict A F read read_map, read_restrict A F read read_map,
    read_familyCutoff, dite_eq_left hy]

/-- On an open disjoint from the selected open, the cutoff is zero. -/
theorem familyCutoff_restrict_zero {U : ActionOpens G X} (V : Opens X)
    (hVU : V ≤ U.openSet) (s : F.obj.obj (op U)) (T : Opens X)
    (hTV : Disjoint (T : Set X) (V : Set X)) :
    (F.obj.map (ActionOpens.inclusionHom (U := ⟨T⟩) (V := (⟨⊤⟩ : ActionOpens G X))
        (show T ≤ ⊤ from le_top)).op).hom
        (familyCutoff A F read V hVU s) = 0 := by
  apply (read (⟨T⟩ : ActionOpens G X)).injective
  funext g ⟨y, hy⟩
  rw [read_restrict A F read read_map, read_familyCutoff]
  have hn : ¬g • y ∈ V := fun hv => Set.disjoint_left.1 hTV hy hv
  simp only [dite_eq_right hn, map_zero, Pi.zero_apply]

/-- A stable cutoff preserves local fixedness at any point of the original open. -/
theorem familyCutoff_locallyFixed {U : ActionOpens G X} (V : Opens X)
    (hVU : V ≤ U.openSet) (s : F.obj.obj (op U)) (H : OpenSubgroup G)
    (hV : ∀ h ∈ H, ∀ y ∈ V, h • y ∈ V) {x : X}
    (hs : IsLocallyFixedAt R F.obj s x) :
    IsLocallyFixedAt R F.obj (familyCutoff A F read V hVU s) x := by
  obtain ⟨T, hTU, J, hT, hxT, hfix⟩ := hs
  let L : OpenSubgroup G := J ⊓ H
  have hLT : ∀ k : (L : Subgroup G), ∀ y ∈ T.openSet, (k : G) • y ∈ T.openSet :=
    fun k => hT ⟨k, (OpenSubgroup.mem_inf.1 k.2).1⟩
  refine ⟨T, le_top, L, hLT, hxT, fun k => ?_⟩
  apply (read T).injective
  funext g ⟨y, hy⟩
  rw [read_invariant A F read read_map,
    read_restrict A F read read_map, read_restrict A F read read_map,
    read_familyCutoff, read_familyCutoff]
  have hkg : ((k : G)⁻¹ * g) • y = (k : G)⁻¹ • (g • y) := mul_smul _ _ _
  by_cases hv : g • y ∈ V
  · have hkv : ((k : G)⁻¹ * g) • y ∈ V := by
      rw [hkg]
      exact hV _ (H.inv_mem (OpenSubgroup.mem_inf.1 k.2).2) _ hv
    rw [dite_eq_left hv, dite_eq_left hkv]
    have e := congrArg (fun t => read T t g ⟨y, hy⟩)
      (hfix ⟨k, (OpenSubgroup.mem_inf.1 k.2).1⟩)
    simpa only [read_invariant A F read read_map,
      read_restrict A F read read_map] using e
  · have hkv : ¬ ((k : G)⁻¹ * g) • y ∈ V := by
      intro hh
      apply hv
      have hh' := hV k (OpenSubgroup.mem_inf.1 k.2).2 _ hh
      simpa only [hkg, smul_inv_smul] using hh'
    rw [dite_eq_right hv, dite_eq_right hkv]

/-- If the closure of a stable cutoff open lies in the original open, cutting off
a locally smooth section produces a global locally smooth section. -/
theorem familyCutoff_smooth {U : ActionOpens G X} (V : Opens X)
    (hVU : closure (V : Set X) ⊆ U.openSet) (s : F.obj.obj (op U))
    (hs : ∀ x ∈ U.openSet, IsLocallyFixedAt R F.obj s x) (H : OpenSubgroup G)
    (hV : ∀ h ∈ H, ∀ y ∈ V, h • y ∈ V) :
    ∀ x ∈ (⊤ : Opens X), IsLocallyFixedAt R F.obj
      (familyCutoff A F read V (show V ≤ U.openSet from subset_closure.trans hVU) s) x := by
  intro x _
  by_cases hxU : x ∈ U.openSet
  · exact familyCutoff_locallyFixed A F read read_map V _ s H hV (hs x hxU)
  · let T : Opens X := ⟨(closure (V : Set X))ᶜ, isClosed_closure.isOpen_compl⟩
    have hxT : x ∈ T := fun hx => hxU (hVU hx)
    apply IsLocallyFixedAt.of_restrict R (W := (⟨T⟩ : ActionOpens G X))
      (show T ≤ (⟨⊤⟩ : ActionOpens G X).openSet from le_top)
    rw [familyCutoff_restrict_zero A F read read_map V _ s T]
    · exact isLocallyFixedAt_zero R F.obj hxT
    · exact Set.disjoint_left.2 fun y hy hv => hy (subset_closure hv)

/-- The smooth part of a sheaf with indexed-family coordinates is c-soft. -/
theorem isCSoft_smooth_of_family [T2Space X] [LocallyCompactSpace X] :
    IsCSoft ((toSheaf G X (ModuleCat.{u} R)).obj ((smoothSubsheafFunctor R).obj F)) := by
  let S := (toSheaf G X (ModuleCat.{u} R)).obj ((smoothSubsheafFunctor R).obj F)
  change IsCSoft S
  rw [isCSoft_iff]
  intro K hK t
  obtain ⟨U, hKU, s, rfl⟩ := exists_setGerm_eq S.presheaf t
  obtain ⟨V, H, hKV, hVU, hVc, hV⟩ :=
    exists_compact_stable_neighbourhood (G := G) hK U hKU
  let hVU' : V ≤ U := subset_closure.trans hVU
  let c := familyCutoff A F read V hVU' s.1
  have hc : c ∈ smoothSubmodule R F.obj (⟨⊤⟩ : ActionOpens G X) :=
    familyCutoff_smooth A F read read_map V hVU s.1 s.2 H hV
  let c' : S.presheaf.obj (op ⊤) := ⟨c, hc⟩
  let W : Opens X := ⟨(closure (V : Set X))ᶜ, isClosed_closure.isOpen_compl⟩
  have hdisj : Disjoint (W : Set X) (V : Set X) :=
    Set.disjoint_left.2 fun _ hw hv => hw (subset_closure hv)
  have hzero : S.presheaf.map (homOfLE le_top : W ⟶ ⊤).op c' = 0 := by
    apply Subtype.ext
    exact familyCutoff_restrict_zero A F read read_map V hVU' s.1 W hdisj
  refine ⟨c', ?_, ?_⟩
  · refine hVc.of_isClosed_subset (Langlands.Sheaf.CompactSupport.isClosed_support _ _) ?_
    intro x hx
    by_contra hxV
    apply hx
    change S.presheaf.Γgerm x c' = 0
    rw [← S.presheaf.Γgerm_res_apply (U := W) x hxV c' (i := homOfLE le_top),
      hzero, map_zero]
  · refine setGerm_ext S.presheaf _ _ hKV (homOfLE le_top : V ⟶ ⊤)
      (homOfLE hVU' : V ⟶ U) ?_
    apply Subtype.ext
    exact familyCutoff_restrict A F read read_map V hVU' s.1

end Coordinates

end Langlands.Cohomology.CompactSoft
