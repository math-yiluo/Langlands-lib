import Langlands.Sheaf.CompactSoft.GermLiftingStatement
import Mathlib.Topology.Sheaves.LocallySurjective
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

/-!
# Compact-germ lifting for a short exact sequence with c-soft kernel
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.Sheaf.CompactSoft

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

variable {X : TopCat.{u}} {R : Type u} [CommRing R]

/-- Restrictions compose, in elementwise form. -/
theorem restrict_restrict (F : X.Presheaf (ModuleCat.{u} R))
    {U V W : Opens X} (i : U ⟶ V) (j : V ⟶ W) (s : F.obj (op W)) :
    F.map i.op (F.map j.op s) = F.map (i ≫ j).op s := by
  rw [← ConcreteCategory.comp_apply, ← F.map_comp]
  rfl

/-- Naturality of a module presheaf morphism in elementwise form. -/
theorem map_restrict {F G : X.Presheaf (ModuleCat.{u} R)} (f : F ⟶ G)
    {U V : Opens X} (i : U ⟶ V) (s : F.obj (op V)) :
    f.app (op U) (F.map i.op s) = G.map i.op (f.app (op V) s) :=
  congrArg (fun φ => φ s) (f.naturality i.op)

/-- Sections over an open set are left exact. -/
theorem exists_kernel_section
    (S : ShortComplex (TopCat.Sheaf (ModuleCat.{u} R) X)) (hS : S.ShortExact)
    (U : Opens X) (s : S.X₂.presheaf.obj (op U)) (hs : S.g.hom.app (op U) s = 0) :
    ∃ t : S.X₁.presheaf.obj (op U), S.f.hom.app (op U) t = s := by
  let E : TopCat.Sheaf (ModuleCat.{u} R) X ⥤ ModuleCat.{u} R :=
    TopCat.Sheaf.forget _ _ ⋙ (evaluation _ _).obj (op U)
  have : E.Additive := { map_add := by intros; rfl }
  have : PreservesFiniteLimits E :=
    inferInstanceAs (PreservesFiniteLimits
      (sheafToPresheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R) ⋙
        (evaluation (Opens X)ᵒᵖ (ModuleCat.{u} R)).obj (op U)))
  have hE : (S.map E).Exact :=
    (E.preservesFiniteLimits_iff_forall_exact_map_and_mono.mp inferInstance S hS).1
  exact (ShortComplex.moduleCat_exact_iff (S.map E)).mp hE s hs

/-- Two sections on a binary open cover glue when their restrictions agree. -/
theorem exists_glue_pair (F : TopCat.Sheaf (ModuleCat.{u} R) X) {U V : Opens X}
    (s : F.presheaf.obj (op U)) (t : F.presheaf.obj (op V))
    (h : F.presheaf.map (homOfLE inf_le_left : U ⊓ V ⟶ U).op s =
      F.presheaf.map (homOfLE inf_le_right : U ⊓ V ⟶ V).op t) :
    ∃ z : F.presheaf.obj (op (U ⊔ V)),
      F.presheaf.map (homOfLE le_sup_left : U ⟶ U ⊔ V).op z = s ∧
      F.presheaf.map (homOfLE le_sup_right : V ⟶ U ⊔ V).op z = t := by
  obtain ⟨l, hl, hr⟩ := PullbackCone.IsLimit.lift' (F.isLimitPullbackCone U V)
    (ModuleCat.ofHom (LinearMap.toSpanSingleton R _ s))
    (ModuleCat.ofHom (LinearMap.toSpanSingleton R _ t)) (by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro r
      simpa using congrArg (fun x => r • x) h)
  refine ⟨l (1 : R), ?_, ?_⟩
  · simpa using congrArg (fun φ => φ (1 : R)) hl
  · simpa using congrArg (fun φ => φ (1 : R)) hr

/-- Sections on a binary open cover are determined by their two restrictions. -/
theorem section_ext_pair (F : TopCat.Sheaf (ModuleCat.{u} R) X) {U V : Opens X}
    {s t : F.presheaf.obj (op (U ⊔ V))}
    (hU : F.presheaf.map (homOfLE le_sup_left : U ⟶ U ⊔ V).op s =
      F.presheaf.map (homOfLE le_sup_left : U ⟶ U ⊔ V).op t)
    (hV : F.presheaf.map (homOfLE le_sup_right : V ⟶ U ⊔ V).op s =
      F.presheaf.map (homOfLE le_sup_right : V ⟶ U ⊔ V).op t) : s = t := by
  have h :
      ModuleCat.ofHom (LinearMap.toSpanSingleton R _ s) =
      ModuleCat.ofHom (LinearMap.toSpanSingleton R _ t) :=
    PullbackCone.IsLimit.hom_ext (F.isLimitPullbackCone U V)
      (by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro r
        simpa using congrArg (fun x => r • x) hU)
      (by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro r
        simpa using congrArg (fun x => r • x) hV)
  simpa using congrArg (fun φ => φ (1 : R)) h

/-- Neighbourhoods of compact sets can be shrunk so that their overlap lies in a
prescribed open neighbourhood of the compact intersection. -/
theorem exists_compact_overlap_shrink [T2Space X] {A B : Set X}
    (hA : IsCompact A) (hB : IsCompact B) {U V W : Opens X}
    (hAU : A ⊆ U) (hBV : B ⊆ V) (hABW : A ∩ B ⊆ W) :
    ∃ (U' V' : Opens X), A ⊆ U' ∧ B ⊆ V' ∧ U' ≤ U ∧ V' ≤ V ∧ U' ⊓ V' ≤ W := by
  classical
  have hd : Disjoint (A \ (W : Set X)) (B \ (W : Set X)) := by
    refine Set.disjoint_left.mpr ?_
    intro x hx hy
    exact hx.2 (hABW ⟨hx.1, hy.1⟩)
  obtain ⟨P, Q, hP, hQ, hAP, hBQ, hPQ⟩ :=
    SeparatedNhds.of_isCompact_isCompact (hA.diff W.isOpen) (hB.diff W.isOpen) hd
  refine ⟨U ⊓ (W ⊔ ⟨P, hP⟩), V ⊓ (W ⊔ ⟨Q, hQ⟩), ?_, ?_,
    inf_le_left, inf_le_left, ?_⟩
  · intro x hx
    exact ⟨hAU hx, by
      by_cases hxW : x ∈ W
      · exact Or.inl hxW
      · exact Or.inr (hAP ⟨hx, hxW⟩)⟩
  · intro x hx
    exact ⟨hBV hx, by
      by_cases hxW : x ∈ W
      · exact Or.inl hxW
      · exact Or.inr (hBQ ⟨hx, hxW⟩)⟩
  · intro x hx
    rcases hx.1.2 with hxW | hxP
    · exact hxW
    rcases hx.2.2 with hxW | hxQ
    · exact hxW
    exact False.elim (Set.disjoint_left.mp hPQ hxP hxQ)

/-- A quotient section admits a lift on an open neighbourhood of the subset. -/
def HasNeighbourhoodLift
    (S : ShortComplex (TopCat.Sheaf (ModuleCat.{u} R) X)) {O : Opens X}
    (s : S.X₃.presheaf.obj (op O)) (K : Set X) : Prop :=
  ∃ (V : Opens X) (_ : K ⊆ V) (i : V ⟶ O) (t : S.X₂.presheaf.obj (op V)),
    S.g.hom.app (op V) t = S.X₃.presheaf.map i.op s

/-- The composite of the two maps of a short complex vanishes on sections. -/
theorem map_kernel_zero (S : ShortComplex (TopCat.Sheaf (ModuleCat.{u} R) X))
    (U : Opens X) (t : S.X₁.presheaf.obj (op U)) :
    S.g.hom.app (op U) (S.f.hom.app (op U) t) = 0 := by
  have e := congrArg (fun φ => φ.hom.app (op U)) S.zero
  exact congrArg (fun φ => φ t) e

/-- Lifts near two compact sets can be corrected and glued near their union. -/
theorem HasNeighbourhoodLift.union [T2Space X]
    (S : ShortComplex (TopCat.Sheaf (ModuleCat.{u} R) X)) (hS : S.ShortExact)
    (hsoft : IsCSoft S.X₁) {O : Opens X} (s : S.X₃.presheaf.obj (op O))
    {A B : Set X} (hA : IsCompact A) (hB : IsCompact B)
    (hLA : HasNeighbourhoodLift S s A) (hLB : HasNeighbourhoodLift S s B) :
    HasNeighbourhoodLift S s (A ∪ B) := by
  obtain ⟨U, hAU, iU, a, ha⟩ := hLA
  obtain ⟨V, hBV, iV, b, hb⟩ := hLB
  let iIU : U ⊓ V ⟶ U := homOfLE inf_le_left
  let iIV : U ⊓ V ⟶ V := homOfLE inf_le_right
  let d := S.X₂.presheaf.map iIU.op a - S.X₂.presheaf.map iIV.op b
  have hd : S.g.hom.app (op (U ⊓ V)) d = 0 := by
    dsimp [d]
    rw [map_sub, map_restrict, map_restrict, ha, hb,
      restrict_restrict, restrict_restrict]
    exact sub_self _
  obtain ⟨c, hc⟩ := exists_kernel_section S hS (U ⊓ V) d hd
  have hABI : A ∩ B ⊆ (U ⊓ V : Opens X) := fun _ hx => ⟨hAU hx.1, hBV hx.2⟩
  obtain ⟨c', _, hc'⟩ := (isCSoft_iff S.X₁).mp hsoft (A ∩ B)
    (hA.inter_right hB.isClosed) (setGerm S.X₁.presheaf (U ⊓ V) hABI c)
  obtain ⟨W, hABW, jWT, jWI, hW⟩ :=
    setGerm_eq S.X₁.presheaf (Set.subset_univ _) hABI c' c hc'
  have hcW : S.f.hom.app (op W) (S.X₁.presheaf.map jWT.op c') =
      S.X₂.presheaf.map (jWI ≫ iIU).op a -
        S.X₂.presheaf.map (jWI ≫ iIV).op b := by
    rw [hW, map_restrict, hc]
    dsimp [d]
    rw [map_sub, restrict_restrict, restrict_restrict]
    congr 2
  let a' := a - S.f.hom.app (op U)
    (S.X₁.presheaf.map (homOfLE le_top : U ⟶ ⊤).op c')
  have ha' : S.g.hom.app (op U) a' = S.X₃.presheaf.map iU.op s := by
    dsimp [a']
    rw [map_sub, map_kernel_zero, sub_zero, ha]
  have hcorr : S.X₂.presheaf.map (jWI ≫ iIU).op a' =
      S.X₂.presheaf.map (jWI ≫ iIV).op b := by
    change S.X₂.presheaf.map (jWI ≫ iIU).op
      (a - S.f.hom.app (op U)
        (S.X₁.presheaf.map (homOfLE le_top : U ⟶ ⊤).op c')) = _
    rw [map_sub, ← map_restrict, restrict_restrict]
    change S.X₂.presheaf.map (jWI ≫ iIU).op a -
      S.f.hom.app (op W) (S.X₁.presheaf.map jWT.op c') = _
    rw [hcW]
    abel
  obtain ⟨U', V', hAU', hBV', hUU, hVV, hUV⟩ :=
    exists_compact_overlap_shrink hA hB hAU hBV hABW
  let jU : U' ⟶ U := homOfLE hUU
  let jV : V' ⟶ V := homOfLE hVV
  let jW : U' ⊓ V' ⟶ W := homOfLE hUV
  obtain ⟨z, hzU, hzV⟩ := exists_glue_pair S.X₂
    (S.X₂.presheaf.map jU.op a') (S.X₂.presheaf.map jV.op b) (by
      have e := congrArg (fun q => S.X₂.presheaf.map jW.op q) hcorr
      simp only [restrict_restrict] at e ⊢
      convert e using 2)
  let iO : U' ⊔ V' ⟶ O := homOfLE
    (sup_le (hUU.trans iU.le) (hVV.trans iV.le))
  refine ⟨U' ⊔ V', Set.union_subset (hAU'.trans le_sup_left) (hBV'.trans le_sup_right),
    iO, z, ?_⟩
  apply section_ext_pair S.X₃
  · rw [← map_restrict, hzU, map_restrict, ha', restrict_restrict, restrict_restrict]
    congr 2
  · rw [← map_restrict, hzV, map_restrict, hb, restrict_restrict, restrict_restrict]
    congr 2

/-- Sections on the empty open set are unique. -/
theorem section_ext_empty (F : TopCat.Sheaf (ModuleCat.{u} R) X)
    (a b : F.presheaf.obj (op ⊥)) : a = b := by
  have e : ModuleCat.ofHom (LinearMap.toSpanSingleton R _ a) =
      ModuleCat.ofHom (LinearMap.toSpanSingleton R _ b) :=
    F.isTerminalOfEmpty.hom_ext _ _
  simpa using congrArg (fun φ => φ (1 : R)) e

/-- Any quotient section lifts near the empty subset. -/
theorem HasNeighbourhoodLift.empty
    (S : ShortComplex (TopCat.Sheaf (ModuleCat.{u} R) X)) {O : Opens X}
    (s : S.X₃.presheaf.obj (op O)) : HasNeighbourhoodLift S s ∅ :=
  ⟨⊥, Set.empty_subset _, homOfLE bot_le, 0, section_ext_empty S.X₃ _ _⟩

/-- A lift near a subset also lifts near every smaller subset. -/
theorem HasNeighbourhoodLift.mono
    {S : ShortComplex (TopCat.Sheaf (ModuleCat.{u} R) X)} {O : Opens X}
    {s : S.X₃.presheaf.obj (op O)} {A B : Set X}
    (h : HasNeighbourhoodLift S s B) (hAB : A ⊆ B) : HasNeighbourhoodLift S s A := by
  obtain ⟨V, hBV, i, t, ht⟩ := h
  exact ⟨V, hAB.trans hBV, i, t, ht⟩

/-- Compatible quotient lifts exist near a finite union of compact sets as soon
as they exist near each member of the family. -/
theorem HasNeighbourhoodLift.finset_union [T2Space X]
    (S : ShortComplex (TopCat.Sheaf (ModuleCat.{u} R) X)) (hS : S.ShortExact)
    (hsoft : IsCSoft S.X₁) {O : Opens X} (s : S.X₃.presheaf.obj (op O))
    {ι : Type u} (I : Finset ι) (C : ι → Set X)
    (hC : ∀ i ∈ I, IsCompact (C i)) (hL : ∀ i ∈ I, HasNeighbourhoodLift S s (C i)) :
    HasNeighbourhoodLift S s (⋃ i ∈ I, C i) := by
  classical
  induction I using Finset.induction_on with
  | empty => simpa using HasNeighbourhoodLift.empty S s
  | @insert i I hi ih =>
    rw [Finset.set_biUnion_insert]
    have hCI : ∀ j ∈ I, IsCompact (C j) := fun j hj => hC j (Finset.mem_insert_of_mem hj)
    have hLI : ∀ j ∈ I, HasNeighbourhoodLift S s (C j) :=
      fun j hj => hL j (Finset.mem_insert_of_mem hj)
    exact HasNeighbourhoodLift.union S hS hsoft s
      (hC i (Finset.mem_insert_self _ _)) (I.isCompact_biUnion hCI)
      (hL i (Finset.mem_insert_self _ _)) (ih hCI hLI)

/-- A quotient section lifts on a neighbourhood of every compact subset of its
open domain, if the kernel sheaf is c-soft. -/
theorem exists_lift_near_compact [T2Space X] [LocallyCompactSpace X]
    (S : ShortComplex (TopCat.Sheaf (ModuleCat.{u} R) X)) (hS : S.ShortExact)
    (hsoft : IsCSoft S.X₁) {O : Opens X} (s : S.X₃.presheaf.obj (op O))
    {K : Set X} (hK : IsCompact K) (hKO : K ⊆ O) : HasNeighbourhoodLift S s K := by
  classical
  have hlocal := (TopCat.Presheaf.isLocallySurjective_iff S.g.hom).mp
    ((TopCat.Sheaf.isLocallySurjective_iff_epi S.g).mpr hS.epi_g)
  have hneighbourhood : ∀ x : K, ∃ C : Set X,
      IsCompact C ∧ (x : X) ∈ interior C ∧ HasNeighbourhoodLift S s C := by
    intro x
    obtain ⟨V, hVO, ⟨t, ht⟩, hxV⟩ := hlocal O s x (hKO x.property)
    obtain ⟨W, hW, hxW, hWV, hWc⟩ := exists_open_between_and_isCompact_closure
      isCompact_singleton V.isOpen (Set.singleton_subset_iff.mpr hxV)
    refine ⟨closure W, hWc, ?_, V, hWV, homOfLE hVO, t, ht⟩
    exact (interior_maximal subset_closure hW) (hxW (Set.mem_singleton (x : X)))
  choose C hCc hxC hLC using hneighbourhood
  obtain ⟨I, hI⟩ := hK.elim_finite_subcover (fun x : K => interior (C x))
    (fun _ => isOpen_interior) (fun x hx => Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hxC ⟨x, hx⟩⟩)
  apply (HasNeighbourhoodLift.finset_union S hS hsoft s I C
    (fun x _ => hCc x) (fun x _ => hLC x)).mono
  exact hI.trans (Set.iUnion₂_mono fun _ _ => interior_subset)

/-- Compact germs lift through a sheaf epimorphism whose kernel is c-soft. -/
theorem compactGermLifting : CompactGermLiftingStatement.{u} := by
  intro X _ _ R _ S hS hsoft K hK q
  obtain ⟨O, hKO, s, rfl⟩ := exists_setGerm_eq S.X₃.presheaf q
  obtain ⟨V, hKV, i, t, ht⟩ := exists_lift_near_compact S hS hsoft s hK hKO
  refine ⟨setGerm S.X₂.presheaf V hKV t, ?_⟩
  have e := congrArg (fun φ => φ t) (setGerm_naturality S.g.hom V hKV)
  change setGerm S.X₃.presheaf V hKV (S.g.hom.app (op V) t) =
    (setSectionsFunctor R K).map S.g.hom (setGerm S.X₂.presheaf V hKV t) at e
  rw [← e, ht, setGerm_res_apply]

end Langlands.Sheaf.CompactSoft
