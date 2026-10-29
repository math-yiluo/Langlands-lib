import Langlands.Cohomology.CompactSoft.Statement
import Langlands.Sheaf.CompactSoft.GermLiftingProof
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

/-!
# Compact support cutoff and c-soft exactness
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.Cohomology

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open TopCat.Presheaf Langlands.Sheaf.CompactSoft
open scoped AlgebraicGeometry

universe u

variable {X : TopCat.{u}} {R : Type u} [CommRing R]

private theorem restrict_zero_off_support (F : TopCat.Sheaf (ModuleCat.{u} R) X)
    (s : F.presheaf.obj (op ⊤)) {U : Opens X}
    (hU : (U : Set X) ⊆ (Sheaf.CompactSupport.support F.presheaf s)ᶜ) : s |_ U = 0 := by
  apply section_ext F U
  intro x hx
  have hz : F.presheaf.Γgerm x s = 0 := not_not.mp (hU hx)
  rw [map_zero]
  change F.presheaf.germ U x hx (F.presheaf.map (homOfLE le_top).op s) = 0
  exact (F.presheaf.Γgerm_res_apply x hx s (i := homOfLE le_top)).trans hz

private theorem exists_glue_binary (F : TopCat.Sheaf (ModuleCat.{u} R) X)
    {V W : Opens X} (s : F.presheaf.obj (op V)) (t : F.presheaf.obj (op W))
    (h : s |_ (V ⊓ W) = t |_ (V ⊓ W)) {U : Opens X}
    (hV : V ≤ U) (hW : W ≤ U) (hc : U ≤ V ⊔ W) :
    ∃ z : F.presheaf.obj (op U), z |_ V = s ∧ z |_ W = t := by
  have hU : U = V ⊔ W := le_antisymm hc (sup_le hV hW)
  subst U
  exact exists_glue_pair F s t h

/-- A quotient section with compact support lifts with compact support, provided
all quotient germs along compact subsets lift. The proof cuts a local lift off
at the boundary of a relatively compact open neighbourhood of its support. -/
theorem compactSections_surjective_of_compactGerm_lifting
    [T2Space X] [LocallyCompactSpace X]
    {S : ShortComplex (TopCat.Sheaf (ModuleCat.{u} R) X)}
    (hS : S.ShortExact) (hF : IsCSoft S.X₁)
    (hLift : ∀ K : Set X, IsCompact K →
      Function.Surjective ((setSectionsFunctor R K).map S.g.hom)) :
    Function.Surjective ((Sheaf.CompactSupport.functor (X := X) (R := R)).map S.g) := by
  intro s
  let K : Set X := Sheaf.CompactSupport.support S.X₃.presheaf s.1
  have hK : IsCompact K := s.2
  obtain ⟨V₀, hVo, hKV, _, hVc⟩ :=
    exists_open_between_and_isCompact_closure hK isOpen_univ (Set.subset_univ K)
  let V : Opens X := ⟨V₀, hVo⟩
  let L : Set X := closure V₀
  have hL : IsCompact L := hVc
  obtain ⟨t₀, ht₀⟩ := hLift L hL (setGerm S.X₃.presheaf ⊤ (Set.subset_univ L) s.1)
  obtain ⟨U₀, hLU₀, t₁, rfl⟩ := exists_setGerm_eq S.X₂.presheaf t₀
  have heq : setGerm S.X₃.presheaf U₀ hLU₀ (S.g.hom.app (op U₀) t₁) =
      setGerm S.X₃.presheaf ⊤ (Set.subset_univ L) s.1 := by
    have e := congrArg (fun f => f t₁) (setGerm_naturality S.g.hom U₀ hLU₀)
    exact e.trans ht₀
  obtain ⟨U, hLU, iU, _, ht⟩ := setGerm_eq S.X₃.presheaf hLU₀
    (Set.subset_univ L) (S.g.hom.app (op U₀) t₁) s.1 heq
  let t : S.X₂.presheaf.obj (op U) := S.X₂.presheaf.map iU.op t₁
  have hgt : S.g.hom.app (op U) t = s.1 |_ U := by
    dsimp only [t]
    change S.g.hom.app (op U) (restrictOpen t₁ U iU.le) = s.1 |_ U
    rw [TopCat.Presheaf.map_restrict]
    exact ht
  let O : Opens X := U ⊓ ⟨Kᶜ, (Sheaf.CompactSupport.isClosed_support _ _).isOpen_compl⟩
  have hO : O ≤ U := inf_le_left
  have hgo : S.g.hom.app (op O) (t |_ O) = 0 := by
    rw [TopCat.Presheaf.map_restrict, hgt, TopCat.Presheaf.restrict_restrict]
    exact restrict_zero_off_support S.X₃ s.1 (fun _ hx => hx.2)
  obtain ⟨a, ha⟩ := exists_kernel_section S hS O (t |_ O) hgo
  let B : Set X := L \ (V : Set X)
  have hB : IsCompact B := hL.diff V.isOpen
  have hBO : B ⊆ O := by
    intro x hx
    exact ⟨hLU hx.1, fun hxK => hx.2 (hKV hxK)⟩
  obtain ⟨a', _, ha'⟩ := (isCSoft_iff _).mp hF B hB
    (setGerm S.X₁.presheaf O hBO a)
  obtain ⟨N, hBN, iNtop, iNO, hN⟩ := setGerm_eq S.X₁.presheaf
    (Set.subset_univ B) hBO a' a ha'
  have hNU : N ≤ U := iNO.le.trans hO
  have hzero : (t - S.f.hom.app (op U) (a' |_ U)) |_ N = 0 := by
    change S.X₂.presheaf.map (homOfLE hNU).op _ = 0
    rw [map_sub, ← S.f.hom.naturality_apply]
    change t |_ N - S.f.hom.app (op N) ((a' |_ U) |_ N) = 0
    rw [TopCat.Presheaf.restrict_restrict]
    change t |_ N - S.f.hom.app (op N) (S.X₁.presheaf.map iNtop.op a') = 0
    rw [hN]
    have ee := congrArg (fun b => restrictOpen b N iNO.le) ha
    change restrictOpen (S.f.hom.app (op O) a) N iNO.le =
      restrictOpen (t |_ O) N iNO.le at ee
    rw [← TopCat.Presheaf.map_restrict, TopCat.Presheaf.restrict_restrict] at ee
    exact sub_eq_zero.mpr ee.symm
  let C : Set X := L \ (N : Set X)
  have hC : IsCompact C := hL.diff N.isOpen
  have hCV : C ⊆ V := by
    intro x hx
    by_contra hxV
    exact hx.2 (hBN ⟨hx.1, hxV⟩)
  have hKC : K ⊆ C := by
    intro x hx
    exact ⟨subset_closure (hKV hx), fun hxN => (iNO.le hxN).2 hx⟩
  let W : Opens X := ⟨Cᶜ, hC.isClosed.isOpen_compl⟩
  have hVU : V ≤ U := subset_closure.trans hLU
  have hVW : V ⊓ W ≤ N := by
    intro x hx
    by_contra hxN
    exact hx.2 ⟨subset_closure hx.1, hxN⟩
  have hcover : (⊤ : Opens X) ≤ V ⊔ W := by
    intro x _
    by_cases hx : x ∈ C
    · exact Or.inl (hCV hx)
    · exact Or.inr hx
  let z : S.X₂.presheaf.obj (op U) := t - S.f.hom.app (op U) (a' |_ U)
  have hcompat : (z |_ V) |_ (V ⊓ W) = (0 : S.X₂.presheaf.obj (op W)) |_ (V ⊓ W) := by
    rw [TopCat.Presheaf.restrict_restrict]
    have e := congrArg (fun b => restrictOpen b (V ⊓ W) hVW) hzero
    change restrictOpen (restrictOpen z N hNU) (V ⊓ W) hVW =
      restrictOpen (0 : S.X₂.presheaf.obj (op N)) (V ⊓ W) hVW at e
    rw [TopCat.Presheaf.restrict_restrict] at e
    simpa only [restrictOpen, restrict, map_zero] using e
  obtain ⟨b, hbV, hbW⟩ := exists_glue_binary S.X₂ (z |_ V) 0 hcompat le_top le_top hcover
  have hbc : IsCompact (Sheaf.CompactSupport.support S.X₂.presheaf b) := by
    apply hC.of_isClosed_subset (Sheaf.CompactSupport.isClosed_support _ _)
    intro x hx
    by_contra hxC
    apply hx
    have hbW' : S.X₂.presheaf.map (homOfLE le_top : W ⟶ ⊤).op b = 0 := hbW
    rw [← S.X₂.presheaf.Γgerm_res_apply (U := W) x hxC b
      (i := homOfLE le_top), hbW', map_zero]
  refine ⟨⟨b, hbc⟩, Subtype.ext ?_⟩
  change S.g.hom.app (op ⊤) b = s.1
  apply S.X₃.eq_of_locally_eq₂ (homOfLE le_top : V ⟶ ⊤)
    (homOfLE le_top : W ⟶ ⊤) hcover
  · change (S.g.hom.app (op ⊤) b) |_ V = s.1 |_ V
    rw [← TopCat.Presheaf.map_restrict, hbV]
    dsimp only [z]
    rw [TopCat.Presheaf.map_restrict, map_sub, hgt]
    have hz : S.g.hom.app (op U) (S.f.hom.app (op U) (a' |_ U)) = 0 := by
      have e := congrArg (fun f => f.hom.app (op U)) S.zero
      exact congrArg (fun f => f (a' |_ U)) e
    rw [hz, sub_zero, TopCat.Presheaf.restrict_restrict]
  · change (S.g.hom.app (op ⊤) b) |_ W = s.1 |_ W
    rw [← TopCat.Presheaf.map_restrict, hbW, map_zero]
    symm
    exact restrict_zero_off_support S.X₃ s.1 (fun x hx hxK => hx (hKC hxK))

/-- Germ surjectivity and c-softness of the middle sheaf imply c-softness of the
quotient, by naturality of compact germs. -/
theorem isCSoft_quotient_of_compactGerm_lifting
    {S : ShortComplex (TopCat.Sheaf (ModuleCat.{u} R) X)}
    (hLift : ∀ K : Set X, IsCompact K →
      Function.Surjective ((setSectionsFunctor R K).map S.g.hom))
    (hG : IsCSoft S.X₂) : IsCSoft S.X₃ := by
  intro K hK t
  obtain ⟨t', ht'⟩ := hLift K hK t
  obtain ⟨s, hs⟩ := hG K hK t'
  refine ⟨Sheaf.CompactSupport.presheafFunctor.map S.g.hom s, ?_⟩
  have e := congrArg (fun f => f s) (compactGerm_naturality S.g.hom K)
  change compactGerm S.X₃.presheaf K
      (Sheaf.CompactSupport.presheafFunctor.map S.g.hom s) =
    (setSectionsFunctor R K).map S.g.hom (compactGerm S.X₂.presheaf K s) at e
  rw [e, hs, ht']

/-- The two conclusions of compact c-soft exactness follow from compact-germ
lifting, using left exactness of compact sections and the cutoff construction. -/
theorem shortExact_of_compactGerm_lifting
    [T2Space X] [LocallyCompactSpace X]
    {S : ShortComplex (TopCat.Sheaf (ModuleCat.{u} R) X)}
    (hS : S.ShortExact) (hF : IsCSoft S.X₁)
    (hLift : ∀ K : Set X, IsCompact K →
      Function.Surjective ((setSectionsFunctor R K).map S.g.hom)) :
    (S.map (Sheaf.CompactSupport.functor (X := X) (R := R))).ShortExact ∧
      (IsCSoft S.X₂ → IsCSoft S.X₃) := by
  let E := Sheaf.CompactSupport.functor (X := X) (R := R)
  obtain ⟨he, hm⟩ :=
    (Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono E).mp inferInstance S hS
  have hg : Epi (E.map S.g) :=
    (ModuleCat.epi_iff_surjective _).mpr
      (compactSections_surjective_of_compactGerm_lifting hS hF hLift)
  exact ⟨ShortComplex.ShortExact.mk' he hm hg,
    isCSoft_quotient_of_compactGerm_lifting hLift⟩

/-- Compactly supported sections preserve a short exact sequence with c-soft
kernel, and a c-soft middle sheaf has c-soft quotient. -/
theorem cSoftShortExact : CSoftShortExactStatement.{u} := by
  intro X _ _ R _ S hS hF
  exact shortExact_of_compactGerm_lifting hS hF (compactGermLifting X R S hS hF)

end Langlands.Cohomology
