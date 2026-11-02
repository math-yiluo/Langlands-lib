import Langlands.Cohomology.AbelianSheafFlasque
import Langlands.Cohomology.CechCochains
import Mathlib.Topology.Sheaves.AddCommGrpCat
import Mathlib.Topology.Sheaves.LocallySurjective
import Mathlib.Topology.Compactness.Compact

/-! # Actual sheaf H¹ classes have finite-cover cocycle presentations on compact spaces -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace Langlands.Cohomology.AbelianSheafH1FiniteCocycles

open Cech

variable {T : TopCat.{u}}

/-- Local lifts of a global section on a finite full open cover. -/
structure FiniteLiftData {F G : TopCat.Sheaf AddCommGrpCat.{u} T} (φ : F ⟶ G)
    (q : G.1.obj (op ⊤)) where
  index : Type u
  finite : Finite index
  cover : index → Opens T
  cover_top : ⊤ ≤ iSup cover
  lifts : C F.1 cover 0
  lift_eq : ∀ σ, φ.hom.app (op (inter cover σ)) (lifts σ) = res le_top q

/-- An epimorphism of abelian sheaves lifts every global section on a finite full cover
when the underlying space is compact. -/
theorem exists_finite_lifts [CompactSpace T]
    {F G : TopCat.Sheaf AddCommGrpCat.{u} T} (φ : F ⟶ G) [Epi φ]
    (q : G.1.obj (op ⊤)) : Nonempty (FiniteLiftData φ q) := by
  classical
  have hloc := (TopCat.Presheaf.isLocallySurjective_iff φ.hom).1
    ((TopCat.Sheaf.isLocallySurjective_iff_epi φ).2 inferInstance)
  have hx : ∀ x : T, ∃ (V : Opens T) (s : F.1.obj (op V)),
      φ.hom.app (op V) s = res le_top q ∧ x ∈ V := by
    intro x
    obtain ⟨V, hV, ⟨s, hs⟩, hxV⟩ := hloc ⊤ q x (by trivial)
    exact ⟨V, s, hs, hxV⟩
  choose V s hs hxV using hx
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x => (V x : Set T))
    (fun x => (V x).isOpen) (fun x _ => Set.mem_iUnion.2 ⟨x, hxV x⟩)
  let U : t → Opens T := fun a => V a.1
  have hcov : ⊤ ≤ iSup U := by
    intro x _
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
    exact Opens.mem_iSup.2 ⟨⟨y, hy⟩, hxy⟩
  refine ⟨⟨t, inferInstance, U, hcov,
    (fun σ => res (inter_le_apply σ 0) (s (σ 0).1)), ?_⟩⟩
  intro σ
  rw [map_res, hs, res_res]

variable (F : TopCat.Sheaf AddCommGrpCat.{u} T)

set_option backward.isDefEq.respectTransparency false in
/-- A finite-cover ordered cocycle representing an actual H¹ class through the chosen
injective sequence, with all section and connecting equations supplied. -/
structure FiniteCocyclePresentation (x : Sheaf.H.{u} F 1) where
  quotientSection : (cokernel (Injective.ι F)).1.obj (op ⊤)
  localLifts : FiniteLiftData (cokernel.π (Injective.ι F)) quotientSection
  cocycle : C F.1 localLifts.cover 1
  closed : d F.1 localLifts.cover 1 cocycle = 0
  primitive_eq : map localLifts.cover (Injective.ι F).hom 1 cocycle =
    d (Injective.under F).1 localLifts.cover 0 localLifts.lifts
  value_eq : Sheaf.H.δ (AbelianSheafFlasque.injectiveSc_shortExact F) 0 1 rfl
    ((Sheaf.H.equiv₀ _ (isTerminalTop (α := Opens T))).symm quotientSection) = x

lemma injective_ι_section (V : Opens T) :
    Function.Injective ((Injective.ι F).hom.app (op V)) := by
  have : Mono (Injective.ι F).hom :=
    (TopCat.Sheaf.forget AddCommGrpCat T).map_mono (Injective.ι F)
  exact (AddCommGrpCat.mono_iff_injective _).1 inferInstance

set_option backward.isDefEq.respectTransparency false in
/-- Every actual first-cohomology class of an abelian sheaf on a compact topological
space admits an explicit ordered cocycle presentation on some finite full open cover. -/
theorem exists_finite_cocycle_presentation [CompactSpace T] (x : Sheaf.H.{u} F 1) :
    Nonempty (FiniteCocyclePresentation F x) := by
  classical
  let S := AbelianSheafFlasque.injectiveSc F
  have hS := AbelianSheafFlasque.injectiveSc_shortExact F
  obtain ⟨y, hy⟩ := Sheaf.H.longSequence_exact₁ hS x (Subsingleton.elim _ _) rfl
  let q := Sheaf.H.equiv₀ S.X₃ (isTerminalTop (α := Opens T)) y
  obtain ⟨L⟩ := exists_finite_lifts S.g q
  have hdt : ∀ σ, S.g.hom.app (op (inter L.cover σ))
      (d S.X₂.1 L.cover 0 L.lifts σ) = 0 := by
    intro σ
    have hz : d S.X₃.1 L.cover 0 (map L.cover S.g.hom 0 L.lifts) = 0 := by
      funext τ
      rw [d_apply, Fin.sum_univ_two]
      simp only [map, AddMonoidHom.coe_mk, ZeroHom.coe_mk, L.lift_eq, res_res,
        Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_smul, Pi.zero_apply]
      exact add_neg_eq_zero.2 rfl
    have h' := congrFun (d_map L.cover S.g.hom 0 L.lifts) σ
    rw [hz, Pi.zero_apply] at h'
    exact h'.symm
  choose z hz using fun σ => TopCat.Sheaf.sections_exact_of_left_exact
    hS.exact hS.mono_f _ (hdt σ)
  have hz' : map L.cover S.f.hom 1 z = d S.X₂.1 L.cover 0 L.lifts := funext hz
  refine ⟨⟨q, L, z, ?_, hz', ?_⟩⟩
  · funext τ
    apply injective_ι_section F _
    have h := congrFun (d_map L.cover S.f.hom 1 z) τ
    rw [hz', d_d, Pi.zero_apply] at h
    rw [Pi.zero_apply, map_zero]
    exact h.symm
  · change Sheaf.H.δ hS 0 1 rfl
      ((Sheaf.H.equiv₀ S.X₃ (isTerminalTop (α := Opens T))).symm
        ((Sheaf.H.equiv₀ S.X₃ (isTerminalTop (α := Opens T))) y)) = x
    simpa only [AddEquiv.symm_apply_apply] using hy

end Langlands.Cohomology.AbelianSheafH1FiniteCocycles
