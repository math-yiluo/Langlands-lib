/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.RingTheory.Valuation.ValuationRing
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
import WeilConjectures.AlgebraicGeometry.QuotientBaseChangeIdeal
import WeilConjectures.AlgebraicGeometry.ClosedImmersionUnitQuotient
import WeilConjectures.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections
import WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula

/-!
# Vanishing of sections on the closed fibre of a valuation ring

Source: Stacks Project, More on Morphisms, Tag 0EX8,
Lemma `lemma-triviality-generic-fibre-valuation-ring`, closed-fibre section descent
(blueprint: lem-sc-valuation-closed-fibre-section-vanishing).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules

open MonoidalCategory in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem quotient_unit_eq_zero_iff
    {A : Type u} [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) (I : Ideal A)
    (L : X.Modules) [L.IsQuasicoherent] (U : X.affineOpens) (t : Γ(L, U.1)) :
    ((Classical.choose (exists_tensorPullbackAdjunction
      (pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))))).unit.app
        L).val.app (op U.1) t = 0 ↔
      t ∈ I.map ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appLE ⊤ U.1 le_top).hom •
        (⊤ : Submodule Γ(X, U.1) Γ(L, U.1)) := by
  classical
  let j := pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
  have : IsClosedImmersion j := (quotientBaseChange_closedImmersion_ideal f I).1
  let adj₀ := Classical.choice (nonempty_tensorPullbackAdjunction j)
  let adj := Classical.choose (exists_tensorPullbackAdjunction j)
  let μ := j.ker.toModulesι ▷ L ≫ (λ_ L).hom
  obtain ⟨w, ⟨hlim⟩⟩ := ((Classical.choose_spec
    (closedImmersion_unit_quotient j)).1 L).2.1
  let e : image μ ≅ kernel (adj₀.unit.app L) :=
    hlim.conePointUniqueUpToIso (limit.isLimit _)
  have he : e.hom ≫ kernel.ι (adj₀.unit.app L) = image.ι μ :=
    hlim.conePointUniqueUpToIso_hom_comp (limit.isLimit _) WalkingParallelPair.zero
  have hr : Set.range ((image.ι μ).app U.1) =
      {t | (adj₀.unit.app L).app U.1 t = 0} := by
    have hrange := range_map_kernelι U.1 (adj₀.unit.app L)
    change Set.range ((kernel.ι (adj₀.unit.app L)).app U.1) =
      {t | (adj₀.unit.app L).app U.1 t = 0} at hrange
    refine Eq.trans ?_ hrange
    ext t
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨e.hom.app U.1 a, congrArg (fun q ↦ q.app U.1 a) he⟩
    · rintro ⟨a, rfl⟩
      refine ⟨e.inv.app U.1 a, ?_⟩
      have hei : e.inv ≫ image.ι μ = kernel.ι (adj₀.unit.app L) := by
        rw [← he, Iso.inv_hom_id_assoc]
      exact congrArg (fun q ↦ q.app U.1 a) hei
  have hd := Adjunction.unit_rightAdjointUniq_hom_app adj₀ adj L
  let d := (Adjunction.rightAdjointUniq adj₀ adj).app ((tensorPullback j).obj L)
  have hi : Function.Injective (d.hom.app U.1) :=
    (ModuleCat.mono_iff_injective
      ((SheafOfModules.evaluation X.ringCatSheaf (op U.1)).map d.hom)).mp inferInstance
  have hz : (adj.unit.app L).app U.1 t = 0 ↔ (adj₀.unit.app L).app U.1 t = 0 := by
    have hh := congrArg (fun q ↦ q.app U.1 t) hd
    change d.hom.app U.1 ((adj₀.unit.app L).app U.1 t) =
      (adj.unit.app L).app U.1 t at hh
    constructor
    · intro ht
      apply hi
      exact (hh.trans ht).trans (map_zero _).symm
    · intro ht
      exact hh.symm.trans ((congrArg (d.hom.app U.1) ht).trans (map_zero _))
  have hideal := (quotientBaseChange_closedImmersion_ideal f I).2
  have hsections := ((ideal_times_quasiCoherent_affine_sections j.ker L).2.2.2.1 U).1
  have hk : j.ker.ideal U =
      I.map ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appLE ⊤ U.1 le_top).hom := by
    rw [hideal.1]
    exact (hideal.2 U).2.1
  change (adj.unit.app L).app U.1 t = 0 ↔ _
  rw [hz, ← hk]
  exact (Set.ext_iff.mp (hr.symm.trans hsections) t)

private theorem exists_principal_stage
    {A B M : Type u} [CommRing A] [IsDomain A] [ValuationRing A]
    [CommRing B] [AddCommGroup M] [Module B M] (φ : A →+* B) (t : M)
    (ht : t ∈ (IsLocalRing.maximalIdeal A).map φ • (⊤ : Submodule B M)) :
    ∃ a : IsLocalRing.maximalIdeal A,
      t ∈ (Ideal.span {a.val}).map φ • (⊤ : Submodule B M) := by
  classical
  let P (a : IsLocalRing.maximalIdeal A) : Ideal A := Ideal.span {a.val}
  have hm : IsLocalRing.maximalIdeal A = ⨆ a, P a := by
    apply le_antisymm
    · intro a ha
      exact (le_iSup P ⟨a, ha⟩) (Ideal.subset_span (Set.mem_singleton a))
    · exact iSup_le fun a ↦ Ideal.span_le.mpr (by simp)
  have hdir : Directed (· ≤ ·) P := by
    intro a b
    rcases le_total (P a) (P b) with h | h
    · exact ⟨b, h, le_rfl⟩
    · exact ⟨a, le_rfl, h⟩
  have hd : Directed (· ≤ ·)
      (fun a ↦ (P a).map φ • (⊤ : Submodule B M)) := by
    intro a b
    obtain ⟨c, ha, hb⟩ := hdir a b
    exact ⟨c, Submodule.smul_mono_left (Ideal.map_mono ha),
      Submodule.smul_mono_left (Ideal.map_mono hb)⟩
  rw [hm, Ideal.map_iSup, Submodule.iSup_smul] at ht
  exact (Submodule.mem_iSup_of_directed _ hd).mp ht

private theorem finite_principal_upper_bound
    {A : Type u} [CommRing A] [IsDomain A] [ValuationRing A]
    (T : Finset (IsLocalRing.maximalIdeal A)) (a₀ : IsLocalRing.maximalIdeal A) :
    ∃ a : IsLocalRing.maximalIdeal A,
      Ideal.span {a₀.val} ≤ Ideal.span {a.val} ∧
        ∀ b ∈ T, Ideal.span {b.val} ≤ Ideal.span {a.val} := by
  classical
  induction T using Finset.induction_on with
  | empty => exact ⟨a₀, le_rfl, by simp⟩
  | @insert b T hb ih =>
    obtain ⟨a, ha₀, ha⟩ := ih
    rcases le_total (Ideal.span {a.val}) (Ideal.span {b.val}) with h | h
    · refine ⟨b, ha₀.trans h, ?_⟩
      intro c hc
      rcases Finset.mem_insert.mp hc with rfl | hc
      · exact le_rfl
      · exact (ha c hc).trans h
    · refine ⟨a, ha₀, ?_⟩
      intro c hc
      rcases Finset.mem_insert.mp hc with rfl | hc
      · exact h
      · exact ha c hc

-- Keep the compactness and sheaf arguments independent of the tensor-pullback construction.
private theorem exists_nonzero_maximalIdeal_family_section_eq_zero
    {A : Type u} [CommRing A] [IsDomain A] [ValuationRing A] (hA : ¬ IsField A)
    {X : Scheme.{u}} [CompactSpace X] (f : X ⟶ Spec (CommRingCat.of A))
    (L : X.Modules) (N : Ideal A → X.Modules) (η : ∀ I, L ⟶ N I)
    (hη : ∀ (I : Ideal A) (U : X.affineOpens) (t : Γ(L, U.1)),
      (η I).app U.1 t = 0 ↔
        t ∈ I.map ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appLE ⊤ U.1 le_top).hom •
          (⊤ : Submodule Γ(X, U.1) Γ(L, U.1)))
    (s : Γ(L, ⊤)) (hs : (η (IsLocalRing.maximalIdeal A)).app ⊤ s = 0) :
    ∃ π : A, π ≠ 0 ∧ π ∈ IsLocalRing.maximalIdeal A ∧
      (η (Ideal.span {π})).app ⊤ s = 0 := by
  classical
  let t (U : X.affineOpens) := L.presheaf.map (homOfLE (show U.1 ≤ ⊤ from le_top)).op s
  have hm (U : X.affineOpens) :
      (η (IsLocalRing.maximalIdeal A)).app U.1 (t U) = 0 := by
    have hn := congrArg (fun q ↦ q s)
      ((η (IsLocalRing.maximalIdeal A)).val.naturality
        (homOfLE (show U.1 ≤ ⊤ from le_top)).op)
    change (η (IsLocalRing.maximalIdeal A)).app U.1 (t U) =
      (N (IsLocalRing.maximalIdeal A)).presheaf.map
        (homOfLE (show U.1 ≤ ⊤ from le_top)).op
        ((η (IsLocalRing.maximalIdeal A)).app ⊤ s) at hn
    exact hn.trans (by rw [hs]; exact map_zero _)
  have hlocal (U : X.affineOpens) : ∃ a : IsLocalRing.maximalIdeal A,
      t U ∈ (Ideal.span {a.val}).map
        ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appLE ⊤ U.1 le_top).hom •
        (⊤ : Submodule Γ(X, U.1) Γ(L, U.1)) := by
    exact exists_principal_stage _ (t U)
      ((hη (IsLocalRing.maximalIdeal A) U (t U)).mp (hm U))
  choose a ha using hlocal
  have hcover : Set.univ ⊆ ⋃ U : X.affineOpens, (U.1 : Set X) := by
    intro x hx
    obtain ⟨U, hU, hxU, _⟩ := exists_isAffineOpen_mem_and_subset
      (show x ∈ (⊤ : X.Opens) from trivial)
    exact Set.mem_iUnion.mpr ⟨⟨U, hU⟩, hxU⟩
  obtain ⟨S, hS⟩ := isCompact_univ.elim_finite_subcover
    (fun U : X.affineOpens ↦ (U.1 : Set X)) (fun U ↦ U.1.isOpen) hcover
  obtain ⟨a₀, ha₀, hne₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (show IsLocalRing.maximalIdeal A ≠ ⊥ from
      fun h ↦ hA (IsLocalRing.isField_iff_maximalIdeal_eq.mpr h))
  obtain ⟨π, hπ₀, hπ⟩ := finite_principal_upper_bound (S.image a) ⟨a₀, ha₀⟩
  have hne : π.val ≠ 0 := by
    intro hz
    have hmem := hπ₀ (Ideal.subset_span (Set.mem_singleton a₀))
    have hdiv : π.val ∣ a₀ := Ideal.mem_span_singleton.mp hmem
    exact hne₀ (zero_dvd_iff.mp (hz ▸ hdiv))
  refine ⟨π.val, hne, π.property, ?_⟩
  have hzero (U : S) : (η (Ideal.span {π.val})).app U.1.1 (t U.1) = 0 := by
    apply (hη (Ideal.span {π.val}) U.1 (t U.1)).mpr
    exact Submodule.smul_mono_left
      (Ideal.map_mono (hπ (a U.1) (Finset.mem_image.mpr ⟨U.1, U.2, rfl⟩))) (ha U.1)
  have htop : (⊤ : X.Opens) ≤ ⨆ U : S, U.1.1 := by
    intro x hx
    obtain ⟨U, hU⟩ := Set.mem_iUnion.mp (hS (Set.mem_univ x))
    obtain ⟨hUS, hxU⟩ := Set.mem_iUnion.mp hU
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨U, hUS⟩, hxU⟩
  apply TopCat.Sheaf.eq_of_locally_eq' ((SheafOfModules.toSheaf _).obj (N (Ideal.span {π.val})))
    (fun U : S ↦ U.1.1) ⊤ (fun _ ↦ homOfLE le_top) htop
  intro U
  have hn := congrArg (fun q ↦ q s)
    ((η (Ideal.span {π.val})).val.naturality
      (homOfLE (show U.1.1 ≤ ⊤ from le_top)).op)
  change (η (Ideal.span {π.val})).app U.1.1 (t U.1) =
    (N (Ideal.span {π.val})).presheaf.map (homOfLE (show U.1.1 ≤ ⊤ from le_top)).op
      ((η (Ideal.span {π.val})).app ⊤ s) at hn
  exact hn.symm.trans ((hzero U).trans (map_zero _).symm)


set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A section vanishing on the closed fibre vanishes modulo a nonzero element of the
maximal ideal. Source: Stacks Project, Tag 0EX8, proof of
`lemma-triviality-generic-fibre-valuation-ring`.
(blueprint: lem-sc-valuation-closed-fibre-section-vanishing)

Proof:
1. Since the valuation ring is not a field, its maximal ideal contains a nonzero element.
   Nonzero elements of the maximal ideal, ordered by divisibility, give a filtered system
   of quotients with colimit the residue field. The corresponding base changes of `X`
   form an inverse system with affine transition maps and limit the closed fibre.
   Fix one stage and restrict `L` and `s` to it; further pullbacks are their restrictions.
2. Apply `lem-sc-valuation-limit-qcoh-section-descent` to this quasi-coherent module on
   the quasi-compact quasi-separated stages. Its eventual-zero clause gives a nonzero
   element of the maximal ideal at whose stage the section vanishes. -/
theorem exists_nonzero_maximalIdeal_section_eq_zero
    (A : Type u) [CommRing A] [IsDomain A] [ValuationRing A] (hA : ¬ IsField A)
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    (L : X.Modules) [L.IsInvertible] (s : L.val.obj (op ⊤))
    (hs : ((Classical.choose (exists_tensorPullbackAdjunction
      (pullback.fst f (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A))))))).unit.app L).val.app (op ⊤) s = 0) :
    ∃ π : A, π ≠ 0 ∧ π ∈ IsLocalRing.maximalIdeal A ∧
      ((Classical.choose (exists_tensorPullbackAdjunction
        (pullback.fst f (Spec.map (CommRingCat.ofHom
          (Ideal.Quotient.mk (Ideal.span {π}))))))).unit.app L).val.app (op ⊤) s = 0 := by
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : L.IsQuasicoherent := IsInvertible.isQuasicoherent L
  exact exists_nonzero_maximalIdeal_family_section_eq_zero hA f L
    (fun I ↦ (pushforward (pullback.fst f (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk I))))).obj
        ((tensorPullback (pullback.fst f (Spec.map (CommRingCat.ofHom
          (Ideal.Quotient.mk I))))).obj L))
    (fun I ↦ (Classical.choose (exists_tensorPullbackAdjunction
      (pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))))).unit.app L)
    (fun I U t ↦ quotient_unit_eq_zero_iff f I L U t) s hs

end AlgebraicGeometry.Scheme.Modules
