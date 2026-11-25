/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
public import Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.AlgebraicGeometry.ModuleInjectiveOpenCoverCechAcyclic
import WeilConjectures.AlgebraicGeometry.PrincipalOpenSubsetCechComparison

/-! # Subset Čech exactness for a single injective coefficient module

Source: Stacks Project, Cohomology, Tags 01EP and 01FM.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- Positive-degree exactness with one fixed coefficient module.

Source: Stacks Project, Cohomology, Tags 01EP and 01FM; Tag 08C1, first paragraph.
(blueprint: lem-sc-principal-open-injective-subset-exact).

Proof: Construct the full Čech complex with the actual finite intersections
inside X and apply injective module open-cover Čech acyclicity to the cover of
the union of the D(f_i). Changing the target from that union to the top open
leaves all intersections, restriction maps and hence the complex unchanged.
Forgetting global scalars and then restricting them to A has the same underlying
abelian presheaf. Use the subset-coordinate comparison, valid for any presheaf
and any family of opens without a covering hypothesis, to transport zero full
homology to zero subset homology in degree k>0. Its explicit differential formula
identifies the assumed signed sum with a cocycle. The elementwise exactness
criterion for abelian groups supplies a primitive in degree k-1. Evaluate its
subset-coordinate isomorphism on subsets of size k and extend by zero at other
cardinalities. On size k+1 every deletion is nonempty and has size k, so the
coordinate differential equation is exactly the claimed primitive equation.
If k+1 exceeds r there are no such subsets; if k+1=r the outgoing equation is
vacuous but positive exactness still applies. Empty or repeated principal opens
and the empty cover are permitted by both cited results. -/
theorem principalOpen_injective_subset_exact
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A)
    (M : SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) :
    let D : Finset (Fin r) → (Spec (.of A)).Opens :=
      fun S ↦ PrimeSpectrum.basicOpen (∏ j ∈ S, f j)
    ∀ (hle : ∀ (S : Finset (Fin r)) (j : Fin r), D S ≤ D (S.erase j))
      (k : ℕ), 1 ≤ k → Injective M →
      ∀ c : (∀ S : {S : Finset (Fin r) // S.Nonempty},
        (modulesSpecToSheaf.obj M).obj.obj (op (D S.val))),
      (∀ S : {S : Finset (Fin r) // S.Nonempty}, S.val.card = k + 2 →
        (∑ j : S.val, if h : (S.val.erase j.val).Nonempty then
            (-1 : A) ^ ((S.val.filter (fun i ↦ i < j.val)).card) •
              (modulesSpecToSheaf.obj M).obj.map (homOfLE (hle S.val j.val)).op
                (c ⟨S.val.erase j.val, h⟩)
          else 0) = 0) →
      ∃ b : (∀ S : {S : Finset (Fin r) // S.Nonempty},
        (modulesSpecToSheaf.obj M).obj.obj (op (D S.val))),
        ∀ S : {S : Finset (Fin r) // S.Nonempty}, S.val.card = k + 1 →
          (∑ j : S.val, if h : (S.val.erase j.val).Nonempty then
            (-1 : A) ^ ((S.val.filter (fun i ↦ i < j.val)).card) •
              (modulesSpecToSheaf.obj M).obj.map (homOfLE (hle S.val j.val)).op
                (b ⟨S.val.erase j.val, h⟩)
          else 0) = c S  := by
  classical
  dsimp only
  intro hle k hk hInject c hc
  have : Injective M := hInject
  obtain ⟨p, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  let U : Fin r → (Spec (.of A)).Opens := fun i ↦ PrimeSpectrum.basicOpen (f i)
  let D : Finset (Fin r) → (Spec (.of A)).Opens :=
    fun T ↦ PrimeSpectrum.basicOpen (∏ j ∈ T, f j)
  let S : SiteCechComplex U (fun i ↦ homOfLE (le_top : U i ≤ ⊤)) :=
    { W := fun a t ↦ ⨅ j : Fin (a + 1), U (t j)
      pr := fun _ t j ↦ homOfLE (iInf_le (fun j ↦ U (t j)) j)
      comm := fun _ _ _ ↦ Subsingleton.elim _ _
      universal := by
        intro a t Z b _
        refine ⟨homOfLE (le_iInf fun j ↦ leOfHom (b j)), ?_, ?_⟩
        · intro j; exact Subsingleton.elim _ _
        · intro b _; exact Subsingleton.elim _ _
      W_zero := by intro t; simp
      pr_zero := fun _ ↦ Subsingleton.elim _ _
      indexMap := fun t α ↦ homOfLE
        (le_iInf fun j ↦ iInf_le (fun j ↦ U (t j)) (α j))
      indexMap_pr := fun _ _ _ ↦ Subsingleton.elim _ _ }
  let V : (Spec (.of A)).Opens := iSup U
  let SV : SiteCechComplex U (fun i ↦ homOfLE (le_iSup U i)) :=
    { W := S.W
      pr := S.pr
      comm := fun _ _ _ ↦ Subsingleton.elim _ _
      universal := by
        intro a t Z b _
        exact S.universal a t Z b (fun _ ↦ Subsingleton.elim _ _)
      W_zero := S.W_zero
      pr_zero := S.pr_zero
      indexMap := S.indexMap
      indexMap_pr := S.indexMap_pr }
  let F := (modulesSpecToSheaf.obj M).obj
  obtain ⟨C, e, z, hd, hz⟩ := principalOpen_subset_cech_comparison A r f F S hle
  have hfull := Scheme.Modules.module_injective_open_cover_cech_acyclic M V
    (Fin r) U (fun i ↦ le_iSup U i) rfl SV (p + 1) (by omega)
  have hfull' : IsZero ((S.complex (F ⋙ forget₂ _ AddCommGrpCat)).homology (p + 1)) :=
    hfull
  have := hz (p + 1)
  have hzero : IsZero (C.homology (p + 1)) :=
    hfull'.of_iso (asIso (HomologicalComplex.homologyMap z (p + 1))).symm
  have hex : C.ExactAt (p + 1) :=
    (HomologicalComplex.exactAt_iff_isZero_homology _ _).mpr hzero
  rw [HomologicalComplex.exactAt_iff' _ p (p + 1) ((p + 1) + 1)
      (by simp) (by simp), ShortComplex.ab_exact_iff] at hex
  let c₀ : C.X (p + 1) := (e (p + 1)).inv
    (fun T ↦ c ⟨T.val, Finset.card_pos.mp (by omega)⟩)
  have hc₀ : C.d (p + 1) ((p + 1) + 1) c₀ = 0 := by
    apply (AddCommGrpCat.mono_iff_injective (e ((p + 1) + 1)).hom).mp inferInstance
    rw [map_zero]
    ext T
    rw [hd]
    change _ = (0 : F.obj (op (D T.val)))
    have hh := hc ⟨T.val, Finset.card_pos.mp (by omega)⟩ T.property
    simp only [c₀, ← ConcreteCategory.comp_apply, Iso.inv_hom_id,
      ConcreteCategory.id_apply]
    convert hh using 1
    apply Finset.sum_congr rfl
    intro j _
    have hn : (T.val.erase j.val).Nonempty := Finset.card_pos.mp (by
      rw [Finset.card_erase_of_mem j.property, T.property]
      omega)
    simp only [dite_eq_left hn]
    rfl
  obtain ⟨b₀, hb₀⟩ := hex c₀ hc₀
  change C.d p (p + 1) b₀ = c₀ at hb₀
  let b : ∀ T : {T : Finset (Fin r) // T.Nonempty}, F.obj (op (D T.val)) :=
    fun T ↦ if h : T.val.card = p + 1 then (e p).hom b₀ ⟨T.val, h⟩ else 0
  refine ⟨b, ?_⟩
  intro T hT
  have hh := congrFun (congrArg (e (p + 1)).hom hb₀) ⟨T.val, hT⟩
  rw [hd] at hh
  simp only [c₀, ← ConcreteCategory.comp_apply, Iso.inv_hom_id,
    ConcreteCategory.id_apply] at hh
  convert hh using 1
  apply Finset.sum_congr rfl
  intro j _
  have hj : (T.val.erase j.val).card = p + 1 := by
    rw [Finset.card_erase_of_mem j.property, hT]
    omega
  have hn : (T.val.erase j.val).Nonempty := Finset.card_pos.mp (by omega)
  simp only [dite_eq_left hn, b, dite_eq_left hj]
  rfl

end AlgebraicGeometry
