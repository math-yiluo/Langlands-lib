/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import WeilConjectures.AlgebraicGeometry.Cohomology.Affine.CechAcyclic
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
public import WeilConjectures.Topology.Sheaves.MayerVietorisVanishing

/-!
# Vanishing of quasi-coherent cohomology above the number of affine opens

Let `X` be a quasi-compact separated scheme, covered by `n` affine opens. The cohomology of a
quasi-coherent `𝒪_X`-module, and more generally of an abelian sheaf which is Čech-acyclic on the
affine opens, vanishes in degrees `q ≥ n`.

On an affine open `U` the higher cohomology `H^q(U, F)` of such a sheaf vanishes, by dimension
shifting along `0 ⟶ F ⟶ I ⟶ Q ⟶ 0` with `I` injective: `Q` is again Čech-acyclic on the affine
opens and `I(U) ⟶ Q(U)` is surjective. As the intersection of two affine opens of a separated
scheme is affine, the Mayer-Vietoris induction `TopCat.Sheaf.subsingleton_H'_finsetSup` then
gives the vanishing on `X`.

This is a weak form of Grothendieck's vanishing theorem
(`AlgebraicGeometry.Scheme.Modules.subsingleton_H_of_topologicalKrullDim_lt`), with the
dimension replaced by the number of affine opens, and restricted to quasi-coherent modules; it
suffices for the finiteness of Euler characteristics on proper schemes over a field.

## Main statements

- `AlgebraicGeometry.Scheme.Modules.subsingleton_H'_succ_of_isAffineOpen`: the vanishing on an
  affine open.
- `AlgebraicGeometry.Scheme.Modules.exists_forall_subsingleton_H_of_isQuasicoherent`: on a
  quasi-compact separated scheme, all quasi-coherent cohomology vanishes above some degree.
-/

@[expose] public section

universe u

open CategoryTheory Limits Abelian TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- **Higher cohomology on an affine open vanishes.** For an abelian sheaf `F` on `X` which is
Čech-acyclic on the affine opens (for instance a quasi-coherent module), `H^q(U, F) = 0` for
every affine open `U` and every `q > 0`. -/
theorem subsingleton_H'_succ_of_isAffineOpen
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (hF : cechAcyclicOnAffines X F)
    {U : X.Opens} (hU : IsAffineOpen U) (q : ℕ) :
    Subsingleton (F.H' (q + 1) U : AddCommGrpCat.{u}) := by
  induction q generalizing F with
  | zero =>
    let S := ShortComplex.mk (Injective.ι F) (cokernel.π (Injective.ι F)) (cokernel.condition _)
    have hS : S.ShortExact := .mk' (ShortComplex.exact_cokernel _) inferInstance inferInstance
    change Subsingleton (Ext (TopCat.Sheaf.freeSheaf U) F 1)
    refine subsingleton_of_forall_eq 0 fun x ↦ ?_
    obtain ⟨y, rfl⟩ :=
      Ext.covariant_sequence_exact₁ _ hS x (Ext.eq_zero_of_injective _) (zero_add 1)
    obtain ⟨z, rfl⟩ := TopCat.Sheaf.surjective_comp_mk₀_of_surjective S.g U
      (surjective_app_of_cechAcyclicOnAffines hS hF hU) y
    dsimp only
    rw [Ext.comp_assoc_of_second_deg_zero, hS.comp_extClass, Ext.comp_zero]
  | succ q ih =>
    let S := ShortComplex.mk (Injective.ι F) (cokernel.π (Injective.ι F)) (cokernel.condition _)
    have hS : S.ShortExact := .mk' (ShortComplex.exact_cokernel _) inferInstance inferInstance
    have hQ : Subsingleton (Ext (TopCat.Sheaf.freeSheaf U) S.X₃ (q + 1)) :=
      ih S.X₃ (cechAcyclicOnAffines_under_cokernel hF).2
    change Subsingleton (Ext (TopCat.Sheaf.freeSheaf U) F (q + 2))
    refine subsingleton_of_forall_eq 0 fun x ↦ ?_
    obtain ⟨y, rfl⟩ :=
      Ext.covariant_sequence_exact₁ _ hS x (Ext.eq_zero_of_injective _) rfl
    rw [Subsingleton.elim y 0, Ext.zero_comp]

/-- **Quasi-coherent cohomology vanishes above the number of affine opens.** Let `X` be a
separated scheme which is the union of a nonempty finite family `U i`, `i ∈ s`, of affine
opens. If an abelian sheaf `F` on `X` is Čech-acyclic on the affine opens (for instance a
quasi-coherent module), then `H^q(X, F) = 0` for `q ≥ #s`. -/
theorem subsingleton_H_of_card_le [IsSeparated (terminal.from X)] {ι : Type*} (s : Finset ι)
    (hs : s.Nonempty) (U : ι → X.Opens) (hU : ∀ i ∈ s, IsAffineOpen (U i)) (hcov : s.sup U = ⊤)
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (hF : cechAcyclicOnAffines X F)
    {q : ℕ} (hq : s.card ≤ q) : Subsingleton (CategoryTheory.Sheaf.H F q) := by
  refine TopCat.Sheaf.subsingleton_H_of_subsingleton_H' F ?_
  rw [← hcov]
  exact TopCat.Sheaf.subsingleton_H'_finsetSup F IsAffineOpen (fun _ _ hU hV ↦ hU.inf hV)
    (fun _ hU q ↦ subsingleton_H'_succ_of_isAffineOpen F hF hU q) s hs U hU q hq

/-- A quasi-compact scheme is the union of a nonempty finite family of affine opens. -/
lemma exists_finset_isAffineOpen_sup_eq_top [CompactSpace X] :
    ∃ s : Finset X.affineOpens, s.Nonempty ∧ s.sup (fun U ↦ (U : X.Opens)) = ⊤ := by
  classical
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun U : X.affineOpens ↦ ((U : X.Opens) : Set X)) (fun U ↦ (U : X.Opens).isOpen)
    (fun x _ ↦ Set.mem_iUnion.2 (by
      obtain ⟨U, hU, hxU, -⟩ :=
        (TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens)
          (show x ∈ (⊤ : X.Opens) from trivial)
      exact ⟨⟨U, hU⟩, hxU⟩))
  let s := insert (⟨⊥, isAffineOpen_bot X⟩ : X.affineOpens) t
  refine ⟨s, Finset.insert_nonempty _ _, eq_top_iff.2 fun x _ ↦ ?_⟩
  obtain ⟨U, hU, hxU⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
  exact (Finset.le_sup (f := fun U : X.affineOpens ↦ (U : X.Opens))
    (Finset.mem_insert_of_mem hU)) hxU

/-- **Quasi-coherent cohomology vanishes in high degrees.** On a quasi-compact separated
scheme there is a degree above which the cohomology of every quasi-coherent module vanishes:
the number of affine opens in a finite affine open covering. -/
theorem exists_forall_subsingleton_H_of_isQuasicoherent [CompactSpace X]
    [IsSeparated (terminal.from X)] :
    ∃ D : ℕ, ∀ (M : X.Modules) [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) M]
      (q : ℕ), D < q → Subsingleton (M.H q) := by
  obtain ⟨s, hs, hcov⟩ := exists_finset_isAffineOpen_sup_eq_top (X := X)
  exact ⟨s.card, fun M _ q hq ↦ subsingleton_H_of_card_le s hs (fun U ↦ (U : X.Opens))
    (fun U _ ↦ U.2) hcov _ (cechAcyclicOnAffines_of_isQuasicoherent M) hq.le⟩

end AlgebraicGeometry.Scheme.Modules
