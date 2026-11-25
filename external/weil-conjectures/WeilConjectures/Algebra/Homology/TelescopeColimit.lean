/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Limits
import WeilConjectures.Algebra.Homology.TelescopeShiftMono
public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-!
# Telescope comparison for complexes of sheaves of modules

Source: Stacks Project, Derived Categories, Lemma 0949, and Cohomology on Sites,
Section 21.17 (blueprint: lem-pc-complex-hocolim-colimit).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

open HomComplex

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{u})
  (E : ℕ ⥤ CochainComplex
    (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ)

/-- The `1 - shift` endomorphism of the direct sum of a sequential system of
complexes (Stacks, Derived Categories, Definition of derived colimits;
blueprint: lem-pc-complex-hocolim-colimit). 
(blueprint: lem-pc-complex-hocolim-colimit)
-/
noncomputable def telescopeColimitShift :
    (∐ (fun n : ℕ => E.obj n)) ⟶ (∐ (fun n : ℕ => E.obj n)) :=
  Sigma.desc (fun n : ℕ =>
    Sigma.ι (fun n : ℕ => E.obj n) n -
      E.map (homOfLE (Nat.le_succ n)) ≫ Sigma.ι (fun n : ℕ => E.obj n) (n + 1))

/-- The canonical map from the direct sum of a sequential system of complexes
to its colimit (Stacks, Derived Categories, Lemma 0949;
blueprint: lem-pc-complex-hocolim-colimit). 
(blueprint: lem-pc-complex-hocolim-colimit)
-/
noncomputable def telescopeToColimit :
    (∐ (fun n : ℕ => E.obj n)) ⟶ colimit E :=
  Sigma.desc (fun n : ℕ => colimit.ι E n)

set_option backward.isDefEq.respectTransparency false in
private noncomputable def telescope_cokernel
    (h : telescopeColimitShift R E ≫ telescopeToColimit R E = 0) :
    IsColimit (CokernelCofork.ofπ (telescopeToColimit R E) h) := by
  let cocone (s : CokernelCofork (telescopeColimitShift R E)) : Cocone E :=
    { pt := s.pt
      ι :=
        { app := fun n ↦ Sigma.ι (fun n : ℕ ↦ E.obj n) n ≫ s.π
          naturality := by
            intro n m f
            have hs (k : ℕ) :
                E.map (homOfLE (Nat.le_succ k)) ≫
                    Sigma.ι (fun n : ℕ ↦ E.obj n) (k + 1) ≫ s.π =
                  Sigma.ι (fun n : ℕ ↦ E.obj n) k ≫ s.π := by
              have hz := congrArg
                (fun z ↦ Sigma.ι (fun n : ℕ ↦ E.obj n) k ≫ z) s.condition
              simp only [telescopeColimitShift, Sigma.ι_comp_desc_assoc, Preadditive.sub_comp,
                Category.assoc, comp_zero] at hz
              exact (sub_eq_zero.mp hz).symm
            have hall (m : ℕ) (hnm : n ≤ m) :
                E.map (homOfLE hnm) ≫
                    Sigma.ι (fun n : ℕ ↦ E.obj n) m ≫ s.π =
                  Sigma.ι (fun n : ℕ ↦ E.obj n) n ≫ s.π := by
              induction m, hnm using Nat.le_induction with
              | base => simp
              | succ k hnk ih =>
                rw [show homOfLE (Nat.le_trans hnk (Nat.le_succ k)) =
                  homOfLE hnk ≫ homOfLE (Nat.le_succ k) from Subsingleton.elim _ _]
                rw [E.map_comp, Category.assoc, hs k]
                exact ih
            have hf : f = homOfLE (leOfHom f) := Subsingleton.elim _ _
            rw [hf]
            exact hall m (leOfHom f) } }
  refine Cofork.IsColimit.mk _ (fun s ↦ colimit.desc E (cocone s)) ?_ ?_
  · intro s
    apply Sigma.hom_ext
    intro n
    simp [telescopeToColimit, cocone]
  · intro s m hm
    apply colimit.hom_ext (F := E)
    intro n
    have hn := congrArg (fun z ↦ Sigma.ι (fun n : ℕ ↦ E.obj n) n ≫ z) hm
    simpa [telescopeToColimit, cocone, Category.assoc] using hn

/-- (blueprint: lem-pc-complex-hocolim-colimit) For a sequential system of cochain
complexes of sheaves of modules on a ringed site, the canonical map from the cone
of `1 - shift` on its direct sum to its termwise filtered colimit is a
quasi-isomorphism (Stacks, Derived Categories, Lemma 0949).

In each degree, `1 - shift` is injective by examining the least nonzero summand.
Its cokernel is the filtered colimit, since the quotient relations identify an
element with its image in the next summand. The cone maps to this cokernel by
projection onto the unshifted summand. The kernel of this projection is
contractible: in the notation of the source proof, the homotopy sends
`(u(c), k)` to `(0, c)`. The long exact cohomology sequence of the resulting
short exact sequence makes the projection a quasi-isomorphism. -/
theorem quasiIso_telescopeColimit
    : ∃ f : mappingCone (telescopeColimitShift R E) ⟶ colimit E,
      mappingCone.inr (telescopeColimitShift R E) ≫ f = telescopeToColimit R E ∧
      (mappingCone.inl (telescopeColimitShift R E)).comp
        (Cochain.ofHom f) (add_zero _) = 0 ∧
      QuasiIso f := by
  have h : telescopeColimitShift R E ≫ telescopeToColimit R E = 0 := by
    apply Sigma.hom_ext
    intro n
    simp [telescopeColimitShift, telescopeToColimit, Preadditive.sub_comp,
      Category.assoc, colimit.w]
  let S := ShortComplex.mk (telescopeColimitShift R E) (telescopeToColimit R E) h
  have hc := telescope_cokernel R E h
  have hmono : Mono (telescopeColimitShift R E) := telescopeShift_mono R E
  have hS : S.ShortExact :=
    { exact := S.exact_of_g_is_cokernel hc
      mono_f := hmono
      epi_g := epi_of_isColimit_cofork hc }
  refine ⟨mappingCone.descShortComplex S, mappingCone.inr_descShortComplex S, ?_,
    mappingCone.quasiIso_descShortComplex hS⟩
  exact mappingCone.inl_desc S.f 0 S.g (by simp)

end CochainComplex
