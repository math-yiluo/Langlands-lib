/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek

import WeilConjectures.AlgebraicGeometry.ModuleSheafConstantRingEquivalence
import WeilConjectures.CategoryTheory.Sites.InjectivePresheafModuleCechCocycleLiftMax
import WeilConjectures.CategoryTheory.InjectiveModulePresheaf
import Mathlib.Algebra.Homology.ShortComplex.Ab
import WeilConjectures.AlgebraicGeometry.EtaleCechVanishingCriterion
import WeilConjectures.AlgebraicGeometry.EtaleSiteCechComplexComparison

/-!
# Underlying abelian acyclicity of injective module-valued étale sheaves

Source: Stacks Project, Cohomology on Sites, Tag 03FD, second paragraph of its proof.
(blueprint: lem-weil-pbc-etale-module-injective-forget-acyclic).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- The underlying abelian sheaf of an injective module-valued étale sheaf is acyclic
for global sections. Its underlying abelian sheaf need not be injective.
Source: Stacks Project, Tag 03FD, second paragraph, via Tags 03FC and 03F9.
(blueprint: lemma-cohomology-modules-underlying-abelian--1).

Proof:
1. Identify sheaves valued in `ModuleCat Λ` with modules over the constant ring sheaf.
Global scalars act sectionwise. Conversely, sections of the constant ring sheaf are
locally represented by scalars; act using representatives and glue. Local equality
makes the action independent of representatives. The sheaf condition proves the
module identities and the inverse equivalence. The equivalence commutes with the
underlying abelian sheaf and preserves injectives.
2. On every object and every covering of the small étale site, positive Čech cohomology
of an injective module sheaf is zero. Use the ringed-site injective-module Čech theorem:
its free Čech chain complex is exact in positive degrees, and Hom into an injective
presheaf of modules is exact. Forgetting module actions leaves the same section groups,
restriction maps, and Čech differential.
3. Apply the abelian Čech vanishing criterion with all étale objects and all covering
families. All covering objects and fibre products belong to this collection, and each
covering refines itself. Step 2 supplies the Čech vanishing hypothesis. Hence positive
right derived evaluation of the underlying abelian sheaf vanishes on every object.
4. The identity of `Y` is terminal in the small étale site. Evaluation there is naturally
abelian global sections; transport the vanishing through this natural isomorphism of
left exact functors and their right derived functors. Take degree `n + 1`. -/
theorem isZero_rightDerived_globalSections_forget_of_injective
    (Y : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ]
    (G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [Injective G] (n : ℕ) :
    IsZero (((Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{u + 1}).rightDerived
      (n + 1)).obj ((sheafCompose Y.smallEtaleTopology
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj G)) := by
  obtain ⟨e, ⟨eAb⟩⟩ := moduleSheaf_constantRing_equivalence Λ Y
  let O := (sheafCompose Y.smallEtaleTopology
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
    ((constantSheaf Y.smallEtaleTopology CommRingCat.{u + 1}).obj (CommRingCat.of Λ))
  let I : SheafOfModules.{u + 1} O := e.functor.obj G
  have : Injective I := (e.map_injective_iff G).mpr inferInstance
  have htop : Y.smallEtaleTopology.toPrecoverage.toGrothendieck =
      Y.smallEtaleTopology := by
    apply le_antisymm
    · exact Y.smallEtaleTopology.toGrothendieck_toPrecoverage_le
    · intro U S hS
      simpa only [Sieve.generate_sieve] using
        Precoverage.generate_mem_toGrothendieck
          ((GrothendieckTopology.arrows_mem_toPrecoverage_iff _ S).mpr hS)
  let J := Y.smallEtaleTopology.toPrecoverage
  have hcech (U : Y.Etale) (T : Type (u + 1)) (V : T → Y.Etale)
      (f : ∀ t : T, V t ⟶ U) (hf : Sieve.ofArrows V f ∈ Y.smallEtaleTopology U)
      (p : ℕ) (hp : 0 < p) :
      IsZero (((cechComplexFunctor fun t : T ↦ Over.mk (f t)).obj
        ((Over.forget U).op ⋙ ((SheafOfModules.toSheaf O).obj I).obj)).homology p) := by
    have hcover : Presieve.ofArrows V f ∈ J U := hf
    obtain ⟨S⟩ := SiteCechComplex.exists_of_covering J hcover
    have hzero : IsZero ((S.cohomologyFunctor p).obj I.val.presheaf) := by
      have : Injective I.val := injective_module_sheaf_injective_presheaf O I
      obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hp)
      change IsZero ((S.complex I.val.presheaf).homology (q + 1))
      apply HomologicalComplex.ExactAt.isZero_homology
      apply (HomologicalComplex.exactAt_iff' (S.complex I.val.presheaf)
        q (q + 1) (q + 2) (by simp) (by simp)).2
      rw [ShortComplex.ab_exact_iff]
      intro c hc
      change (CochainComplex.of.d (S.cochains I.val.presheaf)
        (S.differential I.val.presheaf) (q + 1) ((q + 1) + 1)) c = 0 at hc
      rw [CochainComplex.of_d] at hc
      obtain ⟨b, hb⟩ := injective_presheaf_module_cech_cocycle_lift_max.{u + 1, u, u + 1}
        O.obj I.val V f S q c hc
      refine ⟨b, ?_⟩
      change (CochainComplex.of.d (S.cochains I.val.presheaf)
        (S.differential I.val.presheaf) q (q + 1)) b = c
      rw [CochainComplex.of_d]
      exact hb
    obtain ⟨c⟩ := nonempty_etale_siteCech_complex_iso Y U V f S I.val.presheaf
    exact hzero.of_iso ((HomologicalComplex.homologyFunctor _ _ p).mapIso c.symm)
  have hvan := isZero_rightDerived_etale_of_cech_vanishing Y Set.univ
    (fun U _ V f ↦ Sieve.ofArrows V f ∈ Y.smallEtaleTopology U)
    ((SheafOfModules.toSheaf O).obj I)
    (fun _ _ _ _ h ↦ h)
    (fun _ _ _ _ _ ↦ ⟨Set.mem_univ _, fun _ ↦ Set.mem_univ _,
      fun _ _ ↦ Set.mem_univ _⟩)
    (fun _ _ T V f hf ↦ ⟨T, V, f, hf, fun t ↦ ⟨t, 𝟙 _, by simp⟩⟩)
    hcech (terminal Y.Etale) (Set.mem_univ _) (n + 1) (Nat.zero_lt_succ n)
  let c := Sheaf.ΓNatIsoSheafSections Y.smallEtaleTopology
    AddCommGrpCat.{u + 1} (terminalIsTerminal (C := Y.Etale))
  have : ((sheafSections Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (Opposite.op (terminal Y.Etale))).Additive :=
    Functor.additive_of_iso c
  let d : (Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{u + 1}).rightDerived (n + 1) ≅
      ((sheafSections Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (Opposite.op (terminal Y.Etale))).rightDerived (n + 1) :=
    { hom := c.hom.rightDerived (n + 1)
      inv := c.inv.rightDerived (n + 1)
      hom_inv_id := by rw [← NatTrans.rightDerived_comp, c.hom_inv_id,
        NatTrans.rightDerived_id]
      inv_hom_id := by rw [← NatTrans.rightDerived_comp, c.inv_hom_id,
        NatTrans.rightDerived_id] }
  exact (hvan.of_iso (d.app ((SheafOfModules.toSheaf O).obj I))).of_iso
    (((Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{u + 1}).rightDerived
      (n + 1)).mapIso (eAb.app G).symm)

end AlgebraicGeometry.Scheme
