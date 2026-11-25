/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Coherent
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Subobject.Limits
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.CoherentKernelCokernelSum
import WeilConjectures.AlgebraicGeometry.CoherentSupportUnionExactSequence
import WeilConjectures.AlgebraicGeometry.FiniteTypeModuleSupportClosed

import WeilConjectures.AlgebraicGeometry.CoherentIntegralFiltrationExtension
import WeilConjectures.AlgebraicGeometry.CoherentIntegralFiltrationAdicReduction
import WeilConjectures.AlgebraicGeometry.CoherentIntegralFiltrationGenericStep
import Mathlib.Topology.Sheaves.Abelian
import Mathlib.Algebra.Category.Grp.Zero

/-!
# A coherent filtration supported on integral closed subschemes

Source: Stacks Project, Cohomology of Schemes, Lemma 30.12.3, Tag 01YF
(blueprint: lem-weil-pbc-coherent-filtration-integral-subschemes).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

private theorem filtration_of_isZero {X : Scheme.{u}} [IsLocallyNoetherian X]
    (F : X.Modules) (hF : RingedSpace.IsCoherent X.toRingedSpace F) (hz : IsZero F) :
    HasCoherentIntegralFiltration F := by
  have := Subobject.subsingleton_of_isZero hz
  refine ⟨0, fun _ ↦ ⊥, fun _ _ _ ↦ le_rfl, rfl, Subsingleton.elim _ _, ?_, ?_⟩
  · intro k
    exact (RingedSpace.coherent_kernel_cokernel_sum X.toRingedSpace).2.2.2.2
      F ((⊥ : Subobject F) : X.Modules)
      (hz.isoZero ≪≫ Subobject.botCoeIsoZero.symm) hF
  · intro j
    exact Fin.elim0 j

private theorem support_closed {X : Scheme.{u}} [IsLocallyNoetherian X]
    (F : X.Modules) (hF : RingedSpace.IsCoherent X.toRingedSpace F) :
    IsClosed {x : X | ¬ Subsingleton (F.presheaf.stalk x)} := by
  obtain ⟨hq, ht⟩ := (isCoherent_iff_isQuasicoherent_and_isFiniteType X F).mp hF
  have := hq
  have := ht
  exact (finite_type_module_support_closed X F).2.2.2

private theorem isZero_of_empty_support {X : Scheme.{u}} (F : X.Modules)
    (hSupp : {x : X | ¬ Subsingleton (F.presheaf.stalk x)} = ∅) : IsZero F := by
  classical
  let T := SheafOfModules.toSheaf X.ringCatSheaf
  have hz : IsZero (T.obj F) := by
    apply (TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero _).mpr
    intro x
    have : Subsingleton (F.presheaf.stalk x) := by
      by_contra hn
      have hx : x ∈ {x : X | ¬ Subsingleton (F.presheaf.stalk x)} := hn
      rw [hSupp] at hx
      exact hx
    change IsZero (F.presheaf.stalk x)
    exact AddCommGrpCat.isZero_of_subsingleton _
  rw [IsZero.iff_id_eq_zero]
  apply T.map_injective
  rw [T.map_id, T.map_zero]
  exact hz.eq_of_src _ _

/-- A coherent module on a Noetherian scheme has a finite filtration by coherent submodules
whose successive quotients are pushforwards of nonzero coherent ideals on integral closed
subschemes. A sheaf of ideals of `𝒪_Z` is a `Z.IdealSheafData`, viewed as an `𝒪_Z`-module by
`IdealSheafData.toModules`; it is nonzero (`≠ ⊥`) and its module is coherent.
Quotients are cokernels of the canonical subobject inclusions.

Source: Stacks Project, Cohomology of Schemes, Tag 01YF
(blueprint: lem-weil-pbc-coherent-filtration-integral-subschemes).

Proof:
1. Coherent modules are closed under kernels, cokernels and finite sums on a locally
Noetherian scheme, and have closed support (pqf-lem-coherent-ft-locnoeth,
lem-weil-pbc-coherent-kernel-cokernel-locnoeth,
lem-weil-pbc-finite-type-module-support-closed). Stalk exactness and detection of isomorphisms
are lem-weil-pbc-module-stalk-exact and lem-weil-pbc-module-iso-on-stalks.
2. Call a module good if it admits this filtration. The zero module is good. Pull back a
filtration of a quotient and concatenate with a filtration of the submodule to show goodness
is closed under extensions, using the stalk lemmas of step 1.
3. Choose a minimal closed support of a nongood coherent module by
lem-weil-pbc-noetherian-scheme-closed-subsets-minimal. Its support is nonempty.
4. A reducible support is a union of two proper closed subsets. Apply
lem-weil-pbc-coherent-support-union-exact-sequence and minimality, contradicting step 2.
5. Give this irreducible support its reduced induced structure, an integral closed subscheme
(lem-weil-pbc-reduced-induced-closed-subscheme, lem-weil-pbc-scheme-sober). Its ideal J has
vanishing locus the support and generic stalk equal to the ambient maximal ideal, by
lem-weil-pbc-ideal-module-product-stalk and lem-weil-pbc-basic-open-function.
6. Some power of J kills the module (lem-weil-pbc-coherent-support-power-ideal-kills).
The J-adic filtration has coherent successive quotients annihilated by J, by
lem-weil-pbc-ideal-times-quasi-coherent-affine-sections and the stalk lemmas. If all these
quotients were good, step 2 would give a contradiction. Replace the module by a nongood
quotient; minimality ensures it has the same support.
7. Apply lem-weil-pbc-coherent-generic-point-ideal-inclusion to embed the pushforward of a
finite sum of a coherent ideal into this module, isomorphically near the generic point.
Closed pushforward preserves coherence (lem-weil-pbc-closed-immersion-coherent-equivalence;
local Noetherianity follows from lem-weil-pbc-immersion-base-change-lft and
pqf-lem-locnoeth-lft). Pushforward commutes with finite sums. The generic stalk is nonzero,
so the number of summands and the ideal are nonzero (lem-weil-pbc-closed-pushforward-stalks).
8. The partial sums filter the image with quotients the pushforward of that ideal. The
cokernel has strictly smaller support because its generic stalk vanishes. It is good by
minimality, and then step 2 makes the original module good, the final contradiction. -/
theorem exists_coherent_filtration_integral_subschemes
    (X : Scheme.{u}) [IsNoetherian X]
    (F : X.Modules) (hF : RingedSpace.IsCoherent X.toRingedSpace F) :
    ∃ (m : ℕ) (c : Fin (m + 1) → Subobject F) (hc : Monotone c),
      c 0 = ⊥ ∧ c (Fin.last m) = ⊤ ∧
      (∀ k : Fin (m + 1), RingedSpace.IsCoherent X.toRingedSpace (c k : X.Modules)) ∧
      ∀ j : Fin m, ∃ (Z : Scheme.{u}) (i : Z ⟶ X),
        IsClosedImmersion i ∧ IsIntegral Z ∧
        ∃ I : Z.IdealSheafData,
          I ≠ ⊥ ∧ RingedSpace.IsCoherent Z.toRingedSpace I.toModules ∧
          Nonempty (cokernel (Subobject.ofLE (c j.castSucc) (c j.succ)
            (hc j.castSucc_le_succ)) ≅ (pushforward i).obj I.toModules) := by
  classical
  have all (T : TopologicalSpace.Closeds X) :
      ∀ (G : X.Modules), RingedSpace.IsCoherent X.toRingedSpace G →
        {x : X | ¬ Subsingleton (G.presheaf.stalk x)} = (T : Set X) →
        HasCoherentIntegralFiltration G := by
    refine (wellFounded_lt : WellFounded
      ((· < ·) : TopologicalSpace.Closeds X → TopologicalSpace.Closeds X → Prop)).induction
      (C := fun T ↦ ∀ (G : X.Modules), RingedSpace.IsCoherent X.toRingedSpace G →
        {x : X | ¬ Subsingleton (G.presheaf.stalk x)} = (T : Set X) →
        HasCoherentIntegralFiltration G) T ?_
    intro T ih G hG hSupp
    have smaller (H : X.Modules) (hH : RingedSpace.IsCoherent X.toRingedSpace H)
        (hsub : {x : X | ¬ Subsingleton (H.presheaf.stalk x)} ⊂ (T : Set X)) :
        HasCoherentIntegralFiltration H := by
      let U : TopologicalSpace.Closeds X := ⟨_, support_closed H hH⟩
      exact ih U (show U < T from hsub) H hH rfl
    by_cases hEmpty : T = ⊥
    · apply filtration_of_isZero G hG
      apply isZero_of_empty_support G
      simpa only [hEmpty, TopologicalSpace.Closeds.coe_bot] using hSupp
    by_cases hpre : IsPreirreducible (T : Set X)
    · have hirr : IsIrreducible (T : Set X) :=
        ⟨TopologicalSpace.Closeds.coe_nonempty.mpr hEmpty, hpre⟩
      obtain ⟨ξ, hξ⟩ := QuasiSober.sober hirr T.isClosed
      apply coherentIntegralFiltration_of_generic_annihilated X T ξ hξ G hG hSupp
      intro H hH hsub hkill
      by_cases heq : {x : X | ¬ Subsingleton (H.presheaf.stalk x)} = (T : Set X)
      · exact coherentIntegralFiltration_generic_step X T ξ hξ smaller H hH heq hkill
      · exact smaller H hH (Set.ssubset_iff_subset_ne.mpr ⟨hsub, heq⟩)
    · simp only [isPreirreducible_iff_isClosed_union_isClosed,
        not_forall, not_or] at hpre
      obtain ⟨z₁, z₂, hz₁, hz₂, hcover, hn₁, hn₂⟩ := hpre
      let T₁ : TopologicalSpace.Closeds X := T ⊓ ⟨z₁, hz₁⟩
      let T₂ : TopologicalSpace.Closeds X := T ⊓ ⟨z₂, hz₂⟩
      have ht₁ : T₁ < T := inf_lt_left.mpr hn₁
      have ht₂ : T₂ < T := inf_lt_left.mpr hn₂
      have hcover' : {x : X | ¬ Subsingleton (G.presheaf.stalk x)} =
          (T₁ : Set X) ∪ (T₂ : Set X) := by
        rw [hSupp]
        change (T : Set X) = ((T : Set X) ∩ z₁) ∪ ((T : Set X) ∩ z₂)
        rw [← Set.inter_union_distrib_left, Set.inter_eq_left.mpr hcover]
      obtain ⟨H, f, hH, hQ, hS, hHsub, hQsub⟩ :=
        exists_coherent_submodule_of_support_union X G hG
          (T₁ : Set X) (T₂ : Set X) T₁.isClosed T₂.isClosed hcover'
      apply coherentIntegralFiltration_of_shortExact X
        (ShortComplex.mk f (cokernel.π f) (cokernel.condition f)) hS hH hG hQ
      · exact smaller H hH (lt_of_le_of_lt hHsub ht₂)
      · exact smaller (cokernel f) hQ (lt_of_le_of_lt hQsub ht₁)
  exact all ⟨_, support_closed F hF⟩ F hF rfl

end AlgebraicGeometry.Scheme.Modules
