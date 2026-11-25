/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Subobject.Limits
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module

import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.CoherentKernelCokernelSum
import WeilConjectures.AlgebraicGeometry.CoherentReducibleSupportExactSequence
import WeilConjectures.AlgebraicGeometry.FiniteTypeModuleSupportClosed
import WeilConjectures.AlgebraicGeometry.CoherentIntegralFiltrationExtension
import WeilConjectures.AlgebraicGeometry.CoherentIntegralFiltrationIrreducibleSupport
import Mathlib.Topology.Sheaves.Abelian
import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # A filtration with unresolved factors of smaller support

Source: Stacks Project, Tag 01YF, proof before applying support minimality.
(blueprint: lem-pc-s3-support-reduction-filtration)
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

-- A zero module has this filtration on any scheme; no coherence hypothesis is needed.
private theorem filtration_of_isZero {X : Scheme.{u}}
    (F : X.Modules) (hz : IsZero F) : HasCoherentIntegralFiltration F := by
  have := Subobject.subsingleton_of_isZero hz
  refine ⟨0, fun _ ↦ ⊥, fun _ _ _ ↦ le_rfl, rfl, Subsingleton.elim _ _, ?_, ?_⟩
  · intro k
    exact (RingedSpace.coherent_kernel_cokernel_sum X.toRingedSpace).2.2.2.2
      (@Zero.zero X.Modules (HasZeroObject.zero' X.Modules)) ((⊥ : Subobject F) : X.Modules)
      Subobject.botCoeIsoZero.symm
      (RingedSpace.coherent_kernel_cokernel_sum X.toRingedSpace).2.2.2.1
  · intro j
    exact Fin.elim0 j

/-- The geometric step of support induction: leave smaller-support factors unresolved.
This does not assert integral-ideal filtrations for those factors.

Source: Stacks Project, Tag 01YF (`coherent.tex`, `lemma-coherent-filter`), proof,
reducible support, the J-adic filtration, and the generic ideal inclusion of Tag 01YE.
(blueprint: lem-pc-s3-support-reduction-filtration)

Proof: Finite presentation on a Noetherian scheme gives coherence and closed support.
Prove the stronger coherent integral-ideal filtration assertion by well-founded induction
on closed support. For empty support, stalk detection makes the module zero, and the
length-zero bottom chain works. For reducible support, split into a coherent submodule
and cokernel with strictly smaller supports, apply induction to both, and concatenate
using the coherent short-exact extension theorem. For irreducible nonempty support,
sobriety supplies a generic point. The irreducible-support step uses the induction
hypothesis on smaller supports, the J-adic reduction, and the generic ideal inclusion.
Finally forget coherence of subobjects and nonzero/coherence conditions on ideals, and
place every quotient in the first disjunct. The second disjunct is not needed. -/
theorem exists_finitePresentation_support_reduction_filtration
    (X : Scheme.{u}) [IsNoetherian X] (F : X.Modules) [F.IsFinitePresentation] :
    ∃ (m : ℕ) (c : Fin (m + 1) → Subobject F) (hc : Monotone c),
      c 0 = ⊥ ∧ c (Fin.last m) = ⊤ ∧
      ∀ j : Fin m,
        let Q := cokernel (Subobject.ofLE (c j.castSucc) (c j.succ)
          (hc j.castSucc_le_succ))
        (∃ (Z : Scheme.{u}) (i : Z ⟶ X),
          IsClosedImmersion i ∧ IsIntegral Z ∧
          ∃ I : Z.IdealSheafData, Nonempty (Q ≅ (pushforward i).obj I.toModules)) ∨
        (Q.IsFinitePresentation ∧
          closure {x : X | ¬ Subsingleton (Q.presheaf.stalk x)} ⊂
            closure {x : X | ¬ Subsingleton (F.presheaf.stalk x)}) := by
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
      have ⟨hq, ht⟩ := (isCoherent_iff_isQuasicoherent_and_isFiniteType X H).mp hH
      have := hq
      have := ht
      let U : TopologicalSpace.Closeds X :=
        ⟨_, (finite_type_module_support_closed X H).2.2.2⟩
      exact ih U (show U < T from hsub) H hH rfl
    by_cases hEmpty : T = ⊥
    · apply filtration_of_isZero G
      let forget := SheafOfModules.toSheaf X.ringCatSheaf
      have hz : IsZero (forget.obj G) := by
        apply (TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero _).mpr
        intro x
        have : Subsingleton (G.presheaf.stalk x) := by
          by_contra hn
          have hx : x ∈ (T : Set X) := hSupp ▸ hn
          simp only [hEmpty, TopologicalSpace.Closeds.coe_bot, Set.mem_empty_iff_false]
            at hx
        change IsZero (G.presheaf.stalk x)
        exact AddCommGrpCat.isZero_of_subsingleton _
      rw [IsZero.iff_id_eq_zero]
      apply forget.map_injective
      rw [forget.map_id, forget.map_zero]
      exact hz.eq_of_src _ _
    by_cases hpre : IsPreirreducible (T : Set X)
    · have hirr : IsIrreducible (T : Set X) :=
        ⟨TopologicalSpace.Closeds.coe_nonempty.mpr hEmpty, hpre⟩
      obtain ⟨ξ, hξ⟩ := QuasiSober.sober hirr T.isClosed
      exact coherentIntegralFiltration_of_irreducible_support X T ξ hξ smaller G hG hSupp
    · obtain ⟨H, f, hH, hQ, hS, hHsub, hQsub⟩ :=
        exists_coherent_submodule_of_reducible_support X T G hG hSupp hpre
      apply coherentIntegralFiltration_of_shortExact X
        (ShortComplex.mk f (cokernel.π f) (cokernel.condition f)) hS hH hG hQ
      · exact smaller H hH hHsub
      · exact smaller (cokernel f) hQ hQsub
  have hF : RingedSpace.IsCoherent X.toRingedSpace F :=
    (isCoherent_iff_isQuasicoherent_and_isFiniteType X F).mpr
      ⟨inferInstance, inferInstance⟩
  obtain ⟨m, c, hc, hbot, htop, _, hquot⟩ :=
    all ⟨_, (finite_type_module_support_closed X F).2.2.2⟩ F hF rfl
  refine ⟨m, c, hc, hbot, htop, ?_⟩
  intro j
  obtain ⟨Z, i, hi, hZ, I, _, _, he⟩ := hquot j
  exact Or.inl ⟨Z, i, hi, hZ, I, he⟩


end AlgebraicGeometry.Scheme.Modules
