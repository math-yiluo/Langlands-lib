/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import WeilConjectures.Topology.RingedSpaceModuleCohomology
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
import WeilConjectures.AlgebraicGeometry.Modules.Dual
import WeilConjectures.CategoryTheory.Abelian.RightDerived.FullLongExactSequence

/-! # Surjectivity of twisted formal transition sections

Source: Stacks Project, proof of Lemma 0885 (lemma-existence-projective).
(blueprint: lem-weil-pbc-formal-twisted-transition-sections).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- Vanishing of first cohomology of the twisted transition kernel makes sections
of that transition surjective.

Source: Stacks Project, Cohomology of Schemes, proof of Lemma 0885
(lemma-existence-projective), the surjectivity of the displayed H^0 transition maps.
(blueprint: lem-weil-pbc-formal-twisted-transition-sections).

Proof: The formal quotient isomorphism expresses the transition as a cokernel
projection followed by an isomorphism, hence it is epi. Tensoring by L^d is an
exact equivalence because L is invertible. Its kernel is consequently the tensor
product of the original kernel with L^d. Apply the long exact sequence of derived
global sections to the resulting short exact sequence. The connecting map out of
H^0 of the target has zero target by the hypothesis. Exactness makes the H^0 map
epi. Identify H^0 with global sections; epimorphisms of modules are surjective.
Evaluation at the top open identifies global sections with compatible sections
on all opens, and this identification commutes with the transition map.
-/
theorem formal_twisted_transition_sections_surjective
    {X : Scheme.{u}} [IsNoetherian X] (K : X.IdealSheafData)
    (F : CoherentFormalModule X K) (L : X.Modules) [L.IsInvertible]
    (d k : ℕ)
    (hvan : IsZero ((RingedSpace.moduleCohomology X.toRingedSpace 1).obj
      (Scheme.Modules.tensorObj (kernel (F.obj.map (homOfLE (Nat.le_succ k)).op))
        (L.tensorPow d)))) :
    Function.Surjective (SheafOfModules.sectionsMap
      ((tensorRight (L.tensorPow d)).map (F.obj.map (homOfLE (Nat.le_succ k)).op))) := by
  let : EnoughInjectives (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
    (RingedSpace.moduleSheaves_abelian_enoughInjectives X.toRingedSpace).2
  let t := F.obj.map (homOfLE (Nat.le_succ k)).op
  obtain ⟨q, hq⟩ := F.property.2.2 k
  have : Epi t := by
    dsimp only [t]
    rw [← hq]
    exact epi_comp (cokernel.π _) q.hom
  let T := (BraidedCategory.tensorRightEquivalence (L.tensorPow d)
    (Scheme.Modules.dual (L.tensorPow d))
    (Scheme.Modules.nonempty_tensorObj_dual_iso_unit (L.tensorPow d)).some).functor
  let S := ShortComplex.mk (kernel.ι t) t (kernel.condition t)
  have hS : S.ShortExact := { exact := ShortComplex.exact_kernel t }
  let Γ := RingedSpace.globalSectionsFunctor X.toRingedSpace
  have : PreservesFiniteLimits Γ :=
    inferInstanceAs (PreservesFiniteLimits (SheafOfModules.evaluation _ (op ⊤)))
  obtain ⟨δ, _, hall⟩ := (hS.map_of_exact T).exists_rightDerived_full_long_exact Γ
  obtain ⟨_, w₁, _, hr, _⟩ := hall 0
  have hz : IsZero ((Γ.rightDerived 1).obj (S.map T).X₁) := hvan
  have : Epi ((Γ.rightDerived 0).map (T.map t)) :=
    hr.epi_f (hz.eq_zero_of_tgt (δ 0))
  let e := Γ.rightDerivedZeroIsoSelf
  have hep : Epi (e.hom.app (T.obj (F.obj.obj (op (k + 1)))) ≫ Γ.map (T.map t)) := by
    rw [← e.hom.naturality]
    infer_instance
  have : Epi (Γ.map (T.map t)) :=
    epi_of_epi (e.hom.app (T.obj (F.obj.obj (op (k + 1))))) (Γ.map (T.map t))
  have hsurj := (ModuleCat.epi_iff_surjective (Γ.map (T.map t))).mp inferInstance
  intro s
  obtain ⟨x, hx⟩ := hsurj (s.val (op ⊤))
  change (T.map t).val.app (op ⊤) x = s.val (op ⊤) at hx
  let r : (T.obj (F.obj.obj (op (k + 1)))).sections :=
    PresheafOfModules.sectionsMk
      (fun U ↦ (T.obj (F.obj.obj (op (k + 1)))).val.map (homOfLE le_top).op x)
      (by
        intro U V i
        rw [← (T.obj (F.obj.obj (op (k + 1)))).val.map_comp_apply]
        rfl)
  refine ⟨r, ?_⟩
  apply PresheafOfModules.sections_ext
  intro U
  change (T.map t).val.app U
    ((T.obj (F.obj.obj (op (k + 1)))).val.map (homOfLE le_top).op x) = s.val U
  rw [PresheafOfModules.naturality_apply, hx, PresheafOfModules.sections_property]

end AlgebraicGeometry
