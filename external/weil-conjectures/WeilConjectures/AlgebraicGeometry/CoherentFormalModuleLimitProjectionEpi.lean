/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits

import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic

/-! # Epimorphic projections from coherent formal-module limits

Source: Stacks Project, Lemma 087W, proof of M/I^n M = M_n.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
private theorem affine_surjective_of_epi {Y : Scheme.{u}} {M N : Y.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (φ : M ⟶ N) [Epi φ]
    (U : Y.affineOpens) : Function.Surjective (φ.app U.1) := by
  have hker := (Scheme.Modules.quasiCoherent_cokernel_image φ).2.2.2.2.2.2.2.2 U
  have hz : cokernel.π φ = 0 := by
    apply (cancel_epi φ).1
    simp
  intro y
  have hy : y ∈ LinearMap.range (φ.val.app (op U.1)).hom := by
    rw [← hker.2.2.1]
    change (cokernel.π φ).app U.1 y = 0
    rw [hz]
    rfl
  exact hy

set_option backward.isDefEq.respectTransparency false in
/-- The projection from a coherent adic system's limit sheaf to any level is epic.
Source: Stacks Project, Lemma 087W, proof of the surjectivity and quotient formula
for the projections M -> M_n; Lemma 088B, local uniqueness of alpha.
(blueprint: lem-weil-pbc-coherent-formal-module-limit-projection-epi)

Proof: Coherence makes every level quasi-coherent. Its successor transition is
the quotient projection followed by the defining quotient isomorphism, hence epic.
For a morphism between quasi-coherent modules, the affine cokernel/image formula
identifies the sectionwise image with the kernel of its cokernel projection. For
an epimorphism that projection is zero; therefore every transition is surjective
on sections of every affine open. Evaluation on such an open preserves inverse
limits. To prove surjectivity at level n, restrict the evaluated limit cone to the
cofinal tail k |-> n+k and apply the sequential-limit surjectivity theorem at its
zeroth projection. This gives surjectivity of the sheaf limit projection on every
affine open. The target level is quasi-coherent and all affine opens cover Y.
Apply the source-library affine-cover surjectivity criterion
to conclude that the projection is epic. No finite completed-module reconstruction or
formal-functions theorem is needed. For J=0 projections of constant systems are
isomorphisms; for J=1 the projection is between zero objects. Zero sheaves and the
empty scheme cause no exception.
-/
theorem coherentFormalModule_limit_projection_epi {Y : Scheme.{u}} [IsNoetherian Y]
    (J : Y.IdealSheafData) (G : CoherentFormalModule Y J) (n : ℕ) :
    Epi (limit.π G.obj (op n)) := by
  have hqc (k : ℕ) : (G.obj.obj (op k)).IsQuasicoherent :=
    ((Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType Y _).mp
      (G.property.1 k)).1
  have hsurj (U : Y.affineOpens) (k : ℕ) :
      Function.Surjective ((G.obj.map (homOfLE (Nat.le_succ k)).op).app U.1) := by
    have := hqc k
    have := hqc (k + 1)
    obtain ⟨e, he⟩ := G.property.2.2 k
    have : Epi (G.obj.map (homOfLE (Nat.le_succ k)).op) := by
      rw [← he]
      dsimp [formalModuleQuotientπ]
      infer_instance
    exact affine_surjective_of_epi _ U
  have hπ (U : Y.affineOpens) : Function.Surjective ((limit.π G.obj (op n)).app U.1) := by
    let E := SheafOfModules.evaluation Y.ringCatSheaf (op U.1)
    let shift : ℕ ⥤ ℕ := (show Monotone (fun k : ℕ ↦ n + k) from
      fun _ _ h ↦ Nat.add_le_add_left h n).functor
    have : shift.Final := by
      apply (Monotone.final_functor_iff _).2
      intro k
      exact ⟨k, Nat.le_add_left k n⟩
    have hc := (Functor.Initial.isLimitWhiskerEquiv shift.op
      (E.mapCone (limit.cone G.obj))).symm
        (isLimitOfPreserves E (limit.isLimit G.obj))
    have hs : ∀ k : ℕ, Function.Surjective
        ((shift.op ⋙ G.obj ⋙ E).map (homOfLE (Nat.le_succ k)).op) := by
      intro k
      exact hsurj U (n + k)
    have hp := Concrete.surjective_π_app_zero_of_surjective_map hc hs
    simpa only [E, shift, Nat.add_zero] using! hp
  have := hqc n
  exact Scheme.Modules.epi_of_surjective_app _ (fun U : Y.affineOpens ↦ U.1)
    (fun U ↦ U.2) (iSup_affineOpens_eq_top Y) hπ

end AlgebraicGeometry
