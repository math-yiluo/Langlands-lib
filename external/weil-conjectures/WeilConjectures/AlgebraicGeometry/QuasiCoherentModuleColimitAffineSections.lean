/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.CategoryTheory.Filtered.Basic
import WeilConjectures.AlgebraicGeometry.QuasiCoherentModuleColimitEvaluation
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentCokernel
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.AlgebraicGeometry.AffineScheme

/-! # Directed colimits of quasi-coherent modules

Source: Stacks Project, Schemes, Lemma 01ID and Section 26.24, item (4)
(blueprint: lem-weil-pbc-quasi-coherent-module-colimit-affine-sections).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
/-- A directed colimit of quasi-coherent modules is quasi-coherent, and its sections
on an affine open have the expected elementwise description. Source: Stacks Project,
Schemes, Lemma 01ID and Section 26.24, item (4)
(blueprint: lem-weil-pbc-quasi-coherent-module-colimit-affine-sections).

Proof: for an affine open `U` with `R = Γ(X, U)`, restrict to `Spec R ≅ U`; there the
restricted system is `M_i~` with `M_i = F_i(U)` and the restricted colimit is `M~` for
`M = colim M_i` (the tilde functor preserves colimits), so `F(U) ≅ M` compatibly with the
`c_{i,U}`; the elementwise description of a directed colimit of modules gives the two
clauses, and `F|_U ≅ M~` on an affine cover gives quasi-coherence. -/
theorem quasiCoherentModuleColimitAffineSections
    (X : Scheme.{u}) (I : Type u) [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (F : I ⥤ X.Modules) (c : Cocone F) (hc : IsColimit c)
    (hF : ∀ i : I, (F.obj i).IsQuasicoherent) :
    c.pt.IsQuasicoherent ∧
      ∀ (U : X.Opens), IsAffineOpen U →
        (∀ s : Γ(c.pt, U), ∃ (i : I) (x : Γ(F.obj i, U)),
          ((c.ι.app i).val.app (Opposite.op U)) x = s) ∧
        (∀ (i : I) (x : Γ(F.obj i, U)),
          ((c.ι.app i).val.app (Opposite.op U)) x = 0 ↔
            ∃ (i' : I) (h : i ≤ i'),
              ((F.map (homOfLE h)).val.app (Opposite.op U)) x = 0) := by
  classical
  let : ∀ i, (F.obj i).IsQuasicoherent := hF
  have hqc : c.pt.IsQuasicoherent := by
    let A := fun f : Σ p : I × I, p.1 ⟶ p.2 ↦ F.obj f.1.1
    let B := F.obj
    let s : ∐ A ⟶ ∐ B := Sigma.desc fun f ↦ F.map f.2 ≫ Sigma.ι B f.1.2
    let t : ∐ A ⟶ ∐ B := Sigma.desc fun f ↦ Sigma.ι B f.1.1
    have : (∐ A).IsQuasicoherent := isQuasicoherent_sigma A
    have : (∐ B).IsQuasicoherent := isQuasicoherent_sigma B
    have : (cokernel (s - t)).IsQuasicoherent := isQuasicoherent_cokernel (s - t)
    let q := Preadditive.coforkOfCokernelCofork
      (CokernelCofork.ofπ (cokernel.π (s - t)) (cokernel.condition (s - t)))
    let cq := HasColimitOfHasCoproductsOfHasCoequalizers.buildColimit s t
      (by intro f; simp [s]) (by intro f; simp [t]) q
    have hcq : IsColimit cq :=
      HasColimitOfHasCoproductsOfHasCoequalizers.buildIsColimit s t
        (by intro f; simp [s]) (by intro f; simp [t])
        (colimit.isColimit _) (colimit.isColimit _)
        (Preadditive.isColimitCoforkOfCokernelCofork (cokernelIsCokernel (s - t)))
    exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
      (hcq.coconePointUniqueUpToIso hc)
      (show (cokernel (s - t)).IsQuasicoherent from inferInstance)
  refine ⟨hqc, ?_⟩
  intro U hU
  let E := SheafOfModules.evaluation (R := X.ringCatSheaf) (Opposite.op U)
  let D := F ⋙ E
  have hE : IsColimit (E.mapCocone c) :=
    (quasiCoherentModuleColimitEvaluation X I F c hc hF hqc U hU).some
  refine ⟨?_, ?_⟩
  · intro x
    exact Concrete.isColimit_exists_rep D hE x
  · intro i x
    constructor
    · intro hx
      have heq : (E.mapCocone c).ι.app i x = (E.mapCocone c).ι.app i 0 := by
        change ((c.ι.app i).val.app (Opposite.op U)).hom x =
          ((c.ι.app i).val.app (Opposite.op U)).hom 0
        rw [map_zero]
        exact hx
      obtain ⟨j, f, g, hfg⟩ := Concrete.isColimit_exists_of_rep_eq D hE x 0 heq
      refine ⟨j, leOfHom f, ?_⟩
      change ((F.map f).val.app (Opposite.op U)).hom x =
        ((F.map g).val.app (Opposite.op U)).hom 0 at hfg
      change ((F.map (homOfLE (leOfHom f))).val.app (Opposite.op U)).hom x = 0
      rw [show homOfLE (leOfHom f) = f from Subsingleton.elim _ _]
      simpa only [map_zero] using hfg
    · rintro ⟨j, h, hx⟩
      have hw := ConcreteCategory.congr_hom ((E.mapCocone c).w (homOfLE h)) x
      change ((F.map (homOfLE h)).val.app (Opposite.op U)).hom x = 0 at hx
      change ((c.ι.app j).val.app (Opposite.op U)).hom
        (((F.map (homOfLE h)).val.app (Opposite.op U)).hom x) =
          ((c.ι.app i).val.app (Opposite.op U)).hom x at hw
      rw [hx, map_zero] at hw
      exact hw.symm

end AlgebraicGeometry.Scheme.Modules
