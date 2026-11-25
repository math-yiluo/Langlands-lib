/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import WeilConjectures.AlgebraicGeometry.IdealModuleProductStalk
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import WeilConjectures.AlgebraicGeometry.CoherentOpenSectionCarrier
import WeilConjectures.AlgebraicGeometry.CoherentIdealPowerTorsionFreeProduct

/-! # An ideal-power-torsion-free carrier of an open section

Source: Stacks Project, Tag 01YB, first two paragraphs of the proof.
(blueprint: lem-pc-ideal-power-torsion-free-section-carrier)
-/

@[expose] public section

universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry.Scheme.Modules

noncomputable local instance {X : Scheme.{u}} (F : X.Modules) {V W : X.Opens} (h : V ≤ W) :
    HSMul ((SheafOfModules.unit X.ringCatSheaf).val.obj (op V))
      ((ModuleCat.restrictScalars (X.ringCatSheaf.obj.map (homOfLE h).op).hom).obj
        (F.val.obj (op V))) (F.val.obj (op V)) where
  hSMul := @SMul.smul Γ(X, V) Γ(F, V) inferInstance

/-- A quasi-coherent section on an ideal complement has a quasi-coherent carrier
inside the original module with zero ideal-power annihilators.

Source: Stacks Project, Tag 01YB, first two paragraphs of the proof.
(blueprint: lem-pc-ideal-power-torsion-free-section-carrier)

Proof: The section defines a map from the structure module on U. Its image is
quasi-coherent and finite type. Extend this image to a finite-type quasi-coherent
submodule H of E by 01PF; on a Noetherian scheme H is coherent by 01XZ. The section
therefore lifts to H(U). For each n take the quasi-coherent annihilator H_n of I^n.
These form an increasing chain, so 01Y8 gives r with H_n contained in H_r for all n.
Set T = H_r. Artin-Rees 01YA supplies c such that I^(r+c)H intersects T in zero,
since that intersection is contained in I^r T = 0. Set G = I^(r+c)H with its
canonical inclusion into E. It is quasi-coherent. On U the ideal is the structure
module, so G(U) maps bijectively to H(U); lift the given section to t in G(U).
If a section x of G on W is killed, locally on every smaller open, by I^n, its
image in H lies in H_n and hence in T. It also lies in G, so the zero intersection
forces it to vanish, and the inclusion G into H is injective on sections.
The recursive powers have the same local ideal products, so the stated annihilator
condition is exactly this one. For U empty use the zero carrier; for I the unit
ideal take H itself, and for E zero use the zero carrier. -/
theorem exists_idealPower_torsionFree_section_carrier
    {X : Scheme.{u}} [IsNoetherian X] (I : X.IdealSheafData)
    (E : X.Modules) [E.IsQuasicoherent] (U : X.Opens)
    (hI : (I.support : Set X) = (U : Set X)ᶜ) (s : E.val.obj (op U)) :
    ∃ (G : X.Modules) (g : G ⟶ E) (t : G.val.obj (op U)),
      G.IsQuasicoherent ∧ Mono g ∧ g.val.app (op U) t = s ∧
      ∀ (n : ℕ) (W : X.Opens) (x : G.val.obj (op W)),
        (∀ (V : X.Opens) (h : V ≤ W)
          (b : (idealSheafPower I.toModulesι n).1.val.obj (op V)),
          ((idealSheafPower I.toModulesι n).2.val.app (op V) b : Γ(X, V)) •
            G.val.map (homOfLE h).op x = 0) → x = 0 := by
  obtain ⟨H, h, t, hqc, hcoh, hm, ht⟩ :=
    exists_coherent_open_section_carrier E U s
  have : H.IsQuasicoherent := hqc
  have : Mono h := hm
  obtain ⟨k, hP, hj, hbij, htf⟩ :=
    exists_coherent_idealPower_torsionFree_product I H hcoh U hI
  let P := idealModuleProduct (idealSheafPower I.toModulesι k).2 H
  let j : P ⟶ H := idealModuleProductι (idealSheafPower I.toModulesι k).2 H
  have : Mono j := hj
  obtain ⟨z, hz⟩ := hbij.2 t
  refine ⟨P, j ≫ h, z, hP, inferInstance, ?_, htf⟩
  change h.val.app (op U) (j.val.app (op U) z) = s
  rw [hz, ht]

end AlgebraicGeometry.Scheme.Modules
