/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
import WeilConjectures.AlgebraicGeometry.CoherentHomLocalKernel
import WeilConjectures.AlgebraicGeometry.CoherentKernelCokernelSum
import WeilConjectures.AlgebraicGeometry.CoherentModuleLocalOnOpenCover

/-!
# Sheaf Hom of coherent modules

Source: Stacks Project, Modules, Lemma 01CQ, the coherent case
(blueprint: lem-weil-pbc-coherent-sheaf-hom-coherent).
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- The internal sheaf Hom from a coherent module `G` to a coherent module `F` on any scheme
is coherent, with no Noetherian hypothesis.

Source: Stacks Project, Modules, Lemma 01CQ
(blueprint: lem-weil-pbc-coherent-sheaf-hom-coherent).

Proof:
1. By `pqf-def-coherent`, near each point choose a finite free surjection onto `G`.
   Its kernel is of finite type, so after shrinking there is a finite presentation of `G`
   (Stacks 01BW). Kernels are sectionwise (`situation-conventions`).
2. By `def-pur-sheaf-hom`, restricting the internal Hom to an open `V` gives the internal
   Hom of `G|_V` and `F|_V`: sections, restrictions and scalar actions agree on smaller opens.
3. Apply `lem-weil-pbc-sheaf-hom-finite-presentation-kernel` to the presentation on `V`.
   The internal Hom is the kernel of a map from a finite direct sum of `F|_V` to another
   finite direct sum of `F|_V` (Stacks 01CQ and 01CO).
4. Restriction preserves coherence by `lemma-coherent-base-change-invertible-sheaves--1`.
   By `lem-weil-pbc-coherent-modules-kernel-cokernel-sum`, finite sums, kernels and
   isomorphic modules preserve coherence (Stacks 01BY). Thus the internal Hom on `V`
   is coherent.
5. These opens cover the scheme, so coherence of the internal Hom follows from
   `lemma-coherent-base-change-invertible-sheaves--1`. -/
theorem isCoherent_homObj (X : Scheme.{u}) (F G : X.Modules)
    (hF : RingedSpace.IsCoherent X.toRingedSpace F)
    (hG : RingedSpace.IsCoherent X.toRingedSpace G) :
    RingedSpace.IsCoherent X.toRingedSpace (SheafOfModules.homObj (R := X.sheaf) G F) := by
  classical
  let H := SheafOfModules.homObj (R := X.sheaf) G F
  choose U hx m n α e using homObj_locally_kernel_of_coherent X G F hG
  have hU : ⨆ x : X, U x = ⊤ := by
    apply top_le_iff.mp
    intro x _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hx x⟩
  have hlocal := coherent_module_local_on_open_cover X F X U hU
  apply (coherent_module_local_on_open_cover X H X U hU).2
  intro x
  have hFU := hlocal.1 hF (U x)
  have hclosure := RingedSpace.coherent_kernel_cokernel_sum (U x).toScheme.toRingedSpace
  have hn := hclosure.2.2.1 (n x) (fun _ ↦ F.restrict (U x).ι) (fun _ ↦ hFU)
  have hm := hclosure.2.2.1 (m x) (fun _ ↦ F.restrict (U x).ι) (fun _ ↦ hFU)
  have hk := (hclosure.1 _ _ (α x) hn hm).1
  exact hclosure.2.2.2.2 _ _ (e x).some.symm hk

end AlgebraicGeometry.Scheme.Modules
