/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import WeilConjectures.AlgebraicGeometry.PQFCohomology
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import WeilConjectures.AlgebraicGeometry.FiniteFreeKernelIdealFiltration
import WeilConjectures.CategoryTheory.Abelian.RightDerived.FullLongExactSequence

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Ideal H¹ vanishing annihilates H¹ of the kernel of a map from a finite free module
to the structure sheaf.

Source: Stacks Project, Tag 01XF, label lemma-quasi-compact-h1-zero-covering,
last two paragraphs (blueprint: lem-pqf-finite-free-kernel-h1-vanishing).

Proof: Enumerate the finite index type. The kernel F is quasi-coherent, since both
finite free modules and the structure sheaf are quasi-coherent and kernels of maps
of quasi-coherent modules on schemes are quasi-coherent. Intersect F with the first
j summands to obtain F_j. The kernel of projection from F_j onto its last coordinate
is F_{j-1}; its image is a quasi-coherent ideal subsheaf of the structure sheaf.
Thus F_j/F_{j-1} is such an ideal sheaf. Starting with F_0 = 0, use the exact segment
H¹(F_{j-1}) → H¹(F_j) → H¹(F_j/F_{j-1}). The two outer groups vanish by induction and
the ideal hypothesis, so the middle group vanishes. At the last index this gives
H¹(F) = 0. The empty index type gives the zero kernel directly. This argument does
not require the original map to be an epimorphism. -/
theorem finite_free_kernel_h1_zero (X : Scheme.{u})
    (hI : ∀ (I : X.IdealSheafData), I.toModules.IsQuasicoherent →
      Subsingleton ((RingedSpace.moduleCohomology X.toRingedSpace 1).obj I.toModules))
    {I : Type u} [Finite I]
    (p : SheafOfModules.free (R := X.ringCatSheaf) I ⟶
      SheafOfModules.unit X.ringCatSheaf) :
    Subsingleton ((RingedSpace.moduleCohomology X.toRingedSpace 1).obj (kernel p)) := by
  obtain ⟨n, F, hF₀, ⟨e⟩, hstep⟩ := finite_free_kernel_ideal_filtration X p
  let H := RingedSpace.moduleCohomology X.toRingedSpace 1
  let Γ := RingedSpace.globalSectionsFunctor X.toRingedSpace
  let : PreservesFiniteLimits Γ :=
    inferInstanceAs (PreservesFiniteLimits
      (SheafOfModules.evaluation (moduleRings X.toRingedSpace) (Opposite.op ⊤)))
  have : H.Additive := inferInstanceAs (Γ.rightDerived 1).Additive
  have hF : ∀ j : ℕ, j ≤ n → IsZero (H.obj (F j)) := by
    intro j
    induction j with
    | zero =>
        intro _
        exact H.map_isZero hF₀
    | succ j ih =>
        intro hj
        obtain ⟨J, hJ, a, b, w, hS⟩ := hstep j (Nat.lt_of_succ_le hj)
        have : Subsingleton (H.obj J.toModules) := hI J hJ
        obtain ⟨_, _, hex⟩ := hS.exists_rightDerived_full_long_exact Γ
        exact (hex 1).1.isZero_of_both_isZero
          (ih (Nat.le_of_succ_le hj)) (ModuleCat.isZero_of_subsingleton (H.obj J.toModules))
  exact ModuleCat.subsingleton_of_isZero
    (IsZero.of_iso (hF n le_rfl) (H.mapIso e).symm)

end AlgebraicGeometry
