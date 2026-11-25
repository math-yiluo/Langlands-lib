/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.RingTheory.Ideal.Operations
public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
import WeilConjectures.AlgebraicGeometry.CoherentFormalModuleAnnihilatedLimitScalar
import WeilConjectures.RingTheory.KernelCokernelAnnihilatedModIdeal

/-! # From termwise annihilation to annihilation of an affine limit

Source: Stacks Project, Remark 0888, the implication (1) to (2).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Uniform termwise annihilation gives exponent `2 * t` on an affine inverse-limit map.
Source: Stacks Project, Remark 0888, final paragraph, and Lemma 087W
(blueprint: lem-weil-pbc-formal-annihilation-affine-limit).

Proof:
1. Restrict the component kernels and cokernels to the affine open U. Exact affine
   sections identify them with the kernel and cokernel of the section map. The affine
   ideal-product calculation turns the hypothesis into annihilation by K(U)^t.
2. For f,g in K(U)^t, the scalar quasi-inverse lemma supplies at every level a canonical
   linear map h_n: G_n(U) to F_n(U): lift f*y to x and send y to g*x. Independence
   of the lift follows from annihilation of the kernel. Its composites with alpha_n
   are multiplication by f*g. Naturality of this lifting formula in commuting squares
   shows the h_n commute with the transition maps.
3. Their natural transformation induces a map between the two inverse limits. The
   limit projections are jointly monic, so both composites with the limit of alpha
   are multiplication by f*g. The scalar-composite criterion now kills its kernel
   and cokernel by K(U)^(2*t), since products f*g generate that ideal.
No identification of a formal kernel with a termwise kernel is used. -/
theorem coherentFormalModule_annihilated_affine_limit
    (X : Scheme.{u}) [IsNoetherian X] (I K : X.IdealSheafData)
    (F G : CoherentFormalModule X I) (α : F ⟶ G) (t : ℕ) (ht : 1 ≤ t)
    (h : ∀ n : ℕ,
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι t).2
        (kernel (α.hom.app (op n)))) ∧
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι t).2
        (cokernel (α.hom.app (op n))))) (U : X.affineOpens) :
    K.ideal U ^ (2 * t) ≤ Module.annihilator Γ(X, U.1) (LinearMap.ker
      (lim.map (Functor.whiskerRight α.hom
        (SheafOfModules.evaluation X.ringCatSheaf (op U.1)))).hom) ∧
    K.ideal U ^ (2 * t) ≤ Module.annihilator Γ(X, U.1)
      (↥(limit (G.obj ⋙ SheafOfModules.evaluation X.ringCatSheaf (op U.1)) :
        ModuleCat Γ(X, U.1)) ⧸ LinearMap.range
        (lim.map (Functor.whiskerRight α.hom
          (SheafOfModules.evaluation X.ringCatSheaf (op U.1)))).hom) := by
  let v := (lim.map (Functor.whiskerRight α.hom
    (SheafOfModules.evaluation X.ringCatSheaf (op U.1)))).hom
  have hv := coherentFormalModule_affine_limit_scalar_composites X I K F G α t ht h U
  simpa [v] using LinearMap.annihilated_of_scalar_composites (K.ideal U) t v hv

end AlgebraicGeometry
