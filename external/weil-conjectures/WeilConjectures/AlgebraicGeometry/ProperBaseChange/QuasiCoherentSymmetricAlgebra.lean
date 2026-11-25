/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CommAlgebraSheaf
public import WeilConjectures.AlgebraicGeometry.Coherent
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
import WeilConjectures.AlgebraicGeometry.ProperBaseChange.QuasiCoherentSymmetricAlgebraCore
import WeilConjectures.AlgebraicGeometry.ProperBaseChange.QuasiCoherentSymmetricAlgebraAffine
public import Mathlib.AlgebraicGeometry.AffineScheme

/-! # The symmetric algebra of a quasi-coherent module

The algebra is a commutative ring sheaf under the structure sheaf. The affine comparison
is a ring equivalence commuting with the structure homomorphism and the degree-one map;
this is precisely the canonical algebra isomorphism, without choosing algebra instances.

## References

* Stacks Project, Modules, Section 01CF and Lemmas 01CG, 01CL
* Stacks Project, Modules, Section 01CF, Lemmas 01CG, 01CL
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry

/-- The symmetric algebra of a quasi-coherent module is a quasi-coherent algebra sheaf,
with its universal degree-one map and the canonical affine-section algebra isomorphisms. -/
theorem exists_quasiCoherentSymmetricAlgebra
    (X : Scheme.{u}) (F : X.Modules) [F.IsQuasicoherent] :
    ∃ (S : X.CommAlgebraSheaf) (j : F ⟶ S.toModule),
      S.toModule.IsQuasicoherent ∧
      (∀ (B : X.CommAlgebraSheaf) (f : F ⟶ B.toModule),
        ∃! t : S ⟶ B, ∀ (U : X.Opens) (x : F.val.obj (op U)),
          (t.right.hom.app (op U)) (j.val.app (op U) x) = f.val.app (op U) x) ∧
      (∀ (U : X.affineOpens),
        ∃ e : SymmetricAlgebra (X.presheaf.obj (op U.1)) (F.val.obj (op U.1)) ≃+*
            S.right.obj.obj (op U.1),
          (∀ r : X.presheaf.obj (op U.1),
            e (algebraMap (X.presheaf.obj (op U.1))
              (SymmetricAlgebra (X.presheaf.obj (op U.1)) (F.val.obj (op U.1))) r) =
              S.hom.hom.app (op U.1) r) ∧
          (∀ x : F.val.obj (op U.1),
            e (SymmetricAlgebra.ι (X.presheaf.obj (op U.1)) (F.val.obj (op U.1)) x) =
              j.val.app (op U.1) x)) := by
  obtain ⟨hqc, hAffine⟩ := quasiCoherentSymmetricAlgebra_affine_comparison X F
  refine ⟨SymmetricAlgebraSheaf.algebra F, SymmetricAlgebraSheaf.inclusion F, hqc,
    exists_quasiCoherentSymmetricAlgebra_core X F, ?_⟩
  intro U
  refine ⟨RingEquiv.ofBijective (SymmetricAlgebraSheaf.sectionMap F (op U.1))
    (hAffine U), ?_, ?_⟩
  · intro r
    rfl
  · intro x
    rfl

end AlgebraicGeometry
