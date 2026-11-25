/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ProEtaleLocalSubobjectKernel
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso
import WeilConjectures.AlgebraicGeometry.ProEtaleLocalSubobjectKernelEffective

/-! # Descent of compatible local subobjects of an abelian sheaf

Source: Stacks Project, Sites, Tag 04TR.
(auxiliary; not a blueprint node).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

/-- Compatible local subobjects of an abelian sheaf descend, and the resulting
subobject has the expected local factorization property.

Source: Stacks Project, Sites, Tag 04TR.
(auxiliary; not a blueprint node).

Proof: take the kernel of the map from Q to the product of the pushforwards
of the local cokernels. Its inclusion is monic. The canonical local comparisons
are isomorphisms by the kernel-effectivity theorem. Their commutation equations
are the proved monoLift equations. Finally, a morphism locally factoring through
the q_i has zero composite with every adjoint local quotient map, hence with their
product; kernel.lift supplies its factor through the global subobject. -/
theorem exists_subsheaf_of_compatible_local_monomorphisms
    (X : Scheme.{u}) (Q : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (U : Scheme.Cover.{u} Scheme.proetalePrecoverage X)
    (L : ∀ i, Sheaf (Scheme.ProEt.topology (U.X i)) Ab.{u + 1})
    (q : ∀ i, L i ⟶ (upperStar Ab.{u + 1} (U.f i)).obj Q)
    (hq : ∀ i, Mono (q i))
    (hcompatible : ∀ i j, ∃ c :
      (upperStar Ab.{u + 1} (pullback.fst (U.f i) (U.f j))).obj (L i) ≅
        (upperStar Ab.{u + 1} (pullback.snd (U.f i) (U.f j))).obj (L j),
      c.hom ≫ (upperStar Ab.{u + 1} (pullback.snd (U.f i) (U.f j))).map (q j) =
        (upperStar Ab.{u + 1} (pullback.fst (U.f i) (U.f j))).map (q i) ≫
          (upperStarCompIso Ab.{u + 1}
            (pullback.condition (f := U.f i) (g := U.f j))).hom.app Q) :
    ∃ (P : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (j : P ⟶ Q),
      Mono j ∧ ∃ e : ∀ i, (upperStar Ab.{u + 1} (U.f i)).obj P ≅ L i,
      (∀ i, (upperStar Ab.{u + 1} (U.f i)).map j = (e i).hom ≫ q i) ∧
      (∀ (Z : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (m : Z ⟶ Q),
        (∀ i, ∃ t : (upperStar Ab.{u + 1} (U.f i)).obj Z ⟶ L i,
          t ≫ q i = (upperStar Ab.{u + 1} (U.f i)).map m) →
        ∃ t : Z ⟶ P, t ≫ j = m) := by
  have h := isIso_localSubobjectKernelComparison X Q U L q hq hcompatible
  refine ⟨localSubobjectKernel X Q U L q, localSubobjectKernelι X Q U L q,
    inferInstance, fun i ↦ asIso (localSubobjectKernelComparison X Q U L q hq i), ?_, ?_⟩
  · intro i
    exact (localSubobjectKernelComparison_comp X Q U L q hq i).symm
  · exact localSubobjectKernel_lift X Q U L q

end AlgebraicGeometry.ProEtale
