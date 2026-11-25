/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import WeilConjectures.Algebra.Homology.DerivedHomFiniteFreeModelAux

/-!
# Derived internal Hom from a bounded-above finite free model

Source: Stacks Project, Cohomology, Tag 0GM8, case (2), and Cohomology on Sites,
Section 08J7 (blueprint: lem-sc-derived-hom-finite-free-model).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace AlgebraicGeometry

/-- A bounded-above finite free model computes derived internal Hom into a bounded-below
complex of module sheaves on a ringed space.
Source: Stacks Project, Cohomology, Tag 0GM8, case (2), and Cohomology on Sites,
Section 08J7 (blueprint: lem-sc-derived-hom-finite-free-model).

Proof:
1. By `lem-sc-bounded-below-injective-resolution`, choose a quasi-isomorphism `G ⟶ I`
   with `I` bounded below, termwise injective and K-injective.
2. Its cone is bounded below and acyclic. Apply
   `lem-sc-bounded-above-finite-free-hom-acyclic` to that cone: the induced morphism
   `homComplex E G ⟶ homComplex E I` is a quasi-isomorphism.
3. By `def-pur-derived-internal-hom`, `homComplex E I` computes derived internal Hom
   from `Q(E)` to `Q(G)`. The localization comparison into `I` is bijective by
   `lem-sc-kinjective-quasi-iso-comparison`. Localize the quasi-isomorphism in step 2
   and use `f : E ⟶ K` to identify `Q(E)` with `Q(K)`. Compose the resulting
   isomorphisms to obtain the stated representation. -/
theorem derivedInternalHom_of_boundedAbove_finiteFree
    (U : RingedSpace.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings U))]
    (E G K : CochainComplex (SheafOfModules.{u} (moduleRings U)) ℤ)
    (hEbounded : ∃ N : ℤ, ∀ p : ℤ, N < p → IsZero (E.X p))
    (hEfree : ∀ p : ℤ, ∃ r : ℕ, Nonempty (E.X p ≅
      SheafOfModules.free (R := moduleRings U) (ULift.{u} (Fin r))))
    (hGbounded : ∃ M : ℤ, ∀ q : ℤ, q < M → IsZero (G.X q))
    (f : E ⟶ K) [QuasiIso f] :
    Nonempty (DerivedCategory.Q.obj (CategoryTheory.homComplex (R := U.sheaf) E G) ≅
      (CategoryTheory.derivedInternalHom (Opens.grothendieckTopology U) U.sheaf).obj
        (op (DerivedCategory.Q.obj K), DerivedCategory.Q.obj G)) := by
  obtain ⟨e⟩ := derivedInternalHom_of_boundedAbove_finiteFree_aux U E G
    hEbounded hEfree hGbounded
  let qf := DerivedCategory.Q.map f
  have hqf : IsIso qf :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ f).mpr inferInstance
  let eEK : DerivedCategory.Q.obj E ≅ DerivedCategory.Q.obj K := asIso qf
  exact ⟨e ≪≫
    (CategoryTheory.derivedInternalHom (Opens.grothendieckTopology U) U.sheaf).mapIso
      (eEK.symm.op.prod (Iso.refl _))⟩

end AlgebraicGeometry
