/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.CategoryTheory.Triangulated.Orthogonal
public import WeilConjectures.AlgebraicGeometry.RingComplexCechData
import WeilConjectures.AlgebraicGeometry.PowerTorsionLocalizedShiftHom
import WeilConjectures.AlgebraicGeometry.RingComplexCechCohomologyPowerTorsion

/-! # Orthogonality of an ordered localization model to localized modules -/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Every shift of an augmented ordered localization model is left orthogonal to a module
on which an element of the defining ideal acts invertibly.
Source: Stacks Project, dualizing.tex, Tag 0A6R, lemma-local-cohomology-adjoint,
and the localization/restriction adjunction used in the node's finite localization proof.
(auxiliary; not a blueprint node)

Proof: take a finite generating list for I and append s; it still generates I. Apply
hT to this list. After inverting s, insert or delete the appended index in each ordered
subset, with its alternating sign. The resulting homotopy contracts the localized
ordered complex, including its degree-zero term. Localization is flat and exact, so
this is also vanishing of derived localization of T. If multiplication by s on M is
bijective, M has its unique A[1/s]-module structure, with s inverse acting by the inverse
linear map. The extension/restriction adjunction descends to derived categories because
both functors are exact for a localization. It identifies maps from each shift of T
into M[0] with maps from its zero localized object, and hence every such map is zero.
Evaluation at the unique site object identifies these constructions with ordinary
modules. Transport across the model isomorphism and across shifts and isomorphisms gives
exactly the right-orthogonal predicate displayed here. If s=0, M is zero. If I=0,
only this case is possible; the argument includes the zero ring and repeated generators.
-/
theorem ringComplex_cech_localized_orthogonality
    (A : CommRingCat.{u}) [HasDerivedCategory.{w} (RingSiteModules A)]
    (I : {I : Ideal A // I.FG})
    (T : CochainComplex (RingSiteModules A) ℤ) (εT : T ⟶ ringComplexSingle A)
    (hT : RingComplexHasCechModel A I.val T εT)
    (s : A) (hs : s ∈ I.val) (M : RingSiteModules A)
    (hM : Function.Bijective
      (fun x : M.val.obj (op ⟨PUnit.unit⟩) ↦ s • x)) :
    ((ObjectProperty.singleton (DerivedCategory.Q.obj T)).shiftClosure ℤ).rightOrthogonal
      (DerivedCategory.Q.obj
        ((HomologicalComplex.single (RingSiteModules A) (.up ℤ) 0).obj M)) := by
  have htors := ringComplex_cech_cohomology_power_torsion A I T εT hT s hs
  intro X f hX
  obtain ⟨Y, n, e, hY⟩ := hX
  have hY' : DerivedCategory.Q.obj T = Y :=
    (ObjectProperty.singleton_iff _ _).mp hY
  subst Y
  have hz := power_torsion_localized_shift_hom A T s htors M hM n (e.inv ≫ f)
  calc
    f = e.hom ≫ (e.inv ≫ f) := by simp
    _ = 0 := by rw [hz, comp_zero]

end AlgebraicGeometry
