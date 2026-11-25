/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
import Mathlib.AlgebraicGeometry.FunctionField
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
import WeilConjectures.AlgebraicGeometry.QuasiCoherentIdealZeroSetAffine
import WeilConjectures.AlgebraicGeometry.IntegralIdealGenericStalkEquivalences
import WeilConjectures.AlgebraicGeometry.IntegralIdealAffineSections

/-!
# Nonzero ideals on integral schemes and their generic stalks

Source: Stacks Project, Cohomology of Schemes, proof of Lemma 01YL
(blueprint: lem-weil-pbc-integral-scheme-ideal-generic-stalk).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section

namespace AlgebraicGeometry.Scheme

/-- A quasi-coherent ideal `J` on an integral scheme (`Scheme.IdealSheafData`, with ideal
sheaf `J.toModules ⊆ 𝒪_X`) is nonzero exactly when its sections on every nonempty affine
open are nonzero, exactly when its generic stalk is nonzero, and exactly when its generic
stalk is the whole generic local ring, which is a field. The stalk map of the inclusion
`J.toModulesι` at the generic point is injective; equality of its image with the whole
local ring is surjectivity of this map (independent of the identification of the stalk of
`𝒪_X` as a module with `𝒪_{X,η}`).

Source: Stacks Project, Cohomology of Schemes, proof of Lemma 01YL
(blueprint: lem-weil-pbc-integral-scheme-ideal-generic-stalk).

Proof:
1. Every nonempty open contains the generic point. On a nonempty affine open the section
ring is a domain, and the generic point corresponds to the zero prime. By
lem-weil-pbc-affine-open-spec-points and lem-weil-pbc-spec-domain-stalks-function-field,
the generic local ring is its fraction field, so it is a field.
2. By lem-weil-pbc-quasi-coherent-ideal-zero-set-affine, the generic stalk of the ideal
is the whole field iff its ideal of sections on that affine open is nonzero. Choosing a
nonempty affine open gives the equivalence of (b) and (d).
3. If (b) holds, a nonzero section shows that the ideal sheaf is not zero. Conversely,
a nonzero sheaf has a nonzero section on some open, whose germ is nonzero at some point
by def-weil-pbc-module-stalk and sheaf locality. Restrict to an affine neighbourhood of
that point. Its nonzero section gives (d) by step 2, and then (b). This proves (a), (b),
and (d) equivalent.
4. The inclusion induces an injective map on stalks, since filtered colimits of modules
preserve injections. Its image is an ideal of the generic local ring. A nonzero ideal
of a field contains an invertible element, hence contains 1 and equals the whole field.
Thus (c) and (d) are equivalent, completing all four equivalences. -/
theorem integral_ideal_generic_stalk (X : Scheme.{u}) [IsIntegral X]
    (J : X.IdealSheafData) :
    IsField (X.presheaf.stalk (genericPoint X)) ∧
      Function.Injective
        ((RingedSpace.moduleStalkFunctor X.toRingedSpace (genericPoint X)).map
          J.toModulesι).hom ∧
      (J ≠ ⊥ ↔ ∀ U : X.affineOpens, Nonempty U.1 → J.ideal U ≠ ⊥) ∧
      (J ≠ ⊥ ↔
        Nontrivial ((RingedSpace.moduleStalkFunctor X.toRingedSpace (genericPoint X)).obj
          J.toModules)) ∧
      (J ≠ ⊥ ↔
        Function.Surjective
          ((RingedSpace.moduleStalkFunctor X.toRingedSpace (genericPoint X)).map
            J.toModulesι).hom) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact (inferInstance : Field X.functionField).toIsField
  · exact (quasi_coherent_ideal_zero_set_affine X J).1 _
  · exact integral_ideal_nonzero_iff_affine_sections X J
  · exact (integral_ideal_nonzero_iff_generic_stalk X J).1
  · exact (integral_ideal_nonzero_iff_generic_stalk X J).2

end AlgebraicGeometry.Scheme
