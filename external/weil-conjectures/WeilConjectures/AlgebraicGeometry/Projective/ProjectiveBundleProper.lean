/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveBundleMorphism
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.AlgebraicGeometry.Canonical.CanonicalRelativeProjProper
import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveImpliesProper

/-!
# Properness of projective-bundle morphisms

## References

* Stacks Project, Morphisms
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A morphism presented as a closed subscheme of the relative projective bundle of a
finite-type quasi-coherent module is proper. -/
theorem projectiveBundle_proper {X S : Scheme.{u}} (f : X ⟶ S)
    (hf : IsProjectiveBundle f) : IsProper f := by
  obtain ⟨E, hE, hEfin, i, hi, hcomp⟩ := hf
  have hA : IsProper
      (@SymmetricAlgebraSheaf.gradedAlgebraData S E hE).relProjHom :=
    canonicalRelativeProj_proper E ⟨hE, hEfin⟩
  have hi' : IsProper i :=
    (hProjective_properness.2.2.1 i hi)
  have hicomp : IsProper
      (i ≫ (@SymmetricAlgebraSheaf.gradedAlgebraData S E hE).relProjHom) :=
    hProjective_properness.2.2.2 i
      (@SymmetricAlgebraSheaf.gradedAlgebraData S E hE).relProjHom hi' hA
  rw [← hcomp]
  exact hicomp

end AlgebraicGeometry

end
