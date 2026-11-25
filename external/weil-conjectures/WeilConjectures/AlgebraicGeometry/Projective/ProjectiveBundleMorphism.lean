/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SymmetricAlgebraSheaf.CanonicalSymmetricGradedAlgebra
public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Projectivity by a closed embedding into a projective bundle

The projective bundle is the canonical relative Proj of the symmetric-degree graded
symmetric algebra. No grading or gluing realization is chosen as an extra witness.  The
predicate below
uses the canonical affine-basis symmetric graded algebra construction.

## References

* Stacks Project, Morphisms, Definition 01W8(1), and Constructions, Definition 01OB
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A morphism is projective in the EGA projective-bundle sense if it is the composite
of a closed immersion into P(E) and its structural morphism, for a quasi-coherent
finite-type module E. The algebra, its symmetric grading and relative Proj construction
are canonical. Local freeness is not required. -/
def IsProjectiveBundle {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  ∃ (E : S.Modules) (hE : E.IsQuasicoherent), E.IsFiniteType ∧
    ∃ (i : X ⟶ (@SymmetricAlgebraSheaf.gradedAlgebraData S E hE).relProj),
      IsClosedImmersion i ∧
        i ≫ (@SymmetricAlgebraSheaf.gradedAlgebraData S E hE).relProjHom = f

end AlgebraicGeometry
