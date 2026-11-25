/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Sites.IsSheafFor
import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.Subcanonical
public import Mathlib.CategoryTheory.Sites.SubcanonicalOver

/-!
# Representable presheaves are sheaves on the small étale site

## References

* Stacks Project, Tags 03O3 and 03O4
-/

@[expose] public section

universe u

open CategoryTheory
open AlgebraicGeometry

namespace AlgebraicGeometry

/--
For a scheme `T` and a `T`-scheme `X`, the representable presheaf on the
small étale site of `T` is a sheaf for the étale topology. Its value on an
étale `T`-scheme `U` is the set of morphisms `U ⟶ X` over `T`, and the
statement is expressed by the unique amalgamation condition for every
covering presieve.
-/
theorem smallEtaleRepresentablePresheaf_isSheaf
    (T X : Scheme.{u}) [X.Over T] :
    ∀ (U : T.Etale) (R : Presieve U),
      Sieve.generate R ∈ Scheme.smallEtaleTopology T U →
        Presieve.IsSheafFor
          ((Scheme.Etale.forget T).op ⋙
            yoneda.obj (Over.mk (X ↘ T))) R := by
  let : Scheme.etaleTopology.Subcanonical :=
    GrothendieckTopology.Subcanonical.of_le Scheme.etaleTopology_le_proetaleTopology
  have h : Presieve.IsSheaf (Scheme.etaleTopology.over T)
      (yoneda.obj (Over.mk (X ↘ T))) :=
    GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _
  let : RepresentablyFlat (Scheme.Etale.forget T) :=
    flat_of_preservesFiniteLimits _
  let : (Scheme.Etale.forget T).LocallyCoverDense (Scheme.etaleTopology.over T) :=
    Scheme.locallyCoverDense_of_le T le_rfl
  let : (Scheme.Etale.forget T).IsContinuous (Scheme.smallEtaleTopology T)
      (Scheme.etaleTopology.over T) := by
    apply (Functor.isContinuous_iff_coverPreserving).2
    exact Functor.coverPreserving_restrictedTopology (Scheme.Etale.forget T)
      (Scheme.etaleTopology.over T)
  have hsmall := (Scheme.Etale.forget T).op_comp_isSheaf_of_isSheaf_type
    (Scheme.smallEtaleTopology T) h
  intro U R hR
  exact hsmall.isSheafFor R hR

end AlgebraicGeometry
