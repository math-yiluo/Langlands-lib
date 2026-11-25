/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.KFlat

/-!
# Compatibility names for K-flat complexes of sheaves

The adopted source supplies the tensor localization and zero-morphism instances.
The legacy predicate names below unfold to its identical constructions. This avoids
copying the sectionwise tensor-Hom and sheafification proofs.

Source: Stacks Project, Cohomology on Sites, Definition 06YN and Lemma 06YS
(blueprint: def-pc-kflat-complex).
-/

@[expose] public section

universe u v

open CategoryTheory

namespace CochainComplex

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {R : Sheaf J CommRingCat.{max u v}}

/-- K-flatness against acyclic complexes, with the legacy name.
Source: Stacks Project, Definition 06YN (blueprint: def-pc-kflat-complex). -/
def IsAcyclicTensorKFlat
    (K : CochainComplex
      (SheafOfModules.{max u v} ((sheafCompose J
          (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)) ℤ) :
    Prop :=
  IsKFlatTensor K

end CochainComplex
