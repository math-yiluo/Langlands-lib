/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleTensorSections
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import WeilConjectures.AlgebraicGeometry.EtaleTensorSectionsHomComparison

/-!
# Étale descent for sections of quasi-coherent modules

Source: Stacks Project, Descent, Section 35.8, Tags 03DR and 03DT
(blueprint: proposition-p-torsion-smooth-proper-curve).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

set_option autoImplicit false

/-- The presheaf `u : U ⟶ X ↦ Γ(U, u^*F)`, with pullback restrictions, is a sheaf on
`X.smallEtaleTopology` when `F` is quasi-coherent.
Source: Stacks Project, Descent, Section 35.8, equation (35.8.1) and Lemma 35.8.1,
Tags 03DR and 03DT (blueprint: proposition-p-torsion-smooth-proper-curve).

Proof:
1. Identify the underlying presheaf of sets with `etaleHom (unitObj X) F` using
   `lem-sc-etale-tensor-sections-hom-comparison`. The identification intertwines the
   unit-normalized tensor-pullback restrictions with the restrictions on module maps.
2. The structure sheaf and `F` are quasi-coherent, so `isSheaf_etaleHom` gives the
   sheaf condition for that Hom presheaf. This is the full-faithfulness part of fpqc
   descent, restricted to the small étale site, exactly as in Stacks Tag 03DT.
3. Transport the sheaf condition across the isomorphism, then reflect it through the
   forgetful functor from abelian groups to sets. -/
theorem isSheaf_etaleTensorSectionsPresheaf {X : Scheme.{u}} (F : X.Modules)
    [F.IsQuasicoherent] :
    Presheaf.IsSheaf X.smallEtaleTopology (etaleTensorSectionsPresheaf F) := by
  apply Presheaf.isSheaf_of_isSheaf_comp _ _ (CategoryTheory.forget AddCommGrpCat)
  rw [isSheaf_iff_isSheaf_of_type]
  obtain ⟨e⟩ := nonempty_etaleTensorSectionsHomIso F
  exact Presieve.isSheaf_iso _ e.symm
    ((isSheaf_iff_isSheaf_of_type _ _).1 (isSheaf_etaleHom (unitObj X) F))

end AlgebraicGeometry.Scheme.Modules
