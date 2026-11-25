/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleQuasiCoherentDescent

/-!
# The étale sheaf associated to a quasi-coherent module

Source: Stacks Project, Descent, Definition 35.8.2, Tag 03DU, item 4;
Section 35.8, equation (35.8.1), Tag 03DR
(blueprint: proposition-p-torsion-smooth-proper-curve).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

set_option autoImplicit false

/-- The associated abelian sheaf on the small étale site sends `u : U ⟶ X` to
`Γ(U, u^*F)`. Its underlying presheaf is `etaleTensorSectionsPresheaf F`, whose
restriction along `g : U' ⟶ U` is `c_{g,u}(g^*s)`: section pullback uses the canonical
unit of `tensorPullback g ⊣ pushforward g`, followed by the unit-normalized composition
isomorphism and transport along the equality of structure morphisms.
The sheaf condition is supplied by `isSheaf_etaleTensorSectionsPresheaf`, the separate
quasi-coherent descent theorem; this definition neither sheafifies nor changes the
section groups or their restrictions.
Source: Stacks Project, Descent, Tag 03DU, Definition 35.8.2, item 4, and Tag 03DR,
equation (35.8.1) (blueprint: proposition-p-torsion-smooth-proper-curve). -/
noncomputable def etaleTensorSectionsSheaf {X : Scheme.{u}} (F : X.Modules)
    [F.IsQuasicoherent] : Sheaf X.smallEtaleTopology AddCommGrpCat.{u} :=
  ⟨etaleTensorSectionsPresheaf F, isSheaf_etaleTensorSectionsPresheaf F⟩

end AlgebraicGeometry.Scheme.Modules
