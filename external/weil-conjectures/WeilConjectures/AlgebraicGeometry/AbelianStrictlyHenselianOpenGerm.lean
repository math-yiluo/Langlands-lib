/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import WeilConjectures.Mathlib.RingTheory.Henselian
import WeilConjectures.AlgebraicGeometry.StrictlyHenselianOpenSectionsStalk
import Mathlib.Algebra.Category.Grp.FilteredColimits

/-!
# Abelian sections on a strictly henselian open neighbourhood

Source: Stacks Project, Etale Cohomology, Tags 03QO, 03S2 and 03Q1.
(blueprint: lem-weil-pbc-abelian-strictly-henselian-open-germ)
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Sections of an abelian etale sheaf on a strictly henselian open neighbourhood
identify with its geometric stalk at the closed point.
Source: Stacks Project, Tags 03QO, 03S2 and 03Q1.
(blueprint: lem-weil-pbc-abelian-strictly-henselian-open-germ)

Proof: Apply `strictlyHenselianOpen_toPresheafFiber_bijective` to the sheaf obtained
from F by forgetting its group structure. The resulting map to the underlying-set
stalk is bijective, hence an isomorphism in Type. The forgetful functor on abelian
groups preserves filtered colimits; shrink this instance to the universe of the
pointed neighbourhood category. Consequently `presheafFiberCompIso` identifies
the underlying-set stalk with the underlying set of the abelian-group stalk.
`toPresheafFiber_presheafFiberCompIso_hom_app` identifies the composite of the set
germ with this comparison with the forgetful image of the abelian germ. Both
factors are isomorphisms. The forgetful functor reflects isomorphisms, so the
abelian germ is an isomorphism as claimed. The argument permits arbitrary larger
coefficient universes and does not require T to be finite or zero-dimensional. -/
theorem strictlyHenselianOpen_abelian_germ_isIso
    {T : Scheme.{u}} (U : T.Opens)
    {R : Type u} [CommRing R] [IsLocalRing R]
    (hR : IsStrictlyHenselianLocalRing R) (e : U.toScheme ≅ Spec (.of R))
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ T)
    (t : Spec (.of Ω) ⟶ U.toScheme) (ht : t ≫ U.ι = s)
    (hclosed : (t ≫ e.hom) default = IsLocalRing.closedPoint R)
    (F : Sheaf T.smallEtaleTopology AddCommGrpCat.{(max u v) + 1}) :
    IsIso ((pointSmallEtale s).toPresheafFiber (Etale.mk U.ι) (Over.homMk t ht) F.obj) := by
  have : CategoryTheory.Limits.PreservesFilteredColimitsOfSize.{u, u}
      (CategoryTheory.forget AddCommGrpCat.{(max u v) + 1}) :=
    preservesFilteredColimitsOfSize_shrink.{u, (max u v) + 1, u, (max u v) + 1} _
  let H := (sheafCompose T.smallEtaleTopology
    (CategoryTheory.forget AddCommGrpCat.{(max u v) + 1})).obj F
  have hb := strictlyHenselianOpen_toPresheafFiber_bijective.{u, (max u v) + 1}
    U hR e s t ht hclosed H
  have hi : IsIso ((pointSmallEtale s).toPresheafFiber
      (Etale.mk U.ι) (Over.homMk t ht) H.obj) :=
    (ConcreteCategory.isIso_iff_bijective _).2 hb
  have hcomp := (pointSmallEtale s).toPresheafFiber_presheafFiberCompIso_hom_app
    (CategoryTheory.forget AddCommGrpCat.{(max u v) + 1})
    (Etale.mk U.ι) (Over.homMk t ht) F.obj
  have hf : IsIso ((CategoryTheory.forget AddCommGrpCat.{(max u v) + 1}).map
      ((pointSmallEtale s).toPresheafFiber (Etale.mk U.ι) (Over.homMk t ht) F.obj)) := by
    rw [← hcomp]
    change IsIso ((pointSmallEtale s).toPresheafFiber
      (Etale.mk U.ι) (Over.homMk t ht) H.obj ≫ _)
    infer_instance
  exact isIso_of_reflects_iso _ (CategoryTheory.forget AddCommGrpCat.{(max u v) + 1})

end AlgebraicGeometry.Scheme
