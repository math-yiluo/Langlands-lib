/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.Algebra.Category.Grp.Ulift

import WeilConjectures.AlgebraicGeometry.EtaleULiftInjective
import WeilConjectures.AlgebraicGeometry.EtaleULiftHomology

/-!
# Lifting an injective resolution on the small étale site

Source: Stacks Project, Injectives, Lemma 19.7.3, Tag 01DO;
Mathlib's small affine étale site equivalence and preservation of homology by ULift.
(blueprint: lem-sc-etale-ulift-injective-resolution)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

set_option autoImplicit false

/-- An injective resolution can be lifted to the larger coefficient universe, and
its evaluation complexes are the lifts of the original evaluation complexes.
Source: Stacks Project, Injectives, Lemma 19.7.3, Tag 01DO
(https://stacks.math.columbia.edu/tag/01DO); Mathlib
`AffineEtale.sheafEquiv` and `AddCommGrpCat.uliftFunctor`.
(blueprint: lem-sc-etale-ulift-injective-resolution)

Proof: Restrict to the u-small model of the affine étale site, using
`AffineEtale.sheafEquiv`, then an equivalence with a u-small skeleton of the
essentially u-small affine site. Transport the topology along this equivalence.
On this small site, the free abelian sheaf on each
representable has u-small values. Indeed the representable and its free abelian
presheaf have u-small values, and sheafification uses only u-small limits and
colimits. ULift preserves these constructions. Every subsheaf of the lifted free
representable is u-small objectwise; shrinking these values transports its group
structure and restriction maps to a u-valued sheaf. The inclusion is then the lift
of a monomorphism in the smaller sheaf category. If I is injective there, every map
from this subsheaf to the lift of I extends over the free representable, by full
faithfulness of ULift and injectivity of I. The injectivity criterion of Tag 01DO
therefore proves that the lift of I is injective in the larger sheaf category.
The site equivalence commutes with coefficient lift, so this holds on X.Etale too.

Coefficient lift is exact: kernels are computed objectwise and ULift preserves
them; epimorphisms of sheaves are locally surjective, and local surjectivity is
unchanged by lift. It is additive and commutes with the single complex. Thus
applying coefficient lift degreewise to R and its augmentation gives an injective
resolution S of the lifted sheaf. Evaluating at each U commutes with coefficient
lift on objects and maps, so the complexes in the conclusion are canonically
isomorphic. This includes the empty scheme and the zero sheaf, and requires no
quasi-coherence or affine hypothesis on X. -/
theorem exists_etale_ulift_injectiveResolution
    (X : Scheme.{u}) (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (R : InjectiveResolution F) :
    ∃ S : InjectiveResolution
      ((sheafCompose X.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}).obj F),
      ∀ U : X.Etale, Nonempty
        (((sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
          (CategoryTheory.evaluation X.Etaleᵒᵖ AddCommGrpCat.{u + 1}).obj
            (op U)).mapHomologicalComplex
            (.up ℕ)).obj S.cocomplex ≅
          ((sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u} ⋙
            (CategoryTheory.evaluation X.Etaleᵒᵖ AddCommGrpCat.{u}).obj (op U) ⋙
              AddCommGrpCat.uliftFunctor.{u + 1, u}).mapHomologicalComplex
                (.up ℕ)).obj R.cocomplex) := by
  let L := sheafCompose X.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}
  have : L.PreservesHomology := etale_ulift_preservesHomology X
  have : L.Additive := { map_add := fun {_ _ _ _} => rfl }
  let e := HomologicalComplex.singleMapHomologicalComplex L (.up ℕ) 0
  let S : InjectiveResolution (L.obj F) :=
    { cocomplex := (L.mapHomologicalComplex (.up ℕ)).obj R.cocomplex
      injective := fun n => etale_ulift_injective X (R.cocomplex.X n)
      ι := (e.app F).inv ≫ (L.mapHomologicalComplex (.up ℕ)).map R.ι
      quasiIso := by
        dsimp [e]
        infer_instance }
  refine ⟨S, fun U => ⟨?_⟩⟩
  exact Iso.refl _

end AlgebraicGeometry.Scheme
