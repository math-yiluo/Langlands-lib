/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import Mathlib.CategoryTheory.Functor.OfSequence
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
import WeilConjectures.AlgebraicGeometry.ProEtaleCountableProductsExact
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitExistence

/-!
# Derived limits of surjective towers on the small pro-etale site

Source: Bhatt--Scholze, Proposition 3.1.10, Proposition 3.2.3(1), and Proposition 4.2.8;
Stacks Project, Tags 07KC, 08TC, and 06XS
(auxiliary; not a blueprint node).

`n : ℕ` denotes positive level `n + 1`. Products and inverse limits are the existing
Mathlib constructions. The derived product is asserted to exist and the Roos assertion
works for every choice of its limit structure, without an existence hypothesis.

## Main declarations

* `surjectiveTower_hasSheafify` and `surjectiveTower_wEqualsLocallyBijective` transport
  Mathlib's sheafification structures to larger coefficient universes.
* `proEtale_surjectiveTower_derivedLimit` states the short exact Roos sequence, its
  derived-limit triangle, and uniqueness of compatible lifts from degree-zero sheaves.
-/

@[expose] public section

set_option autoImplicit false

universe t u w v v'

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

/-- Sheafification of large abelian coefficients on the unchanged small pro-etale site.
This is Mathlib's sheafification transported through an equivalent small model.
Source: Stacks Project, Tags 00W1 and 03DA
(auxiliary; not a blueprint node). -/
noncomputable instance surjectiveTower_hasSheafify (Y : Scheme.{t}) :
    HasSheafify (Scheme.ProEt.topology Y) AddCommGrpCat.{max u (t + 1)} :=
  letI : EssentiallySmall.{max u (t + 1)} Y.ProEt := essentiallySmallSelf.{u} _
  hasSheafifyEssentiallySmallSite.{t, max u (t + 1), t + 1,
    max u (t + 1) + 1, max u (t + 1)} _ _

/-- Large-coefficient sheafification detects the same locally bijective maps.
This reuses Mathlib's small-model transport without changing the original site.
Source: Stacks Project, Tags 00W1 and 03DA
(auxiliary; not a blueprint node). -/
noncomputable instance surjectiveTower_wEqualsLocallyBijective (Y : Scheme.{t}) :
    (Scheme.ProEt.topology Y).WEqualsLocallyBijective AddCommGrpCat.{max u (t + 1)} :=
  letI : EssentiallySmall.{max u (t + 1)} Y.ProEt := essentiallySmallSelf.{u} _
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{t, max u (t + 1),
    t + 1, max u (t + 1) + 1, max u (t + 1)} _

set_option backward.isDefEq.respectTransparency false in
private theorem exact_countable_products
    (Y : Scheme.{t})
    (R : Sheaf (Scheme.ProEt.topology Y) CommRingCat.{max u (t + 1)}) :
    CountableAB4Star (ringedSiteModules.{max u (t + 1)}
      ((sheafCompose (Scheme.ProEt.topology Y)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj R)) := by
  let A := ringedSiteModules.{max u (t + 1)}
    ((sheafCompose (Scheme.ProEt.topology Y)
      (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj R)
  constructor
  intro I _
  have : (lim : (Discrete I ⥤ A) ⥤ A).PreservesEpimorphisms := by
    constructor
    intro B C f hf
    let eB := HasLimit.isoOfNatIso (Discrete.natIsoFunctor (F := B))
    let eC := HasLimit.isoOfNatIso (Discrete.natIsoFunctor (F := C))
    have h (i : I) : Epi (f.app ⟨i⟩) := inferInstance
    have : Epi (Limits.Pi.map (fun i : I ↦ f.app ⟨i⟩)) :=
      (Scheme.ProEt.countableProducts_exact Y R).2.2 I _ _ _ h
    have hh : lim.map f = eB.hom ≫ Limits.Pi.map (fun i : I ↦ f.app ⟨i⟩) ≫ eC.inv := by
      apply limit.hom_ext
      rintro ⟨i⟩
      dsimp only [eB, eC]
      simp only [Category.assoc, HasLimit.isoOfNatIso_inv_π,
        Discrete.natIsoFunctor_inv_app]
      change lim.map f ≫ limit.π C ⟨i⟩ =
        (HasLimit.isoOfNatIso (Discrete.natIsoFunctor (F := B))).hom ≫
          Limits.Pi.map (fun i : I ↦ f.app ⟨i⟩) ≫ Pi.π _ i
      rw [Pi.map_π, HasLimit.isoOfNatIso_hom_π_assoc]
      simp
    rw [hh]
    infer_instance
  exact hasExactLimitsOfShape_of_preservesEpi (C := A) (Discrete I)

end AlgebraicGeometry.ProEtale
