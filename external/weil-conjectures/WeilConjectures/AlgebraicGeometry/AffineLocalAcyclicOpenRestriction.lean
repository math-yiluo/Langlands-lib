/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

import WeilConjectures.AlgebraicGeometry.EtalePullbackForgetModules
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-! # Affine-local acyclicity under open restriction

Source: Stacks Project, Tag 0A51, the Mayer--Vietoris induction, and Tag 03D3.
(blueprint: lem-weil-pbc-affine-local-acyclic-open-restriction).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme Etale

/-- Affine-local acyclicity is inherited by restriction to an open subscheme.
Source: Stacks Project, Tag 0A51, induction step; inverse-image composition and
base-change associativity, Stacks Project, Tag 03D3.
(blueprint: lem-weil-pbc-affine-local-acyclic-open-restriction)

Proof: Let O be an affine open of W. Its image W.ι(O) is an affine open of X,
because O and its image are isomorphic as schemes. Apply hlocal to that image.
The iterated fibre product O ×_W (W ×_X Z) is canonically isomorphic to
W.ι(O) ×_X Z, by the open-image isomorphism and associativity of fibre products.
Under this isomorphism the sheaves in the two groups agree: both are the inverse
image of J along the same composite to X. The composition isomorphisms of module
inverse image and their compatibility with forgetting coefficients give an
isomorphism of abelian sheaves. Cohomology preserves sheaf isomorphisms, and
pullback along a scheme isomorphism induces an isomorphism on cohomology.
Transport the subsingleton instance supplied by hlocal across these isomorphisms.
The argument also applies to empty opens, to W = top, and to any morphism i. -/
theorem Etale.affine_local_acyclic_open_restriction
    (Λ : Type (u + 1)) [CommRing Λ] {X Z : Scheme.{u}} (i : Z ⟶ X)
    (J : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hlocal : ∀ (W : X.Opens), IsAffineOpen W → ∀ (q : ℕ), 0 < q →
      Subsingleton (Sheaf.H
        ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
          ((pullback.fst W.ι i)^*[ModuleCat.{u + 1} Λ].obj
            ((W.ι)^*[ModuleCat.{u + 1} Λ].obj J))) q))
    (W : X.Opens) :
    ∀ (O : W.toScheme.Opens), IsAffineOpen O → ∀ (q : ℕ), 0 < q →
      Subsingleton (Sheaf.H
        ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
          ((pullback.fst O.ι (pullback.fst W.ι i))^*[ModuleCat.{u + 1} Λ].obj
            ((O.ι)^*[ModuleCat.{u + 1} Λ].obj
              ((W.ι)^*[ModuleCat.{u + 1} Λ].obj J)))) q) := by
  intro O hO q hq
  have hT := hO.image_of_isOpenImmersion W.ι
  let := hlocal (W.ι ''ᵁ O) hT q hq
  let M := ModuleCat.{u + 1} Λ
  let T := W.ι ''ᵁ O
  let a := W.ι.isoImage O
  let b := asIso (pullback.map (O.ι ≫ W.ι) i T.ι i a.hom (𝟙 Z) (𝟙 X)
    (by simp [a, T]) (by simp))
  let e := pullbackRightPullbackFstIso W.ι i O.ι ≪≫ b
  let p := pullback.fst O.ι (pullback.fst W.ι i)
  let r := pullback.fst T.ι i
  have he : e.hom ≫ r ≫ T.ι = p ≫ O.ι ≫ W.ι := by
    simp [e, b, r, p, a, T, Category.assoc]
  let F := (r)^*[M].obj ((T.ι)^*[M].obj J)
  let U := sheafCompose (pullback O.ι (pullback.fst W.ι i)).smallEtaleTopology
    (forget₂ M AddCommGrpCat.{u + 1})
  let V := sheafCompose (pullback T.ι i).smallEtaleTopology
    (forget₂ M AddCommGrpCat.{u + 1})
  let c₁ := ((e.hom)^*[M]).mapIso ((Etale.upperStarComp M r T.ι).symm.app J)
  let c₂ := (Etale.upperStarComp M e.hom (r ≫ T.ι)
    (p ≫ O.ι ≫ W.ι) he.symm).symm.app J
  let c₃ := (Etale.upperStarComp M p (O.ι ≫ W.ι)).app J
  let c₄ := ((p)^*[M]).mapIso ((Etale.upperStarComp M O.ι W.ι).app J)
  let c := c₁ ≪≫ c₂ ≪≫ c₃ ≪≫ c₄
  obtain ⟨d⟩ := Etale.pullback_forget_modules_iso Λ e.hom F
  let s := d.symm ≪≫ U.mapIso c
  let t := (Sheaf.functorH _ q).mapIso s
  let h := (Etale.cohomologyEquiv e.hom (V.obj F) q).trans
    (Iso.addCommGroupIsoToAddEquiv t)
  exact h.symm.injective.subsingleton

end AlgebraicGeometry
