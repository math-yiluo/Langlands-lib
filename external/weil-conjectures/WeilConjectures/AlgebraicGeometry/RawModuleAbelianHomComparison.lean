/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.HigherDirectImageRawDiagram
public import WeilConjectures.AlgebraicGeometry.RestrictedOverAbelianComplexData
public import WeilConjectures.AlgebraicGeometry.AbelianHigherDirectImageNaturalComparison
import WeilConjectures.AlgebraicGeometry.RawModuleAbelianHomMapIsIso
import WeilConjectures.AlgebraicGeometry.RawModuleAbelianHomMapNaturality

/-! # Scalar comparison for raw derived Hom

Source: Stacks Project, Tags 03FD and 03Q8.
-/

@[expose] public section

universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

/-- Compare module raw Hom to abelian raw Hom, before taking restricted cohomology.
Source: Stacks Project, Tag 03FD, lemma-cohomology-modules-abelian-agree;
Tag 03Q8 and its cited restriction lemmas, the sections description.
(blueprint: lem-sbc-raw-module-abelian-hom-comparison).

Proof: Resolve each pulled-back module sheaf by injectives. The free-module
sheaf adjunction identifies Hom from the pulled-back free representable with
sections on the etale fibre product. Forget scalars termwise. Injective module
sheaves are acyclic for abelian sections (03FD), so this same complex computes
abelian derived Hom from the free abelian representable, using its sections
adjunction. Forgetting scalars commutes with inverse image, identifying the
coefficient with the abelian pullback from W. The resulting additive comparison
is an isomorphism since it identifies the section complexes and their
cohomology. For f, expand the five factors of both raw pullbacks. Naturality of
the sections adjunction moves the class across the unit; the triangle identity
cancels the counit. The single and shift comparisons commute with scalar
forgetting, and inverse-image composition gives exactly the coefficient map
upperStarComp.inv used below. Hence the comparisons intertwine raw pullback
pointwise. In degree zero this is the ordinary free-sheaf sections adjunction;
on an empty test object both section complexes vanish. No cohomology
continuity or restricted derived-sections comparison is used. -/
theorem exists_rawModule_abelianHom_comparison
    (Λ : Type (u + 1)) [CommRing Λ] {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ) (U : S.Etale) :
    ∃ e : ∀ A : Over W,
      (higherDirectImageRawOverFunctor Λ k G (q : ℤ) U).obj (op A) ≅
        (abelianHigherDirectImageRawPresheaf (A.hom ≫ k) q
          (restrictedOverCoefficient
            ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj G)
            A)).obj (op U),
      ∀ (A B : Over W) (f : A ⟶ B)
        (z : (higherDirectImageRawOverFunctor Λ k G (q : ℤ) U).obj (op B)),
        (e A).hom ((higherDirectImageRawOverFunctor Λ k G (q : ℤ) U).map f.op z) =
          abelianHigherDirectImageRawPullback f.left (B.hom ≫ k) (A.hom ≫ k)
            (by rw [← Category.assoc, Over.w]) q
            (restrictedOverCoefficient
              ((sheafCompose _
                (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj G) B)
            (restrictedOverCoefficient
              ((sheafCompose _
                (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj G) A)
            ((upperStarComp AddCommGrpCat.{u + 1} f.left B.hom A.hom
              (Over.w f).symm).inv.app
                ((sheafCompose _
                  (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj G))
            U ((e B).hom z) := by
  have (A : Over W) : IsIso (rawModuleAbelianHomMap Λ k G q U A) :=
    isIso_rawModuleAbelianHomMap Λ k G q U A
  refine ⟨fun A ↦ asIso (rawModuleAbelianHomMap Λ k G q U A), ?_⟩
  exact rawModuleAbelianHomMap_naturality Λ k G q U

end AlgebraicGeometry.Etale
