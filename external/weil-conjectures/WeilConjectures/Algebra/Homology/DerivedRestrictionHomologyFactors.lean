/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-! # Homology of exact restriction after localization
Source: Stacks Project, Tag 05RR.
(blueprint: lem-pc-derived-restriction-homology-factors). -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w w'
open CategoryTheory
open scoped TensorProduct ChangeOfRings
namespace ModuleCat

/-- A localization factorization of exact restriction induces its homology
comparison, including compatibility with the homotopy factorization.
Source: Stacks Project, Tag 05RR (localization universal property).
(blueprint: lem-pc-derived-restriction-homology-factors).

Proof: combine q with the degree-i derived/homotopy homology factorization
isomorphisms and the exact-restriction short-complex homology isomorphism.
This gives an isomorphism between the two homology functors after
precomposition with complex localization. Complex localization is fully
faithful on functor categories, so the isomorphism lifts uniquely to z.
Its factorization equation is the displayed compatibility. Naturality of
short-complex homology and of the two factorization isomorphisms verifies
naturality before descent. Exactness of restriction holds for every ring
homomorphism, including maps involving zero rings. -/
theorem exists_derivedRestriction_homology_factors
    {B₀ B : Type u} [CommRing B₀] [CommRing B]
    [HasDerivedCategory.{w} (ModuleCat.{u} B₀)]
    [HasDerivedCategory.{w'} (ModuleCat.{u} B)]
    (f : B₀ →+* B)
    (E : DerivedCategory (ModuleCat.{u} B) ⥤ DerivedCategory (ModuleCat.{u} B₀))
    (i : ℤ) :
    let S₀ := HomotopyCategory.quotient (ModuleCat.{u} B₀) (.up ℤ) ⋙ DerivedCategory.Qh
    let S := HomotopyCategory.quotient (ModuleCat.{u} B) (.up ℤ) ⋙ DerivedCategory.Qh
    let U := restrictScalars.{u} f
    let H₀ := DerivedCategory.homologyFunctor (ModuleCat.{u} B₀) i
    let H := DerivedCategory.homologyFunctor (ModuleCat.{u} B) i
    let F₀ := Functor.isoWhiskerLeft (HomotopyCategory.quotient _ (.up ℤ))
      (DerivedCategory.homologyFunctorFactorsh (ModuleCat.{u} B₀) i) ≪≫
      HomotopyCategory.homologyFunctorFactors (ModuleCat.{u} B₀) (.up ℤ) i
    let F := Functor.isoWhiskerLeft (HomotopyCategory.quotient _ (.up ℤ))
      (DerivedCategory.homologyFunctorFactorsh (ModuleCat.{u} B) i) ≪≫
      HomotopyCategory.homologyFunctorFactors (ModuleCat.{u} B) (.up ℤ) i
    ∀ q : S ⋙ E ≅ U.mapHomologicalComplex (.up ℤ) ⋙ S₀,
      ∃ z : E ⋙ H₀ ≅ H ⋙ U,
        ∀ K : CochainComplex (ModuleCat.{u} B) ℤ,
          z.hom.app (S.obj K) ≫ U.map (F.hom.app K) =
            H₀.map (q.hom.app K) ≫
              F₀.hom.app ((U.mapHomologicalComplex (.up ℤ)).obj K) ≫
                ((K.sc i).mapHomologyIso U).hom  := by
  dsimp only
  intro q
  let U := restrictScalars.{u} f
  let Uc := U.mapHomologicalComplex (.up ℤ)
  let S := HomotopyCategory.quotient (ModuleCat.{u} B) (.up ℤ) ⋙ DerivedCategory.Qh
  let H₀ := DerivedCategory.homologyFunctor (ModuleCat.{u} B₀) i
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} B) i
  let F₀ := Functor.isoWhiskerLeft (HomotopyCategory.quotient _ (.up ℤ))
    (DerivedCategory.homologyFunctorFactorsh (ModuleCat.{u} B₀) i) ≪≫
    HomotopyCategory.homologyFunctorFactors (ModuleCat.{u} B₀) (.up ℤ) i
  let F := Functor.isoWhiskerLeft (HomotopyCategory.quotient _ (.up ℤ))
    (DerivedCategory.homologyFunctorFactorsh (ModuleCat.{u} B) i) ≪≫
    HomotopyCategory.homologyFunctorFactors (ModuleCat.{u} B) (.up ℤ) i
  let C : Uc ⋙ HomologicalComplex.homologyFunctor _ (.up ℤ) i ≅
      HomologicalComplex.homologyFunctor _ (.up ℤ) i ⋙ U :=
    NatIso.ofComponents (fun K ↦ (K.sc i).mapHomologyIso U) (by
      intro K K' g
      exact ShortComplex.mapHomologyIso_hom_naturality
        ((HomologicalComplex.shortComplexFunctor _ (.up ℤ) i).map g) U)
  let e : S ⋙ E ⋙ H₀ ≅ S ⋙ H ⋙ U :=
    Functor.isoWhiskerRight q H₀ ≪≫ Functor.isoWhiskerLeft Uc F₀ ≪≫ C ≪≫
      (Functor.isoWhiskerRight F U).symm
  let W := HomologicalComplex.quasiIso (ModuleCat.{u} B) (.up ℤ)
  let : S.IsLocalization W := Functor.IsLocalization.of_iso W
    (DerivedCategory.quotientCompQhIso (ModuleCat.{u} B)).symm
  let ff := Localization.fullyFaithfulWhiskeringLeft S W (ModuleCat.{u} B₀)
  let z : E ⋙ H₀ ≅ H ⋙ U := ff.preimageIso e
  refine ⟨z, ?_⟩
  intro K
  have hz := congr_app (ff.map_preimage e.hom) K
  change z.hom.app (S.obj K) = e.hom.app K at hz
  rw [hz]
  change (H₀.map (q.hom.app K) ≫ F₀.hom.app (Uc.obj K) ≫
      ((K.sc i).mapHomologyIso U).hom ≫ U.map (F.inv.app K)) ≫
      U.map (F.hom.app K) = _
  simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app]
  erw [U.map_id, Category.comp_id]

end ModuleCat
