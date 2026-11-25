/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitExistence

/-!
# Countable products and unbounded right derived functors

Source: Stacks Project, Tag 08U1, proof of `lemma-RF-commutes-with-Rlim`.
(blueprint: lem-pc-right-derived-functor-countable-products).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- An additive countable-product-preserving functor from sheaves of modules to abelian
 groups has a countable-product-preserving unbounded right derived functor.
Source: Stacks Project, Tag 08U1, proof of `lemma-RF-commutes-with-Rlim`.
(blueprint: lem-pc-right-derived-functor-countable-products).

Proof: For a countable family `K n`, choose K-injective representatives `I n`, together
with isomorphisms `Q(I n) ≅ K n`. The termwise product `P` of the representatives is
K-injective and its localized projections form a product cone by
`HomotopyCategory.isLimitFanQuotient` and the K-injective Hom comparison
(Tag 0BK6). The unit of the right derived
functor is invertible on each `I n` and on `P`. Its naturality on every projection
identifies the image product cone with the localization of the cone obtained by applying
`F` termwise to `P`. Since `F` preserves countable products, that cone is the termwise
product cone of the complexes `F(I n)`. Abelian groups have exact countable products,
so the termwise-product clause of `derivedCategory_countableProducts_and_towerLimit`
(Tag 07KC) makes its localization a product cone, even though the complexes `F(I n)`
need not be K-injective. Transport this limit property along the unit isomorphisms and
the representative isomorphisms. Thus the image of the product cone of `K` is a limit
cone. Every discrete countable diagram is isomorphic to such a family diagram, which
proves preservation of all limits of shape `Discrete ℕ`. -/
theorem rightDerivedFunctor_preservesCountableProducts (X : Scheme.{u})
    (F : X.Modules ⥤ AddCommGrpCat.{u}) [F.Additive]
    [PreservesLimitsOfShape (Discrete ℕ) F]
    [Abelian.HasKInjectiveResolutions X.Modules]
    [Abelian.HasKInjectiveResolutions AddCommGrpCat.{u}]
    [HasDerivedCategory X.Modules] [HasDerivedCategory AddCommGrpCat.{u}] :
    PreservesLimitsOfShape (Discrete ℕ) F.rightDerivedFunctor := by
  classical
  let G := F.mapHomologicalComplex (ComplexShape.up ℤ)
  let q := HomotopyCategory.quotient X.Modules (ComplexShape.up ℤ)
  let a : G ⋙ DerivedCategory.Q ≅
      q ⋙ (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) :=
    Functor.isoWhiskerLeft G (DerivedCategory.quotientCompQhIso AddCommGrpCat).symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (F.mapHomotopyCategoryFactors _).symm DerivedCategory.Qh ≪≫
      Functor.associator _ _ _
  let β : G ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ F.rightDerivedFunctor :=
    a.hom ≫ Functor.whiskerLeft q F.rightDerivedFunctorUnit ≫
      (Functor.associator _ _ _).inv ≫
      (Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso X.Modules)
        F.rightDerivedFunctor).hom
  have hβ (I : CochainComplex X.Modules ℤ) [I.IsKInjective] : IsIso (β.app I) := by
    dsimp [β, a]
    infer_instance
  obtain ⟨hP, hQ, _⟩ := derivedCategory_countableProducts_and_towerLimit AddCommGrpCat.{u}
  have : ∀ (I : ℕ → CochainComplex AddCommGrpCat.{u} ℤ),
      PreservesLimit (Discrete.functor I) DerivedCategory.Q := fun I ↦
    preservesLimit_of_preserves_limit_cone (limit.isLimit _) (hQ ℕ I).some
  have : PreservesLimitsOfShape (Discrete ℕ) (DerivedCategory.Q (C := AddCommGrpCat.{u})) :=
    preservesLimitsOfShape_of_discrete _
  have hfamily (K : ℕ → DerivedCategory X.Modules) :
      PreservesLimit (Discrete.functor K) F.rightDerivedFunctor := by
    have hex (n : ℕ) := DerivedCategory.exists_iso_Q_obj_of_isKInjective (K n)
    choose I hI he using hex
    let e (n : ℕ) := (Classical.choice (he n)).symm
    have : ∀ n, (I n).IsKInjective := hI
    let P := HomologicalComplex.coneOfHasLimitEval (Discrete.functor I)
    let qP := HomotopyCategory.quotient (X.Modules) (.up ℤ)
    let hqFan := HomotopyCategory.isLimitFanQuotient (X.Modules) (.up ℤ)
      (HomologicalComplex.isLimitConeOfHasLimitEval (Discrete.functor I))
    have hPI : CochainComplex.IsKInjective P.pt := by
      rw [CochainComplex.isKInjective_iff_rightOrthogonal]
      exact (HomotopyCategory.subcategoryAcyclic (X.Modules)).rightOrthogonal.prop_of_isLimit
        hqFan (fun j ↦ CochainComplex.IsKInjective.rightOrthogonal (I j.as))
    have : CochainComplex.IsKInjective P.pt := hPI
    let hqP := (Fan.isLimitMapConeEquiv qP I P).symm hqFan
    let L := DerivedCategory.Qh (C := X.Modules)
    let pre (s : Cone ((Discrete.functor I ⋙ qP) ⋙ L)) :
        Cone (Discrete.functor I ⋙ qP) :=
      { pt := L.objPreimage s.pt
        π := Discrete.natTrans fun j ↦
          (Equiv.ofBijective _ (CochainComplex.IsKInjective.Qh_map_bijective
            (L.objPreimage s.pt) (I j.as))).symm
              ((L.objObjPreimageIso s.pt).hom ≫ s.π.app j) }
    have key (s : Cone ((Discrete.functor I ⋙ qP) ⋙ L)) (j : Discrete ℕ) :
        L.map ((pre s).π.app j) = (L.objObjPreimageIso s.pt).hom ≫ s.π.app j :=
      (Equiv.ofBijective _ (CochainComplex.IsKInjective.Qh_map_bijective
        (L.objPreimage s.pt) (I j.as))).apply_symm_apply _
    have hd : IsLimit (L.mapCone (qP.mapCone P)) := by
      refine
        { lift := fun s ↦ (L.objObjPreimageIso s.pt).inv ≫ L.map (hqP.lift (pre s))
          fac := ?_
          uniq := ?_ }
      · intro s j
        dsimp only [Functor.mapCone_π_app]
        have fac := hqP.fac (pre s) j
        dsimp only [Functor.mapCone_π_app] at fac
        rw [Category.assoc, ← L.map_comp, fac, key]
        simp
      · intro s m hm
        dsimp only [Functor.mapCone_π_app] at hm
        obtain ⟨m', hm'⟩ := (CochainComplex.IsKInjective.Qh_map_bijective
          (L.objPreimage s.pt) P.pt).surjective ((L.objObjPreimageIso s.pt).hom ≫ m)
        have eq : m' = hqP.lift (pre s) := by
          apply hqP.uniq (pre s) m'
          intro j
          apply (CochainComplex.IsKInjective.Qh_map_bijective
            (L.objPreimage s.pt) (I j.as)).injective
          simp only [Functor.mapCone_π_app]
          rw [L.map_comp, hm', Category.assoc, hm j, key]
        rw [← eq, hm']
        simp
    have hPL : IsLimit (DerivedCategory.Q.mapCone P) :=
      IsLimit.mapConeEquiv (DerivedCategory.quotientCompQhIso (X.Modules)) hd
    have hFPL := isLimitOfPreserves DerivedCategory.Q
      (isLimitOfPreserves G (HomologicalComplex.isLimitConeOfHasLimitEval (Discrete.functor I)))
    let α : Discrete.functor I ⋙ DerivedCategory.Q ≅ Discrete.functor K :=
      Discrete.natIso (fun (n : Discrete ℕ) ↦ e n.as)
    let c := (Cone.postcompose α.hom).obj (DerivedCategory.Q.mapCone P)
    have hc : IsLimit c := (IsLimit.postcomposeHomEquiv α _).symm hPL
    apply preservesLimit_of_preserves_limit_cone hc
    let αβ : (Discrete.functor I ⋙ G) ⋙ DerivedCategory.Q ≅
        (Discrete.functor I ⋙ DerivedCategory.Q) ⋙ F.rightDerivedFunctor :=
      Discrete.natIso (fun (n : Discrete ℕ) ↦ asIso (β.app (I n.as)))
    have hmap : IsLimit (F.rightDerivedFunctor.mapCone (DerivedCategory.Q.mapCone P)) :=
      (IsLimit.equivOfNatIsoOfIso αβ
        (DerivedCategory.Q.mapCone (G.mapCone P))
        (F.rightDerivedFunctor.mapCone (DerivedCategory.Q.mapCone P))
        (Cone.ext (asIso (β.app P.pt)) (fun n ↦ by
          simpa [αβ] using β.naturality (P.π.app n)))).1 hFPL
    exact (IsLimit.equivOfNatIsoOfIso (Functor.isoWhiskerRight α F.rightDerivedFunctor)
      (F.rightDerivedFunctor.mapCone (DerivedCategory.Q.mapCone P))
      (F.rightDerivedFunctor.mapCone c) (Cone.ext (Iso.refl _) (fun n ↦ by simp [c]))).1 hmap
  exact preservesLimitsOfShape_of_discrete _

end AlgebraicGeometry.Scheme
