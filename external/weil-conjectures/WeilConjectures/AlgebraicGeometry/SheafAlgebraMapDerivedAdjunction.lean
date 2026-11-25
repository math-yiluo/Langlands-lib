/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedRHomAlgebraModule
public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
import WeilConjectures.AlgebraicGeometry.SheafAlgebraHomAdjunction
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HasSheafComposeForgetCommRingCat

/-! # Deriving the algebra-valued Hom adjunction and comparing its localization

Source: Stacks Project, Duality for Schemes, Tags 0BV0 and 0BV1;
Modules Tag 0A6F; Derived Categories Tag 09T5
(blueprint: lem-sc-sheaf-algebra-derived-hom-adjunction-map).
-/

@[expose] public section

universe u w wB

open CategoryTheory TopologicalSpace

attribute [local instance] SheafOfModules.isGrothendieckAbelian

namespace AlgebraicGeometry

/-- The localization of exact scalar restriction is left adjoint to the explicit
algebra-valued derived Hom.

Proof: The underived adjunction is `sheafAlgebraHom_adjunction`. Its sectionwise
inverse maps are φ ↦ (m ↦ (b ↦ φ(bm))) and ψ ↦ (m ↦ ψ(m)(1)).
`sheafAlgebraHom_smul` identifies the B action with precomposition by multiplication;
module associativity and commutativity give B-linearity, while distributivity and
O-linearity of φ give additivity and O-linearity. Ring restrictions preserve products
and 1, giving restriction compatibility. Precomposition in M and postcomposition
in F commute with both formulas, giving naturality. The identities are φ(1m) = φ(m)
and ψ(bm)(1) = ψ(m)(b). These checks are the smaller underived theorem's obligation.

`sheafAlgebraRestrictScalars_preservesFiniteLimits` and
`sheafAlgebraRestrictScalars_preservesFiniteColimits` provide exactness of the left
adjoint. `Adjunction.mapDerivedCategoryRightDerivedAdjunction` derives the underived
adjunction, using `Adjunction.derived` and the K-injective derivability structure.
Exact scalar restriction preserves acyclic complexes; the complex adjunction turns
maps from an acyclic complex into Hom(B,I) into maps from its scalar restriction into
I, which are null-homotopic. This is the argument of
`Adjunction.preservesKInjectiveComplexes`. The derivability structure computes the
absolute right derived Hom on K-injective complexes, without boundedness assumptions.

For the localization comparison, put R = `sheafAlgebraHom Y B` and
I = `sheafAlgebraHomResolution Y`. The components of
`toSheafAlgebraHomResolution Y` are quasi-isomorphisms by
`CochainComplex.monoQuasiIso_toKInjectiveResolution_app`. Hence Q maps this natural
transformation to an isomorphism j. The complexes I(K) are K-injective by
`CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj`, so the components of
`R.rightDerivedFunctorUnit` at their homotopy classes are invertible. Whiskering that
unit by I and the homotopy quotient gives the natural isomorphism t. Compose j,
`DerivedCategory.quotientCompQhIso`, the inverse of t, and
`R.mapHomotopyCategoryFactors` to identify Q followed by R.rightDerivedFunctor with
I followed by termwise R and Q_B. Compose with the inverse of
`derivedRHomAlgebraModule_comparison`. Finally
`Localization.fullyFaithfulWhiskeringLeft` and its `preimageIso` descend this
isomorphism through Q. This identifies the right functor in the constructed derived
adjunction with the specified `derivedRHomAlgebraModule`, with its B-action intact.
`Adjunction.ofNatIsoRight` gives the asserted adjunction.

Source: Stacks Project, Duality for Schemes, Tags 0BV0, 0BV1;
Modules Tag 0A6F; Derived Categories Tag 09T5
(blueprint: lem-sc-sheaf-algebra-derived-hom-adjunction-map). -/
theorem sheafAlgebra_mapDerivedCategory_adjunction
    (Y : Scheme.{u}) (B : Y.CommAlgebraSheaf) (hB : B.toModule.IsQuasicoherent)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [HasDerivedCategory.{wB} (SheafOfModules.{u}
      ((sheafCompose (Opens.grothendieckTopology Y)
        (forget₂ CommRingCat RingCat)).obj B.right))] :
    Nonempty ((SheafOfModules.restrictScalars.{u}
      ((sheafCompose (Opens.grothendieckTopology Y)
        (forget₂ CommRingCat RingCat)).map B.hom)).mapDerivedCategory ⊣
          derivedRHomAlgebraModule Y B hB) := by
  let C := SheafOfModules.{u} (moduleRings Y.toRingedSpace)
  let D := SheafOfModules.{u}
    ((sheafCompose (Opens.grothendieckTopology Y)
      (forget₂ CommRingCat RingCat)).obj B.right)
  let R := sheafAlgebraHom Y B
  let I := sheafAlgebraHomResolution Y
  let q := HomotopyCategory.quotient C (ComplexShape.up ℤ)
  let qD := HomotopyCategory.quotient D (ComplexShape.up ℤ)
  let i := toSheafAlgebraHomResolution Y
  have hi (K : CochainComplex C ℤ) : QuasiIso (i.app K) :=
    (CochainComplex.monoQuasiIso_toKInjectiveResolution_app C K).2
  let t := Functor.whiskerLeft (I ⋙ q) R.rightDerivedFunctorUnit
  have ht (K : CochainComplex C ℤ) : IsIso (t.app K) := by
    change IsIso (R.rightDerivedFunctorUnit.app (q.obj (I.obj K)))
    have : (I.obj K).IsKInjective := by
      dsimp [I, sheafAlgebraHomResolution]
      infer_instance
    infer_instance
  have : IsIso t := NatIso.isIso_of_isIso_app t
  let j := Functor.whiskerRight i (DerivedCategory.Q (C := C))
  have hj (K : CochainComplex C ℤ) : IsIso (j.app K) := by
    let := hi K
    change IsIso (DerivedCategory.Q.map (i.app K))
    infer_instance
  have : IsIso j := NatIso.isIso_of_isIso_app j
  let e : DerivedCategory.Q ⋙ R.rightDerivedFunctor ≅
      I ⋙ R.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q :=
    (Functor.leftUnitor DerivedCategory.Q).symm |> fun e₀ ↦
      Functor.isoWhiskerRight (e₀ ≪≫ asIso j) R.rightDerivedFunctor ≪≫
      Functor.associator I DerivedCategory.Q R.rightDerivedFunctor ≪≫
      Functor.isoWhiskerLeft I
        (Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso C).symm
          R.rightDerivedFunctor ≪≫ Functor.associator q DerivedCategory.Qh
          R.rightDerivedFunctor) ≪≫
      (Functor.associator I q (DerivedCategory.Qh ⋙ R.rightDerivedFunctor)).symm ≪≫
      (asIso t).symm ≪≫
      Functor.associator I q (R.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh) ≪≫
      Functor.isoWhiskerLeft I
        ((Functor.associator q (R.mapHomotopyCategory (ComplexShape.up ℤ))
          DerivedCategory.Qh).symm ≪≫
        Functor.isoWhiskerRight (R.mapHomotopyCategoryFactors (ComplexShape.up ℤ))
          DerivedCategory.Qh ≪≫
        Functor.associator (R.mapHomologicalComplex (ComplexShape.up ℤ)) qD
          DerivedCategory.Qh ≪≫
        Functor.isoWhiskerLeft (R.mapHomologicalComplex (ComplexShape.up ℤ))
          (DerivedCategory.quotientCompQhIso D))
  obtain ⟨ec⟩ := derivedRHomAlgebraModule_comparison Y B hB
  let er := (Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Q
    (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) (DerivedCategory D)).preimageIso
      (e ≪≫ ec.symm)
  obtain ⟨adj⟩ := sheafAlgebraHom_adjunction Y B
  exact ⟨adj.mapDerivedCategoryRightDerivedAdjunction.ofNatIsoRight er⟩

end AlgebraicGeometry
