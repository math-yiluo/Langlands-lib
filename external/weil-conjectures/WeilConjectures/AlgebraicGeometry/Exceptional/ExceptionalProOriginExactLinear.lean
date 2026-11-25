/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Exceptional.ExceptionalSystemInterfaces
import WeilConjectures.AlgebraicGeometry.Exceptional.ExceptionalProScalarActions
import WeilConjectures.CategoryTheory.Exact.ExactDerivedAdjunctionBounds

/-! # Exact and scalar-linear pro-etale operations -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option genCtorIdx false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite SheafOfModules
namespace AlgebraicGeometry

variable {O : Type (u + 1)} [CommRing O] {ell : O}
  {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
  {S : StrictEtaleCompactSupport O ell c}
  (G : StrictEtaleExceptionalAdjoint O ell c S)
  (CX : ExceptionalSystemSiteComparison O ell X S.PX)
  (CY : ExceptionalSystemSiteComparison O ell Y S.PY)
  (CZ : ExceptionalSystemSiteComparison O ell c.Z S.PZ)

variable (P : ExceptionalProCompactSupport O ell c
    CX.proEvaluation CY.proEvaluation CZ.proEvaluation)

/-- The actual pro-etale compact support and site-transported right functor carry
triangulated and coefficient-linear structures.
Source: Zheng Proposition 2.29(2), Construction 5.15 and Lemma 5.22.
(blueprint: lem-sf-exceptional-pro-origin-exact-linear).

Proof: extension by zero is additive and exact, so localization gives its
canonical additive and shift structures and preserves distinguished triangles.
Proper direct image is its universal K-injective right-derived functor and is
triangulated. The site inverse image is exact; the site direct image is a total
right-derived functor. Compose these structures with the recorded triangulated
etale right adjoint. Multiplication by r is the ordinary natural endomorphism
whose component at level n is multiplication by the image of r in the quotient
constant ring sheaf. Its compatibility with transitions is scalar linearity.
Localize that natural transformation on complexes. On representatives each
inverse image, open extension and proper direct image commutes with this scalar;
the universal localization or right-derived property extends the identities to
all derived objects. The etale right adjoint has this property by its recorded
linearity, so the transported right composite has it as well. -/
private def derivedExactIso {A B : Type*} [Category A] [Category B]
    [Abelian A] [Abelian B] [HasDerivedCategory A] [HasDerivedCategory B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (FD : DerivedCategory A ⥤ DerivedCategory B)
    (fac : DerivedCategory.Q ⋙ FD ≅ F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) :
    FD ≅ F.mapDerivedCategory :=
  Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso A (.up ℤ))
    (DerivedCategory.Q ⋙ FD) (DerivedCategory.Q ⋙ F.mapDerivedCategory)
    FD F.mapDerivedCategory (fac ≪≫ F.mapDerivedCategoryFactors.symm)

set_option linter.style.haveILetI false in
set_option linter.unusedVariables false in
theorem exceptionalProOriginExactLinear :
    ∃ (leftAdditive : (exceptionalProSupport P).Additive)
      (rightAdditive : (exceptionalSystemRight G CX CY).Additive)
      (leftShift : (exceptionalProSupport P).CommShift ℤ)
      (rightShift : (exceptionalSystemRight G CX CY).CommShift ℤ)
      (scalarX : ExceptionalProScalarAction X O ell)
      (scalarY : ExceptionalProScalarAction Y O ell),
      (@Functor.IsTriangulated _ _ _ _ _ _
        (exceptionalProSupport P) leftShift _ _ _ _ _ _ _ _) ∧
      (@Functor.IsTriangulated _ _ _ _ _ _
        (exceptionalSystemRight G CX CY) rightShift _ _ _ _ _ _ _ _) ∧
      (∀ r M, (exceptionalProSupport P).map ((scalarX.derived r).app M) =
        (scalarY.derived r).app ((exceptionalProSupport P).obj M)) ∧
      (∀ r N, (exceptionalSystemRight G CX CY).map ((scalarY.derived r).app N) =
        (scalarX.derived r).app ((exceptionalSystemRight G CX CY).obj N)) := by
  letI : P.val.openImage.inverse.Additive := P.val.openImage.systemInverseAdditive
  letI : P.val.properImage.inverse.Additive := P.val.properImage.systemInverseAdditive
  letI : PreservesFiniteLimits P.val.openImage.inverse :=
    P.val.openImage.systemExact.1
  letI : PreservesFiniteColimits P.val.openImage.inverse :=
    P.val.openImage.systemExact.2
  letI : PreservesFiniteLimits P.val.properImage.inverse :=
    P.val.properImage.systemExact.1
  letI : PreservesFiniteColimits P.val.properImage.inverse :=
    P.val.properImage.systemExact.2
  let eo := derivedExactIso P.val.openImage.inverse P.val.openDerived.system.inverse
    P.val.openDerived.system.inverseFactors
  let ep := derivedExactIso P.val.properImage.inverse P.val.properDerived.system.inverse
    P.val.properDerived.system.inverseFactors
  letI : P.val.openDerived.system.inverse.Additive :=
    Functor.additive_of_iso eo.symm
  letI : P.val.properDerived.system.inverse.Additive :=
    Functor.additive_of_iso ep.symm
  letI : P.val.openDerived.system.inverse.CommShift ℤ := CommShift.ofIso eo.symm ℤ
  letI : NatTrans.CommShift eo.symm.hom ℤ := CommShift.ofIso_compatibility eo.symm ℤ
  letI : P.val.properDerived.system.inverse.CommShift ℤ := CommShift.ofIso ep.symm ℤ
  letI : NatTrans.CommShift ep.symm.hom ℤ := CommShift.ofIso_compatibility ep.symm ℤ
  letI : P.val.openDerived.system.inverse.IsTriangulated :=
    Functor.isTriangulated_of_iso eo.symm
  letI : P.val.properDerived.system.inverse.IsTriangulated :=
    Functor.isTriangulated_of_iso ep.symm
  letI : P.val.derivedOpen.CommShift ℤ :=
    P.val.derivedOpenAdjunction.leftAdjointCommShift ℤ
  letI : P.val.derivedOpenAdjunction.CommShift ℤ :=
    P.val.derivedOpenAdjunction.commShift_of_rightAdjoint ℤ
  letI : P.val.derivedOpen.IsTriangulated :=
    P.val.derivedOpenAdjunction.isTriangulated_leftAdjoint
  letI : P.val.derivedOpen.Additive :=
    P.val.derivedOpenAdjunction.left_adjoint_additive
  letI : P.val.properDerived.system.direct.CommShift ℤ :=
    P.val.properDerived.system.adjunction.rightAdjointCommShift ℤ
  letI : P.val.properDerived.system.adjunction.CommShift ℤ :=
    P.val.properDerived.system.adjunction.commShift_of_leftAdjoint ℤ
  letI : P.val.properDerived.system.direct.IsTriangulated :=
    P.val.properDerived.system.adjunction.isTriangulated_rightAdjoint
  letI : P.val.properDerived.system.direct.Additive :=
    P.val.properDerived.system.adjunction.right_adjoint_additive
  let leftShift :
      (P.val.derivedOpen ⋙ P.val.properDerived.system.direct).CommShift ℤ := inferInstance
  let leftAdditive :
      (P.val.derivedOpen ⋙ P.val.properDerived.system.direct).Additive := inferInstance
  let leftTriangulated :
      (P.val.derivedOpen ⋙ P.val.properDerived.system.direct).IsTriangulated := inferInstance
  letI : G.right.Additive := G.val.rightAdditive
  letI : G.right.CommShift ℤ := G.val.shift
  letI : G.right.IsTriangulated := G.property.1
  letI : PreservesFiniteLimits CY.ordinary.inverse := CY.ordinary.systemExact.1
  letI : PreservesFiniteColimits CY.ordinary.inverse := CY.ordinary.systemExact.2
  letI : PreservesFiniteLimits CX.ordinary.inverse := CX.ordinary.systemExact.1
  letI : PreservesFiniteColimits CX.ordinary.inverse := CX.ordinary.systemExact.2
  let ey := derivedExactIso CY.ordinary.inverse CY.image.system.inverse
    CY.image.system.inverseFactors
  let ex := derivedExactIso CX.ordinary.inverse CX.image.system.inverse
    CX.image.system.inverseFactors
  letI : CY.image.system.inverse.Additive := Functor.additive_of_iso ey.symm
  letI : CY.image.system.inverse.CommShift ℤ := CommShift.ofIso ey.symm ℤ
  letI : NatTrans.CommShift ey.symm.hom ℤ := CommShift.ofIso_compatibility ey.symm ℤ
  letI : CY.image.system.inverse.IsTriangulated := Functor.isTriangulated_of_iso ey.symm
  letI : CX.image.system.inverse.Additive := Functor.additive_of_iso ex.symm
  letI : CX.image.system.inverse.CommShift ℤ := CommShift.ofIso ex.symm ℤ
  letI : NatTrans.CommShift ex.symm.hom ℤ := CommShift.ofIso_compatibility ex.symm ℤ
  letI : CX.image.system.inverse.IsTriangulated := Functor.isTriangulated_of_iso ex.symm
  letI : CY.image.system.direct.CommShift ℤ :=
    CY.image.system.adjunction.rightAdjointCommShift ℤ
  letI : CY.image.system.adjunction.CommShift ℤ :=
    CY.image.system.adjunction.commShift_of_leftAdjoint ℤ
  letI : CY.image.system.direct.IsTriangulated :=
    CY.image.system.adjunction.isTriangulated_rightAdjoint
  letI : CY.image.system.direct.Additive :=
    CY.image.system.adjunction.right_adjoint_additive
  let rightFunctor := (CY.image.system.direct ⋙ G.right) ⋙ CX.image.system.inverse
  let rightAdditive : rightFunctor.Additive := inferInstance
  let rightShift : rightFunctor.CommShift ℤ := inferInstance
  letI : (CY.image.system.direct ⋙ G.right).IsTriangulated :=
    { map_distinguished := by
        intro T hT
        exact Pretriangulated.isomorphic_distinguished _
          (G.right.map_distinguished _
            (CY.image.system.direct.map_distinguished T hT)) _
          ((mapTriangleCompIso CY.image.system.direct G.right).app T) }
  let rightTriangulated : rightFunctor.IsTriangulated := by
    change ((CY.image.system.direct ⋙ G.right) ⋙ CX.image.system.inverse).IsTriangulated
    refine { map_distinguished := ?_ }
    intro T hT
    exact Pretriangulated.isomorphic_distinguished _
      (CX.image.system.inverse.map_distinguished _
        ((CY.image.system.direct ⋙ G.right).map_distinguished T hT)) _
      ((mapTriangleCompIso (CY.image.system.direct ⋙ G.right)
        CX.image.system.inverse).app T)
  obtain ⟨scalarX, scalarY, hleft, hright⟩ :=
    exceptionalProScalarActions G CX CY CZ P
  refine ⟨leftAdditive, rightAdditive, leftShift, rightShift, scalarX, scalarY, ?_, ?_, hleft,
    hright⟩
  · exact leftTriangulated
  · exact rightTriangulated

end AlgebraicGeometry
