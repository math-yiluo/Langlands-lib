import Langlands.Representation.Exponents.LeviJacquetContragredientDynamic
import Langlands.Representation.Aubert.General.DynamicOppositeHaarReciprocity

/-! # Jacquet modules of contragredients for dynamic parabolics, with Haar reciprocity

Renard 2026, VI.9.6 Theorem (VI.9.6.2) (printed p.201, PDF p.207), for represented
parabolics whose point images are `N(χ)`, `M(χ)` and `N(χ⁻¹)`. The Haar reciprocity premise
of `nonempty_leviJacquetContragredient_iso_of_dynamic` is discharged by
`dynamicOppositeHaarReciprocity_of_leviAdjoint`.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G P Pbar M N Nbar : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance dynamicLeviJacquetContragredientReciprocityPointTopology :
    TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]

/-- Renard VI.9.6 Theorem (VI.9.6.2) for represented parabolics realized by a cocharacter
`χ`, from the VI.9.1 uniform stabilization statement and the vanishing of the sum of
opposite adjoint determinants on dynamic Levis. -/
theorem nonempty_leviJacquetContragredient_iso_of_dynamic_of_leviAdjoint
    (hstab : RationalPointFamily.UniformCompressionStabilizationStatement.{u, v})
    (h2 : Dynamic.LeviAdjointDeterminantReciprocityStatement.{u})
    (hG : IsConnectedReductive G)
    (p : P ⟶ G) (m : M ⟶ P) (n : N ⟶ P)
    (hp : IsParabolicSubgroup p) (hm : IsRationalLeviSubgroup m)
    (hn : LeviSubgroup.IsGeometricUnipotentRadical n)
    (hmul : IsIso (subgroupMultiplication m n))
    (pbar : Pbar ⟶ G) (mbar : M ⟶ Pbar) (nbar : Nbar ⟶ Pbar)
    (hpbar : IsParabolicSubgroup pbar) (hmbar : IsRationalLeviSubgroup mbar)
    (hnbar : LeviSubgroup.IsGeometricUnipotentRadical nbar)
    (hmulbar : IsIso (subgroupMultiplication mbar nbar))
    (hP : mbar ≫ pbar = m ≫ p)
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (hN : pointImage (n ≫ p) = (Dynamic.unipotent χ).carrier (Over.mk (𝟙 _)))
    (hM : pointImage (m ≫ p) = (Dynamic.centralizer χ).carrier (Over.mk (𝟙 _)))
    (hNbar : pointImage (nbar ≫ pbar) =
      (Dynamic.unipotent (Dynamic.inverseCocharacter χ)).carrier (Over.mk (𝟙 _))) :
    letI := leviPointTopology m hm
    haveI : NonarchimedeanGroup (rationalPoints M) :=
      leviPoints_nonarchimedeanGroup p m hp hm
    Nonempty
      (SmoothRep.contragredientFunctor.{0, u, v} ⋙
          leviJacquetFunctor.{u, v} pbar mbar nbar hpbar hnbar hmbar hmulbar ≅
        (leviJacquetFunctor.{u, v} p m n hp hn hm hmul).op ⋙
          SmoothRep.contragredientFunctor.{0, u, v}) :=
  nonempty_leviJacquetContragredient_iso_of_dynamic hstab hG p m n hp hm hn hmul
    pbar mbar nbar hpbar hmbar hnbar hmulbar hP χ hN hM hNbar
    fun hU hO hMU hMO x =>
      RationalPointFamily.dynamicOppositeHaarReciprocity_of_leviAdjoint h2 hG χ _ _ _
        hNbar hM hN hU hO hMU hMO x

/-- The same as `nonempty_leviJacquetContragredient_iso_of_dynamic_of_leviAdjoint`, with
the adjoint determinant input replaced by the relative root reflection and central split
torus character statements. -/
theorem nonempty_leviJacquetContragredient_iso_of_dynamic_of_reflection_centralSplitTorus
    (hstab : RationalPointFamily.UniformCompressionStabilizationStatement.{u, v})
    (hRefl : RelativeRootReflectionExistenceStatement.{u})
    (hCST : CentralSplitTorusCharacterStatement.{u})
    (hG : IsConnectedReductive G)
    (p : P ⟶ G) (m : M ⟶ P) (n : N ⟶ P)
    (hp : IsParabolicSubgroup p) (hm : IsRationalLeviSubgroup m)
    (hn : LeviSubgroup.IsGeometricUnipotentRadical n)
    (hmul : IsIso (subgroupMultiplication m n))
    (pbar : Pbar ⟶ G) (mbar : M ⟶ Pbar) (nbar : Nbar ⟶ Pbar)
    (hpbar : IsParabolicSubgroup pbar) (hmbar : IsRationalLeviSubgroup mbar)
    (hnbar : LeviSubgroup.IsGeometricUnipotentRadical nbar)
    (hmulbar : IsIso (subgroupMultiplication mbar nbar))
    (hP : mbar ≫ pbar = m ≫ p)
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (hN : pointImage (n ≫ p) = (Dynamic.unipotent χ).carrier (Over.mk (𝟙 _)))
    (hM : pointImage (m ≫ p) = (Dynamic.centralizer χ).carrier (Over.mk (𝟙 _)))
    (hNbar : pointImage (nbar ≫ pbar) =
      (Dynamic.unipotent (Dynamic.inverseCocharacter χ)).carrier (Over.mk (𝟙 _))) :
    letI := leviPointTopology m hm
    haveI : NonarchimedeanGroup (rationalPoints M) :=
      leviPoints_nonarchimedeanGroup p m hp hm
    Nonempty
      (SmoothRep.contragredientFunctor.{0, u, v} ⋙
          leviJacquetFunctor.{u, v} pbar mbar nbar hpbar hnbar hmbar hmulbar ≅
        (leviJacquetFunctor.{u, v} p m n hp hn hm hmul).op ⋙
          SmoothRep.contragredientFunctor.{0, u, v}) :=
  nonempty_leviJacquetContragredient_iso_of_dynamic hstab hG p m n hp hm hn hmul
    pbar mbar nbar hpbar hmbar hnbar hmulbar hP χ hN hM hNbar
    fun hU hO hMU hMO x =>
      RationalPointFamily.dynamicOppositeHaarReciprocity_of_reflection_centralSplitTorus
        hRefl hCST hG χ _ _ _ hNbar hM hN hU hO hMU hMO x

end Langlands.Aubert.General.RepresentedParabolic
