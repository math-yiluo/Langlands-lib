/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
import WeilConjectures.AlgebraicGeometry.ContinuousIntegralScalarExact
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteCondensedRing
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteConstructibleEncoding
import all WeilConjectures.AlgebraicGeometry.FiniteDiscreteRestrictionEncoding
import WeilConjectures.AlgebraicGeometry.FiniteTypeAlgClHeartFiniteImage
import WeilConjectures.AlgebraicGeometry.FiniteTypeIntegralHeartBound
import WeilConjectures.AlgebraicGeometry.FiniteTypeRationalHeartIntegralImage
import WeilConjectures.AlgebraicGeometry.InternalModuleAbEquivalence
import WeilConjectures.AlgebraicGeometry.UnboundedDirectImageBoundedBelow
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage

/-! # Finiteness of direct images of constructible sheaves in degree zero -/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime]
  {k : Type u} [Field k] [Fact (ringChar k ≠ ℓ)]
  {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (f : X ⟶ Y)

include ℓ k

private theorem torsion_single_bound
    (T : Type) [CommRing T] [TopologicalSpace T] [IsTopologicalRing T]
    [DiscreteTopology T] [Finite T] (n : ℕ) (hn : (ℓ : T) ^ n = 0)
    (F : Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T) X.left))
    (hF : IsConstructibleModuleObject
      (condensedRingObj (Profinite.continuousMapRingObj T) X.left) F) :
    ∃ b : ℤ, ((R((f.left)_*⟦Profinite.continuousMapRingObj T⟧)).obj
      ((DerivedCategory.singleFunctor _ 0).obj F)).IsLE b := by
  obtain ⟨eR, heR⟩ := Profinite.finiteDiscreteCondensedRing_constant.{u} T
  have : IsMonHom eR.hom := heR
  obtain ⟨G, hG, hforget⟩ := internalModuleAb_equivalence (ULift.{u + 1} T)
  have : G.IsEquivalence := hG
  let ES := finiteDiscreteCoefficientEquivalence T eR G hforget X.left
  let ET := finiteDiscreteCoefficientEquivalence T eR G hforget Y.left
  obtain ⟨L, hL, ⟨eL⟩⟩ := exists_isConstructibleSheaf_iso_comparisonUpperStar_obj
    (ULift.{u + 1} T) (finiteDiscreteCoefficient_constructible T eR G hforget X.left F hF)
  have : Scheme.IsConstructibleSheaf L := hL
  let A := ModuleCat.{u + 1} (ULift.{u + 1} T)
  let K := (DerivedCategory.singleFunctor _ 0).obj L
  have hell : IsUnit (ℓ : k) := isUnit_iff_ne_zero.mpr
    (CharP.cast_ne_zero_of_ne_of_prime k (p := ringChar k) (Fact.out : ℓ.Prime)
      (Fact.out : ringChar k ≠ ℓ))
  have : HasInvertibleExponent (ULift.{u + 1} T) (Spec (.of k)) := by
    refine ⟨ℓ ^ n, pow_pos (Fact.out : ℓ.Prime).pos _, ?_, ?_⟩
    · apply (ULift.ringEquiv : ULift.{u + 1} T ≃+* T).injective
      simpa only [map_pow, map_natCast, map_zero, Nat.cast_pow] using hn
    · simpa only [← Nat.cast_pow, map_natCast] using
        (hell.pow n).map (Scheme.ΓSpecIso (.of k)).inv.hom
  have hK := Etale.DerivedCategory.boundedConstructible_singleFunctor_obj L (0 : ℤ)
  have hb := Etale.boundedConstructible_rightDerivedLowerStar_of_locallyOfFiniteType
    (ULift.{u + 1} T) f.left X.hom Y.hom (Over.w f) K hK
  let N := comparisonUpperStar A Y.left
  have hNb := N.bounded_mapDerivedCategory_obj hb.1
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have : QuasiSeparatedSpace X.left := quasiSeparatedSpace_of_quasiSeparated X.hom
  have : QuasiSeparatedSpace Y.left := quasiSeparatedSpace_of_quasiSeparated Y.hom
  have : QuasiCompact f.left := inferInstance
  have : QuasiSeparated f.left := inferInstance
  have hm : IsIso (unboundedDirectImageComparisonMap (ULift.{u + 1} T) f.left K) :=
    unboundedDirectImageComparison_boundedBelow (ULift.{u + 1} T) f.left K 0
  let I := lowerStar (Profinite.continuousMapRingObj T) f.left
  let H := ProEtale.lowerStar A f.left
  let i := encodingPushforwardNatIso T eR G hforget Y.left X.left f.left
  let j : (ES.functor ⋙ I) ⋙ ET.inverse ≅ H :=
    Functor.associator _ _ _ ≪≫ Iso.inverseCompIso (G := ES.symm) i
  let k : H ⋙ ET.functor ≅ ES.functor ⋙ I :=
    (Iso.isoCompInverse (H := ET.symm) j).symm
  let d : R(H) ⋙ D(ET.functor) ≅ D(ES.functor) ⋙ R(I) :=
    (Functor.rightDerivedFunctorCompMapDerivedCategoryIso H ET.functor).symm ≪≫
      Functor.rightDerivedFunctorNatIso k ≪≫
      Functor.rightDerivedFunctorCompIso ES.functor I ≪≫
      Functor.isoWhiskerRight ES.functor.rightDerivedFunctorIsoMapDerivedCategory R(I)
  let eF : ES.functor.obj ((comparisonUpperStar A X.left).obj L) ≅ F :=
    ES.functor.mapIso eL ≪≫ ES.counitIso.app F
  let eS := ES.functor.mapDerivedCategory.mapIso
      (((comparisonUpperStar A X.left).mapDerivedCategorySingleFunctor 0).app L) ≪≫
    (ES.functor.mapDerivedCategorySingleFunctor 0).app _ ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso eF
  let e := ET.functor.mapDerivedCategory.mapIso
      (asIso (unboundedDirectImageComparisonMap (ULift.{u + 1} T) f.left K)) ≪≫
    d.app ((comparisonUpperStar A X.left).mapDerivedCategory.obj K) ≪≫
    R(I).mapIso eS
  exact (DerivedCategory.TStructure.t.bounded.prop_of_iso e
    (ET.functor.bounded_mapDerivedCategory_obj hNb)).2

private theorem rational_single_bound
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    [FiniteDimensional ℚ_[ℓ] E]
    (F : Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) X.left))
    (hF : IsConstructibleModuleObject
      (condensedRingObj (Profinite.continuousMapRingObj E) X.left) F) :
    ∃ b : ℤ, ((R((f.left)_*⟦Profinite.continuousMapRingObj E⟧)).obj
      ((DerivedCategory.singleFunctor _ 0).obj F)).IsLE b := by
  obtain ⟨N, hN, ⟨e⟩⟩ := finiteTypeRationalHeart_integralImage ℓ f E F hF
  obtain ⟨b, hb⟩ := finiteTypeIntegralHeart_boundedAbove ℓ f E N hN
  let S := Mod.extendScalars (coefficientMap (integralScalarMap ℓ E) Y.left)
  have : PreservesFiniteLimits S := integralScalarExtension_exact ℓ E Y.left
  have : (((R((f.left)_*⟦integralCoeff ℓ E⟧)).obj
      ((DerivedCategory.singleFunctor _ 0).obj N))).IsLE b := hb
  have hs := S.isLE_mapDerivedCategory_obj
    ((R((f.left)_*⟦integralCoeff ℓ E⟧)).obj
      ((DerivedCategory.singleFunctor _ 0).obj N)) b
  have hloc := DerivedCategory.TStructure.t.isLE_of_iso
    (S.leftDerivedFunctorIsoMapDerivedCategory.app
      ((R((f.left)_*⟦integralCoeff ℓ E⟧)).obj
        ((DerivedCategory.singleFunctor _ 0).obj N))).symm b
  exact ⟨b, DerivedCategory.TStructure.t.isLE_of_iso e b⟩

private theorem integral_subring_single_bound
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    [FiniteDimensional ℚ_[ℓ] E] (O : Subring E) (hO : O = continuousIntegers ℓ E)
    (F : Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj O) X.left))
    (hF : IsConstructibleModuleObject
      (condensedRingObj (Profinite.continuousMapRingObj O) X.left) F) :
    ∃ b : ℤ, ((R((f.left)_*⟦Profinite.continuousMapRingObj O⟧)).obj
      ((DerivedCategory.singleFunctor _ 0).obj F)).IsLE b := by
  subst O
  exact finiteTypeIntegralHeart_boundedAbove ℓ f E F hF

/-- The direct image of a constructible `ℚ̲̄_ℓ`-sheaf placed in degree zero is bounded above.
The other coefficient rings of Deligne's finiteness theorem are the declarations of the same
name in the namespaces `ContinuousMapRingObj`, `PadicIntegersRingObj`, `UnitBallRingObj` and
`FiniteDiscreteRingObj`.

Source: Deligne, SGA 4½, Th. finitude 1.1; Bhatt--Scholze, Sections 6.7--6.8;
blueprint `proposition-six-operations-dctf--5`, coefficient-reduction argument.
(auxiliary; not a blueprint node)

Proof: finite type over a field makes both schemes noetherian of finite dimension and
makes the morphism qcqs. For finite discrete coefficients killed by a power of ell,
use the classical etale model and the finite cohomological bound in Deligne's theorem.
For integral coefficients, a constructible sheaf is derived complete and its derived
residue-field reduction is bounded constructible on the etale site. Direct image
commutes with derived inverse limits and with this reduction, since the residue field
is a perfect coefficient complex. The uniform finite-coefficient direct-image bound
and the integral completeness criterion imply boundedness above of the integral image.
For rational coefficients choose a constructible integral sheaf model and use the
qcqs comparison of direct image with inversion of the uniformizer. Localization is
exact and preserves the bound. For the algebraic closure descend the constructible
sheaf to a finite extension, apply its bound, and use the direct-image scalar-change
comparison and exact extension to the algebraic closure. For embedded integer rings,
the induced norm identifies their subrings with the closed unit ball by equality.
The general closed-unit-ball case uses its defining norm inequality. The finite
torsion argument also covers the zero coefficient ring and n=0, since its
annihilating exponent is then one. These arguments concern only a single sheaf, not a general
bounded complex; finite truncation induction is performed by the consumer. -/
theorem finiteTypeDirectImage_single_boundedAbove
    (F : Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left))
    (hF : IsConstructibleModuleObject (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left) F) :
    ∃ b : ℤ, ((R((f.left)_*⟦Profinite.padicAlgClRingObj ℓ⟧)).obj
      ((DerivedCategory.singleFunctor _ 0).obj F)).IsLE b := by
  obtain ⟨E, N, hN, ⟨e⟩⟩ := finiteTypeAlgClHeart_finiteImage ℓ f F hF
  let := PadicAlgCl.normedFieldOfAlgebra ℓ E.1
  let : NormedAlgebra ℚ_[ℓ] E.1 :=
    { norm_smul_le c x := by
        change ‖algebraMap E.1 (PadicAlgCl ℓ) (c • x)‖ ≤
          ‖c‖ * ‖algebraMap E.1 (PadicAlgCl ℓ) x‖
        rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, norm_mul,
          PadicAlgCl.norm_extends] }
  obtain ⟨b, hb⟩ := rational_single_bound ℓ f E.1 N hN
  let S := Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl Y.left ℓ E)
  have : ((R((f.left)_*⟦Profinite.continuousMapRingObj E.1⟧)).obj
      ((DerivedCategory.singleFunctor _ 0).obj N)).IsLE b := hb
  have hs := S.isLE_mapDerivedCategory_obj
    ((R((f.left)_*⟦Profinite.continuousMapRingObj E.1⟧)).obj
      ((DerivedCategory.singleFunctor _ 0).obj N)) b
  have hloc := DerivedCategory.TStructure.t.isLE_of_iso
    (S.leftDerivedFunctorIsoMapDerivedCategory.app
      ((R((f.left)_*⟦Profinite.continuousMapRingObj E.1⟧)).obj
        ((DerivedCategory.singleFunctor _ 0).obj N))).symm b
  exact ⟨b, DerivedCategory.TStructure.t.isLE_of_iso e b⟩

namespace ContinuousMapRingObj

/-- The direct image of a constructible `E̲`-sheaf placed in degree zero is bounded above, for a
finite subextension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ` (the case `E̲` of
`ProEtale.CondensedRing.finiteTypeDirectImage_single_boundedAbove`). -/
theorem finiteTypeDirectImage_single_boundedAbove (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (F : Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) X.left))
    (hF : IsConstructibleModuleObject
      (condensedRingObj (Profinite.continuousMapRingObj E) X.left) F) :
    ∃ b : ℤ, ((R((f.left)_*⟦Profinite.continuousMapRingObj E⟧)).obj
      ((DerivedCategory.singleFunctor _ 0).obj F)).IsLE b := by
  let := PadicAlgCl.normedFieldOfAlgebra ℓ E.1
  let : NormedAlgebra ℚ_[ℓ] E.1 :=
    { norm_smul_le c x := by
        change ‖algebraMap E.1 (PadicAlgCl ℓ) (c • x)‖ ≤
          ‖c‖ * ‖algebraMap E.1 (PadicAlgCl ℓ) x‖
        rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, norm_mul,
          PadicAlgCl.norm_extends] }
  exact rational_single_bound ℓ f E.1 F hF

end ContinuousMapRingObj

namespace PadicIntegersRingObj

/-- The direct image of a constructible `𝒪̲_E`-sheaf placed in degree zero is bounded above, for a
finite subextension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ` (the case `𝒪̲_E` of
`ProEtale.CondensedRing.finiteTypeDirectImage_single_boundedAbove`). -/
theorem finiteTypeDirectImage_single_boundedAbove
    (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
    [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]
    (F : Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X.left))
    (hF : IsConstructibleModuleObject
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X.left) F) :
    ∃ b : ℤ, ((R((f.left)_*⟦Profinite.padicIntegersRingObj ℓ E⟧)).obj
      ((DerivedCategory.singleFunctor _ 0).obj F)).IsLE b := by
  let := PadicAlgCl.normedFieldOfAlgebra ℓ E
  let : NormedAlgebra ℚ_[ℓ] E :=
    { norm_smul_le c x := by
        change ‖algebraMap E (PadicAlgCl ℓ) (c • x)‖ ≤
          ‖c‖ * ‖algebraMap E (PadicAlgCl ℓ) x‖
        rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, norm_mul,
          PadicAlgCl.norm_extends] }
  have hO : (PadicAlgCl.integers ℓ E).toSubring = continuousIntegers ℓ E := by
    ext x
    rfl
  exact integral_subring_single_bound ℓ f E _ hO F hF

end PadicIntegersRingObj

namespace UnitBallRingObj

/-- The direct image of a constructible `O̲`-sheaf placed in degree zero is bounded above, for the
closed unit ball `O` of a finite normed extension `E` of `ℚ_ℓ` (the case `O̲` of
`ProEtale.CondensedRing.finiteTypeDirectImage_single_boundedAbove`). -/
theorem finiteTypeDirectImage_single_boundedAbove
    {E : Type} [NormedField E] [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]
    (O : Subring E) [hO : Fact (∀ x : E, x ∈ O ↔ ‖x‖ ≤ 1)]
    (F : Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj O) X.left))
    (hF : IsConstructibleModuleObject
      (condensedRingObj (Profinite.continuousMapRingObj O) X.left) F) :
    ∃ b : ℤ, ((R((f.left)_*⟦Profinite.continuousMapRingObj O⟧)).obj
      ((DerivedCategory.singleFunctor _ 0).obj F)).IsLE b := by
  have h : O = continuousIntegers ℓ E := by
    ext x
    rw [hO.out]
    change ‖x‖ ≤ 1 ↔ ‖x‖₊ ≤ 1
    simpa only [NNReal.coe_one, coe_nnnorm] using
      (NNReal.coe_le_coe : (‖x‖₊ : ℝ) ≤ ((1 : NNReal) : ℝ) ↔ ‖x‖₊ ≤ 1)
  exact integral_subring_single_bound ℓ f E O h F hF

end UnitBallRingObj

namespace FiniteDiscreteRingObj

/-- The direct image of a constructible `T̲`-sheaf placed in degree zero is bounded above, for a
finite discrete ring `T` in which `ℓ` is nilpotent (the case `T̲` of
`ProEtale.CondensedRing.finiteTypeDirectImage_single_boundedAbove`). -/
theorem finiteTypeDirectImage_single_boundedAbove
    (T : Type) [CommRing T] [TopologicalSpace T] [IsTopologicalRing T]
    [DiscreteTopology T] [Finite T] [hT : Fact (IsNilpotent (ℓ : T))]
    (F : Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T) X.left))
    (hF : IsConstructibleModuleObject
      (condensedRingObj (Profinite.continuousMapRingObj T) X.left) F) :
    ∃ b : ℤ, ((R((f.left)_*⟦Profinite.continuousMapRingObj T⟧)).obj
      ((DerivedCategory.singleFunctor _ 0).obj F)).IsLE b := by
  obtain ⟨n, hn⟩ := hT.out
  exact torsion_single_bound ℓ f T n hn F hF

end FiniteDiscreteRingObj

end AlgebraicGeometry.ProEtale.CondensedRing
