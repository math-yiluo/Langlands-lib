/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientDiagrams
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.DiagonalFlatScalarEndpoint
import WeilConjectures.CategoryTheory.InternalSectionModuleFlat
import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
import WeilConjectures.CategoryTheory.RingObjects.Ab
import WeilConjectures.CategoryTheory.Sites.MonObj
import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import WeilConjectures.SmoothPurity.Supporting.SignedLineTensorEquivalence
import WeilConjectures.CategoryTheory.RingObjects.Condensed.BaseCoefficientCondensedIdentification
import WeilConjectures.CategoryTheory.ModuleObjects.MapModMonoidal
import WeilConjectures.CategoryTheory.Abelian.Flat.PreservesFlat
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Integral.DiagonalIntegralRootLevelScalars
import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientsFiniteFree
import all WeilConjectures.CategoryTheory.ModuleObjects.ProEtaleCoefficients.FiniteFreeScalarCoordinates
import WeilConjectures.CategoryTheory.ModuleObjects.FinitelyPresentedComap
import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsUnit

/-! # The normalized finite integral Tate-line endpoint

Source: diagonal tower coefficient changes, paragraph (1).
(blueprint: lem-diagonal-finite-integral-endpoint).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

attribute [local irreducible] Functor.leftDerivedFunctor
  Mod.derivedExtendMapDerivedCategoryAdjunction

private theorem bottomMap_isIso (l : ℕ) [Fact l.Prime] :
    IsIso (integralMap.{u} l (bottomField l)) := by
  obtain ⟨e, eInt, _, heInt, _, _, _, _, q, z, _, _, hz, _, _⟩ :=
    Profinite.base_coefficient_condensed_identification.{u} l
  have h : integralMap.{u} l (bottomField l) = z.hom.hom := by
    ext S a
    apply ULift.ext
    apply ContinuousMap.ext
    intro t
    exact (congrArg (fun f : ℤ_[l] →+* _ ↦ f (a.down t)) heInt).symm.trans
      (hz S.unop a.down t).symm
  rw [h]
  infer_instance

@[instance_reducible] private def residueInvertible (l : ℕ) (X : Scheme.{u})
    (hX : IsUnit (l : Γ(X, ⊤))) : ∀ x : X, Invertible (l : X.residueField x) := by
  intro x
  let φ := (X.residue x).hom.comp (X.presheaf.germ ⊤ x trivial).hom
  exact (show IsUnit (l : X.residueField x) from by
    simpa only [map_natCast] using hX.map φ).invertible

private theorem integralLine_flat (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
    [∀ x : X, Invertible (l : X.residueField x)]
    (E : PadicAlgCl.FiniteIntermediateField l) : ObjectProperty.flat (spIntegralTwist X l E) := by
  let R := InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
    (Scheme.ProEt.topology X) (condensedRingObj (Profinite.padicIntegersRingObj l E.1) X)
  let L := (InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
    (Scheme.ProEt.topology X)
    (condensedRingObj (Profinite.padicIntegersRingObj l E.1) X)).functor.obj
      (spIntegralTwist X l E)
  have : L.IsFiniteLocallyFreeOfRank 1 := (spTwists_locallyFree X l E).1
  apply (InternalAbelianSheafModule.flat_iff_sectionModule
    (Scheme.ProEt.topology X) _ (spIntegralTwist X l E)).mpr
  obtain ⟨a⟩ := (WeilConjectures.signedLineTensor_equivalence X R L 1).2
  obtain ⟨b⟩ := (WeilConjectures.signedLineTensor_equivalence X R L (-1)).2
  let G := SheafOfModules.siteSheafTensorRight.{u, u + 1, u + 1, u + 1} (A := R)
    (WeilConjectures.coefficientTwistLine X L (-1))
  let H := SheafOfModules.siteSheafTensorRight.{u, u + 1, u + 1, u + 1} (A := R) L
  have b' : G ⋙ H ≅ 𝟭 _ := by
    simpa only [G, H, WeilConjectures.coefficientTwistLine,
      WeilConjectures.coefficientTwistPower, SheafOfModules.scalarTensorPower, neg_neg] using b
  change exactFunctor _ _ H
  exact (exactFunctor_iff _).mpr
    (let e := CategoryTheory.Equivalence.mk H G a.symm b'
     ⟨inferInstanceAs (PreservesFiniteLimits e.functor),
      inferInstanceAs (PreservesFiniteColimits e.functor)⟩)

private theorem zlLine_flat (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
    [∀ x : X, Invertible (l : X.residueField x)] : ObjectProperty.flat (zlLine l X) := by
  let a := integralMap l (bottomField l)
  have : IsIso a := bottomMap_isIso l
  have : IsIso (coefficientMap a X) := (upperStarFromPoint X).map_isIso a
  let F : Modules (Profinite.padicIntegersRingObj.{u} l (bottomField l).1) X ⥤
      Modules (Profinite.continuousMapRingObj.{u} ℤ_[l]) X :=
    Mod.comap (coefficientMap a X)
  have : F.IsEquivalence := (Mod.comapEquivalenceOfIsIso (coefficientMap a X)).isEquivalence_functor
  let : F.PreservesFlat := Functor.preservesFlat_of_isEquivalence F
  exact Functor.PreservesFlat.flat_obj (F := F) (integralLine_flat l X (bottomField l))

private theorem integralMap_point_comp (l : ℕ) [Fact l.Prime]
    (E : PadicAlgCl.FiniteIntermediateField l) (X : Scheme.{u}) :
    coefficientMap (integralMap l (bottomField l)) X ≫
        coefficientMap (finiteCoefficientIntegersPointMap l
          (show (bottomField l).1 ≤ E.1 from bot_le)) X =
      coefficientMap (integralMap l E) X := by
  rw [← coefficientMap_comp]
  congr 1

private theorem integralScalars_preserveLimits (l : ℕ) [Fact l.Prime]
    (E : PadicAlgCl.FiniteIntermediateField l) (X : Scheme.{u}) :
    PreservesLimitsOfShape ℕᵒᵖ
      (Mod.extendScalars (coefficientMap (integralMap l E) X)) := by
  let a₀ := coefficientMap (integralMap l (bottomField l)) X
  let h : (bottomField l).1 ≤ E.1 := bot_le
  let b := coefficientMap (finiteCoefficientIntegersPointMap l h) X
  let a := coefficientMap (integralMap l E) X
  have : IsIso (integralMap.{u} l (bottomField l)) := bottomMap_isIso l
  have : IsIso a₀ := (upperStarFromPoint X).map_isIso _
  have hab : a₀ ≫ b = a := integralMap_point_comp l E X
  obtain ⟨basis⟩ := (cartesianCoefficients_finiteFree.{u} l h).1
  obtain ⟨e₀, _⟩ := (cartesianCoefficients_finiteFree.{u} l h).2.1 basis
  let θ := (Mod.finiteFreeIsoComap a₀ (finiteCoefficientDegree l h)).symm ≪≫
    (Mod.comap a₀).mapIso (e₀ X) ≪≫
    ((Mod.comapComp a₀ b).symm.app _) ≪≫ (Mod.comapCongr hab).app _
  let F : Modules (Profinite.continuousMapRingObj.{u} ℤ_[l]) X ⥤
      Modules (Profinite.padicIntegersRingObj.{u} l E.1) X := Mod.extendScalars a
  let U : Modules (Profinite.padicIntegersRingObj.{u} l E.1) X ⥤
      Modules (Profinite.continuousMapRingObj.{u} ℤ_[l]) X := Mod.comap a
  let R := condensedRingObj (Profinite.continuousMapRingObj.{u} ℤ_[l]) X
  let S := condensedRingObj (Profinite.padicIntegersRingObj.{u} l E.1) X
  let α : F ⋙ U ≅ Functor.const (Discrete (Fin (finiteCoefficientDegree l h))) ⋙ lim :=
    NatIso.ofComponents (Mod.finiteCoordinateIso θ)
      (fun f ↦ Mod.finiteCoordinateIso_naturality θ f)
  have : PreservesLimitsOfShape ℕᵒᵖ (F ⋙ U) :=
    preservesLimitsOfShape_of_natIso α.symm
  have : PreservesLimitsOfShape ℕᵒᵖ (F ⋙ Mod.forget S) :=
    inferInstanceAs (PreservesLimitsOfShape ℕᵒᵖ ((F ⋙ U) ⋙ Mod.forget R))
  exact preservesLimitsOfShape_of_reflects_of_preserves F (Mod.forget S)

private theorem integralOrdinaryComparison (l : ℕ) [Fact l.Prime]
    (E : PadicAlgCl.FiniteIntermediateField l) (X : Scheme.{u}) :
    ∃ j : (Mod.extendScalars (coefficientMap (integralMap l E) X)).obj
        (zlLine l X) ≅ spIntegralTwist X l E,
      Mod.extendUnitHom (coefficientMap (integralMap l E) X) (zlLine l X) ≫
        j.hom.hom = integralLineMap l E X := by
  let a := coefficientMap (integralMap l E) X
  let U : Modules (Profinite.padicIntegersRingObj.{u} l (bottomField l).1) X ⥤
      Modules (Profinite.continuousMapRingObj.{u} ℤ_[l]) X :=
    Mod.comap (coefficientMap (integralMap l (bottomField l)) X)
  let F : Modules (Profinite.continuousMapRingObj.{u} ℤ_[l]) X ⥤
      Modules (Profinite.padicIntegersRingObj.{u} l E.1) X := Mod.extendScalars a
  let T₀ := spIntegralTwistSystem X l (bottomField l)
  let T := spIntegralTwistSystem X l E
  obtain ⟨i, hi⟩ := diagonalIntegral_rootLevelScalars l E X
  have : PreservesLimitsOfShape ℕᵒᵖ F := integralScalars_preserveLimits l E X
  let c := F.mapCone (U.mapCone (limit.cone T₀))
  have hc : IsLimit c := isLimitOfPreserves F
    (isLimitOfPreserves U (limit.isLimit T₀))
  have hc' := (IsLimit.postcomposeHomEquiv i c).symm hc
  let j := hc'.conePointUniqueUpToIso (limit.isLimit T)
  refine ⟨j, ?_⟩
  apply (isLimitOfPreserves (Mod.forget _) (limit.isLimit T)).hom_ext
  intro n
  change (Mod.extendUnitHom a (zlLine l X) ≫ j.hom.hom) ≫
      (limit.π T n).hom = integralLineMap l E X ≫ (limit.π T n).hom
  have hj : j.hom ≫ limit.π T n = F.map (U.map (limit.π T₀ n)) ≫ i.hom.app n :=
    hc'.conePointUniqueUpToIso_hom_comp (limit.isLimit T) n
  rw [Category.assoc, ← Mod.comp_hom', hj, Mod.comp_hom']
  change Mod.extendUnitHom a (zlLine l X) ≫
      (Mod.extendScalarsMap a (U.map (limit.π T₀ n))).hom ≫ (i.hom.app n).hom = _
  rw [← Category.assoc, Mod.extendUnitHom_extendScalarsMap, Category.assoc]
  exact (congrArg ((U.map (limit.π T₀ n)).hom ≫ ·) (hi n.unop)).trans
    ((spIntegralTwistMap_existsUnique X l
      (show (bottomField l).1 ≤ E.1 from bot_le)).exists.choose_spec n.unop).symm

-- Keep the root-limit objects abstract in the derived adjunction calculation.
attribute [local irreducible] spIntegralTwist spIntegralTwistSystem

private def transportEndpoint
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (a : Λ ⟶ Λ') [IsMonHom a] {X : Scheme.{u}} {M : Modules Λ X}
    {N N' : Modules Λ' X} {m : M.X ⟶ N.X} (e : Endpoint a M N m) (q : N ≅ N') :
    Endpoint a M N' (m ≫ q.hom.hom) where
  semilinear := ⟨e.semilinear.hom ≫ (Mod.comap (coefficientMap a X)).map q.hom, by
    change e.semilinear.hom.hom ≫ q.hom.hom = m ≫ q.hom.hom
    rw [e.semilinear.underlying]⟩
  iso := e.iso ≪≫ (DerivedCategory.singleFunctor (Modules Λ' X) 0).mapIso q
  normalization := by
    change (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a X)).homEquiv
        _ _ (e.iso.hom ≫ (DerivedCategory.singleFunctor (Modules Λ' X) 0).map q.hom) =
      (DerivedCategory.singleFunctor (Modules Λ X) 0).map
          (e.semilinear.hom ≫ (Mod.comap (coefficientMap a X)).map q.hom) ≫
        ((Mod.comap (coefficientMap a X)).mapDerivedCategorySingleFunctor 0).inv.app N'
    rw [Adjunction.homEquiv_naturality_right, e.normalization]
    simp only [Functor.map_comp, Category.assoc]
    exact congrArg (_ ≫ ·)
      (((Mod.comap (coefficientMap a X)).mapDerivedCategorySingleFunctor 0).inv.naturality
        q.hom).symm

/-- Finite integral scalar extension identifies the prescribed root-limit lines,
with the adjoint fixed by the actual root transition.

Source: blueprint latest, sec-six-functors-basics/sk-prop-diagonal-tower/
sk-prop-diagonal-tower-coefficients.proof.md, paragraph (1).
(blueprint: lem-diagonal-finite-integral-endpoint).

Proof: Choose an integral basis of O_E over Z_l. Tensoring with this basis
identifies scalar extension with a finite biproduct. It is exact and commutes
with the inverse limit defining the root line. At each positive ell-power
level, the scalar comparison is the balanced-tensor associativity map and its
composite with the scalar unit is the specified coefficient-root transition.
The compatible projections identify their inverse limit with spIntegralTwist.
For the bottom field the continuous Z_l coefficient and O_Q_l are identified
by the inclusion used in zlLine; the same identification on each finite
quotient makes the resulting map precisely integralLineMap. Exact scalar
extension computes its own left derived functor on the single complex.
The derived adjunction unit is the localized ordinary scalar unit, so the
comparison just constructed satisfies Endpoint.normalization. The ordinary
transition is semilinear by its root projections. These give all fields of
Endpoint. The argument also applies to the bottom field itself and to an
empty scheme, where the same universal projection equations hold. -/
theorem diagonalFinite_integralEndpoint
    (l : ℕ) [Fact l.Prime] (E : PadicAlgCl.FiniteIntermediateField l)
    (X : Scheme.{u}) (hX : IsUnit (l : Γ(X, ⊤))) :
    Nonempty (Endpoint (integralMap l E) (zlLine l X) (spIntegralTwist X l E)
      (integralLineMap l E X)) := by
  let := residueInvertible l X hX
  let a := coefficientMap (integralMap l E) X
  let M := zlLine l X
  obtain ⟨j, hj⟩ := integralOrdinaryComparison l E X
  obtain ⟨i, hi, _⟩ := diagonal_flat_scalar_endpoint_iso (integralMap l E) X M
    (zlLine_flat l X)
  let e : Endpoint (integralMap l E) M ((Mod.extendScalars a).obj M)
      (Mod.extendUnitHom a M) :=
    { semilinear := ⟨Mod.extendUnit a M, rfl⟩
      iso := i
      normalization := hi }
  exact ⟨hj ▸ transportEndpoint (integralMap l E) e j⟩

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
