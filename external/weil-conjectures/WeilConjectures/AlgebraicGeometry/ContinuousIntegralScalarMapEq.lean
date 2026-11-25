/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ContinuousIntegralLocalizationColimitTransport
public import WeilConjectures.AlgebraicGeometry.IntegralConstructibleSequentialHom
import all WeilConjectures.AlgebraicGeometry.IntegralConstructibleSequentialHom

/-!

# Integral morphisms identified after extension of scalars

Let `E` be a finite extension of `ℚ_ℓ` with closed unit ball `𝒪_E`, and `X` a topologically
noetherian scheme. Two morphisms `f g : K ⟶ B` of bounded constructible `𝒪_{E,X}`-complexes
with the same image under the derived extension of scalars
`CondensedRing.integralScalarExtension ℓ E X` to `E_X` agree after multiplication by a power
of `ℓ` (`AlgebraicGeometry.ProEtale.CondensedRing.integral_scalar_map_eq`).

The image of `B` is the colimit of the multiplications by `ℓ` on `B`, and `Hom(K, -)` commutes
with this sequential colimit since `K` is bounded constructible
(`CondensedRing.integralConstructible_sheaf_hom_colimit`): two morphisms with the same image are
equal at a finite stage, where the transition map is `ℓⁿ`.

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonObj Limits

open scoped CategoryTheory.Obj

namespace CategoryTheory

private lemma scalar_unit_cocone_zero
    {A B : Type*} [Category A] [Category B] [Preadditive A] [Preadditive B]
    (ℓ : ℕ) {L : A ⥤ B} {U : B ⥤ A} [U.Additive] (adj : L ⊣ U) (K : A)
    [IsIso (ℓ • 𝟙 (L.obj K))] :
    (AlgebraicGeometry.ProEtale.CondensedRing.scalarLocalizationUnitCocone ℓ adj K).ι.app 0 =
      adj.unit.app K := by
  change adj.unit.app K ≫ U.map (𝟙 (L.obj K)) = adj.unit.app K
  rw [U.map_id]
  exact Category.comp_id _

end CategoryTheory

namespace AlgebraicGeometry.ProEtale

open Scheme

namespace CondensedRing

open Opposite CategoryTheory.Category

attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.mapDerivedCategory

set_option backward.isDefEq.respectTransparency false in
/-- Two morphisms of bounded constructible `𝒪_{E,X}`-complexes with the same image under the
derived extension of scalars to `E_X` agree after multiplication by a power of `ℓ`.

Proof: the image of `B` is the sequential colimit of the multiplications by `ℓ` on `B`, which
`Hom(K, -)` preserves because `K` is bounded constructible; two morphisms with the same image are
equal at a finite stage of the colimit, where the transition map from the first stage is `ℓⁿ`. -/
theorem integral_scalar_map_eq
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E]
    [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]
    (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
    (K B : integralConstructible ℓ E X) (f g : K.obj ⟶ B.obj)
    (hfg : (integralScalarExtension ℓ E X).map f =
      (integralScalarExtension ℓ E X).map g) :
    ∃ n : ℕ, ℓ ^ n • f = ℓ ^ n • g := by
  let A := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (condensedRingObj (integralCoeff ℓ E) X)
  let H := preadditiveCoyoneda.obj (op K.obj)
  let t := integralLocalizationCocone ℓ E X B.obj
  let J := (ULift.orderIso : ULift.{u + 1} ℕ ≃o ℕ).equivalence.functor
  have : HasColimitsOfShape (ULift.{u + 1} ℕ) A := inferInstance
  obtain ⟨m⟩ := exists_integralLocalization_complex_model ℓ E X B.obj B.property.1.1
  have hcol : Nonempty (IsColimit (H.mapCocone (t.whisker J))) := by
    apply localizationCocone_isColimit_of_model ℓ B.obj t m H
    intro C a hC
    have : C.IsStrictlyGE a := hC
    have : HasColimitsOfShape (ULift.{u + 1} ℕ) (CochainComplex A ℤ) := inferInstance
    let : IsFiltered (ULift.{u + 1} ℕ) :=
      IsFiltered.of_equivalence
        (ULift.orderIso : ULift.{u + 1} ℕ ≃o ℕ).equivalence.symm
    let D := integralLocalizationLiftedSequence.{u + 2, u + 1, u + 1} ℓ C
    let π := Functor.whiskerLeft D
      ((ComplexShape.embeddingUpIntGE a).πTruncGENatTrans A)
    have : ∀ i, IsIso (π.app i) := fun i ↦
      (HomologicalComplex.isIso_πTruncGE_iff C _).2 hC
    have : IsIso π := NatIso.isIso_of_isIso_app π
    have : HasColimit (D ⋙ (ComplexShape.embeddingUpIntGE a).truncGEFunctor A) :=
      HasColimitsOfShape.has_colimit _
    let c := condensedContinuityCocone D a
    have hc : IsColimit c :=
      (IsColimit.precomposeHomEquiv (asIso π) _).symm (colimit.isColimit _)
    let ei : AsSmall.{u + 1} ℕ ≌ ULift.{u + 1} ℕ :=
      (AsSmall.equiv : ℕ ≌ AsSmall.{u + 1} ℕ).symm.trans
        (ULift.orderIso : ULift.{u + 1} ℕ ≃o ℕ).equivalence.symm
    let D' := ei.functor ⋙ D
    let c' := c.whisker ei.functor
    have hc' : IsColimit c' := hc.whiskerEquivalence ei
    have hD' : ∃ a : ℤ, ∀ i, (DerivedCategory.Q.obj (D'.obj i)).IsGE a :=
      ⟨a, fun _ ↦ (DerivedCategory.isGE_Q_obj_iff C a).2 inferInstance⟩
    let P := ObjectProperty.isoClosure
      (IsConstructibleModuleObject (condensedRingObj (integralCoeff ℓ E) X))
    have hK : homColimitProperty (D' ⋙ DerivedCategory.Q)
        (DerivedCategory.Q.mapCocone c') K.obj := by
      apply CategoryTheory.homColimit_bounded _ _ P
      · rintro M ⟨N, hN, ⟨e⟩⟩
        apply CategoryTheory.homColimit_iso _ _
          ((DerivedCategory.singleFunctor _ 0).mapIso e)
        exact integralConstructible_sheaf_hom_colimit ℓ E X N hN D' c' ⟨hc'⟩ hD'
      · exact K.property.1
      · exact fun n ↦ ⟨_, K.property.2 n, ⟨Iso.refl _⟩⟩
    obtain ⟨hc0⟩ := (colimit.isColimit _).nonempty_isColimit_iff_isIso_desc.2 (hK 0)
    let e0 : shiftFunctor (DerivedCategory A) (0 : ℤ) ⋙ H ≅ H :=
      Functor.isoWhiskerRight (shiftFunctorZero _ ℤ) H ≪≫ H.leftUnitor
    exact ⟨IsColimit.ofWhiskerEquivalence ei (IsColimit.mapCoconeEquiv e0 hc0)⟩
  obtain ⟨hc⟩ := hcol
  let : IsFiltered (ULift.{u + 1} ℕ) :=
    IsFiltered.of_equivalence
      (ULift.orderIso : ULift.{u + 1} ℕ ≃o ℕ).equivalence.symm
  let adj := Mod.derivedExtendMapDerivedCategoryAdjunction
    (coefficientMap (integralScalarMap ℓ E) X)
  have he : f ≫ adj.unit.app B.obj = g ≫ adj.unit.app B.obj := by
    have h := congrArg (adj.homEquiv K.obj _) hfg
    change adj.unit.app K.obj ≫ _ = adj.unit.app K.obj ≫ _ at h
    exact (adj.unit.naturality f).trans (h.trans (adj.unit.naturality g).symm)
  have : IsIso (ℓ • 𝟙 ((integralScalarExtension ℓ E X).obj B.obj)) :=
    derived_nsmul_isIso ℓ E X _
  change IsIso (ℓ • 𝟙
    ((Mod.extendScalars (coefficientMap (integralScalarMap ℓ E) X)).leftDerivedFunctor.obj
      B.obj)) at this
  have he0 : (H.mapCocone (t.whisker J)).ι.app (ULift.up 0) f =
      (H.mapCocone (t.whisker J)).ι.app (ULift.up 0) g := by
    change f ≫ t.ι.app 0 = g ≫ t.ι.app 0
    have hz : t.ι.app 0 = adj.unit.app B.obj := scalar_unit_cocone_zero ℓ adj B.obj
    simpa only [hz] using he
  obtain ⟨n, α, β, hn⟩ := Concrete.isColimit_exists_of_rep_eq
    (integralLocalizationLiftedSequence.{u + 2, u + 1, u + 1} ℓ B.obj ⋙ H) hc f g he0
  have hα : α = homOfLE (show (ULift.up 0 : ULift.{u + 1} ℕ) ≤ n by exact Nat.zero_le n.down) :=
    Subsingleton.elim _ _
  have hβ : β = α := Subsingleton.elim _ _
  rw [hβ, hα] at hn
  change f ≫ (Mod.smulSequence B.obj ℓ).map (homOfLE (show 0 ≤ n.down by omega)) =
    g ≫ (Mod.smulSequence B.obj ℓ).map (homOfLE (show 0 ≤ n.down by omega)) at hn
  have hmap (k : ℕ) : (Mod.smulSequence B.obj ℓ).map
      (homOfLE (show 0 ≤ k by omega)) = ℓ ^ k • 𝟙 B.obj := by
    simp
  rw [hmap] at hn
  exact ⟨n.down, by simpa only [Preadditive.comp_nsmul, Category.comp_id] using hn⟩

end CondensedRing

end AlgebraicGeometry.ProEtale
