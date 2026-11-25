/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.AlgebraicGeometry.AdicCompletion.DerivedCompletionSupplement
public import WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedPushpull
public import WeilConjectures.SixFunctors.ProEtale.Comparison
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.SixFunctors.ProEtale.IntegralReductionPullbackNormalization
import WeilConjectures.SixFunctors.ProEtale.IntegralDirectImageReductionTower
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.CategoryTheory.Functor.ReflectsIso.Balanced

/-! # Underlying abelian comparison for reduction and ordinary direct image -/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

private theorem inverseMate_eq_of_unit
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {L : C ⥤ D} {R : D ⥤ C} {L' : C' ⥤ D'} {R' : D' ⥤ C'}
    (adj : L ⊣ R) (adj' : L' ⊣ R') {G : C ⥤ C'} {H : D ⥤ D'}
    (r : R ⋙ G ⟶ H ⋙ R') (b : G ⋙ L' ≅ L ⋙ H)
    (hb : ∀ M, G.map (adj.unit.app M) ≫ r.app (L.obj M) =
      adj'.unit.app (G.obj M) ≫ R'.map (b.hom.app M)) :
    ((mateEquiv adj adj').symm (TwoSquare.mk _ _ _ _ r)) = b.hom := by
  ext M
  apply (adj'.homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit]
  exact (unit_mateEquiv_symm adj adj' (TwoSquare.mk _ _ _ _ r) M).symm.trans (hb M)

private theorem reductionPullback_isIso
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {U X : Scheme.{u}} (j : U ⟶ X) (n : ℕ) :
    IsIso (integralReductionPullbackMap l E j n) := by
  obtain ⟨b, hb⟩ := integral_reduction_pullback_normalization l E j n
  have h := inverseMate_eq_of_unit
    (Mod.derivedExtendMapDerivedCategoryAdjunction (AdicCompletion.quotient l E X n))
    (Mod.derivedExtendMapDerivedCategoryAdjunction (AdicCompletion.quotient l E U n))
    (CondensedRing.derivedComapUpperStarIso
      (DerivedNakayama.reductionRing l E (n + 1)) j).inv b hb
  change IsIso (((mateEquiv _ _).symm (TwoSquare.mk _ _ _ _ _)))
  rw [h]
  infer_instance

private theorem reflectsDerivedIso
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [F.Faithful] {K L : DerivedCategory C} (f : K ⟶ L)
    [IsIso (F.mapDerivedCategory.map f)] : IsIso f := by
  rw [DerivedCategory.isIso_iff]
  intro i
  have hF : IsIso ((DerivedCategory.homologyFunctor D i).map
      (F.mapDerivedCategory.map f)) := inferInstance
  have : IsIso ((DerivedCategory.homologyFunctor C i ⋙ F).map f) :=
    (NatIso.isIso_map_iff (F.mapDerivedCategoryHomologyFunctorIso i) f).2 hF
  have : IsIso (F.map ((DerivedCategory.homologyFunctor C i).map f)) := by
    change IsIso ((DerivedCategory.homologyFunctor C i ⋙ F).map f)
    infer_instance
  exact isIso_of_reflects_iso ((DerivedCategory.homologyFunctor C i).map f) F

private theorem finiteProjection_isIso
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {U X : Scheme.{u}} (j : U ⟶ X) (n : ℕ)
    [IsIso (integralReductionPullbackMap l E j n)]
    (K : DerivedCategory (AdicCompletion.Modules l E U)) :
    IsIso (integralFiniteProjection l E j n K) := by
  obtain ⟨s, q, δ, q', δ', hT, hT', hq, hδ⟩ :=
    integral_direct_image_reduction_cone l E j n K
  let φ : Pretriangulated.Triangle.mk s q δ ⟶
      Pretriangulated.Triangle.mk s q' δ' :=
    { hom₁ := 𝟙 _
      hom₂ := 𝟙 _
      hom₃ := (AdicCompletion.restrict l E X n).map (integralFiniteProjection l E j n K)
      comm₁ := by simp
      comm₂ := by simpa using hq
      comm₃ := by simpa using hδ.symm }
  have : IsIso φ.hom₃ :=
    Pretriangulated.isIso₃_of_isIso₁₂ φ hT hT' (IsIso.id _) (IsIso.id _)
  exact reflectsDerivedIso (Mod.comap (AdicCompletion.quotient l E X n))
    (integralFiniteProjection l E j n K)

private theorem flat_abelianGroup (M : Ab.{u + 1}) [Module.Flat ℤ M] :
    ObjectProperty.flat M := by
  rw [ObjectProperty.flat_iff_preservesFiniteLimits,
    Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono]
  intro S hS
  have := hS.epi_g
  refine ⟨hS.exact.map_of_epi_of_preservesCokernel _ hS.epi_g inferInstance, ?_⟩
  apply (AddCommGrpCat.mono_iff_injective _).2
  exact Module.Flat.lTensor_preserves_injective_linearMap S.f.hom.toIntLinearMap
    ((AddCommGrpCat.mono_iff_injective _).1 hS.mono_f)

private instance pointFiniteLimits : PreservesFiniteLimits pointUpperStar.{u} := by
  have : AB5OfSize.{u, u + 1} Ab.{u + 1} :=
    AB5OfSize_shrink.{u, u + 1, u + 1, u + 1} _
  dsimp [pointUpperStar, Functor.sheafPullbackConstruction.sheafPullback]
  infer_instance

private instance fromPointFiniteLimits (X : Scheme.{u}) :
    PreservesFiniteLimits (upperStarFromPoint X) := by
  dsimp [upperStarFromPoint]
  infer_instance

private theorem integerRing_zsmul_mono
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℤ) (hn : n ≠ 0) :
    Mono (n • 𝟙 (DerivedNakayama.integerRing l E)) := by
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  let : CharZero E := charZero_of_injective_algebraMap (algebraMap (Padic l) E).injective
  apply (sheafToPresheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).mono_of_mono_map
  have hmono (S : Profinite.{u}ᵒᵖ) :
      Mono (((sheafToPresheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).map
        (n • 𝟙 (DerivedNakayama.integerRing l E))).app S) := by
    apply (AddCommGrpCat.mono_iff_injective _).2
    intro f g h
    apply ULift.ext
    apply ContinuousMap.ext
    intro x
    have hx : n • f.down x = n • g.down x := congrArg (fun t ↦ t.down x) h
    have : CharZero (Padic.coefficientExtensionIntegers l E) := inferInstance
    exact zsmul_right_injective hn hx
  exact NatTrans.mono_of_mono_app _

private theorem integralRing_flat
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u}) :
    ObjectProperty.flat (AdicCompletion.ring l E X) := by
  let R := AdicCompletion.ring l E X
  have : (upperStarFromPoint X).Additive :=
    Functor.additive_of_preserves_binary_products _
  have hmono (n : ℤ) (hn : n ≠ 0) : Mono (n • 𝟙 R) := by
    have := integerRing_zsmul_mono l E n hn
    have := (upperStarFromPoint X).map_mono (n • 𝟙 (DerivedNakayama.integerRing l E))
    simpa only [CategoryTheory.Functor.map_zsmul, CategoryTheory.Functor.map_id] using this
  have hTF (U : X.ProEtᵒᵖ) : Module.IsTorsionFree ℤ (R.obj.obj U) := by
    apply Module.IsTorsionFree.of_smul_eq_zero
    intro n m h
    by_cases hn : n = 0
    · exact Or.inl hn
    right
    have := hmono n hn
    let ev := sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1} ⋙
      (evaluation X.ProEtᵒᵖ Ab.{u + 1}).obj U
    have hm : Mono (ev.map (n • 𝟙 R)) := ev.map_mono _
    apply ((AddCommGrpCat.mono_iff_injective _).1 hm)
    change n • m = n • (0 : R.obj.obj U)
    simpa using h
  apply ObjectProperty.prop_of_iso _
    (asIso ((sheafificationAdjunction (Scheme.ProEt.topology X) Ab.{u + 1}).counit.app R))
  apply GrothendieckTopology.flat_presheafToSheaf_obj
  intro U
  have := hTF U
  have : Module.Flat ℤ (R.obj.obj U) := inferInstance
  exact flat_abelianGroup (R.obj.obj U)

private theorem integralForget_preservesKInjective
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u}) :
    (Mod.forget (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (AdicCompletion.ring l E X)).PreservesKInjectiveComplexes := by
  let R := AdicCompletion.ring l E X
  have : PreservesFiniteLimits (tensorLeft R) := (integralRing_flat l E X).tensorLeft.1
  let adj := Mod.freeForgetAdjunction (C := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R
  have : (Mod.free R).PreservesMonomorphisms := by
    constructor
    intro M N f hf
    have : Mono ((Mod.forget (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R).map
        ((Mod.free R).map f)) := (tensorLeft R).map_mono f
    exact (Mod.forget (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R).mono_of_mono_map
      this
  have : (Mod.free R).IsLeftAdjoint := adj.isLeftAdjoint
  have : (Mod.free R).Additive := adj.left_adjoint_additive
  have : (Mod.free R).PreservesHomology :=
    Functor.preservesHomology_of_preservesMonos_and_cokernels _
  exact adj.preservesKInjectiveComplexes

private noncomputable def integralForgetDirectImageIso
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} (p : X ⟶ Y) :
    CondensedRing.moduleObjectDerivedPushforward (DerivedNakayama.integerRing l E) p ⋙
        (Mod.forget (AdicCompletion.ring l E Y)).mapDerivedCategory ≅
      (Mod.forget (AdicCompletion.ring l E X)).mapDerivedCategory ⋙
        (ProEtale.lowerStar Ab.{u + 1} p).rightDerivedFunctor := by
  let F := CondensedRing.lowerStar (DerivedNakayama.integerRing l E) p
  let U := Mod.forget (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (AdicCompletion.ring l E X)
  let V := Mod.forget (D := Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
    (AdicCompletion.ring l E Y)
  let G := ProEtale.lowerStar Ab.{u + 1} p
  have : U.PreservesKInjectiveComplexes := integralForget_preservesKInjective l E X
  exact (Functor.rightDerivedFunctorCompMapDerivedCategoryIso F V).symm ≪≫
    Functor.rightDerivedFunctorNatIso
      (eqToIso (CondensedRing.lowerStar_comp_forget (DerivedNakayama.integerRing l E) p)) ≪≫
    Functor.rightDerivedFunctorCompIso U G ≪≫
    Functor.isoWhiskerRight U.rightDerivedFunctorIsoMapDerivedCategory G.rightDerivedFunctor

/-- On bounded input, positive integral reduction commutes with ordinary direct image
on the underlying abelian complexes. -/
theorem integralReduction_underlying_directImage
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} (p : X ⟶ Y) [QuasiCompact p] [QuasiSeparated p]
    (K : DerivedCategory (AdicCompletion.Modules l E X))
    (hK : DerivedCategory.TStructure.t.bounded K) (n : ℕ) :
    Nonempty ((Mod.forget (AdicCompletion.ring l E Y)).mapDerivedCategory.obj
      (AdicCompletion.integralLevel l E Y
        ((CondensedRing.moduleObjectDerivedPushforward
          (DerivedNakayama.integerRing l E) p).obj K) n) ≅
      (ProEtale.lowerStar Ab.{u + 1} p).rightDerivedFunctor.obj
        ((Mod.forget (AdicCompletion.ring l E X)).mapDerivedCategory.obj
          (AdicCompletion.integralLevel l E X K n))) := by
  classical
  have _bounded := hK
  have hχ (i : ℕ) := reductionPullback_isIso l E p i
  have hproj (i : ℕ) : letI := hχ i; IsIso (integralFiniteProjection l E p i K) := by
    let := hχ i
    exact finiteProjection_isIso l E p i K
  obtain ⟨a, _, _⟩ := integral_direct_image_reduction_tower l E p K hχ hproj
  exact ⟨(Mod.forget (AdicCompletion.ring l E Y)).mapDerivedCategory.mapIso (a n).symm ≪≫
    (integralForgetDirectImageIso l E p).app (AdicCompletion.integralLevel l E X K n)⟩

end AlgebraicGeometry.ProEtale
