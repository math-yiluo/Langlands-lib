/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedPushpull
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProperOpenComplementSquare
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Open.OpenExtensionConstructibleFiniteTor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteProperBaseChange
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralProperBaseChange
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedCoefficientIsoConstructible
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.CategoryTheory.Monoidal.Conjugate
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteCondensedRing
import WeilConjectures.NumberTheory.Padics.FiniteCoefficientFields
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.Algebra.Field.ULift
import all WeilConjectures.AlgebraicGeometry.NormedCoefficientRealization.NormedCoefficientRealization
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactConstructibleEllAdic
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProperBaseChangeRational

/-! # Boundary vanishing of proper direct image of open extension by zero

All functors act on ordinary unbounded derived categories of internal modules. The
input belongs to the bounded constructible finite-Tor full subcategory. The conclusion
is vanishing of the target object in the ambient derived category on the boundary.

## Implementation details

`IsFiniteSubextensionLocalizingAdmissibleCoefficient` is a specialization of
`IsLocalizingAdmissibleCoefficient` that omits its all-continuous-map algebraic-closure case.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- The finite discrete ell-primary rings, ell-adic integers, finite ell-adic fields,
their integer rings, and the finite-subextension condensed algebraic closure, up to
isomorphism of ring objects. The separate rational and integral ground-field clauses
include Q_ell and Z_ell explicitly. -/
def IsFiniteSubextensionLocalizingAdmissibleCoefficient (ℓ : ℕ) [Fact ℓ.Prime]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] : Prop :=
  (∃ (A : Type) (_ : CommRing A) (_ : TopologicalSpace A)
      (_ : DiscreteTopology A) (_ : IsTopologicalRing A),
    Finite A ∧ (∃ n : ℕ, ∀ a : A, (ℓ ^ n) • a = 0) ∧
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj A))) ∨
  Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℤ_[ℓ])) ∨
  Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℚ_[ℓ])) ∨
  (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
    Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E))) ∨
  (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
    Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj ℓ E))) ∨
  Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ℓ))

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale.CondensedRing

set_option Elab.async false

attribute [local irreducible] upperStarFromPoint upperStar
  DerivedCategory.monoidalClosed CategoryTheory.Mod.monoidalClosed
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  derivedComapUpperStarIso derivedComapLowerStarIso

private def BoundaryVanishing
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {W Ybar Z : Scheme.{u}} (r : W ⟶ Ybar) (c : Z ⟶ Ybar) : Prop :=
  ∀ K : ConstantModelConstructibleFiniteTor Λ W,
    boundedConstructible (condensedRingObj Λ W) K.obj →
    IsZero ((moduleObjectDerivedPullback Λ (pullback.fst r c)).obj K.obj) →
    IsZero ((moduleObjectDerivedPullback Λ c).obj
      ((moduleObjectDerivedPushforward Λ r).obj K.obj))

attribute [local irreducible] BoundaryVanishing

private local instance comap_iso_equivalence {Z : Scheme.{u}}
    {R S : Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}} [MonObj R] [MonObj S]
    [IsCommMonObj R] (φ : R ⟶ S) [IsMonHom φ] [IsIso φ] :
    (Mod.comap φ : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) S ⥤
      Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) R).IsEquivalence :=
  (Mod.comapEquivalenceOfIsIso φ).isEquivalence_functor

private theorem boundaryVanishing_transport
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (e : Mon.mk Λ ≅ Mon.mk Λ')
    {W Ybar Z : Scheme.{u}} (r : W ⟶ Ybar) (c : Z ⟶ Ybar)
    (h : BoundaryVanishing Λ' r c) : BoundaryVanishing Λ r c := by
  unfold BoundaryVanishing at h ⊢
  intro K hK hz
  let φ := e.inv.hom
  let T (X : Scheme.{u}) :=
    (Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (coefficientMap φ X)).mapDerivedCategory
  have (X : Scheme.{u}) : (T X).IsEquivalence := inferInstance
  have (X : Scheme.{u}) : PreservesFiniteLimits
      (Mod.extendScalars (C := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (coefficientMap φ X)) :=
    preservesFiniteLimits_of_natIso (Mod.extendScalarsIsoComapInv _).symm
  let pull {X Y : Scheme.{u}} (f : X ⟶ Y) :
      moduleObjectDerivedPullback Λ f ⋙ T X ≅ T Y ⋙ moduleObjectDerivedPullback Λ' f :=
    Functor.isoWhiskerRight (leftDerivedUpperStarIsoMapDerivedCategory Λ f) (T X) ≪≫
      derivedComapUpperStarIso φ f ≪≫
      Functor.isoWhiskerLeft (T Y) (leftDerivedUpperStarIsoMapDerivedCategory Λ' f).symm
  let K' : ConstantModelConstructibleFiniteTor Λ' W :=
    ⟨(T W).obj K.obj, constantModelCtf_coefficientIso e W K⟩
  have hb : boundedConstructible (condensedRingObj Λ' W) K'.obj :=
    (NormedCoefficientRealization.bounded_comap_iff (coefficientMap φ W) K.obj).mpr hK
  have hz' : IsZero
      ((moduleObjectDerivedPullback Λ' (pullback.fst r c)).obj K'.obj) :=
    ((T (pullback r c)).map_isZero hz).of_iso ((pull (pullback.fst r c)).app K.obj).symm
  have hv := h K' hb hz'
  let push : moduleObjectDerivedPushforward Λ r ⋙ T Ybar ≅
      T W ⋙ moduleObjectDerivedPushforward Λ' r := derivedComapLowerStarIso φ r
  have hout : IsZero ((T Z).obj ((moduleObjectDerivedPullback Λ c).obj
      ((moduleObjectDerivedPushforward Λ r).obj K.obj))) := by
    apply hv.of_iso
    let e₁ := (pull c).app ((moduleObjectDerivedPushforward Λ r).obj K.obj)
    let e₂ := (moduleObjectDerivedPullback Λ' c).mapIso (push.app K.obj)
    exact e₁ ≪≫ e₂
  exact IsZero.of_full_of_faithful_of_isZero (T Z) _ hout

private theorem boundaryVanishing_rational
    (ℓ : ℕ) [Fact ℓ.Prime]
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {W Ybar Z : Over (Spec (.of k))}
    [LocallyOfFiniteType W.hom] [QuasiCompact W.hom] [IsSeparated W.hom]
    [LocallyOfFiniteType Ybar.hom] [QuasiCompact Ybar.hom] [IsSeparated Ybar.hom]
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
    (r : W ⟶ Ybar) [IsProper r.left] (c : Z ⟶ Ybar) [IsClosedImmersion c.left]
    (R : Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}))
    [IsCommMonObj R.X]
    (hR : (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
      R = Mon.mk (Profinite.continuousMapRingObj E)) ∨
        R = Mon.mk (Profinite.padicAlgClRingObj ℓ)) :
    BoundaryVanishing R.X r.left c.left := by
  unfold BoundaryVanishing
  intro K hK hz
  let T : Over (Spec (.of k)) := Over.mk (pullback.fst r.left c.left ≫ W.hom)
  let a : T ⟶ W := Over.homMk (pullback.fst r.left c.left) rfl
  let b : T ⟶ Z := Over.homMk (pullback.snd r.left c.left)
    (by
      change _ = pullback.fst r.left c.left ≫ W.hom
      rw [← Over.w r, ← Over.w c, pullback.condition_assoc])
  have : LocallyOfFiniteType T.hom := by
    dsimp [T]
    infer_instance
  have : QuasiCompact T.hom := by
    dsimp [T]
    infer_instance
  have : IsSeparated T.hom := by
    dsimp [T]
    infer_instance
  have sq : IsPullback a b r c := by
    apply IsPullback.of_map (Over.forget (Spec (.of k)))
      (by ext; exact pullback.condition)
    exact IsPullback.of_hasPullback r.left c.left
  rcases hR with ⟨E, hE⟩ | hQ
  · subst R
    let := isIso_boundedConstructibleBaseChange_of_isProper ℓ E sq
    let β := (ContinuousMapRingObj.boundedConstructibleBaseChange ℓ E
      sq.toCommSq).app ⟨K.obj, hK⟩
    have : IsIso β := inferInstance
    exact ((lowerStar (Profinite.continuousMapRingObj E) b.left).isZero_rightDerivedFunctor_obj
      hz).of_iso ((ObjectProperty.ι _).mapIso (asIso β))
  · subst R
    let := isIso_boundedConstructibleBaseChange_of_isProper_padicAlgCl ℓ sq
    let β := (boundedConstructibleBaseChange ℓ
      sq.toCommSq).app ⟨K.obj, hK⟩
    have : IsIso β := inferInstance
    exact ((lowerStar (Profinite.padicAlgClRingObj ℓ) b.left).isZero_rightDerivedFunctor_obj
      hz).of_iso ((ObjectProperty.ι _).mapIso (asIso β))

private theorem field_model (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    [FiniteDimensional ℚ_[ℓ] E] :
    ∃ F : PadicAlgCl.FiniteIntermediateField ℓ,
      ∃ σ : E ≃ₐ[ℚ_[ℓ]] F, Isometry σ := by
  let i : E →ₐ[ℚ_[ℓ]] PadicAlgCl ℓ := IsAlgClosed.lift
  let F := i.fieldRange
  let σ := i.equivFieldRange
  have : FiniteDimensional ℚ_[ℓ] F := σ.toLinearEquiv.finiteDimensional
  refine ⟨⟨F, inferInstance⟩, σ, ?_⟩
  exact NormedCoefficientRealization.embedding_isometry ℓ
    (fun x ↦ norm_algebraMap' E x) (fun x ↦ norm_algebraMap' F x) σ.toAlgHom

private theorem field_realization (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    [FiniteDimensional ℚ_[ℓ] E] :
    ∃ F : PadicAlgCl.FiniteIntermediateField ℓ,
      Nonempty (Mon.mk (Profinite.continuousMapRingObj.{u} E) ≅
        Mon.mk (Profinite.continuousMapRingObj.{u} F)) := by
  obtain ⟨F, σ, hσ⟩ := field_model ℓ E
  have hσi : Isometry σ.symm := fun x y ↦ by
    simpa only [σ.apply_symm_apply] using (hσ (σ.symm x) (σ.symm y)).symm
  exact ⟨F, ⟨continuousIso σ.toRingEquiv hσ.continuous hσi.continuous⟩⟩

private theorem unitBall_realization (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    [FiniteDimensional ℚ_[ℓ] E]
    (O : Subring E) (hO : ∀ x : E, x ∈ O ↔ ‖x‖ ≤ 1) :
    ∃ F : PadicAlgCl.FiniteIntermediateField ℓ,
      Nonempty (Mon.mk (Profinite.continuousMapRingObj.{u} O) ≅
        Mon.mk (Profinite.padicIntegersRingObj.{u} ℓ F)) := by
  obtain ⟨F, σ, hiso⟩ := field_model ℓ E
  have hmem (x : E) : x ∈ O ↔ σ x ∈ PadicAlgCl.integers ℓ F := by
    rw [hO, PadicAlgCl.mem_integers_iff]
    change ‖x‖ ≤ 1 ↔ ‖σ x‖₊ ≤ 1
    rw [← NNReal.coe_le_coe, NNReal.coe_one, coe_nnnorm]
    rw [(AddMonoidHomClass.isometry_iff_norm σ).mp hiso x]
  let ei := σ.toRingEquiv.restrict O (PadicAlgCl.integers ℓ F) hmem
  have hi : Isometry ei := fun x y ↦ hiso x.val y.val
  have hii : Isometry ei.symm := fun x y ↦ by
    simpa only [ei.apply_symm_apply] using (hi (ei.symm x) (ei.symm y)).symm
  exact ⟨F, ⟨continuousIso ei hi.continuous hii.continuous⟩⟩

private theorem finiteBoundaryCoefficientIso
    (A : Type) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [DiscreteTopology A] [Finite A] :
    Nonempty (Mon.mk (Profinite.continuousMapRingObj.{u} A) ≅
      Mon.mk (finiteProperCoefficientRing (ULift.{u} A)).X) := by
  let : EssentiallySmall.{u + 1} Profinite.{u} := essentiallySmallSelf.{0} _
  obtain ⟨e, he⟩ := Profinite.finiteDiscreteCondensedRing_constant.{u} A
  let er : ULift.{u + 1} (ULift.{u} A) ≃+* ULift.{u + 1} A :=
    (ULift.ringEquiv.trans ULift.ringEquiv).trans ULift.ringEquiv.symm
  let P := (Functor.const Profinite.{u}ᵒᵖ).obj
    (RingCat.of (ULift.{u + 1} (ULift.{u} A)))
  let Q := (Functor.const Profinite.{u}ᵒᵖ).obj (RingCat.of (ULift.{u + 1} A))
  let i : P ≅ Q := NatIso.ofComponents (fun _ ↦ er.toRingCatIso) (by intros; rfl)
  let iAb := (presheafToSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).mapIso
    (Functor.isoWhiskerRight i (forget₂ RingCat.{u + 1} Ab.{u + 1}))
  have : IsMonHom e.hom := he
  have : IsMonHom iAb.hom := by dsimp [iAb, i]; infer_instance
  exact ⟨(Mon.mkIso' e).symm ≪≫ (Mon.mkIso' iAb).symm⟩

/-- The source of an isomorphism onto a zero object is zero. -/
private theorem isZero_source_of_isIso
    {C : Type*} [Category C] {X Y : C} (f : X ⟶ Y) (hf : IsIso f)
    (hY : IsZero Y) : IsZero X :=
  hY.of_iso (@asIso _ _ _ _ f hf)

private theorem boundaryVanishing_finite
    (A : Type u) [CommRing A] [Finite A]
    (ℓ : ℕ) [Fact ℓ.Prime] (hA : ∃ n : ℕ, (ℓ ^ n) • (1 : A) = 0)
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {W Ybar : Over (Spec (.of k))}
    [LocallyOfFiniteType W.hom] [QuasiCompact W.hom] [IsSeparated W.hom]
    [LocallyOfFiniteType Ybar.hom] [QuasiCompact Ybar.hom] [IsSeparated Ybar.hom]
    (r : W ⟶ Ybar) [IsProper r.left] (Z : Scheme.{u}) (c : Z ⟶ Ybar.left) :
    BoundaryVanishing (finiteProperCoefficientRing A).X r.left c := by
  unfold BoundaryVanishing
  intro K _ hz
  let sq : ChosenCartesianSquare (pullback.fst r.left c) (pullback.snd r.left c) r.left c :=
    { toCommSq := ⟨pullback.condition⟩
      isoPullback := Iso.refl _
      hom_fst := Category.id_comp _
      hom_snd := Category.id_comp _ }
  let β := (finiteProperAmbientExchange (finiteProperCoefficientRing A).X
    sq.toCommSq).app K.obj
  have hi : IsIso β := (finiteProperBaseChange A ℓ hA k W Ybar r).2.1
    _ Z c (pullback.snd r.left c) (pullback.fst r.left c) sq K
  have hzpush := (lowerStar (finiteProperCoefficientRing A).X
    (pullback.snd r.left c)).isZero_rightDerivedFunctor_obj hz
  exact isZero_source_of_isIso β hi hzpush

private theorem boundaryVanishing_integral
    (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {W Ybar : Over (Spec (.of k))}
    [LocallyOfFiniteType W.hom] [QuasiCompact W.hom] [IsSeparated W.hom]
    [LocallyOfFiniteType Ybar.hom] [QuasiCompact Ybar.hom] [IsSeparated Ybar.hom]
    (r : W ⟶ Ybar) [IsProper r.left] (Z : Scheme.{u}) (c : Z ⟶ Ybar.left) :
    BoundaryVanishing (DerivedNakayama.integerRing ℓ E) r.left c := by
  unfold BoundaryVanishing
  intro K _ hz
  let : W.left.Over (Spec (.of k)) := ⟨W.hom⟩
  let : Ybar.left.Over (Spec (.of k)) := ⟨Ybar.hom⟩
  let : r.left.IsOver (Spec (.of k)) := ⟨r.w⟩
  have : LocallyOfFiniteType (W.left ↘ Spec (.of k)) := ‹LocallyOfFiniteType W.hom›
  have : QuasiCompact (W.left ↘ Spec (.of k)) := ‹QuasiCompact W.hom›
  have : IsSeparated (W.left ↘ Spec (.of k)) := ‹IsSeparated W.hom›
  have : LocallyOfFiniteType (Ybar.left ↘ Spec (.of k)) := ‹LocallyOfFiniteType Ybar.hom›
  have : QuasiCompact (Ybar.left ↘ Spec (.of k)) := ‹QuasiCompact Ybar.hom›
  have : IsSeparated (Ybar.left ↘ Spec (.of k)) := ‹IsSeparated Ybar.hom›
  let sq : ChosenCartesianSquare (pullback.fst r.left c) (pullback.snd r.left c) r.left c :=
    { toCommSq := ⟨pullback.condition⟩
      isoPullback := Iso.refl _
      hom_fst := Category.id_comp _
      hom_snd := Category.id_comp _ }
  have hi := (integralProperDirectImageAndFormulas ℓ E k r.left).2.2.1
    c (pullback.snd r.left c) (pullback.fst r.left c) sq K.obj K.property.1
  let β := (condensedAmbientExchange (DerivedNakayama.integerRing ℓ E) sq).app K.obj
  exact ((lowerStar (DerivedNakayama.integerRing ℓ E)
    (pullback.snd r.left c)).isZero_rightDerivedFunctor_obj hz).of_iso (asIso β)

/-- Proper direct image of extension by zero from the inverse image of an open has zero
restriction to the reduced closed complement. -/
theorem proper_open_boundary_zero
    (ℓ : ℕ) [Fact ℓ.Prime]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hΛ : IsFiniteSubextensionLocalizingAdmissibleCoefficient ℓ Λ)
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (W Ybar Y Z : Over (Spec (.of k)))
    [LocallyOfFiniteType W.hom] [QuasiCompact W.hom] [IsSeparated W.hom]
    [LocallyOfFiniteType Ybar.hom] [QuasiCompact Ybar.hom] [IsSeparated Ybar.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
    (r : W ⟶ Ybar) [IsProper r.left]
    (i : Y ⟶ Ybar) [IsOpenImmersion i.left] [QuasiCompact i.left]
    (c : Z ⟶ Ybar) [IsClosedImmersion c.left] [IsReduced Z.left]
    (hc : Set.range c.left.base = (Set.range i.left.base)ᶜ)
    (A : ConstantModelConstructibleFiniteTor Λ (pullback r.left i.left)) :
    IsZero ((moduleObjectDerivedPullback Λ c.left).obj
      ((moduleObjectDerivedPushforward Λ r.left).obj
        ((openImmersionLowerShriek Λ (pullback.fst r.left i.left)).mapDerivedCategory.obj
          A.obj))) := by
  have hv : BoundaryVanishing Λ r.left c.left := by
    rcases hΛ with h | h | h | h | h | h
    · obtain ⟨B, _, _, _, _, hfin, ⟨n, hn⟩, ⟨e⟩⟩ := h
      let : Finite B := hfin
      have hB : ∃ n : ℕ, (ℓ ^ n) • (1 : ULift.{u} B) = 0 := by
        refine ⟨n, ?_⟩
        exact ULift.ext (hn 1)
      obtain ⟨eB⟩ := finiteBoundaryCoefficientIso.{u} B
      exact boundaryVanishing_transport (e ≪≫ eB) r.left c.left
        (boundaryVanishing_finite (ULift.{u} B) ℓ hB k r Z.left c.left)
    · obtain ⟨e⟩ := h
      obtain ⟨F, ⟨eF⟩⟩ := unitBall_realization.{u} ℓ ℚ_[ℓ]
        (PadicInt.subring ℓ) (fun _ ↦ Iff.rfl)
      exact boundaryVanishing_transport (e ≪≫ eF ≪≫ integerIso ℓ F) r.left c.left
        (boundaryVanishing_integral ℓ (ULift.{u} F.val) k r Z.left c.left)
    · obtain ⟨e⟩ := h
      obtain ⟨F, ⟨eF⟩⟩ := field_realization.{u} ℓ ℚ_[ℓ]
      exact boundaryVanishing_transport (e ≪≫ eF) r.left c.left
        (boundaryVanishing_rational ℓ k r c _ (Or.inl ⟨F, rfl⟩))
    · obtain ⟨F, ⟨e⟩⟩ := h
      exact boundaryVanishing_transport e r.left c.left
        (boundaryVanishing_rational ℓ k r c _ (Or.inl ⟨F, rfl⟩))
    · obtain ⟨F, ⟨e⟩⟩ := h
      exact boundaryVanishing_transport (e ≪≫ integerIso ℓ F) r.left c.left
        (boundaryVanishing_integral ℓ (ULift.{u} F.val) k r Z.left c.left)
    · obtain ⟨e⟩ := h
      exact boundaryVanishing_transport e r.left c.left
        (boundaryVanishing_rational ℓ k r c _ (Or.inr rfl))
  obtain ⟨hU, _, _, _, _, _, _, _, hz⟩ := proper_open_complement_square ℓ r i c hc
  let U : Over (Spec (.of k)) := Over.mk (pullback.fst r.left i.left ≫ W.hom)
  let j : U ⟶ W := Over.homMk (pullback.fst r.left i.left) rfl
  have : LocallyOfFiniteType U.hom := hU.2.1
  have : QuasiCompact U.hom := hU.2.2
  have : IsSeparated U.hom := hU.1
  obtain ⟨m, n, hcoh⟩ :=
    (DerivedCategory.exists_homologyConcentratedIn_iff_bounded A.obj).mpr A.property.1.1
  obtain ⟨a, b, htor⟩ := A.property.2
  have : IsOpenImmersion j.left := inferInstanceAs
    (IsOpenImmersion (pullback.fst r.left i.left))
  have he := openExtension_constructible_finiteTor ℓ k Λ j A m n a b hcoh htor
  let K : ConstantModelConstructibleFiniteTor Λ W.left := ⟨_, he.1⟩
  unfold BoundaryVanishing at hv
  exact hv K he.2.2.2 (hz (Mon.mk Λ) A.obj)

end AlgebraicGeometry.ProEtale.CondensedRing
