import Langlands.AlgebraicGeometry.Picard.FieldFiniteMumfordMapSurjectiveStatement
import Langlands.AlgebraicGeometry.Picard.FiniteTranslationDifferenceLifting
import Langlands.AlgebraicGeometry.Picard.MumfordMap
import Langlands.AlgebraicGeometry.Picard.FieldMumfordPointComparisonProof
import Langlands.AlgebraicGeometry.Picard.DualSchemeOrigin
import Langlands.AlgebraicGeometry.Picard.PicardZeroPullbackProof
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Proof that a finite Mumford map to the chosen dual over a field is surjective -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

/-- For a finite morphism `f : X ⟶ Y`, a point `e : Spec K ⟶ Y` over a field `K` and a
morphism `b : Spec Ω ⟶ Spec K` from the spectrum of another field, only finitely many
`a : Spec Ω ⟶ X` satisfy `a ≫ f = b ≫ e`. -/
theorem finite_setOf_comp_eq_of_isFinite {K Ω : Type u} [Field K] [Field Ω] {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsFinite f] (e : Spec (CommRingCat.of K) ⟶ Y)
    (b : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of K)) :
    {a : Spec (CommRingCat.of Ω) ⟶ X | a ≫ f = b ≫ e}.Finite := by
  let π : pullback f e ⟶ Spec (CommRingCat.of K) := pullback.snd f e
  have : IsAffine (pullback f e) := isAffine_of_isAffineHom π
  let ιR : CommRingCat.of K ⟶ Γ(pullback f e, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ π.appTop
  let ψ : CommRingCat.of K ⟶ CommRingCat.of Ω :=
    (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ b.appTop ≫
      (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom
  let _ : Algebra K Γ(pullback f e, ⊤) := ιR.hom.toAlgebra
  let _ : Algebra K Ω := ψ.hom.toAlgebra
  have hfin : ιR.hom.Finite :=
    RingHom.Finite.comp (Scheme.Hom.finite_appTop π)
      (RingHom.Finite.of_surjective _
        (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.symm.surjective)
  have : Module.Finite K Γ(pullback f e, ⊤) := hfin
  let Φ : {a : Spec (CommRingCat.of Ω) ⟶ X | a ≫ f = b ≫ e} →
      (Γ(pullback f e, ⊤) →ₐ[K] Ω) := fun a ↦
    { toRingHom := ((pullback.lift a.1 b a.2).appTop ≫
        (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom).hom
      commutes' := fun k ↦ by
        change ((π.appTop ≫ (pullback.lift a.1 b a.2).appTop) ≫
          (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom).hom
            ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom k) = ψ.hom k
        rw [← Scheme.Hom.comp_appTop, pullback.lift_snd]
        rfl }
  have hinj : Function.Injective Φ := by
    rintro ⟨a₁, h₁⟩ ⟨a₂, h₂⟩ h
    have h' : (pullback.lift a₁ b h₁).appTop = (pullback.lift a₂ b h₂).appTop := by
      have := congrArg (fun φ : Γ(pullback f e, ⊤) →ₐ[K] Ω ↦
        CommRingCat.ofHom φ.toRingHom ≫ (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv) h
      simpa [Φ] using this
    have hz := ext_of_isAffine h'
    apply Subtype.ext
    simpa only [pullback.lift_fst] using congrArg (· ≫ pullback.fst f e) hz
  exact Set.finite_coe_iff.mp (Finite.of_injective Φ hinj)

end Langlands.AlgebraicGeometry

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Two maps into the chosen dual which classify the same rigidified class are equal. -/
lemma dualScheme_hom_ext {S : Scheme.{u}} (A : AbelianScheme S) (hA : HasDualScheme A)
    {T : Over S} {h₁ h₂ : T ⟶ dualScheme A hA}
    (e : RigidifiedLineBundle.classifyingMap A.X.hom (unitSection A) (unitSection_comp A)
        (poincareFamily A hA) T h₁ =
      RigidifiedLineBundle.classifyingMap A.X.hom (unitSection A) (unitSection_comp A)
        (poincareFamily A hA) T h₂) : h₁ = h₂ := by
  let q : PicardZeroClasses A T :=
    ⟨_, isPicardZeroClass_pullback picardZeroPullback A h₂
      (RigidifiedLineBundle.classOf A.X.hom (unitSection A) (unitSection_comp A)
        (poincareFamily A hA)) (poincareFamily_universal A hA).1⟩
  exact (dualClassify_unique A hA T q h₁ e).trans (dualClassify_unique A hA T q h₂ rfl).symm

namespace FiniteMumfordSurjective

variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})
  (square : MumfordBundlePicardZeroStatement.{u})
  {K : Type u} [Field K] (A : AbelianScheme (Spec (CommRingCat.of K))) (hA : HasDualScheme A)
  (L : RigidifiedLineBundle (unitSection A)) (M : LineBundle A.X.left)
  (evaluation : tensorObj L.obj.carrier M.obj ≅ structureSheaf A.X.left)
  {Ω : Type u} [Field Ω] (b : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of K))

/-- The `K`-morphism `Spec Ω → A` underlying a rational point of the base change `A_Ω`. -/
def pointOf (x : Over.mk (𝟙 (Spec (CommRingCat.of Ω))) ⟶ ((baseChange b).obj A).X) :
    Over.mk b ⟶ A.X :=
  Over.homMk (x.left ≫ pullback.fst A.X.hom b) (by
    have hx : x.left ≫ pullback.snd A.X.hom b = 𝟙 _ := Over.w x
    change (x.left ≫ pullback.fst A.X.hom b) ≫ A.X.hom = b
    rw [Category.assoc, pullback.condition, ← Category.assoc, hx, Category.id_comp])

lemma pointOf_left (x : Over.mk (𝟙 (Spec (CommRingCat.of Ω))) ⟶ ((baseChange b).obj A).X) :
    (pointOf A b x).left = x.left ≫ pullback.fst A.X.hom b := rfl

/-- Rational points of `A_Ω` are determined by their image in `A`. -/
lemma pointOf_injective : Function.Injective (fun x :
    Over.mk (𝟙 (Spec (CommRingCat.of Ω))) ⟶ ((baseChange b).obj A).X ↦ (pointOf A b x).left) := by
  intro x x' h
  have hx : x.left ≫ pullback.snd A.X.hom b = 𝟙 _ := Over.w x
  have hx' : x'.left ≫ pullback.snd A.X.hom b = 𝟙 _ := Over.w x'
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · exact h
  · exact hx.trans hx'.symm

/-- The translation difference `t_x^*L_Ω ⊗ M_Ω` on the base change `A_Ω`. -/
def difference (x : Over.mk (𝟙 (Spec (CommRingCat.of Ω))) ⟶ ((baseChange b).obj A).X) :
    LineBundle ((baseChange b).obj A).X.left :=
  LineBundle.tensor preservation
    ((LineBundle.pullback (GroupScheme.translation ((baseChange b).obj A).toGrp x).left).obj
      ((LineBundle.pullback (pullback.fst A.X.hom b)).obj
        ((RigidifiedLineBundle.forget (unitSection A)).obj L)))
    ((LineBundle.pullback (pullback.fst A.X.hom b)).obj M)

/-- The underlying bundle of the Mumford family pulled back along the point of `A` under a
rational point `x` of `A_Ω` is the translation difference at `x`. -/
def familyLineBundleIso
    (x : Over.mk (𝟙 (Spec (CommRingCat.of Ω))) ⟶ ((baseChange b).obj A).X) :
    familyLineBundle A (T := Over.mk b)
        ((RigidifiedLineBundle.relativePullback A.X.hom (unitSection A) (unitSection_comp A)
          (pointOf A b x)).obj (mumfordBundle A preservation L M evaluation)) ≅
      difference preservation A L M b x := by
  let σ := pullbackSymmetry b A.X.hom
  let E := (difference preservation A L M b x).obj
  let premise : (Scheme.Modules.pullback σ.inv).obj ((Scheme.Modules.pullback σ.hom).obj E) ≅
      E :=
    (Scheme.Modules.pullbackComp σ.inv σ.hom).app E ≪≫
      (Scheme.Modules.pullbackCongr σ.inv_hom_id).app E ≪≫ (Scheme.Modules.pullbackId _).app E
  let c := FieldMumfordPoint.carrierIso A (pointOf A b x) preservation x rfl L.obj.carrier M.obj
    ((Scheme.Modules.pullback σ.hom).obj E)
    (fieldLineBundleTriviality Ω ((LineBundle.pullback (pointOf A b x).left).obj M)).some
    premise.symm
  exact ObjectProperty.isoMk _ ((Scheme.Modules.pullback σ.inv).mapIso c ≪≫ premise)

include square evaluation in
/-- Every translation difference on `A_Ω` is translation invariant, since it underlies a
pullback of the Picard-zero Mumford family. -/
lemma isTranslationInvariant_difference [IsAlgClosed Ω]
    (x : Over.mk (𝟙 (Spec (CommRingCat.of Ω))) ⟶ ((baseChange b).obj A).X) :
    GroupScheme.IsTranslationInvariant ((baseChange b).obj A).toGrp
      (difference preservation A L M b x) := by
  have hR := picardZeroPullback _ A _ _ (pointOf A b x) _
    (square preservation _ A L M evaluation)
  exact GroupScheme.isTranslationInvariant_of_iso _
    (familyLineBundleIso preservation A L M evaluation b x)
    (isTranslationInvariant_of_isGeometricallyPicardZero Ω _ hR)

variable {L M evaluation} in
/-- If the translation difference at `x` is trivial, the Mumford map sends the point of `A`
under `x` to the origin of the dual. -/
lemma comp_mumfordSchemeMap_of_trivial
    (x : Over.mk (𝟙 (Spec (CommRingCat.of Ω))) ⟶ ((baseChange b).obj A).X)
    (hx : Nonempty (difference preservation A L M b x ≅
      LineBundle.trivial ((baseChange b).obj A).X.left)) :
    (pointOf A b x).left ≫ (mumfordSchemeMap preservation square A L M evaluation hA).left =
      b ≫ (dualOrigin A hA).left := by
  obtain ⟨d⟩ := hx
  let T : Over (Spec (CommRingCat.of K)) := Over.mk b
  let Q : RigidifiedFamily A T := RigidifiedLineBundle.trivial
    ((relativeSection A.X.hom (unitSection A) (unitSection_comp A)).app T)
  obtain ⟨e⟩ := fieldMumfordPointComparison preservation K A L M evaluation Ω b (pointOf A b x)
    x rfl Q ⟨d ≪≫ (LineBundle.pullbackTrivialIso _).symm⟩
  have h : pointOf A b x ≫ mumfordSchemeMap preservation square A L M evaluation hA =
      dualClassify A hA T (trivialPicardZeroClass A T) :=
    dualClassify_unique A hA T _ _
      ((mumfordSchemeMap_points preservation square A L M evaluation hA T _).trans
        (Quotient.sound ⟨e⟩))
  rw [dualClassify_trivial picardZeroPullback A hA T] at h
  exact congrArg CommaMorphism.left h

variable {L M evaluation} in
/-- Only finitely many translation differences on `A_Ω` are trivial when the Mumford map is
finite. -/
lemma finite_setOf_difference_trivial
    [IsFinite (mumfordSchemeMap preservation square A L M evaluation hA).left] :
    {x : Over.mk (𝟙 (Spec (CommRingCat.of Ω))) ⟶ ((baseChange b).obj A).X |
      Nonempty (difference preservation A L M b x ≅
        LineBundle.trivial ((baseChange b).obj A).X.left)}.Finite := by
  refine Set.Finite.of_finite_image ((Langlands.AlgebraicGeometry.finite_setOf_comp_eq_of_isFinite
    (mumfordSchemeMap preservation square A L M evaluation hA).left
    (dualOrigin A hA).left b).subset ?_) ((pointOf_injective A b).injOn)
  rintro _ ⟨x, hx, rfl⟩
  exact comp_mumfordSchemeMap_of_trivial preservation square A hA b x hx

/-- The pulled-back evaluation `L_Ω ⊗ M_Ω ≅ 𝒪` on the base change `A_Ω`. -/
def evaluationOf :
    tensorObj
      ((LineBundle.pullback (pullback.fst A.X.hom b)).obj
        ((RigidifiedLineBundle.forget (unitSection A)).obj L)).obj
      ((LineBundle.pullback (pullback.fst A.X.hom b)).obj M).obj ≅
        structureSheaf ((baseChange b).obj A).X.left :=
  (MumfordPicardZero.pullbackTensorIso preservation (pullback.fst A.X.hom b)
      L.obj.carrier M.obj).symm ≪≫
    (Scheme.Modules.pullback (pullback.fst A.X.hom b)).mapIso evaluation ≪≫
    pullbackUnitIso (pullback.fst A.X.hom b)

variable {L M evaluation} in
/-- Every Picard-zero family over `Spec Ω`, for an algebraically closed field `Ω`, is a
pullback of the Mumford family along a point of `A`, when the Mumford map is finite. -/
lemma exists_relativePullback_mumfordBundle_iso [IsAlgClosed Ω]
    [IsFinite (mumfordSchemeMap preservation square A L M evaluation hA).left]
    (Q : RigidifiedFamily A (Over.mk b)) (hQ : IsPicardZeroFamily A Q) :
    ∃ x : Over.mk (𝟙 (Spec (CommRingCat.of Ω))) ⟶ ((baseChange b).obj A).X,
      Nonempty ((RigidifiedLineBundle.relativePullback A.X.hom (unitSection A)
        (unitSection_comp A) (pointOf A b x)).obj (mumfordBundle A preservation L M evaluation) ≅
          Q) := by
  obtain ⟨x, ⟨e⟩⟩ := translationDifferenceLifting_of_finite preservation Ω ((baseChange b).obj A)
    ((LineBundle.pullback (pullback.fst A.X.hom b)).obj
      ((RigidifiedLineBundle.forget (unitSection A)).obj L))
    ((LineBundle.pullback (pullback.fst A.X.hom b)).obj M)
    (evaluationOf preservation A L M evaluation b)
    (isTranslationInvariant_difference preservation square A L M evaluation b)
    (finite_setOf_difference_trivial preservation square A hA (evaluation := evaluation) b)
    (familyLineBundle A (T := Over.mk b) Q)
    (isTranslationInvariant_of_isGeometricallyPicardZero Ω _ hQ)
  exact ⟨x, fieldMumfordPointComparison preservation K A L M evaluation Ω b (pointOf A b x)
    x rfl Q ⟨e⟩⟩

/-- Every `Ω`-point of the dual, for an algebraically closed field `Ω`, lifts along a finite
Mumford map. -/
lemma exists_comp_mumfordSchemeMap_eq [IsAlgClosed Ω]
    [IsFinite (mumfordSchemeMap preservation square A L M evaluation hA).left]
    (yo : Over.mk b ⟶ dualScheme A hA) :
    ∃ a : Over.mk b ⟶ A.X, a ≫ mumfordSchemeMap preservation square A L M evaluation hA = yo := by
  obtain ⟨x, ⟨e⟩⟩ := exists_relativePullback_mumfordBundle_iso preservation square A hA
    (L := L) (M := M) (evaluation := evaluation) b
    ((RigidifiedLineBundle.relativePullback A.X.hom (unitSection A) (unitSection_comp A)
      yo).obj (poincareFamily A hA))
    (picardZeroPullback _ A _ _ yo _ (poincareFamily_universal A hA).1)
  refine ⟨pointOf A b x, dualScheme_hom_ext A hA ?_⟩
  rw [mumfordSchemeMap_points preservation square A L M evaluation hA _ (pointOf A b x)]
  exact Quotient.sound ⟨e⟩

/-- A finite Mumford map to the chosen dual of an abelian variety over a field is
surjective. -/
theorem surjective_mumfordSchemeMap
    [IsFinite (mumfordSchemeMap preservation square A L M evaluation hA).left] :
    Function.Surjective (mumfordSchemeMap preservation square A L M evaluation hA).left := by
  intro y
  let D := dualScheme A hA
  let κ := D.left.residueField y
  let yb : Spec (CommRingCat.of (AlgebraicClosure κ)) ⟶ D.left :=
    Spec.map (CommRingCat.ofHom (algebraMap κ (AlgebraicClosure κ))) ≫
      D.left.fromSpecResidueField y
  obtain ⟨a, ha⟩ := exists_comp_mumfordSchemeMap_eq preservation square A hA L M evaluation
    (yb ≫ D.hom) (Over.homMk yb rfl)
  refine ⟨a.left (IsLocalRing.closedPoint (AlgebraicClosure κ)), ?_⟩
  have h' := congrArg (fun g ↦ g.left (IsLocalRing.closedPoint (AlgebraicClosure κ))) ha
  simp only [Over.comp_left, Scheme.Hom.comp_apply, Over.homMk_left] at h'
  rw [h']
  change D.left.fromSpecResidueField y
    ((Spec.map (CommRingCat.ofHom (algebraMap κ (AlgebraicClosure κ))))
      (IsLocalRing.closedPoint (AlgebraicClosure κ))) = y
  rw [Subsingleton.elim ((Spec.map (CommRingCat.ofHom (algebraMap κ (AlgebraicClosure κ))))
    (IsLocalRing.closedPoint (AlgebraicClosure κ))) (IsLocalRing.closedPoint κ)]
  exact D.left.fromSpecResidueField_apply y _

end FiniteMumfordSurjective

/-- A finite Mumford map to the chosen dual of an abelian variety over a field is surjective. -/
theorem fieldFiniteMumfordMapSurjective : FieldFiniteMumfordMapSurjectiveStatement.{u} := by
  intro preservation square K _ A hA L M evaluation _
  exact FiniteMumfordSurjective.surjective_mumfordSchemeMap preservation square A hA L M
    evaluation

end Langlands.AbelianScheme
