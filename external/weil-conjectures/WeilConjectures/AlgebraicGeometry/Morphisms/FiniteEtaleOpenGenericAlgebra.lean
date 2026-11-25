/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.RingTheory.Etale.Basic
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Functoriality
import WeilConjectures.Mathlib.AlgebraicGeometry.FunctionField

/-!
# Generic algebra of a finite etale open cover

## References

* Stacks Project, Tags 02GL and 081I
* Stacks Project, and Tag 081I (flat base change of scheme-theoretic images)
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
/-- Sections of a finite etale open cover embed into a finite etale generic algebra. -/
theorem exists_finiteEtale_open_generic_algebra {X : Scheme.{u}} [IsIntegral X]
    (U : X.Opens) (P : U.toScheme.FiniteEtale) (V : X.Opens) [Nonempty V]
    (hV : IsAffineOpen V) :
    letI : Algebra Γ(X, V) Γ(P.obj.left, (P.obj.hom ≫ U.ι) ⁻¹ᵁ V) :=
      ((P.obj.hom ≫ U.ι).app V).hom.toAlgebra
    ∃ (D : Type u) (_ : CommRing D) (_ : Algebra (FractionRing Γ(X, V)) D),
      Module.Finite (FractionRing Γ(X, V)) D ∧
      Algebra.FormallyEtale (FractionRing Γ(X, V)) D ∧
      letI : Algebra Γ(X, V) D :=
        Algebra.compHom D (algebraMap Γ(X, V) (FractionRing Γ(X, V)))
      ∃ e : Γ(P.obj.left, (P.obj.hom ≫ U.ι) ⁻¹ᵁ V) →ₐ[Γ(X, V)] D,
        Function.Injective e := by
  classical
  let : Algebra Γ(X, V) Γ(P.obj.left, (P.obj.hom ≫ U.ι) ⁻¹ᵁ V) :=
    ((P.obj.hom ≫ U.ι).app V).hom.toAlgebra
  let A := Γ(X, V)
  let K := FractionRing A
  let := functionField_isFractionRing_of_isAffineOpen X V hV
  let c : X.functionField ≃ₐ[A] K := IsLocalization.algEquiv (nonZeroDivisors A) X.functionField K
  let k : X.functionField ⟶ CommRingCat.of K := CommRingCat.ofHom c.toRingHom
  have : IsIso k := show IsIso c.toRingEquiv.toCommRingCatIso.hom from inferInstance
  let a : Spec (.of K) ⟶ X := Spec.map k ≫ X.fromSpecFunctionField
  let Q := Limits.pullback U.ι a
  let q : Q ⟶ Spec (.of K) := Limits.pullback.snd U.ι a
  have : Subsingleton Q := q.isOpenEmbedding.injective.subsingleton
  have : IsReduced Q := isReduced_of_isOpenImmersion q
  have : IsFinite q :=
    isFinite_iff_locallyOfFiniteType_of_jacobsonSpace.mpr inferInstance
  let T := Limits.pullback P.obj.hom (Limits.pullback.fst U.ι a)
  let s : T ⟶ P.obj.left := Limits.pullback.fst P.obj.hom (Limits.pullback.fst U.ι a)
  let r : T ⟶ Spec (.of K) :=
    Limits.pullback.snd P.obj.hom (Limits.pullback.fst U.ι a) ≫ q
  have : IsFinite P.obj.hom := P.property
  have : IsFinite r := inferInstance
  have : Etale r := inferInstance
  have : IsAffine T := isAffine_of_isAffineHom r
  let D := Γ(T, ⊤)
  let d : CommRingCat.of K ⟶ D := (ΓSpecIso (.of K)).inv ≫ r.appTop
  let : Algebra K D := d.hom.toAlgebra
  have hfin : Module.Finite K D := by
    exact RingHom.Finite.comp r.finite_appTop
      (RingHom.Finite.of_surjective _
        (ConcreteCategory.bijective_of_isIso (ΓSpecIso (.of K)).inv).2)
  have het : Algebra.FormallyEtale K D := by
    have hr : RingHom.Etale r.appTop.hom :=
      (HasRingHomProperty.iff_of_isAffine (P := @Etale) (f := r)).mp inferInstance
    have hd : RingHom.Etale d.hom := RingHom.Etale.stableUnderComposition _ _
      (RingHom.Etale.of_bijective
        (ConcreteCategory.bijective_of_isIso (ΓSpecIso (.of K)).inv)) hr
    exact (RingHom.etale_algebraMap.mp hd).formallyEtale
  refine ⟨D, inferInstance, inferInstance, hfin, het, ?_⟩
  let : Algebra A D := Algebra.compHom D (algebraMap A K)
  let f := P.obj.hom ≫ U.ι
  have hsquare : IsPullback s r f a := by
    exact (IsPullback.of_hasPullback P.obj.hom (Limits.pullback.fst U.ι a)).flip.paste_horiz
      (IsPullback.of_hasPullback U.ι a).flip |>.flip
  have : QuasiCompact a := by
    constructor
    intro W hW hWc
    exact Set.toFinite _ |>.isCompact
  have : IsDominant a := by
    dsimp [a]
    infer_instance
  have : IsSchemeTheoreticallyDominant a := .of_isDominant a
  have : IsSchemeTheoreticallyDominant s := .of_isPullback hsquare.flip
  have : QuasiCompact s := MorphismProperty.of_isPullback hsquare.flip inferInstance
  have hVη : genericPoint X ∈ V :=
    ((genericPoint_spec X).mem_open_set_iff V.isOpen).mpr (by simpa using ‹Nonempty V›)
  have ha (z : Spec (.of K)) : a z = genericPoint X := by
    change X.fromSpecFunctionField (Spec.map k z) = genericPoint X
    have : Subsingleton (Spec X.functionField) :=
      (inv (Spec.map k)).isOpenEmbedding.injective.subsingleton
    have hz : Spec.map k z = IsLocalRing.closedPoint X.functionField := Subsingleton.elim _ _
    rw [hz]
    exact X.fromSpecStalk_closedPoint
  have hpre : s ⁻¹ᵁ (f ⁻¹ᵁ V) = ⊤ := by
    ext t
    change (s ≫ f) t ∈ V ↔ True
    rw [hsquare.w]
    change a (r t) ∈ V ↔ True
    rw [ha]
    exact iff_true_intro hVη
  let e₀ : Γ(P.obj.left, f ⁻¹ᵁ V) ⟶ D :=
    s.app (f ⁻¹ᵁ V) ≫ T.presheaf.map (eqToHom hpre.symm).op
  have hinj : Function.Injective e₀ := by
    exact (ConcreteCategory.bijective_of_isIso (T.presheaf.map (eqToHom hpre.symm).op)).1.comp
      (s.app_injective _)
  refine ⟨{ e₀.hom with commutes' := ?_ }, hinj⟩
  have hapre : ⊤ ≤ a ⁻¹ᵁ V := by
    intro z hz
    change a z ∈ V
    rw [ha]
    exact hVη
  have hasec : a.appLE V ⊤ hapre =
      CommRingCat.ofHom (algebraMap A K) ≫ (ΓSpecIso (.of K)).inv := by
    dsimp only [a]
    rw [Hom.appLE, Hom.comp_app]
    rw [X.fromSpecStalk_app hVη]
    simp only [Category.assoc]
    rw [(Spec.map k).naturality_assoc]
    simp only [← Functor.map_comp]
    change X.germToFunctionField V ≫ (ΓSpecIso X.functionField).inv ≫
      (Spec.map k).appTop ≫ (Spec (.of K)).presheaf.map (𝟙 _) = _
    rw [CategoryTheory.Functor.map_id, Category.comp_id, ← ΓSpecIso_inv_naturality]
    rw [← Category.assoc]
    congr 1
    ext x
    exact c.commutes x
  have hcomm : f.app V ≫ e₀ = CommRingCat.ofHom (algebraMap A K) ≫ d := by
    change f.app V ≫ s.appLE (f ⁻¹ᵁ V) ⊤ hpre.ge = _
    calc
      _ = (r ≫ a).appLE V ⊤ (by
          intro t ht
          change a (r t) ∈ V
          exact hapre trivial) := by
        rw [← Hom.comp_appLE]
        congr 1
        exact hsquare.w
      _ = a.appLE V ⊤ hapre ≫ r.appTop := by
        rw [Hom.appTop, Hom.app_eq_appLE, Hom.appLE_comp_appLE]
        simp only [Scheme.Hom.preimage_top]
      _ = _ := by rw [hasec, Category.assoc]
  intro x
  exact congr($(hcomm).hom x)

end AlgebraicGeometry.Scheme
