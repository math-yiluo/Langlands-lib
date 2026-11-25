/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.AdicResidueQuotientTensorTower
import all WeilConjectures.AlgebraicGeometry.ConstantCompletionInverseImage
import all WeilConjectures.AlgebraicGeometry.ConstantRealizationDerivedScalarExtension
import WeilConjectures.CategoryTheory.RingedDerivedRestrictionGeneral

/-! # Exact realization of the coefficient ring and its finite quotients

Source: Stacks Project, proetale.tex, lemma-naive-completion (099M), and
Modules on Sites, Tags 03CY and 03EK.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u v
open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.ConstantCompletion
namespace AlgebraicGeometry.Scheme

attribute [local irreducible] completed adicResidueQuotientCoefficientUnit

section Realization

universe w
variable {C : Type w} [SmallCategory C] (T : GrothendieckTopology C)
  {A : Type w} [CommRing A] {B : Sheaf T CommRingCat.{w}}
  (φ : constant T A ⟶ B)

attribute [local instance] GrothendieckTopology.hasSheafify_of_essentiallySmall

private abbrev realize := commutativeSiteConstantModuleFunctor T A ⋙ change φ

private abbrev generator (M : ModuleCat.{w} A) (V : Cᵒᵖ) (a : M) :
    ((realize T φ).obj M).val.obj V :=
  ((SheafOfModules.RingedTensor.tensorAdjunction φ).unit.app
    ((commutativeSiteConstantModuleFunctor T A).obj M)).val.app V
      (ConstantScalarRealization.constantSection T M V a)

private theorem generator_map (M : ModuleCat.{w} A) {V W : Cᵒᵖ}
    (f : V ⟶ W) (a : M) :
    ((realize T φ).obj M).val.map f (generator T φ M V a) =
      generator T φ M W a := by
  let η := (SheafOfModules.RingedTensor.tensorAdjunction φ).unit.app
    ((commutativeSiteConstantModuleFunctor T A).obj M)
  have h := PresheafOfModules.naturality_apply η.val f
    (ConstantScalarRealization.constantSection T M V a)
  change η.val.app W
    (((commutativeSiteConstantModuleFunctor T A).obj M).val.map f
      (ConstantScalarRealization.constantSection T M V a)) = _ at h
  rw [ConstantScalarRealization.constantSection_map] at h
  exact h.symm

private def oneMap : SheafOfModules.unit (siteModuleRings B) ⟶
    (realize T φ).obj (ModuleCat.of A A) :=
  (SheafOfModules.unitHomEquiv _).symm
    ⟨fun V ↦ generator T φ (ModuleCat.of A A) V 1,
      fun f ↦ generator_map T φ (ModuleCat.of A A) f 1⟩

private theorem oneMap_one (V : Cᵒᵖ) :
    (oneMap T φ).val.app V (1 : B.obj.obj V) =
      generator T φ (ModuleCat.of A A) V 1 := by
  change (1 : B.obj.obj V) • generator T φ (ModuleCat.of A A) V 1 = _
  exact one_smul _ _

private theorem oneMap_isIso : IsIso (oneMap T φ) := by
  have := (realizationRingUnit_locallyBijective T A).1
  have := (realizationRingUnit_locallyBijective T A).2
  let P := (siteConstantModulePresheafGeneral (C := C) A).obj (ModuleCat.of A A)
  let K := (commutativeSiteConstantModuleFunctor T A).obj (ModuleCat.of A A)
  let adj := SheafOfModules.RingedTensor.tensorAdjunction φ
  let e (N : Mod B) : ((realize T φ).obj (ModuleCat.of A A) ⟶ N) ≃ N.sections :=
    ((adj.homEquiv K N).trans
      (PresheafOfModules.sheafificationHomEquiv (realizationRingUnit T A))).trans
        (PresheafOfModules.unitHomEquiv _)
  have he (N : Mod B) (f : (realize T φ).obj (ModuleCat.of A A) ⟶ N) :
      e N f = N.unitHomEquiv (oneMap T φ ≫ f) := by
    apply PresheafOfModules.sections_ext
    intro V
    dsimp only [e, Equiv.trans_apply]
    change ((PresheafOfModules.sheafificationHomEquiv (realizationRingUnit T A))
      (adj.homEquiv K N f)).app V (1 : A) =
        f.val.app V ((oneMap T φ).val.app V (1 : B.obj.obj V))
    rw [oneMap_one, Adjunction.homEquiv_unit]
    rfl
  apply isIso_of_coyoneda_map_bijective
  intro N
  have hf : (fun f ↦ oneMap T φ ≫ f) = N.unitHomEquiv.symm ∘ e N := by
    funext f
    exact N.unitHomEquiv.injective (by simp only [Function.comp_apply,
      Equiv.apply_symm_apply, he])
  rw [hf]
  exact N.unitHomEquiv.symm.bijective.comp (e N).bijective

private theorem generator_naturality {M N : ModuleCat.{w} A} (f : M ⟶ N)
    (V : Cᵒᵖ) (a : M) :
    ((realize T φ).map f).val.app V (generator T φ M V a) =
      generator T φ N V (f a) := by
  have h := congrArg (fun k ↦ k.val.app V
    (ConstantScalarRealization.constantSection T M V a))
    ((SheafOfModules.RingedTensor.tensorAdjunction φ).unit_naturality
      ((commutativeSiteConstantModuleFunctor T A).map f))
  change ((realize T φ).map f).val.app V (generator T φ M V a) =
    ((SheafOfModules.RingedTensor.tensorAdjunction φ).unit.app
      ((commutativeSiteConstantModuleFunctor T A).obj N)).val.app V
        (((commutativeSiteConstantModuleFunctor T A).map f).val.app V
          (ConstantScalarRealization.constantSection T M V a)) at h
  rw [ConstantScalarRealization.constantSection_naturality] at h
  exact h

private theorem generator_smul (M : ModuleCat.{w} A) (V : Cᵒᵖ) (a : A) (m : M) :
    generator T φ M V (a • m) =
      φ.hom.app V ((realizationRingUnit T A).app V a) • generator T φ M V m := by
  unfold generator
  rw [ConstantScalarRealization.constantSection_smul, map_smul]
  rfl

private theorem oneMap_scalar (a : A) :
    oneMap T φ ≫ (realize T φ).map (ModuleCat.ofHom (LinearMap.mul A A a)) =
      (ringedKoszulScalar B (algebraSection φ a)).asHom ≫ oneMap T φ := by
  apply (SheafOfModules.unitHomEquiv _).injective
  apply PresheafOfModules.sections_ext
  intro V
  change ((realize T φ).map (ModuleCat.ofHom (LinearMap.mul A A a))).val.app V
      ((oneMap T φ).val.app V (1 : B.obj.obj V)) =
    (oneMap T φ).val.app V
      ((ringedKoszulScalar B (algebraSection φ a)).asHom.val.app V (1 : B.obj.obj V))
  rw [oneMap_one, generator_naturality]
  change generator T φ (ModuleCat.of A A) V (a * 1) = _
  rw [mul_one]
  have hs : (ringedKoszulScalar B (algebraSection φ a)).asHom.val.app V
      (1 : B.obj.obj V) = (algebraSection φ a).val V := by
    change (1 : B.obj.obj V) *
      (show B.obj.obj V from (algebraSection φ a).val V) = _
    exact one_mul _
  rw [hs]
  change generator T φ (ModuleCat.of A A) V a =
    φ.hom.app V ((realizationRingUnit T A).app V a) •
      generator T φ (ModuleCat.of A A) V 1
  simpa only [smul_eq_mul, mul_one] using
    generator_smul T φ (ModuleCat.of A A) V a 1

private theorem realize_hom_ext {M : ModuleCat.{w} A} {N : Mod B}
    {f g : (realize T φ).obj M ⟶ N}
    (h : ∀ (V : Cᵒᵖ) (m : M),
      f.val.app V (generator T φ M V m) = g.val.app V (generator T φ M V m)) : f = g := by
  apply ((SheafOfModules.RingedTensor.tensorAdjunction φ).homEquiv _ _).injective
  apply ConstantScalarRealization.constantSection_ext T
  intro V m
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  change f.val.app V (generator T φ M V m) = g.val.app V (generator T φ M V m)
  exact h V m

private theorem generator_zero (M : ModuleCat.{w} A) (V : Cᵒᵖ) :
    generator T φ M V 0 = 0 := by
  unfold generator ConstantScalarRealization.constantSection
  rw [map_zero, map_zero]

variable (I : Ideal A) (p : B ⟶ constant T (A ⧸ I))
  (hp : φ ≫ p = (constantSheaf T CommRingCat.{w}).map (CommRingCat.ofHom (Ideal.Quotient.mk I)))

include hp in
private theorem projection_scalar (V : Cᵒᵖ) (a : A) :
    p.hom.app V (φ.hom.app V ((realizationRingUnit T A).app V a)) =
      (realizationRingUnit T (A ⧸ I)).app V (Ideal.Quotient.mk I a) := by
  have h := congrArg (fun k ↦ k.hom.app V ((realizationRingUnit T A).app V a)) hp
  exact h.trans (ConstantScalarRealization.realizationRingUnit_naturality
    T (Ideal.Quotient.mk I) V a)

private def quotientSeed :
    (siteConstantModulePresheafGeneral (C := C) A).obj (ModuleCat.of A (A ⧸ I)) ⟶
      (PresheafOfModules.restrictScalars (realizationRingUnit T A)).obj
        ((res φ).obj ((res p).obj (SheafOfModules.unit
          (siteModuleRings (constant T (A ⧸ I)))))).val where
  app V := ModuleCat.ofHom
    (X := ((siteConstantModulePresheafGeneral (C := C) A).obj
      (ModuleCat.of A (A ⧸ I))).obj V)
    (Y := ((PresheafOfModules.restrictScalars (realizationRingUnit T A)).obj
      ((res φ).obj ((res p).obj (SheafOfModules.unit
        (siteModuleRings (constant T (A ⧸ I)))))).val).obj V)
    { toFun := fun x ↦ (realizationRingUnit T (A ⧸ I)).app V x
      map_add' := map_add _
      map_smul' := fun a x ↦ by
        let a' : A := a
        let x' : A ⧸ I := x
        change (realizationRingUnit T (A ⧸ I)).app V (Ideal.Quotient.mk I a' * x') =
          p.hom.app V (φ.hom.app V ((realizationRingUnit T A).app V a')) *
            (show (constant T (A ⧸ I)).obj.obj V from
              (realizationRingUnit T (A ⧸ I)).app V x')
        rw [map_mul, projection_scalar T φ I p hp] }
  naturality {V W} f := by
    ext x
    exact NatTrans.naturality_apply (realizationRingUnit T (A ⧸ I)) f x

private def quotientMap : (realize T φ).obj (ModuleCat.of A (A ⧸ I)) ⟶
    (res p).obj (SheafOfModules.unit (siteModuleRings (constant T (A ⧸ I)))) := by
  have := (realizationRingUnit_locallyBijective T A).1
  have := (realizationRingUnit_locallyBijective T A).2
  exact ((SheafOfModules.RingedTensor.tensorAdjunction φ).homEquiv _ _).symm
    ((PresheafOfModules.sheafificationHomEquiv (realizationRingUnit T A)).symm
      (quotientSeed T φ I p hp))

private theorem quotientMap_generator (V : Cᵒᵖ) (x : A ⧸ I) :
    (quotientMap T φ I p hp).val.app V
      (generator T φ (ModuleCat.of A (A ⧸ I)) V x) =
        (realizationRingUnit T (A ⧸ I)).app V x := by
  have := (realizationRingUnit_locallyBijective T A).1
  have := (realizationRingUnit_locallyBijective T A).2
  have h : (PresheafOfModules.sheafificationHomEquiv (realizationRingUnit T A))
      (((SheafOfModules.RingedTensor.tensorAdjunction φ).homEquiv _ _)
        (quotientMap T φ I p hp)) = quotientSeed T φ I p hp := by
    dsimp only [quotientMap, commutativeSiteConstantModuleFunctor, Functor.comp_obj]
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  exact congrArg (fun k ↦ k.app V x) h

private def quotientOne : SheafOfModules.unit (siteModuleRings B) ⟶
    (realize T φ).obj (ModuleCat.of A (A ⧸ I)) :=
  (SheafOfModules.unitHomEquiv _).symm
    ⟨fun V ↦ generator T φ (ModuleCat.of A (A ⧸ I)) V 1,
      fun f ↦ generator_map T φ (ModuleCat.of A (A ⧸ I)) f 1⟩

private theorem quotientOne_scalar (V : Cᵒᵖ) (a : A) :
    (quotientOne T φ I).val.app V (φ.hom.app V ((realizationRingUnit T A).app V a)) =
      generator T φ (ModuleCat.of A (A ⧸ I)) V (Ideal.Quotient.mk I a) := by
  have h := generator_smul T φ (ModuleCat.of A (A ⧸ I)) V a 1
  change generator T φ (ModuleCat.of A (A ⧸ I)) V (Ideal.Quotient.mk I a * 1) = _ at h
  rw [mul_one] at h
  exact h.symm

private def descendLinear {R M N : Type w} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (f : R →ₗ[R] M) (hf : Function.Surjective f)
    (g : R →ₗ[R] N) (h : LinearMap.ker f ≤ LinearMap.ker g) : M →ₗ[R] N :=
  ((LinearMap.ker f).liftQ g h).comp (f.quotKerEquivOfSurjective hf).symm.toLinearMap

private theorem descendLinear_apply {R M N : Type w} [CommRing R] [AddCommGroup M]
    [Module R M] [AddCommGroup N] [Module R N] (f : R →ₗ[R] M)
    (hf : Function.Surjective f) (g : R →ₗ[R] N) (h : LinearMap.ker f ≤ LinearMap.ker g)
    (r : R) : descendLinear f hf g h (f r) = g r := by
  simp only [descendLinear, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
    LinearMap.quotKerEquivOfSurjective_symm_apply, Submodule.liftQ_apply]

private theorem quotientMap_isIso
    (hsurj : ∀ V : Cᵒᵖ, Function.Surjective (p.hom.app V))
    (hker : ∀ V : Cᵒᵖ, RingHom.ker (p.hom.app V).hom =
      Ideal.span (Set.range (fun a : I ↦
        φ.hom.app V ((realizationRingUnit T A).app V (a : A))))) :
    IsIso (quotientMap T φ I p hp) := by
  let M := (realize T φ).obj (ModuleCat.of A (A ⧸ I))
  let N := (res p).obj (SheafOfModules.unit (siteModuleRings (constant T (A ⧸ I))))
  let t := quotientOne T φ I
  let l (V : Cᵒᵖ) : B.obj.obj V →ₗ[B.obj.obj V] N.val.obj V :=
    { toFun := p.hom.app V
      map_add' := map_add _
      map_smul' := fun b b' ↦ by
        change p.hom.app V (b * b') = p.hom.app V b * p.hom.app V b'
        exact map_mul _ _ _ }
  have hk (V : Cᵒᵖ) : LinearMap.ker (l V) ≤ LinearMap.ker (t.val.app V).hom := by
    intro b hb
    change b ∈ RingHom.ker (p.hom.app V).hom at hb
    rw [hker V] at hb
    change b ∈ Submodule.span (B.obj.obj V)
      (Set.range (fun a : I ↦ φ.hom.app V ((realizationRingUnit T A).app V (a : A)))) at hb
    change t.val.app V b = 0
    induction hb using Submodule.span_induction with
    | mem b hb =>
      obtain ⟨a, rfl⟩ := hb
      rw [quotientOne_scalar, Ideal.Quotient.eq_zero_iff_mem.mpr a.property]
      exact generator_zero T φ _ V
    | zero => exact map_zero _
    | add b c hb hc ihb ihc => rw [map_add, ihb, ihc, add_zero]
    | smul a b hb ih => rw [map_smul, ih, smul_zero]
  let invV (V : Cᵒᵖ) : N.val.obj V →ₗ[B.obj.obj V] M.val.obj V :=
    descendLinear (l V) (hsurj V) (t.val.app V).hom (hk V)
  have hi (V : Cᵒᵖ) (b : B.obj.obj V) :
      invV V (p.hom.app V b) = t.val.app V b :=
    descendLinear_apply (l V) (hsurj V) (t.val.app V).hom (hk V) b
  let invMap : N ⟶ M :=
    { val :=
      { app V := ModuleCat.ofHom (X := N.val.obj V) (Y := M.val.obj V) (invV V)
        naturality {V W} f := by
          ext y
          obtain ⟨b, rfl⟩ := hsurj V y
          change invV W ((constant T (A ⧸ I)).obj.map f (p.hom.app V b)) =
            M.val.map f (invV V (p.hom.app V b))
          rw [← NatTrans.naturality_apply p.hom f b, hi, hi]
          exact PresheafOfModules.naturality_apply t.val f b } }
  refine ⟨⟨invMap, ?_, ?_⟩⟩
  · apply realize_hom_ext T φ
    intro V x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    change invV V ((quotientMap T φ I p hp).val.app V
      (generator T φ (ModuleCat.of A (A ⧸ I)) V (Ideal.Quotient.mk I a))) = _
    rw [quotientMap_generator, ← projection_scalar T φ I p hp, hi, quotientOne_scalar]
    rfl
  · apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro V
    ext y
    obtain ⟨b, rfl⟩ := hsurj V y
    change (quotientMap T φ I p hp).val.app V (invV V (p.hom.app V b)) = p.hom.app V b
    rw [hi]
    change (quotientMap T φ I p hp).val.app V
      (b • generator T φ (ModuleCat.of A (A ⧸ I)) V 1) = _
    rw [map_smul, quotientMap_generator, map_one]
    change p.hom.app V b * 1 = _
    exact mul_one _

end Realization

/-- Exact coefficient realization, with the regular-module and quotient normalizations.
This statement contains no Koszul complexes, exterior powers, cones or derived categories.

Source: Stacks Project, proetale.tex, proof of lemma-naive-completion (099M);
Modules on Sites, Tags 03CY and 03EK.
(auxiliary; not a blueprint node).

Proof: write T for the coefficient model topology and phi for the completed
coefficient map. Take E to be commutativeSiteConstantModuleFunctor T A, then
ordinary extension of scalars along phi, then overFunctor at U. Constant module
realization is exact. By flat_and_quotients, the completed regular module is flat
over the constant ring, so extension of scalars is exact. Slice restriction is
exact as well. The regular-module isomorphism c is inverse to multiplication, which sends
a local tensor s tensor a to s phi(a). Multiplication commutes with
the scalar endomorphism x, giving the first displayed identity. For the quotient,
the same multiplication map sends s tensor [a] to pi_n(s) [a]. The kernel
calculation in flat_and_quotients says exactly that this map is an isomorphism:
both sides are the cokernel of the ideal J^(n+1) acting on the regular completed
module. Before extension, exact constant sheafification identifies the same
cokernel with the constant quotient module. Restrict these identifications to U.
The image of 1 tensor [a] is [a], so the resulting isomorphism q has the displayed
projection normalization. All maps descend from balanced tensor maps and hence
are natural under restrictions; sheafification preserves their inverse equations.
For the zero ring or J=A both quotient sides vanish. For J=0 multiplication is
the usual constant-module comparison. Empty sites and empty slices are covered
by the same sheafification and cokernel universal properties. -/
theorem adicResidue_exact_coefficient_realization
    (X : Scheme.{u}) {A : Type (max v (u + 1))} [CommRing A] [IsNoetherianRing A]
    (J : Ideal A) (U : coefficientProEtaleSiteModel.{u, v} X) :
    let O := (completed (coefficientProEtaleModelTopology.{u, v} X) A J).over U
    let s := fun x : A ↦ ringedKoszulSliceSection
      (completed (coefficientProEtaleModelTopology.{u, v} X) A J)
      (algebraSection (coefficientMap (coefficientProEtaleModelTopology.{u, v} X) A J)
        x) U
    ∃ (E : ModuleCat.{max v (u + 1)} A ⥤ Mod O) (_hadd : E.Additive)
      (_hlim : PreservesFiniteLimits E) (_hcolim : PreservesFiniteColimits E)
      (c : SheafOfModules.unit (siteModuleRings O) ≅ E.obj (ModuleCat.of A A))
      (q : ∀ n : ℕ, E.obj (ModuleCat.of A (A ⧸ J ^ (n + 1))) ≅
        adicResidueQuotientModule X J U n),
      (∀ x : A, c.hom ≫ E.map (ModuleCat.ofHom (LinearMap.mul A A x)) =
        (ringedKoszulScalar O (s x)).asHom ≫ c.hom) ∧
      ∀ n : ℕ, c.hom ≫ E.map (ModuleCat.ofHom (J ^ (n + 1)).mkQ) ≫ (q n).hom =
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 _).inv ≫
          (adicResidueQuotientCoefficientUnit X J U n).f 0 ≫
            (HomologicalComplex.singleObjXSelf (.up ℤ) 0 _).hom := by
  let T := coefficientProEtaleModelTopology.{u, v} X
  let B := completed T A J
  let φ := coefficientMap T A J
  let R : Mod B ⥤ Mod (B.over U) :=
    SheafOfModules.overFunctor (siteModuleRings B) U
  have hx := change_exact φ (flat_and_quotients T A J).1
  have : PreservesFiniteLimits (change φ) := hx.1
  have : PreservesFiniteColimits (change φ) := hx.2
  have hr := ringedOverFunctor_exactGeneral (siteModuleRings B) U
  have : R.Additive := hr.1
  have : PreservesFiniteLimits R := hr.2.1
  have : PreservesFiniteColimits R := hr.2.2
  let E : ModuleCat.{max v (u + 1)} A ⥤ Mod (B.over U) := realize T φ ⋙ R
  have : IsIso (oneMap T φ) := oneMap_isIso T φ
  let c : SheafOfModules.unit (siteModuleRings (B.over U)) ≅
      E.obj (ModuleCat.of A A) := R.mapIso (asIso (oneMap T φ))
  let hπ (n : ℕ) : φ ≫ projection T A J n =
      (constantSheaf T CommRingCat.{max v (u + 1)}).map
        (CommRingCat.ofHom (Ideal.Quotient.mk (J ^ (n + 1)))) :=
    limit.lift_π (quotientCone T A J) (op n)
  have hi (n : ℕ) :
      IsIso (quotientMap T φ (J ^ (n + 1)) (projection T A J n) (hπ n)) := by
    apply quotientMap_isIso
    · intro V
      exact ((flat_and_quotients T A J).2.1 n V.unop).1
    · intro V
      exact ((flat_and_quotients T A J).2.1 n V.unop).2
  let q (n : ℕ) : E.obj (ModuleCat.of A (A ⧸ J ^ (n + 1))) ≅
      adicResidueQuotientModule X J U n := by
    have := hi n
    exact R.mapIso (asIso (quotientMap T φ (J ^ (n + 1)) (projection T A J n) (hπ n)))
  refine ⟨E, inferInstance, inferInstance, inferInstance, c, q, ?_, ?_⟩
  · intro a
    change R.map (oneMap T φ) ≫
      R.map ((realize T φ).map (ModuleCat.ofHom (LinearMap.mul A A a))) = _
    rw [← Functor.map_comp, oneMap_scalar, Functor.map_comp]
    rfl
  · intro n
    simp only [adicResidueQuotientCoefficientUnit, HomologicalComplex.single_map_f_self,
      Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
    apply (SheafOfModules.unitHomEquiv _).injective
    rw [Equiv.apply_symm_apply]
    apply PresheafOfModules.sections_ext
    intro V
    change (quotientMap T φ (J ^ (n + 1)) (projection T A J n) (hπ n)).val.app
      (op V.unop.left)
        (((realize T φ).map (ModuleCat.ofHom (J ^ (n + 1)).mkQ)).val.app
          (op V.unop.left) ((oneMap T φ).val.app (op V.unop.left)
            (1 : B.obj.obj (op V.unop.left)))) =
      (1 : (constant T (A ⧸ J ^ (n + 1))).obj.obj (op V.unop.left))
    rw [oneMap_one, generator_naturality, quotientMap_generator]
    change (realizationRingUnit T (A ⧸ J ^ (n + 1))).app (op V.unop.left)
      (Ideal.Quotient.mk (J ^ (n + 1)) 1) = 1
    rw [map_one, map_one]

end AlgebraicGeometry.Scheme
