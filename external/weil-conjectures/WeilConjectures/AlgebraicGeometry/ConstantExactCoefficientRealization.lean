/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ConstantCompletionCore
import all WeilConjectures.AlgebraicGeometry.ConstantCompletionInverseImage
import all WeilConjectures.AlgebraicGeometry.ConstantRealizationDerivedScalarExtension

/-! # Exact constant coefficient realization and finite quotient normalization

Source: Stacks Project, Tags 093M, 099M and 03EK.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory.ConstantCompletion

namespace FiniteCoefficientRealization

universe w
variable {C : Type w} [SmallCategory C] (T : GrothendieckTopology C)
  {A : Type w} [CommRing A] {B : Sheaf T CommRingCat.{w}}
  (φ : constant T A ⟶ B)

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

end FiniteCoefficientRealization

open FiniteCoefficientRealization

/-- Exact constant realization followed by scalar extension identifies the regular
module and all finite quotients, with their scalar and quotient unit formulas.
This is entirely a statement about ordinary modules, without Koszul complexes.

Source: Stacks Project, Tags 093M, 099M and 03EK.
(auxiliary; not a blueprint node).

Proof: take constant-module sheafification followed by change of rings along
baseMap. Both functors are exact, the second by flat_and_quotients or the identity
map. Its regular-module isomorphism is the map given by the global section
1 tensor 1. The scalar equation is checked on that section. Send a local tensor
s tensor [a] to pi(s)[a] in the restricted constant quotient. The sectionwise
surjectivity and kernel formula in flat_and_quotients construct its inverse by
linear descent; these inverses commute with restrictions. The quotient unit
formula follows by evaluation at 1. The same argument covers I=0, I=A and zero
rings, since only quotient universal properties are used. -/
theorem constantExactCoefficientRealization
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) (b : Bool) :
    ∃ (E : ModuleCat.{u} A ⥤ Mod (coefficients J A I b)) (_hadd : E.Additive)
      (_hlim : PreservesFiniteLimits E) (_hcolim : PreservesFiniteColimits E)
      (c : SheafOfModules.unit (siteModuleRings (coefficients J A I b)) ≅
        E.obj (ModuleCat.of A A))
      (q : ∀ n : ℕ, E.obj (ModuleCat.of A (A ⧸ I ^ (n + 1))) ≅
        (res (finiteMap J A I b n)).obj
          (SheafOfModules.unit (siteModuleRings (finite J A I n)))),
      (∀ x : A, c.hom ≫ E.map (ModuleCat.ofHom (LinearMap.mul A A x)) =
        (ringedKoszulScalar (coefficients J A I b) (algebraSection (baseMap J A I b) x)).asHom ≫
          c.hom) ∧
      ∀ n : ℕ, c.hom ≫ E.map (ModuleCat.ofHom (I ^ (n + 1)).mkQ) ≫ (q n).hom =
        (SheafOfModules.unitHomEquiv
          ((res (finiteMap J A I b n)).obj
            (SheafOfModules.unit (siteModuleRings (finite J A I n))))).symm
          ⟨fun V ↦ (1 : (finite J A I n).obj.obj V),
            fun f ↦ map_one ((finite J A I n).obj.map f).hom⟩ := by
  let B := coefficients J A I b
  let φ := baseMap J A I b
  have hf : SheafOfModules.IsFlat
      ((res φ).obj (SheafOfModules.unit (siteModuleRings B))) := by
    cases b with
    | true => exact (flat_and_quotients J A I).1
    | false =>
      change SheafOfModules.IsFlat
        ((res (𝟙 (constant J A))).obj (SheafOfModules.unit (siteModuleRings (constant J A))))
      let R := constant J A
      let := SheafOfModules.monoidalCategory R
      change SheafOfModules.IsFlat (SheafOfModules.unit (siteModuleRings R))
      exact ⟨preservesFiniteLimits_of_natIso (MonoidalCategory.rightUnitorNatIso (Mod R)).symm,
        preservesFiniteColimits_of_natIso (MonoidalCategory.rightUnitorNatIso (Mod R)).symm⟩
  have hx := change_exact φ hf
  have : PreservesFiniteLimits (change φ) := hx.1
  have : PreservesFiniteColimits (change φ) := hx.2
  let E := realize J φ
  have : IsIso (oneMap J φ) := oneMap_isIso J φ
  let c := asIso (oneMap J φ)
  have hπ (n : ℕ) : φ ≫ finiteMap J A I b n =
      (constantSheaf J CommRingCat.{u}).map
        (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))) := by
    cases b with
    | false => exact Category.id_comp _
    | true => exact limit.lift_π (quotientCone J A I) (op n)
  have hi (n : ℕ) :
      IsIso (quotientMap J φ (I ^ (n + 1)) (finiteMap J A I b n) (hπ n)) := by
    apply quotientMap_isIso
    · intro V
      cases b with
      | false => exact ((flat_and_quotients J A I).2.2 n V.unop).1
      | true => exact ((flat_and_quotients J A I).2.1 n V.unop).1
    · intro V
      cases b with
      | false => exact ((flat_and_quotients J A I).2.2 n V.unop).2
      | true => exact ((flat_and_quotients J A I).2.1 n V.unop).2
  let q (n : ℕ) := @asIso _ _ _ _
    (quotientMap J φ (I ^ (n + 1)) (finiteMap J A I b n) (hπ n)) (hi n)
  refine ⟨E, inferInstance, inferInstance, inferInstance, c, q, ?_, ?_⟩
  · exact oneMap_scalar J φ
  · intro n
    apply (SheafOfModules.unitHomEquiv _).injective
    rw [Equiv.apply_symm_apply]
    apply PresheafOfModules.sections_ext
    intro V
    change (quotientMap J φ (I ^ (n + 1)) (finiteMap J A I b n) (hπ n)).val.app V
      (((realize J φ).map (ModuleCat.ofHom (I ^ (n + 1)).mkQ)).val.app V
        ((oneMap J φ).val.app V (1 : B.obj.obj V))) =
        (1 : (finite J A I n).obj.obj V)
    rw [oneMap_one, generator_naturality, quotientMap_generator]
    change (realizationRingUnit J (A ⧸ I ^ (n + 1))).app V
      (Ideal.Quotient.mk (I ^ (n + 1)) 1) = 1
    rw [map_one, map_one]

end CategoryTheory.ConstantCompletion
