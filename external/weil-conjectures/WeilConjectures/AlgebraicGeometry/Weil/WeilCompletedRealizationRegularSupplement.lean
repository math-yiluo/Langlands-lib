/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Weil.WeilCompletedKoszulSite

/-! # The regular module under completed constant realization

Source: Stacks Project, Modules on Sites, Tags 03D8 and 03EK,
lemma-adjointness-tensor-restrict, and Tag 0GMW, lemma-sheafification-tensor.
(blueprint: lem-weil-pbc-completed-realization-regular).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

private theorem completedOne_isIso
    (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (d : ProEtaleAdicCoefficientDatum A) : IsIso (completedKoszulOne X d) := by
  let M := (adicLisseConstantModules X A).obj (ModuleCat.of A A)
  let α := adicDatumScalar X d
  let adj := adicDatumOrdinaryAdjunction X α
  let e (N : adicDatumModules X d) :
      ((completedKoszulConstant X d).obj (ModuleCat.of A A) ⟶ N) ≃ N.sections :=
    ((adj.homEquiv M N).trans
      (PresheafOfModules.sheafificationHomEquiv (adicLisseConstantUnit X A))).trans
        (PresheafOfModules.unitHomEquiv _)
  have he (N : adicDatumModules X d)
      (f : (completedKoszulConstant X d).obj (ModuleCat.of A A) ⟶ N) :
      e N f = N.unitHomEquiv (completedKoszulOne X d ≫ f) := by
    apply PresheafOfModules.sections_ext
    intro U
    dsimp only [e, Equiv.trans_apply]
    change ((PresheafOfModules.sheafificationHomEquiv (adicLisseConstantUnit X A))
      (adj.homEquiv M N f)).app U (1 : A) =
        f.val.app U ((completedKoszulOne X d).val.app U
          (1 : (adicDatumRing X d).obj.obj U))
    rw [Adjunction.homEquiv_unit]
    change f.val.app U ((adj.unit.app M).val.app U
      (completedConstantGenerator X A (ModuleCat.of A A) U 1)) =
        f.val.app U ((completedKoszulOne X d).val.app U (1 : (adicDatumRing X d).obj.obj U))
    have hu : adj.unit.app M = adicDatumOrdinaryUnit X α M :=
      (adicDatumOrdinaryAdjunction_exists X α).choose_spec M
    rw [hu]
    exact congrArg (f.val.app U)
      (((adicDatumOrdinaryUnit_exists X α M).exists.choose_spec U
        (completedConstantGenerator X A (ModuleCat.of A A) U 1)).trans
          ((completedKoszulOne_exists X d).exists.choose_spec U).symm)
  apply isIso_of_coyoneda_map_bijective
  intro N
  have hf : (fun f ↦ completedKoszulOne X d ≫ f) =
      N.unitHomEquiv.symm ∘ e N := by
    funext f
    exact N.unitHomEquiv.injective (by simp [he])
  rw [hf]
  exact N.unitHomEquiv.symm.bijective.comp (e N).bijective

private theorem completedOne_scalar
    (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (d : ProEtaleAdicCoefficientDatum A) (a : A) (U : X.ProEtᵒᵖ) :
    ((completedKoszulConstant X d).map
        (ModuleCat.ofHom (LinearMap.mul A A a))).val.app U
        ((completedKoszulOne X d).val.app U (1 : (adicDatumRing X d).obj.obj U)) =
      (adicDatumScalar X d).hom.app U ((adicLisseConstantUnit X A).app U a) •
        ((completedKoszulOne X d).val.app U (1 : (adicDatumRing X d).obj.obj U)) := by
  let M := (adicLisseConstantModules X A).obj (ModuleCat.of A A)
  let adj := adicDatumOrdinaryAdjunction X (adicDatumScalar X d)
  let η := adj.unit.app M
  have hη (x : M.val.obj U) : η.val.app U x =
      adicDatumTensorSection X (adicDatumScalar X d) M U 1 x := by
    dsimp only [η]
    erw [(adicDatumOrdinaryAdjunction_exists X (adicDatumScalar X d)).choose_spec]
    exact (adicDatumOrdinaryUnit_exists X (adicDatumScalar X d) M).exists.choose_spec U x
  have hc : (completedKoszulOne X d).val.app U (1 : (adicDatumRing X d).obj.obj U) =
      η.val.app U (completedConstantGenerator X A (ModuleCat.of A A) U 1) := by
    rw [hη]
    exact (completedKoszulOne_exists X d).exists.choose_spec U
  rw [hc]
  have hn := congrArg (fun f ↦ f.val.app U
    (completedConstantGenerator X A (ModuleCat.of A A) U 1))
    (adj.unit_naturality ((adicLisseConstantModules X A).map
      (ModuleCat.ofHom (LinearMap.mul A A a))))
  have hmap : ((adicLisseConstantModules X A).map
      (ModuleCat.ofHom (LinearMap.mul A A a))).val.app U
      (completedConstantGenerator X A (ModuleCat.of A A) U 1) =
        completedConstantGenerator X A (ModuleCat.of A A) U a := by
    have hx := congrArg (fun f ↦ f.app U (1 : A))
      (toSheafify_naturality (ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).map (AddCommGrpCat.ofHom
          (LinearMap.mul A A a).toAddMonoidHom)))
    change completedConstantGenerator X A (ModuleCat.of A A) U (a * 1) =
      ((adicLisseConstantModules X A).map (ModuleCat.ofHom (LinearMap.mul A A a))).val.app U
        (completedConstantGenerator X A (ModuleCat.of A A) U 1) at hx
    simpa only [mul_one] using hx.symm
  have hg : completedConstantGenerator X A (ModuleCat.of A A) U a =
      (adicLisseConstantUnit X A).app U a •
        completedConstantGenerator X A (ModuleCat.of A A) U 1 := by
    let η₀ := (PresheafOfModules.sheafificationAdjunction
      (adicLisseConstantUnit X A)).unit.app
        (PresheafOfModules.unit ((Functor.const X.ProEtᵒᵖ).obj (RingCat.of A)))
    have h := (η₀.app U).hom.map_smul a (1 : A)
    change completedConstantGenerator X A (ModuleCat.of A A) U (a * 1) =
      (adicLisseConstantUnit X A).app U a •
        completedConstantGenerator X A (ModuleCat.of A A) U 1 at h
    simpa only [mul_one] using h
  change ((completedKoszulConstant X d).map
      (ModuleCat.ofHom (LinearMap.mul A A a))).val.app U
      (η.val.app U (completedConstantGenerator X A (ModuleCat.of A A) U 1)) =
    η.val.app U (((adicLisseConstantModules X A).map
      (ModuleCat.ofHom (LinearMap.mul A A a))).val.app U
        (completedConstantGenerator X A (ModuleCat.of A A) U 1)) at hn
  rw [hmap, hg, map_smul] at hn
  exact hn

private theorem transportedUnit_one
    (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (U : (completedCechSite X)ᵒᵖ) :
    (completedCechCoefficientUnit X d).val.app U
      (1 : (completedCechRing X d).obj.obj U) =
        (1 : (adicDatumRing X (intrinsicPresentationDatum d)).obj.obj
          ((completedCechSiteEquiv X).inverse.op.obj U)) := by
  let N := (intrinsicPresentationModulesBack X d ⋙
    (completedCechModulesEquiv X d).functor).obj
      (SheafOfModules.unit ((adicLisseForget X).obj
        (adicDatumRing X (intrinsicPresentationDatum d))))
  dsimp only [completedCechCoefficientUnit]
  exact congrArg (fun s : N.sections ↦ s.val U) (N.unitHomEquiv.apply_symm_apply _)

private theorem transportedUnit_apply
    (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (U : (completedCechSite X)ᵒᵖ) (r : (completedCechRing X d).obj.obj U) :
    (completedCechCoefficientUnit X d).val.app U r =
      (pbcCompletedComparison X d).inv.hom.app
        ((completedCechSiteEquiv X).inverse.op.obj U) r := by
  have h := ((completedCechCoefficientUnit X d).val.app U).hom.map_smul r
    (1 : (completedCechRing X d).obj.obj U)
  rw [transportedUnit_one] at h
  change (completedCechCoefficientUnit X d).val.app U
    (r * (1 : (completedCechRing X d).obj.obj U)) =
      (pbcCompletedComparison X d).inv.hom.app
        ((completedCechSiteEquiv X).inverse.op.obj U) r *
          (1 : (adicLisseCompletedRing X d.ideal).obj.obj
            ((completedCechSiteEquiv X).inverse.op.obj U)) at h
  simpa only [mul_one] using h

private def transportedUnitInverse
    (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) :
    (intrinsicPresentationModulesBack X d ⋙ (completedCechModulesEquiv X d).functor).obj
        (SheafOfModules.unit ((adicLisseForget X).obj
          (adicDatumRing X (intrinsicPresentationDatum d)))) ⟶
      SheafOfModules.unit ((sheafCompose (completedCechTopology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (completedCechRing X d)) where
  val :=
    { app := fun U ↦ ModuleCat.ofHom
        (X := ((intrinsicPresentationModulesBack X d ⋙
          (completedCechModulesEquiv X d).functor).obj
            (SheafOfModules.unit ((adicLisseForget X).obj
              (adicDatumRing X (intrinsicPresentationDatum d))))).val.obj U)
        (Y := (SheafOfModules.unit ((sheafCompose (completedCechTopology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
            (completedCechRing X d))).val.obj U) {
        toFun := (pbcCompletedComparison X d).hom.hom.app
          ((completedCechSiteEquiv X).inverse.op.obj U)
        map_add' := map_add _
        map_smul' := by
          intro r x
          let V := (completedCechSiteEquiv X).inverse.op.obj U
          let r' : (pbcAdicCompletion X d).obj.obj V := r
          let x' : (adicLisseCompletedRing X d.ideal).obj.obj V := x
          change (pbcCompletedComparison X d).hom.hom.app V
            ((pbcCompletedComparison X d).inv.hom.app V r' * x') =
              r' * (pbcCompletedComparison X d).hom.hom.app V x'
          rw [map_mul]
          congr 1
          exact ConcreteCategory.congr_hom
            (congrArg (fun f ↦ f.hom.app ((completedCechSiteEquiv X).inverse.op.obj U))
              (pbcCompletedComparison X d).inv_hom_id) r' }
      naturality := by
        intro U V f
        ext x
        exact ConcreteCategory.congr_hom ((pbcCompletedComparison X d).hom.hom.naturality
          ((completedCechSiteEquiv X).inverse.op.map f)) x }

private theorem transportedUnit_isIso
    (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) :
    IsIso (completedCechCoefficientUnit X d) := by
  refine ⟨transportedUnitInverse X d, ?_, ?_⟩
  · apply (SheafOfModules.unitHomEquiv _).injective
    apply PresheafOfModules.sections_ext
    intro U
    change (transportedUnitInverse X d).val.app U
      ((completedCechCoefficientUnit X d).val.app U
        (1 : (completedCechRing X d).obj.obj U)) =
          (1 : (completedCechRing X d).obj.obj U)
    rw [transportedUnit_one]
    change (pbcCompletedComparison X d).hom.hom.app _
      (1 : (adicLisseCompletedRing X d.ideal).obj.obj _) = _
    exact map_one _
  · apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    let V := (completedCechSiteEquiv X).inverse.op.obj U
    let x' : (adicLisseCompletedRing X d.ideal).obj.obj V := x
    change (completedCechCoefficientUnit X d).val.app U
      ((pbcCompletedComparison X d).hom.hom.app V x') = x'
    erw [transportedUnit_apply]
    exact ConcreteCategory.congr_hom
      (congrArg (fun f ↦ f.hom.app V) (pbcCompletedComparison X d).hom_inv_id) x'

/-- The specified coefficient unit identifies the realized regular module with the
regular coefficient sheaf, and it intertwines multiplication by every scalar.

Source: Stacks Project, Modules on Sites, Tags 03D8 and 03EK,
lemma-adjointness-tensor-restrict, and Tag 0GMW, lemma-sheafification-tensor.
(blueprint: lem-weil-pbc-completed-realization-regular).

Proof: compose the scalar-extension/restriction adjunction with the
constant-module sheafification Hom equivalence and the regular-module/sections
bijection. For every completed module N this gives a bijection from maps
G(A) to N to global sections of N. The normalized ordinary adjunction unit
sends the constant generator 1 to 1 tensor 1, exactly the section formula
characterizing completedKoszulOne. Hence this bijection equals precomposition
with completedKoszulOne followed by the regular-module/sections bijection.
Precomposition is therefore bijective for every N, and the Yoneda criterion
makes completedKoszulOne invertible.

Naturality of the ordinary adjunction unit with respect to multiplication by a
says that the extended map sends 1 tensor 1 to 1 tensor a. Linearity of the
constant-module sheafification unit identifies the constant generator a with
the scalar section a times the generator 1. Linearity of the ordinary unit
then identifies 1 tensor a with the image of a times 1 tensor 1.

Under restriction through the inverse completed coefficient-ring isomorphism,
the regular-module map classified by section 1 sends r to the inverse ring
isomorphism applied to r. Its inverse is sectionwise the forward ring
isomorphism. Reindex these maps along the site equivalence to identify this
map with completedCechCoefficientUnit and prove it invertible. Compose with
the image of completedKoszulOne. Equality of maps from the regular module is
tested at 1. The scalar equation already proved before transport then becomes
the claimed equation because completedCechScalar is the forward ring
isomorphism applied to the original scalar section. These unit, adjunction
and ring-isomorphism identities include the zero ring and the empty site. -/
theorem completedRealizationRegular
    (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) :
    let F := intrinsicPresentationModulesBack X d ⋙ (completedCechModulesEquiv X d).functor
    let G := completedKoszulConstant X (intrinsicPresentationDatum d)
    let Q := G ⋙ F
    let O := completedCechRing X d
    let c := completedCechCoefficientUnit X d ≫
      F.map (completedKoszulOne X (intrinsicPresentationDatum d))
    IsIso c ∧ ∀ a : A, c ≫ Q.map (ModuleCat.ofHom (LinearMap.mul A A a)) =
      (ringedKoszulScalar O (completedCechScalar X d a)).asHom ≫ c := by
  let F := intrinsicPresentationModulesBack X d ⋙ (completedCechModulesEquiv X d).functor
  let G := completedKoszulConstant X (intrinsicPresentationDatum d)
  have := completedOne_isIso X (intrinsicPresentationDatum d)
  have := transportedUnit_isIso X d
  refine ⟨inferInstance, ?_⟩
  intro a
  apply (SheafOfModules.unitHomEquiv _).injective
  apply PresheafOfModules.sections_ext
  intro U
  let V := (completedCechSiteEquiv X).inverse.op.obj U
  have hs : (ringedKoszulScalar (completedCechRing X d)
      (completedCechScalar X d a)).asHom.val.app U
        (1 : (completedCechRing X d).obj.obj U) =
        (completedCechScalar X d a).val U := by
    let N := SheafOfModules.unit ((sheafCompose (completedCechTopology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (completedCechRing X d))
    exact congrArg (fun s : N.sections ↦ s.val U)
      (N.unitHomEquiv.apply_symm_apply ⟨(completedCechScalar X d a).val,
        (completedCechScalar X d a).property⟩)
  change ((F.map (G.map (ModuleCat.ofHom (LinearMap.mul A A a)))).val.app U)
      ((F.map (completedKoszulOne X (intrinsicPresentationDatum d))).val.app U
        ((completedCechCoefficientUnit X d).val.app U
        (1 : (completedCechRing X d).obj.obj U))) =
    (F.map (completedKoszulOne X (intrinsicPresentationDatum d))).val.app U
      ((completedCechCoefficientUnit X d).val.app U
        ((ringedKoszulScalar (completedCechRing X d)
          (completedCechScalar X d a)).asHom.val.app U
        (1 : (completedCechRing X d).obj.obj U)))
  rw [transportedUnit_one, hs]
  erw [transportedUnit_apply]
  change ((G.map (ModuleCat.ofHom (LinearMap.mul A A a))).val.app V)
      ((completedKoszulOne X (intrinsicPresentationDatum d)).val.app V
        (1 : (adicDatumRing X (intrinsicPresentationDatum d)).obj.obj V)) =
    (completedKoszulOne X (intrinsicPresentationDatum d)).val.app V
      ((pbcCompletedComparison X d).inv.hom.app V ((completedCechScalar X d a).val U))
  have hb : (pbcCompletedComparison X d).inv.hom.app V
      ((completedCechScalar X d a).val U) =
        (adicDatumScalar X (intrinsicPresentationDatum d)).hom.app V
          ((adicLisseConstantUnit X A).app V a) := by
    exact ConcreteCategory.congr_hom
      (congrArg (fun f ↦ f.hom.app V) (pbcCompletedComparison X d).hom_inv_id) _
  rw [hb]
  have hc := ((completedKoszulOne X (intrinsicPresentationDatum d)).val.app V).hom.map_smul
    ((adicDatumScalar X (intrinsicPresentationDatum d)).hom.app V
      ((adicLisseConstantUnit X A).app V a))
        (1 : (adicDatumRing X (intrinsicPresentationDatum d)).obj.obj V)
  change (completedKoszulOne X (intrinsicPresentationDatum d)).val.app V
    ((adicDatumScalar X (intrinsicPresentationDatum d)).hom.app V
      ((adicLisseConstantUnit X A).app V a) *
        (1 : (adicDatumRing X (intrinsicPresentationDatum d)).obj.obj V)) = _ at hc
  rw [mul_one] at hc
  rw [hc]
  exact completedOne_scalar X (intrinsicPresentationDatum d) a V

end AlgebraicGeometry.Scheme
