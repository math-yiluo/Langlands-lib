/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition
import WeilConjectures.AlgebraicGeometry.OpenDerivedStalkIso
import WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk
/-! # Normalized ring and input-stalk coordinates

Source: Stacks Project, Tag 0098, stalks of pullback and restriction.
-/


@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
noncomputable section
namespace AlgebraicGeometry
open TopologicalSpace Opposite
set_option synthInstance.maxSize 2048
/-- The inverse stalk ring map acts on germs through the inverse section-ring map. -/
private theorem inverse_stalkMap_germ
    {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] (x : X)
    (U : X.Opens) (hx : x ∈ U) (r : Γ(X, U)) :
    (inv (j.stalkMap x)) (X.presheaf.germ U x hx r) =
      Y.presheaf.germ (j ''ᵁ U) (j x) (by simpa) ((j.appIso U).inv r) := by
  apply (ConcreteCategory.bijective_of_isIso (j.stalkMap x)).1
  simp only [IsIso.inv_hom_id_apply]
  rw [Scheme.Hom.germ_stalkMap_apply]
  change X.presheaf.germ U x hx r =
    ((j.appIso U).inv ≫ j.app _ ≫ X.presheaf.germ _ x _) r
  rw [Scheme.Hom.appIso_inv_app_assoc]
  exact (X.presheaf.germ_res_apply (eqToHom (j.preimage_image_eq U)) x
    (by simpa) r).symm

/-- The additive restriction-stalk comparison is semilinear over the inverse stalk map. -/
private theorem restriction_stalk_smul
    {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] (x : X) (M : Y.Modules)
    (r : X.presheaf.stalk x)
    (m : ((Scheme.Modules.restrictFunctor j).obj M).presheaf.stalk x) :
    (Scheme.Modules.restrictStalkNatIso j x).hom.app M (r • m) =
      (inv (j.stalkMap x)) r •
        (show M.presheaf.stalk (j x) from
          (Scheme.Modules.restrictStalkNatIso j x).hom.app M m) := by
  let N := (Scheme.Modules.restrictFunctor j).obj M
  obtain ⟨U, hxU, r, rfl⟩ := X.presheaf.exists_germ_eq r
  obtain ⟨V, hxV, m, rfl⟩ := N.presheaf.exists_germ_eq m
  have hx : x ∈ U ⊓ V := ⟨hxU, hxV⟩
  rw [← X.presheaf.germ_res_apply (homOfLE inf_le_left : U ⊓ V ⟶ U) x hx r,
    ← N.presheaf.germ_res_apply (homOfLE inf_le_right : U ⊓ V ⟶ V) x hx m]
  erw [← PresheafOfModules.germ_smul (R := X.presheaf) N.val]
  rw [inverse_stalkMap_germ]
  have hg (s : Γ(N, U ⊓ V)) :
      (Scheme.Modules.restrictStalkNatIso j x).hom.app M
        (N.presheaf.germ (U ⊓ V) x hx s) =
        M.presheaf.germ (j ''ᵁ (U ⊓ V)) (j x) (by simpa) s :=
    ConcreteCategory.congr_hom
      (Scheme.Modules.germ_restrictStalkNatIso_hom_app j x M hx) s
  erw [hg, hg]
  exact PresheafOfModules.germ_smul (R := Y.presheaf) M.val _ _ _ _ _

/-- The additive stalk comparison, viewed as a linear map after restriction of scalars. -/
private noncomputable def restrictionStalkLinearMap
    {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] (x : X) (M : Y.Modules) :
    (ModuleCat.restrictScalars (j.stalkMap x).hom).obj
        ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj
          ((Scheme.Modules.restrictFunctor j).obj M)) ⟶
      (RingedSpace.moduleStalkFunctor Y.toRingedSpace (j x)).obj M :=
  ModuleCat.ofHom
    (X := (ModuleCat.restrictScalars (j.stalkMap x).hom).obj
      ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj
        ((Scheme.Modules.restrictFunctor j).obj M)))
    (Y := (RingedSpace.moduleStalkFunctor Y.toRingedSpace (j x)).obj M)
    { toFun := (Scheme.Modules.restrictStalkNatIso j x).hom.app M
      map_add' := map_add _
      map_smul' := fun r m ↦ by
        change (Scheme.Modules.restrictStalkNatIso j x).hom.app M
            ((j.stalkMap x) r •
              (show ((Scheme.Modules.restrictFunctor j).obj M).presheaf.stalk x from m)) =
          r • (show M.presheaf.stalk (j x) from
            (Scheme.Modules.restrictStalkNatIso j x).hom.app M m)
        rw [restriction_stalk_smul]
        simp }

/-- The linear stalk comparison is invertible because its underlying additive map is. -/
private noncomputable def restrictionStalkLinearIso
    {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] (x : X) (M : Y.Modules) :
    (ModuleCat.restrictScalars (j.stalkMap x).hom).obj
        ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj
          ((Scheme.Modules.restrictFunctor j).obj M)) ≅
      (RingedSpace.moduleStalkFunctor Y.toRingedSpace (j x)).obj M := by
  let a := restrictionStalkLinearMap j x M
  have : IsIso a :=
    (ConcreteCategory.isIso_iff_bijective a).mpr
      (ConcreteCategory.bijective_of_isIso
        ((Scheme.Modules.restrictStalkNatIso j x).hom.app M))
  exact asIso a

/-- The linear stalk comparisons are natural in the module sheaf. -/
private noncomputable def restrictionStalkLinearNatIso
    {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] (x : X) :
    (Scheme.Modules.restrictFunctor j ⋙ RingedSpace.moduleStalkFunctor X.toRingedSpace x) ⋙
        ModuleCat.restrictScalars (j.stalkMap x).hom ≅
      RingedSpace.moduleStalkFunctor Y.toRingedSpace (j x) :=
  NatIso.ofComponents (restrictionStalkLinearIso j x) (by
    intro M N f
    ext m
    exact ConcreteCategory.congr_hom
      ((Scheme.Modules.restrictStalkNatIso j x).hom.naturality f) m)


/-- Transported same-germ input chain isomorphism, with its component normalization. -/
private theorem exists_normalized_input_iso
    {Y Z : Scheme.{u}} (j : Y ⟶ Z) [IsOpenImmersion j] (x : Y)
    (y : Z) (h : y = j x)
    (P : CochainComplex (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) ℤ) :
    let e := (Z.presheaf.stalkCongr (.of_eq h) ≪≫
      asIso (j.stalkMap x)).commRingCatIsoToRingEquiv
    let K := ((RingedSpace.moduleStalkFunctor Z.toRingedSpace y).mapHomologicalComplex
      (.up ℤ)).obj P
    let K0 := ((RingedSpace.moduleStalkFunctor Y.toRingedSpace x).mapHomologicalComplex
      (.up ℤ)).obj (((Scheme.Modules.restrictFunctor j).mapHomologicalComplex (.up ℤ)).obj P)
    ∃ q : K ≅ ((ModuleCat.restrictScalars e.toRingHom).mapHomologicalComplex
        (.up ℤ)).obj K0,
      ∀ (k : ℤ) (m : K.X k),
        (show K0.X k from q.hom.f k m) =
          (Scheme.Modules.restrictStalkNatIso j x).inv.app (P.X k)
            (((show Z.Modules from P.X k).presheaf.stalkCongr (.of_eq h)).hom m) := by
  subst y
  dsimp only
  have he : (Z.presheaf.stalkCongr (.of_eq (Eq.refl (j x))) ≪≫
      asIso (j.stalkMap x)).commRingCatIsoToRingEquiv.toRingHom =
        (j.stalkMap x).hom := by
    change ((Z.presheaf.stalkCongr (.of_eq (Eq.refl (j x)))).hom ≫
      (j.stalkMap x)).hom = _
    simp only [TopCat.Presheaf.stalkCongr_hom,
      TopCat.Presheaf.stalkSpecializes_refl, Category.id_comp]
  rw [he]
  have : (Scheme.Modules.restrictFunctor j).PreservesZeroMorphisms := inferInstance
  have : (RingedSpace.moduleStalkFunctor Y.toRingedSpace x).PreservesZeroMorphisms :=
    RingedSpace.moduleStalkFunctor_preservesZeroMorphisms Y.toRingedSpace x
  have : (RingedSpace.moduleStalkFunctor Z.toRingedSpace (j x)).PreservesZeroMorphisms :=
    RingedSpace.moduleStalkFunctor_preservesZeroMorphisms Z.toRingedSpace (j x)
  have : (ModuleCat.restrictScalars.{u} (j.stalkMap x).hom).PreservesZeroMorphisms :=
    inferInstance
  let a := restrictionStalkLinearNatIso j x
  let q := ((NatIso.mapHomologicalComplex a (.up ℤ)).app P).symm
  refine ⟨q, ?_⟩
  intro k m
  apply (ConcreteCategory.bijective_of_isIso
    ((Scheme.Modules.restrictStalkNatIso j x).hom.app (P.X k))).1
  have hq := ConcreteCategory.congr_hom
    ((HomologicalComplex.eval _ _ k).mapIso q).hom_inv_id m
  change (Scheme.Modules.restrictStalkNatIso j x).hom.app (P.X k)
      (q.hom.f k m) = _
  rw [Iso.inv_hom_id_app_apply]
  change restrictionStalkLinearMap j x (P.X k) (q.hom.f k m) = m at hq
  change (Scheme.Modules.restrictStalkNatIso j x).hom.app (P.X k)
    (q.hom.f k m) = m at hq
  simpa only [TopCat.Presheaf.stalkCongr_hom,
    TopCat.Presheaf.stalkSpecializes_refl, AddCommGrpCat.id_apply] using hq

end AlgebraicGeometry

namespace AlgebraicGeometry.SingleComplexBaseChange
variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]


/-- The canonical tensor-to-stalk map multiplies the two projection images. -/
private theorem tensorMap_tmul_formula
    {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g) (z : X') :
    letI := leftAlgebra f g' z
    letI := rightAlgebra f f' g g' sq z
    ∀ (a : A g' z) (b : B f' z),
      tensorMap f f' g g' sq z (a ⊗ₜ[R f g' z] b) =
        (g'.stalkMap z).hom a * (f'.stalkMap z).hom b := by
  let := leftAlgebra f g' z
  let := rightAlgebra f f' g g' sq z
  intro a b
  have hl := (Classical.choose_spec (exists_tensorMap f f' g g' sq z)).1
  have hr := (Classical.choose_spec (exists_tensorMap f f' g g' sq z)).2
  change (tensorMap f f' g g' sq z).comp
    (algebraMap (A g' z) (A g' z ⊗[R f g' z] B f' z)) =
      (g'.stalkMap z).hom at hl
  change (tensorMap f f' g g' sq z).comp
    Algebra.TensorProduct.includeRight.toRingHom = (f'.stalkMap z).hom at hr
  have ht : a ⊗ₜ[R f g' z] b =
      algebraMap (A g' z) (A g' z ⊗[R f g' z] B f' z) a *
        Algebra.TensorProduct.includeRight (R := R f g' z) (A := A g' z) b := by
    simp
  rw [ht, map_mul]
  change ((tensorMap f f' g g' sq z).comp
    (algebraMap (A g' z) (A g' z ⊗[R f g' z] B f' z))) a *
      ((tensorMap f f' g g' sq z).comp Algebra.TensorProduct.includeRight.toRingHom) b = _
  rw [hl, hr]

/-- Normalized ring and input-stalk coordinates for a source open.

Proof: Let p and s be the two projections of X' times_X U. The pullback equation
identifies g'(p z0) with U.ι(s z0). Compose this stalk congruence with the invertible
stalk map of U.ι to obtain eA, and use p.stalkMap for eD. Use the corresponding
point congruences in S and S' for eR and eB. Functoriality of stalkMap proves the
two base-algebra equations. The restrictions of tensorMap to its two inclusions
are the projection stalk maps, so their products prove the tensor-ring equation.
Represent scalar and module germs on a common open. The inverse ring-stalk germ
formula and germ_smul show that the inverse same-germ restriction map is linear
into restriction of scalars along eA. It is bijective; its naturality for each
differential gives q. Its construction gives the last, degreewise normalization.
The empty open has no z0; zero stalk rings and the zero complex use the same maps.
This lemma constructs no tensor-complex transport and asserts no homology square.
Source: Stacks Project, Tag 0098, Lemma 6.26.4; Mathlib restriction-stalk germ formulas.
(blueprint: lem-pc-open-restricted-stalk-coordinates). -/
theorem exists_openRestricted_stalk_coordinates
    {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g)
    (U : X.Opens)
    (sq0 : IsPullback (pullback.snd g' U.ι) (pullback.fst g' U.ι ≫ f') (U.ι ≫ f) g)
    (z0 : (pullback g' U.ι : Scheme.{u}))
    (P : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :
    let z := pullback.fst g' U.ι z0
    let P0 := ((Scheme.Modules.restrictFunctor U.ι).mapHomologicalComplex
      (.up ℤ)).obj P
    letI := leftAlgebra f g' z
    letI := rightAlgebra f f' g g' sq z
    letI := (tensorMap f f' g g' sq z).toAlgebra
    letI := leftAlgebra (U.ι ≫ f) (pullback.snd g' U.ι) z0
    letI := rightAlgebra (U.ι ≫ f) (pullback.fst g' U.ι ≫ f')
      g (pullback.snd g' U.ι) sq0 z0
    letI := (tensorMap (U.ι ≫ f) (pullback.fst g' U.ι ≫ f')
      g (pullback.snd g' U.ι) sq0 z0).toAlgebra
    let R0 := R (U.ι ≫ f) (pullback.snd g' U.ι) z0
    let A0 := A (pullback.snd g' U.ι) z0
    let B0 := B (pullback.fst g' U.ι ≫ f') z0
    let D0 := C z0
    let Q := stalkComplex g' z P
    let Q0 := stalkComplex (pullback.snd g' U.ι) z0 P0
    let hp : g' z = U.ι (pullback.snd g' U.ι z0) :=
      congrArg (fun h : pullback g' U.ι ⟶ X => h z0) pullback.condition
    ∃ (eR : R f g' z ≃+* R0) (eA : A g' z ≃+* A0)
      (eB : B f' z ≃+* B0) (eD : C z ≃+* D0)
      (q : Q ≅ ((ModuleCat.restrictScalars.{u} eA.toRingHom).mapHomologicalComplex
        (.up ℤ)).obj Q0),
      (∀ r : R f g' z,
        eA (algebraMap (R f g' z) (A g' z) r) = algebraMap R0 A0 (eR r)) ∧
      (∀ r : R f g' z,
        eB (algebraMap (R f g' z) (B f' z) r) = algebraMap R0 B0 (eR r)) ∧
      (∀ (a : A g' z) (b : B f' z),
        eD (algebraMap (A g' z ⊗[R f g' z] B f' z) (C z) (a ⊗ₜ[R f g' z] b)) =
          algebraMap (A0 ⊗[R0] B0) D0 (eA a ⊗ₜ[R0] eB b)) ∧
      eD.toRingHom = ((pullback.fst g' U.ι).stalkMap z0).hom ∧
      ∀ (k : ℤ) (x : Q.X k),
        (show Q0.X k from q.hom.f k x) =
          (Scheme.Modules.restrictStalkNatIso U.ι (pullback.snd g' U.ι z0)).inv.app
            (P.X k) (((show X.Modules from P.X k).presheaf.stalkCongr (.of_eq hp)).hom x)
    := by
  classical
  intro z P0 R0 A0 B0 D0 Q Q0 hp
  let := leftAlgebra f g' z
  let := rightAlgebra f f' g g' sq z
  let := (tensorMap f f' g g' sq z).toAlgebra
  let := leftAlgebra (U.ι ≫ f) (pullback.snd g' U.ι) z0
  let := rightAlgebra (U.ι ≫ f) (pullback.fst g' U.ι ≫ f')
    g (pullback.snd g' U.ι) sq0 z0
  let := (tensorMap (U.ι ≫ f) (pullback.fst g' U.ι ≫ f')
    g (pullback.snd g' U.ι) sq0 z0).toAlgebra
  let a := X.presheaf.stalkCongr (.of_eq hp) ≪≫
    asIso (U.ι.stalkMap (pullback.snd g' U.ι z0))
  let d := asIso ((pullback.fst g' U.ι).stalkMap z0)
  let r := S.presheaf.stalkCongr (.of_eq (congrArg f hp))
  let b := S'.presheaf.stalkCongr (.of_eq
    (show f' z = (pullback.fst g' U.ι ≫ f') z0 from rfl))
  let eA := a.commRingCatIsoToRingEquiv
  let eD := d.commRingCatIsoToRingEquiv
  let eR := r.commRingCatIsoToRingEquiv
  let eB := b.commRingCatIsoToRingEquiv
  obtain ⟨q, hq⟩ := exists_normalized_input_iso U.ι (pullback.snd g' U.ι z0)
    (g' z) hp P
  refine ⟨eR, eA, eB, eD, q, ?_, ?_, ?_, rfl, hq⟩
  · intro c
    change (a.hom.hom.comp (f.stalkMap (g' z)).hom) c =
      (((U.ι ≫ f).stalkMap (pullback.snd g' U.ι z0)).hom.comp r.hom.hom) c
    have hf := Scheme.Hom.stalkMap_congr_point f (g' z)
      (U.ι (pullback.snd g' U.ι z0)) hp
    rw [Scheme.Hom.stalkMap_comp]
    have heq : f.stalkMap (g' z) ≫ a.hom = r.hom ≫
        f.stalkMap (U.ι (pullback.snd g' U.ι z0)) ≫
          U.ι.stalkMap (pullback.snd g' U.ι z0) := by
      simpa only [a, r, Iso.trans_hom, asIso_hom, Category.assoc] using
        congrArg (fun h => h ≫ U.ι.stalkMap (pullback.snd g' U.ι z0)) hf
    exact congrArg (fun h : R f g' z ⟶ CommRingCat.of A0 => h.hom c) heq
  · intro c
    have hbase : (S.presheaf.stalkCongr
        (.of_eq (congrArg (fun k : X' ⟶ S => k z) sq.w))).hom =
        r.hom ≫ (S.presheaf.stalkCongr (.of_eq
          (congrArg (fun k : pullback g' U.ι ⟶ S => k z0) sq0.w))).hom := by
      simp only [r, TopCat.Presheaf.stalkCongr_hom,
        TopCat.Presheaf.stalkSpecializes_comp]
    change b.hom ((S.presheaf.stalkCongr
      (.of_eq (congrArg (fun k : X' ⟶ S => k z) sq.w))).hom ≫
        g.stalkMap (f' z) |>.hom <| c) = _
    simp only [b, TopCat.Presheaf.stalkCongr_hom,
      TopCat.Presheaf.stalkSpecializes_refl]
    change ((S.presheaf.stalkCongr
      (.of_eq (congrArg (fun k : X' ⟶ S => k z) sq.w))).hom ≫
        g.stalkMap (f' z)).hom c =
      ((S.presheaf.stalkCongr (.of_eq
        (congrArg (fun k : pullback g' U.ι ⟶ S => k z0) sq0.w))).hom ≫
          g.stalkMap ((pullback.fst g' U.ι ≫ f') z0)).hom (r.hom c)
    rw [hbase]
    rfl
  · intro c c'
    change eD (tensorMap f f' g g' sq z (c ⊗ₜ[R f g' z] c')) =
      tensorMap (U.ι ≫ f) (pullback.fst g' U.ι ≫ f')
        g (pullback.snd g' U.ι) sq0 z0 (eA c ⊗ₜ[R0] eB c')
    rw [tensorMap_tmul_formula, tensorMap_tmul_formula, map_mul]
    congr 1
    · have hs := Scheme.Hom.stalkMap_congr_hom
        (pullback.fst g' U.ι ≫ g') (pullback.snd g' U.ι ≫ U.ι)
        pullback.condition z0
      rw [Scheme.Hom.stalkMap_comp, Scheme.Hom.stalkMap_comp] at hs
      have heq : g'.stalkMap z ≫ d.hom = a.hom ≫
          (pullback.snd g' U.ι).stalkMap z0 := by
        simpa only [a, d, Iso.trans_hom, asIso_hom, Category.assoc] using hs
      exact congrArg (fun h : A g' z ⟶ CommRingCat.of D0 => h.hom c) heq
    · change (f'.stalkMap z ≫ d.hom).hom c' =
        ((pullback.fst g' U.ι ≫ f').stalkMap z0).hom (b.hom c')
      rw [Scheme.Hom.stalkMap_comp]
      simp only [b, d, asIso_hom, TopCat.Presheaf.stalkCongr_hom,
        TopCat.Presheaf.stalkSpecializes_refl]
      rfl


end AlgebraicGeometry.SingleComplexBaseChange
