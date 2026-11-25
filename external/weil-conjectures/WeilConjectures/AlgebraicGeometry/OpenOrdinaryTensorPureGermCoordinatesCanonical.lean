/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition
public import WeilConjectures.AlgebraicGeometry.OpenPinnedSingleDegreeZeroCounitIso
import WeilConjectures.AlgebraicGeometry.OpenPinnedTensorRestrictionStalkUnit
import WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk
import all WeilConjectures.AlgebraicGeometry.OpenModuleStalkRestrictionComparison

/-! # Unit-scalar generators and scalar extension for the pinned tensor comparison

Source: Stacks Project, Tags 0098 and 0096.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
set_option linter.unusedVariables false
universe u w
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ChangeOfRings
namespace AlgebraicGeometry
open SingleComplexBaseChange
open TopologicalSpace Opposite

private theorem tensor_unit_stalk {X Y : Scheme.{u}} (k : X ⟶ Y) (x : X)
    (M : Y.Modules) (m : M.presheaf.stalk (k x)) :
    (Classical.choose (Scheme.Modules.exists_tensorPullback_stalk_iso k x)).inv.app M
        ((1 : X.presheaf.stalk x) ⊗ₜ[Y.presheaf.stalk (k x), (k.stalkMap x).hom] m) =
      (((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (k x)).map
        (Scheme.Modules.Hom.mapPresheaf
          ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction k)).unit.app M))) ≫
        ((Scheme.Modules.tensorPullback k).obj M).presheaf.stalkPushforward
          AddCommGrpCat.{u} k.base x) m := by
  dsimp only [Scheme.Modules, Scheme.ringCatSheaf] at *
  obtain ⟨W, hx, s, rfl⟩ := M.presheaf.exists_germ_eq m
  have he := Classical.choose_spec (Scheme.Modules.exists_tensorPullback_stalk_iso k x)
    M W hx s
  have hi := congrArg (fun t ↦
    (Classical.choose (Scheme.Modules.exists_tensorPullback_stalk_iso k x)).inv.app M t) he
  have hunit :
      (Classical.choose (Scheme.Modules.exists_tensorPullback_stalk_iso k x)).inv.app M
          ((1 : X.presheaf.stalk x) ⊗ₜ[_, (k.stalkMap x).hom]
            (M.presheaf.germ W (k x) hx s)) =
        ((Scheme.Modules.tensorPullback k).obj M).presheaf.germ (k ⁻¹ᵁ W) x hx
          ((Classical.choose
            (Scheme.Modules.exists_tensorPullbackAdjunction k)).unit.app M |>.app W s) := by
    simp only [← ModuleCat.comp_apply, Iso.hom_inv_id_app, ModuleCat.id_apply] at hi
    exact hi.symm
  rw [hunit]
  change _ = ((Scheme.Modules.tensorPullback k).obj M).presheaf.stalkPushforward
    AddCommGrpCat.{u} k.base x
      (((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (k x)).map
        (Scheme.Modules.Hom.mapPresheaf
          ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction k)).unit.app M)))
        (M.presheaf.germ W (k x) hx s))
  have hm := TopCat.Presheaf.stalkFunctor_map_germ_apply W (k x) hx
    (Scheme.Modules.Hom.mapPresheaf
      ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction k)).unit.app M)) s
  have hp := TopCat.Presheaf.stalkPushforward_germ_apply AddCommGrpCat.{u} k.base
    ((Scheme.Modules.tensorPullback k).obj M).presheaf W x hx
    (((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction k)).unit.app M).app W s)
  exact hp.symm.trans (congrArg
    (((Scheme.Modules.tensorPullback k).obj M).presheaf.stalkPushforward
      AddCommGrpCat.{u} k.base x) hm.symm)

private theorem tensor_unit_stalk_cast {X Y : Scheme.{u}} (k : X ⟶ Y) (x : X)
    (M : Y.Modules) (a : Y.presheaf.stalk (k x) →+* X.presheaf.stalk x)
    (ha : a = (k.stalkMap x).hom) (m : M.presheaf.stalk (k x)) :
    (eqToHom (congrArg (fun b ↦ (ModuleCat.extendScalars b).obj
        ((RingedSpace.moduleStalkFunctor Y.toRingedSpace (k x)).obj M)) ha) ≫
      (Classical.choose (Scheme.Modules.exists_tensorPullback_stalk_iso k x)).inv.app M)
        ((1 : X.presheaf.stalk x) ⊗ₜ[Y.presheaf.stalk (k x), a] m) =
      (((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (k x)).map
        (Scheme.Modules.Hom.mapPresheaf
          ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction k)).unit.app M))) ≫
        ((Scheme.Modules.tensorPullback k).obj M).presheaf.stalkPushforward
          AddCommGrpCat.{u} k.base x) m := by
  subst a
  simpa using tensor_unit_stalk k x M m

/-- The degreewise tensor-stalk comparison sends a unit tensor to the pullback unit. -/
private theorem tensorStalkIso_unit
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g) (z : X')
    (P : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (n : ℤ) (m : (stalkComplex g' z P).X n) :
    letI := leftAlgebra f g' z
    letI := rightAlgebra f f' g g' sq z
    (tensorStalkIso f f' g g' sq z P).hom.f n
        ((1 : C z) ⊗ₜ[A g' z, (tensorMap f f' g g' sq z).comp
          (algebraMap (A g' z) (A g' z ⊗[R f g' z] B f' z))] m) =
      (((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (g' z)).map
        (Scheme.Modules.Hom.mapPresheaf
          ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction g')).unit.app
            (P.X n)))) ≫
        ((Scheme.Modules.tensorPullback g').obj (P.X n)).presheaf.stalkPushforward
          AddCommGrpCat.{u} g'.base z) m := by
  let := leftAlgebra f g' z
  let := rightAlgebra f f' g g' sq z
  exact (ConcreteCategory.congr_hom
    (Classical.choose_spec (exists_tensorStalkIso f f' g g' sq z P) n) _).trans
      (tensor_unit_stalk_cast g' z (P.X n) _
        (Classical.choose_spec (exists_tensorMap f f' g g' sq z)).1 m)

private theorem open_coordinate_smul (X : Scheme.{u}) (U : X.Opens) (x : U.toScheme)
    (M : X.Modules) (r : U.toScheme.presheaf.stalk x)
    (m : (RingedSpace.moduleStalkFunctor U.toScheme.toRingedSpace x).obj
      ((schemeOpenRestriction X U).obj M)) :
    let L := RingedSpace.moduleStalkFunctor U.toScheme.toRingedSpace x
    let F := forget₂ (ModuleCat.{u} (U.toScheme.presheaf.stalk x)) AddCommGrpCat.{u}
    let γ := Functor.isoWhiskerRight (Scheme.Modules.overFunctorEquiv U) (L ⋙ F) ≪≫
      Scheme.Modules.restrictStalkNatIso U.ι x
    γ.hom.app M (r • m) = (U.stalkIso x).commRingCatIsoToRingEquiv r •
      (show M.presheaf.stalk x.val from γ.hom.app M m) := by
  dsimp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.comp_map, AddCommGrpCat.comp_apply]
  change (Scheme.Modules.restrictStalkNatIso U.ι x).hom.app M
      (((RingedSpace.moduleStalkFunctor U.toScheme.toRingedSpace x).map
        ((Scheme.Modules.overFunctorEquiv U).hom.app M)) (r • m)) = _
  erw [map_smul, Scheme.restriction_stalk_smul]
  have he : (U.stalkIso x).hom = inv (U.ι.stalkMap x) := by
    apply (cancel_mono (U.ι.stalkMap x)).1
    simpa only [Scheme.Opens.stalkIso_inv, IsIso.inv_hom_id] using
      (U.stalkIso x).hom_inv_id
  change _ = ((U.stalkIso x).hom r) • _
  rw [he]
  rfl

/-- The unit-scalar section-germ generator equation for the pinned comparison.

Expand the tensor-stalk and pinned restriction maps on a section germ. Their
units send the germ to `1 ⊗ s`, and `restrictStalkNatIso` identifies the
restricted germ with the ambient germ. Point transport follows by equality
induction. The linear extension theorem handles the remaining coefficients.
Source: Stacks Project, Tags 0098 and 0096.
(blueprint: lem-pc-open-ordinary-tensor-pure-germ-coordinates-canonical). -/
theorem openOrdinaryTensor_pure_germ_coordinates_canonical
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g)
    (V : S.Opens) (V' : S'.Opens) (hV' : V' ≤ g ⁻¹ᵁ V)
    (j : (f' ⁻¹ᵁ V').toScheme ⟶ (f ⁻¹ᵁ V).toScheme)
    (hj : j ≫ (f ⁻¹ᵁ V).ι = (f' ⁻¹ᵁ V').ι ≫ g')
    (sq₀ : IsPullback j (f' ∣_ V') (f ∣_ V) (g.resLE V V' hV'))
    (P : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (z : (f' ⁻¹ᵁ V').toScheme) :
    letI : (schemeOpenRestriction X (f ⁻¹ᵁ V)).Additive :=
      schemeOpenRestriction_additive X (f ⁻¹ᵁ V)
    letI : (schemeOpenRestriction X (f ⁻¹ᵁ V)).PreservesZeroMorphisms :=
      Functor.preservesZeroMorphisms_of_additive _
    let Q₀ := ((schemeOpenRestriction X (f ⁻¹ᵁ V)).mapHomologicalComplex (.up ℤ)).obj P
    let R₀ := R (f ∣_ V) j z
    let A₀ := A j z
    let B₀ := B (f' ∣_ V') z
    let C₀ := C z
    let R₁ := R f g' z.val
    let A₁ := A g' z.val
    let B₁ := B f' z.val
    let C₁ := C z.val
    letI := leftAlgebra (f ∣_ V) j z
    letI := rightAlgebra (f ∣_ V) (f' ∣_ V') (g.resLE V V' hV') j sq₀ z
    letI := (tensorMap (f ∣_ V) (f' ∣_ V') (g.resLE V V' hV') j sq₀ z).toAlgebra
    letI := leftAlgebra f g' z.val
    letI := rightAlgebra f f' g g' sq z.val
    letI := (tensorMap f f' g g' sq z.val).toAlgebra
    let K₀ := stalkComplex j z Q₀
    let K := stalkComplex g' z.val P
    let T₀ := tensorComplex (f ∣_ V) (f' ∣_ V') (g.resLE V V' hV') j sq₀ z Q₀
    let T := tensorComplex f f' g g' sq z.val P
    let F₀ := forget₂ (ModuleCat.{u} C₀) AddCommGrpCat.{u}
    let F := forget₂ (ModuleCat.{u} C₁) AddCommGrpCat.{u}
    let L₀ := RingedSpace.moduleStalkFunctor (f' ⁻¹ᵁ V').toScheme.toRingedSpace z
    let γ := Functor.isoWhiskerRight (Scheme.Modules.overFunctorEquiv (f' ⁻¹ᵁ V'))
        (L₀ ⋙ F₀) ≪≫ Scheme.Modules.restrictStalkNatIso (f' ⁻¹ᵁ V').ι z
    let Lᵢ := RingedSpace.moduleStalkFunctor (f ⁻¹ᵁ V).toScheme.toRingedSpace (j z)
    let Fᵢ := forget₂ (ModuleCat.{u} A₀) AddCommGrpCat.{u}
    let γᵢ := Functor.isoWhiskerRight (Scheme.Modules.overFunctorEquiv (f ⁻¹ᵁ V))
        (Lᵢ ⋙ Fᵢ) ≪≫ Scheme.Modules.restrictStalkNatIso (f ⁻¹ᵁ V).ι (j z)
    let hx := congrArg (fun k : (f' ⁻¹ᵁ V').toScheme ⟶ X => k z) hj
    ∀ (n : ℤ) (q : K₀.X n),
      F.map ((tensorStalkIso f f' g g' sq z.val P).hom.f n)
              (((f' ⁻¹ᵁ V').stalkIso z).commRingCatIsoToRingEquiv 1 ⊗ₜ[A₁,
                (algebraMap (A₁ ⊗[R₁] B₁) C₁).comp
                (algebraMap A₁ (A₁ ⊗[R₁] B₁))] (show K.X n from
                  (γᵢ.hom.app (P.X n) ≫
                    ((show X.Modules from P.X n).presheaf.stalkCongr (.of_eq hx)).hom) q)) =
            (F₀.map ((tensorStalkIso (f ∣_ V) (f' ∣_ V')
                (g.resLE V V' hV') j sq₀ z Q₀).hom.f n) ≫
              F₀.map (L₀.map ((openPinnedTensorRestrictionIso g'
                (f ⁻¹ᵁ V) (f' ⁻¹ᵁ V') j hj).inv.app (P.X n))) ≫
              γ.hom.app ((Scheme.Modules.tensorPullback g').obj (P.X n)))
                ((1 : C₀) ⊗ₜ[A₀,(algebraMap (A₀ ⊗[R₀] B₀) C₀).comp
                  (algebraMap A₀ (A₀ ⊗[R₀] B₀))] q) := by
  intro Q₀ R₀ A₀ B₀ C₀ R₁ A₁ B₁ C₁ K₀ K T₀ T F₀ F L₀ γ Lᵢ Fᵢ γᵢ hx n q
  dsimp only [Scheme.Modules, Scheme.ringCatSheaf] at *
  let := leftAlgebra (f ∣_ V) j z
  let := rightAlgebra (f ∣_ V) (f' ∣_ V') (g.resLE V V' hV') j sq₀ z
  let := (tensorMap (f ∣_ V) (f' ∣_ V') (g.resLE V V' hV') j sq₀ z).toAlgebra
  let := leftAlgebra f g' z.val
  let := rightAlgebra f f' g g' sq z.val
  let := (tensorMap f f' g g' sq z.val).toAlgebra
  simp only [map_one]
  let m : K.X n := (γᵢ.hom.app (P.X n) ≫
    ((show X.Modules from P.X n).presheaf.stalkCongr (.of_eq hx)).hom) q
  let d := L₀.map ((openPinnedTensorRestrictionIso g'
    (f ⁻¹ᵁ V) (f' ⁻¹ᵁ V') j hj).inv.app (P.X n))
  let δ := γ.hom.app ((Scheme.Modules.tensorPullback g').obj (P.X n))
  have h₁ := tensorStalkIso_unit f f' g g' sq z.val P n m
  have h₀ := tensorStalkIso_unit (f ∣_ V) (f' ∣_ V') (g.resLE V V' hV') j sq₀ z Q₀ n q
  have hunit := ConcreteCategory.congr_hom
    (openPinnedTensorRestriction_stalk_unit g' (f ⁻¹ᵁ V) (f' ⁻¹ᵁ V') j hj (P.X n) z) q
  exact h₁.trans (hunit.trans (congrArg (fun t ↦ δ (d t)) h₀.symm))


-- Explicit stalk and tensor module coercions require additional definitional checks.
/-- Scalar extension of the canonical unit-scalar pinned comparison equation.

Apply `openOrdinaryTensor_pure_germ_coordinates_canonical` in degree `n` to `q`,
then multiply its equality by the canonical output stalk scalar `e c`.
`ModuleCat.ExtendScalars.smul_tmul` and `mul_one` identify the pure tensors
`c ⊗ q` and `e c ⊗ q` with scalar multiples of the corresponding unit tensors.
The two tensor-stalk components and the stalk map of the inverse pinned
restriction comparison preserve scalars by `map_smul`. The output additive
coordinate preserves scalar multiplication over `e` by `open_coordinate_smul`:
its overFunctorEquiv component is linear, and its restrictStalkNatIso component
is semilinear over the inverse inclusion stalk map by the existing private
`Scheme.restriction_stalk_smul` from `OpenModuleStalkRestrictionComparison`,
made available to this proof through `import all`.
`Scheme.Opens.stalkIso_inv` identifies that inverse map with the canonical
output ring equivalence. These identities transform the scalar multiple of the
canonical equation into the displayed arbitrary-scalar equation. No additional
hypothesis on the coefficient, degree or stalk element is needed.
Source: Stacks Project, Tags 0098 and 0096.
(blueprint: lem-pc-open-ordinary-tensor-pure-germ-coordinates-linear-extension). -/
theorem openOrdinaryTensor_pure_germ_coordinates_linear_extension
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g)
    (V : S.Opens) (V' : S'.Opens) (hV' : V' ≤ g ⁻¹ᵁ V)
    (j : (f' ⁻¹ᵁ V').toScheme ⟶ (f ⁻¹ᵁ V).toScheme)
    (hj : j ≫ (f ⁻¹ᵁ V).ι = (f' ⁻¹ᵁ V').ι ≫ g')
    (sq₀ : IsPullback j (f' ∣_ V') (f ∣_ V) (g.resLE V V' hV'))
    (P : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (z : (f' ⁻¹ᵁ V').toScheme) :
    letI : (schemeOpenRestriction X (f ⁻¹ᵁ V)).Additive :=
      schemeOpenRestriction_additive X (f ⁻¹ᵁ V)
    letI : (schemeOpenRestriction X (f ⁻¹ᵁ V)).PreservesZeroMorphisms :=
      Functor.preservesZeroMorphisms_of_additive _
    let Q₀ := ((schemeOpenRestriction X (f ⁻¹ᵁ V)).mapHomologicalComplex (.up ℤ)).obj P
    let R₀ := R (f ∣_ V) j z
    let A₀ := A j z
    let B₀ := B (f' ∣_ V') z
    let C₀ := C z
    let R₁ := R f g' z.val
    let A₁ := A g' z.val
    let B₁ := B f' z.val
    let C₁ := C z.val
    letI := leftAlgebra (f ∣_ V) j z
    letI := rightAlgebra (f ∣_ V) (f' ∣_ V') (g.resLE V V' hV') j sq₀ z
    letI := (tensorMap (f ∣_ V) (f' ∣_ V') (g.resLE V V' hV') j sq₀ z).toAlgebra
    letI := leftAlgebra f g' z.val
    letI := rightAlgebra f f' g g' sq z.val
    letI := (tensorMap f f' g g' sq z.val).toAlgebra
    let K₀ := stalkComplex j z Q₀
    let K := stalkComplex g' z.val P
    let T₀ := tensorComplex (f ∣_ V) (f' ∣_ V') (g.resLE V V' hV') j sq₀ z Q₀
    let T := tensorComplex f f' g g' sq z.val P
    let F₀ := forget₂ (ModuleCat.{u} C₀) AddCommGrpCat.{u}
    let F := forget₂ (ModuleCat.{u} C₁) AddCommGrpCat.{u}
    let L₀ := RingedSpace.moduleStalkFunctor (f' ⁻¹ᵁ V').toScheme.toRingedSpace z
    let γ := Functor.isoWhiskerRight (Scheme.Modules.overFunctorEquiv (f' ⁻¹ᵁ V'))
        (L₀ ⋙ F₀) ≪≫ Scheme.Modules.restrictStalkNatIso (f' ⁻¹ᵁ V').ι z
    let Lᵢ := RingedSpace.moduleStalkFunctor (f ⁻¹ᵁ V).toScheme.toRingedSpace (j z)
    let Fᵢ := forget₂ (ModuleCat.{u} A₀) AddCommGrpCat.{u}
    let γᵢ := Functor.isoWhiskerRight (Scheme.Modules.overFunctorEquiv (f ⁻¹ᵁ V))
        (Lᵢ ⋙ Fᵢ) ≪≫ Scheme.Modules.restrictStalkNatIso (f ⁻¹ᵁ V).ι (j z)
    let hx := congrArg (fun k : (f' ⁻¹ᵁ V').toScheme ⟶ X => k z) hj
    ∀ (n : ℤ) (c : C₀) (q : K₀.X n),
          F.map ((tensorStalkIso f f' g g' sq z.val P).hom.f n)
              (((f' ⁻¹ᵁ V').stalkIso z).commRingCatIsoToRingEquiv c ⊗ₜ[A₁,
                (algebraMap (A₁ ⊗[R₁] B₁) C₁).comp
                (algebraMap A₁ (A₁ ⊗[R₁] B₁))] (show K.X n from
                  (γᵢ.hom.app (P.X n) ≫
                    ((show X.Modules from P.X n).presheaf.stalkCongr (.of_eq hx)).hom) q)) =
            (F₀.map ((tensorStalkIso (f ∣_ V) (f' ∣_ V')
                (g.resLE V V' hV') j sq₀ z Q₀).hom.f n) ≫
              F₀.map (L₀.map ((openPinnedTensorRestrictionIso g'
                (f ⁻¹ᵁ V) (f' ⁻¹ᵁ V') j hj).inv.app (P.X n))) ≫
              γ.hom.app ((Scheme.Modules.tensorPullback g').obj (P.X n)))
                (c ⊗ₜ[A₀,(algebraMap (A₀ ⊗[R₀] B₀) C₀).comp
                  (algebraMap A₀ (A₀ ⊗[R₀] B₀))] q) := by
  intro Q₀ R₀ A₀ B₀ C₀ R₁ A₁ B₁ C₁ K₀ K T₀ T F₀ F L₀ γ Lᵢ Fᵢ γᵢ hx n c q
  let := leftAlgebra (f ∣_ V) j z
  let := rightAlgebra (f ∣_ V) (f' ∣_ V') (g.resLE V V' hV') j sq₀ z
  let := (tensorMap (f ∣_ V) (f' ∣_ V') (g.resLE V V' hV') j sq₀ z).toAlgebra
  let := leftAlgebra f g' z.val
  let := rightAlgebra f f' g g' sq z.val
  let := (tensorMap f f' g g' sq z.val).toAlgebra
  let φ₀ := (algebraMap (A₀ ⊗[R₀] B₀) C₀).comp
    (algebraMap A₀ (A₀ ⊗[R₀] B₀))
  let φ₁ := (algebraMap (A₁ ⊗[R₁] B₁) C₁).comp
    (algebraMap A₁ (A₁ ⊗[R₁] B₁))
  let e := ((f' ⁻¹ᵁ V').stalkIso z).commRingCatIsoToRingEquiv
  let a := (tensorStalkIso f f' g g' sq z.val P).hom.f n
  let b := (tensorStalkIso (f ∣_ V) (f' ∣_ V')
    (g.resLE V V' hV') j sq₀ z Q₀).hom.f n
  let d := L₀.map ((openPinnedTensorRestrictionIso g'
    (f ⁻¹ᵁ V) (f' ⁻¹ᵁ V') j hj).inv.app (P.X n))
  let m : K.X n := (γᵢ.hom.app (P.X n) ≫
    ((show X.Modules from P.X n).presheaf.stalkCongr (.of_eq hx)).hom) q
  let δ := γ.hom.app ((Scheme.Modules.tensorPullback g').obj (P.X n))
  change a (e c ⊗ₜ[A₁,φ₁] m) = δ (d (b (c ⊗ₜ[A₀,φ₀] q)))
  have h : a (e 1 ⊗ₜ[A₁,φ₁] m) = δ (d (b ((1 : C₀) ⊗ₜ[A₀,φ₀] q))) :=
    openOrdinaryTensor_pure_germ_coordinates_canonical f f' g g' sq
      V V' hV' j hj sq₀ P z n q
  have hc := congrArg (fun t ↦ e c • (show
    ((Scheme.Modules.tensorPullback g').obj (P.X n)).presheaf.stalk z.val from t)) h
  have hγ := open_coordinate_smul X' (f' ⁻¹ᵁ V') z
    ((Scheme.Modules.tensorPullback g').obj (P.X n)) c (d (b ((1 : C₀) ⊗ₜ[A₀,φ₀] q)))
  have t₀ : c ⊗ₜ[A₀,φ₀] q = c • ((1 : C₀) ⊗ₜ[A₀,φ₀] q : T₀.X n) := by
    rw [ModuleCat.ExtendScalars.smul_tmul, mul_one]
  have t₁ : e c ⊗ₜ[A₁,φ₁] m = e c • ((1 : C₁) ⊗ₜ[A₁,φ₁] m : T.X n) := by
    rw [ModuleCat.ExtendScalars.smul_tmul, mul_one]
  rw [t₀, t₁, a.hom.map_smul, b.hom.map_smul, d.hom.map_smul]
  rw [hγ]
  simpa only [map_one] using hc


end AlgebraicGeometry
