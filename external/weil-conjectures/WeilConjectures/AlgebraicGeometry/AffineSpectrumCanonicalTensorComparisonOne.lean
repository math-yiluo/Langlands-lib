/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.AffineSpectrumCanonicalStalkRingCoordinates
public import WeilConjectures.AlgebraicGeometry.IsoPullbackStalkCohomology
public import WeilConjectures.AlgebraicGeometry.TensorPullbackCompositionIso
public import WeilConjectures.AlgebraicGeometry.AffineSpectrumCanonicalStalkComplexIso
/-! # The canonical affine-spectrum comparison on coefficient-one tensors -/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ChangeOfRings
noncomputable section
namespace AlgebraicGeometry.SingleComplexBaseChange

-- The restriction and tensor comparison identify several concrete stalk functors.
private theorem additive_one {Y Z : Scheme.{u}} (j : Y ⟶ Z) [IsIso j]
    (y : Y) (M : Z.Modules)
    (x : (RingedSpace.moduleStalkFunctor Z.toRingedSpace (j y)).obj M) :
    (isoPullbackAdditiveStalkIso j y).hom.app M x =
      (Classical.choose (Scheme.Modules.exists_tensorPullback_stalk_iso j y)).inv.app M
        ((1 : Y.presheaf.stalk y) ⊗ₜ[_, (j.stalkMap y).hom] x) := by
  let e := Classical.choose (Scheme.Modules.exists_tensorPullback_stalk_iso j y)
  have he := Classical.choose_spec (Scheme.Modules.exists_tensorPullback_stalk_iso j y)
  obtain ⟨V, hy, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq M.val.presheaf x
  let t := tensorPullbackRestrictIso j
  let a := isoPullbackAdditiveStalkIso j y
  let unit := (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction j)).unit
  let m := TopCat.Presheaf.germ ((Scheme.Modules.tensorPullback j).obj M).val.presheaf
    (j ⁻¹ᵁ V) y hy ((unit.app M).val.app (Opposite.op V) s)
  have hm : a.inv.app M m = TopCat.Presheaf.germ M.val.presheaf V (j y) hy s := by
    change (Scheme.Modules.restrictStalkNatIso j y).hom.app M
      ((RingedSpace.moduleStalkFunctor Y.toRingedSpace y).map (t.hom.app M) m) = _
    have hmap := TopCat.Presheaf.stalkFunctor_map_germ_apply (j ⁻¹ᵁ V) y hy
      ((PresheafOfModules.toPresheaf _).map (t.hom.app M).val)
      ((unit.app M).val.app (Opposite.op V) s)
    change (RingedSpace.moduleStalkFunctor Y.toRingedSpace y).map (t.hom.app M) m =
      TopCat.Presheaf.germ ((Scheme.Modules.restrictFunctor j).obj M).val.presheaf
        (j ⁻¹ᵁ V) y hy ((t.hom.app M).val.app (Opposite.op (j ⁻¹ᵁ V))
          ((unit.app M).val.app (Opposite.op V) s)) at hmap
    rw [hmap]
    have hu := Adjunction.unit_leftAdjointUniq_hom_app
      (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction j))
      (Scheme.Modules.restrictAdjunction j) M
    have hsec := congrArg (fun v ↦ v.val.app (Opposite.op V) s) hu
    change (t.hom.app M).val.app (Opposite.op (j ⁻¹ᵁ V)) ((unit.app M).val.app (Opposite.op V) s) =
      ((Scheme.Modules.restrictAdjunction j).unit.app M).val.app (Opposite.op V) s at hsec
    rw [hsec]
    have hr := ConcreteCategory.congr_hom
      (Scheme.Modules.germ_restrictStalkNatIso_hom_app j y M hy)
      (((Scheme.Modules.restrictAdjunction j).unit.app M).val.app (Opposite.op V) s)
    refine hr.trans ?_
    change TopCat.Presheaf.germ M.val.presheaf (j ''ᵁ (j ⁻¹ᵁ V)) (j y) _
      (M.val.presheaf.map (homOfLE (j.image_preimage_le V)).op s) = _
    exact TopCat.Presheaf.germ_res_apply M.val.presheaf
      (homOfLE (j.image_preimage_le V)) (j y) _ s
  have ha := congrArg (fun v ↦ a.hom.app M v) hm
  simp only [← NatIso.inv_hom_app, IsIso.inv_hom_id_apply] at ha
  have hh := congrArg (fun v ↦ e.inv.app M v) (he M V hy s)
  change (e.app M).inv ((e.app M).hom m) = _ at hh
  simp only [Iso.hom_inv_id_apply] at hh
  exact ha.symm.trans hh

-- The composition mate identifies the successive adjunction-unit germs.
private theorem composition_one {X Y Z : Scheme.{u}}
    (g : Z ⟶ Y) (h : Y ⟶ X) (k : Z ⟶ X) (w : g ≫ h = k)
    (z : Z) (M : X.Modules) (x : ↑(TopCat.Presheaf.stalk (C := Ab.{u}) (X := X.toTopCat)
      M.val.presheaf (h (g z)))) :
    let pk := Classical.choose (Scheme.Modules.exists_tensorPullback_stalk_iso k z)
    let ph := Classical.choose (Scheme.Modules.exists_tensorPullback_stalk_iso h (g z))
    let pg := Classical.choose (Scheme.Modules.exists_tensorPullback_stalk_iso g z)
    let hx : h (g z) = k z := congrArg (fun a : Z ⟶ X ↦ a z) w
    (RingedSpace.moduleStalkFunctor Z.toRingedSpace z).map
        ((Scheme.Modules.tensorPullbackCompositionIso g h k w).hom.app M)
        (pk.inv.app M ((1 : Z.presheaf.stalk z) ⊗ₜ[_, (k.stalkMap z).hom]
          ((eqToHom (congrArg
            (TopCat.Presheaf.stalk (C := Ab.{u}) (X := X.toTopCat)
              M.val.presheaf) hx)) x))) =
      pg.inv.app ((Scheme.Modules.tensorPullback h).obj M)
        ((1 : Z.presheaf.stalk z) ⊗ₜ[_, (g.stalkMap z).hom]
          (ph.inv.app M ((1 : Y.presheaf.stalk (g z)) ⊗ₜ[_, (h.stalkMap (g z)).hom] x))) := by
  subst k
  dsimp only
  let pgh := Classical.choose
    (Scheme.Modules.exists_tensorPullback_stalk_iso (g ≫ h) z)
  let ph := Classical.choose (Scheme.Modules.exists_tensorPullback_stalk_iso h (g z))
  let pg := Classical.choose (Scheme.Modules.exists_tensorPullback_stalk_iso g z)
  let adjh := Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction h)
  let adjg := Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction g)
  let adjgh := Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction (g ≫ h))
  have hpf : Scheme.Modules.pushforwardComp g h ≪≫
      Scheme.Modules.pushforwardCongr (rfl : g ≫ h = g ≫ h) =
      Scheme.Modules.pushforwardComp g h := by
    ext N U
    simp
  have hu := unit_conjugateEquiv_symm (adjh.comp adjg) adjgh
    (Scheme.Modules.pushforwardComp g h).hom M
  have hu' : (adjh.comp adjg).unit.app M ≫
      (Scheme.Modules.pushforwardComp g h).hom.app _ =
      adjgh.unit.app M ≫ (Scheme.Modules.pushforward (g ≫ h)).map
        ((Scheme.Modules.tensorPullbackCompositionIso g h (g ≫ h) rfl).hom.app M) := by
    simpa only [Scheme.Modules.tensorPullbackCompositionIso, hpf, conjugateIsoEquiv,
      Equiv.symm, Equiv.coe_fn_mk, adjh, adjg, adjgh] using hu
  obtain ⟨V, hz, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq M.val.presheaf x
  have hsec := congrArg (fun v ↦ v.val.app (Opposite.op V) s) hu'
  have hsec' :
      ((Scheme.Modules.tensorPullbackCompositionIso g h (g ≫ h) rfl).hom.app M).val.app
        (Opposite.op ((g ≫ h) ⁻¹ᵁ V)) ((adjgh.unit.app M).val.app (Opposite.op V) s) =
      (adjg.unit.app ((Scheme.Modules.tensorPullback h).obj M)).val.app
        (Opposite.op (h ⁻¹ᵁ V)) ((adjh.unit.app M).val.app (Opposite.op V) s) := by
    rw [Adjunction.comp_unit_app] at hsec
    exact hsec.symm
  have hgerm (f : Z ⟶ X) (hx : f z ∈ V) :
      (Classical.choose (Scheme.Modules.exists_tensorPullback_stalk_iso f z)).inv.app M
        ((1 : Z.presheaf.stalk z) ⊗ₜ[_, (f.stalkMap z).hom]
          (TopCat.Presheaf.germ M.val.presheaf V (f z) hx s)) =
      TopCat.Presheaf.germ ((Scheme.Modules.tensorPullback f).obj M).val.presheaf
        (f ⁻¹ᵁ V) z hx
        (((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction f)).unit.app
          M).val.app (Opposite.op V) s) := by
    let pf := Classical.choose (Scheme.Modules.exists_tensorPullback_stalk_iso f z)
    have hp := congrArg (fun t ↦ pf.inv.app M t)
      (Classical.choose_spec (Scheme.Modules.exists_tensorPullback_stalk_iso f z)
        M V hx s)
    change (pf.app M).inv ((pf.app M).hom _) = _ at hp
    simpa only [Iso.hom_inv_id_apply] using hp.symm
  simp only [eqToHom_refl]
  change (RingedSpace.moduleStalkFunctor Z.toRingedSpace z).map
    ((Scheme.Modules.tensorPullbackCompositionIso g h (g ≫ h) rfl).hom.app M)
    (pgh.inv.app M ((1 : Z.presheaf.stalk z) ⊗ₜ[_, ((g ≫ h).stalkMap z).hom]
      (TopCat.Presheaf.germ M.val.presheaf V (h (g z)) hz s))) = _
  erw [hgerm (g ≫ h) hz]
  have hh := congrArg (fun t ↦ ph.inv.app M t)
    (Classical.choose_spec (Scheme.Modules.exists_tensorPullback_stalk_iso h (g z))
      M V hz s)
  change (ph.app M).inv ((ph.app M).hom _) = _ at hh
  simp only [Iso.hom_inv_id_apply] at hh
  erw [← hh]
  have hg := congrArg (fun t ↦ pg.inv.app ((Scheme.Modules.tensorPullback h).obj M) t)
    (Classical.choose_spec (Scheme.Modules.exists_tensorPullback_stalk_iso g z)
      ((Scheme.Modules.tensorPullback h).obj M) (h ⁻¹ᵁ V) hz
      ((adjh.unit.app M).val.app (Opposite.op V) s))
  change (pg.app _).inv ((pg.app _).hom _) = _ at hg
  simp only [Iso.hom_inv_id_apply] at hg
  erw [← hg]
  have hmap := TopCat.Presheaf.stalkFunctor_map_germ_apply ((g ≫ h) ⁻¹ᵁ V) z hz
    ((PresheafOfModules.toPresheaf _).map
      ((Scheme.Modules.tensorPullbackCompositionIso g h (g ≫ h) rfl).hom.app M).val)
    ((adjgh.unit.app M).val.app (Opposite.op V) s)
  exact hmap.trans (congrArg
    (TopCat.Presheaf.germ
      ((Scheme.Modules.tensorPullback g).obj ((Scheme.Modules.tensorPullback h).obj M)).val.presheaf
      ((g ≫ h) ⁻¹ᵁ V) z hz) hsec')

-- Comparing source-point transports reduces the concrete stalk functors.
private theorem square_one {X X' Z Z' : Scheme.{u}}
    (g' : X' ⟶ X) (j : Z' ⟶ X') (a : Z ⟶ X) (g0 : Z' ⟶ Z)
    (w : j ≫ g' = g0 ≫ a) (z : Z') (M : X.Modules)
    (x : ↑(TopCat.Presheaf.stalk (C := Ab.{u}) (X := X.toTopCat)
      M.val.presheaf (g' (j z)))) :
    let pg := Classical.choose (Scheme.Modules.exists_tensorPullback_stalk_iso g' (j z))
    let pj := Classical.choose (Scheme.Modules.exists_tensorPullback_stalk_iso j z)
    let pa := Classical.choose (Scheme.Modules.exists_tensorPullback_stalk_iso a (g0 z))
    let p0 := Classical.choose (Scheme.Modules.exists_tensorPullback_stalk_iso g0 z)
    let hx : g' (j z) = a (g0 z) := congrArg (fun b : Z' ⟶ X ↦ b z) w
    let alpha :=
      (Scheme.Modules.tensorPullbackCompositionIso g0 a (g0 ≫ a) rfl).symm ≪≫
        Scheme.Modules.tensorPullbackCompositionIso j g' (g0 ≫ a) w
    (RingedSpace.moduleStalkFunctor Z'.toRingedSpace z).map (alpha.inv.app M)
      (pj.inv.app ((Scheme.Modules.tensorPullback g').obj M)
        ((1 : Z'.presheaf.stalk z) ⊗ₜ[_, (j.stalkMap z).hom]
          (pg.inv.app M ((1 : X'.presheaf.stalk (j z)) ⊗ₜ[_, (g'.stalkMap (j z)).hom] x)))) =
      p0.inv.app ((Scheme.Modules.tensorPullback a).obj M)
        ((1 : Z'.presheaf.stalk z) ⊗ₜ[_, (g0.stalkMap z).hom]
          (pa.inv.app M ((1 : Z.presheaf.stalk (g0 z)) ⊗ₜ[_, (a.stalkMap (g0 z)).hom]
            ((eqToHom (congrArg
              (TopCat.Presheaf.stalk (C := Ab.{u}) (X := X.toTopCat)
                M.val.presheaf) hx)) x)))) := by
  dsimp only
  let S := RingedSpace.moduleStalkFunctor Z'.toRingedSpace z
  let c1 := Scheme.Modules.tensorPullbackCompositionIso g0 a (g0 ≫ a) rfl
  let c2 := Scheme.Modules.tensorPullbackCompositionIso j g' (g0 ≫ a) w
  have h1 := composition_one j g' (g0 ≫ a) w z M x
  let hx : g' (j z) = a (g0 z) := congrArg (fun b : Z' ⟶ X ↦ b z) w
  let x0 := (eqToHom (congrArg
    (TopCat.Presheaf.stalk (C := Ab.{u}) (X := X.toTopCat) M.val.presheaf) hx)) x
  have h2 := composition_one g0 a (g0 ≫ a) rfl z M x0
  dsimp only at h1 h2
  have hi := congrArg (fun t ↦ S.map (c2.inv.app M) t) h1
  change ((S.mapIso (c2.app M)).inv) (((S.mapIso (c2.app M)).hom) _) = _ at hi
  simp only [Iso.hom_inv_id_apply] at hi
  have hi' := congrArg (fun t ↦ S.map (c1.hom.app M) t) hi.symm
  change S.map (c1.hom.app M) (S.map (c2.inv.app M) _) = _ at hi'
  change S.map ((c2.inv.app M) ≫ (c1.hom.app M)) _ = _
  rw [Functor.map_comp]
  change S.map (c1.hom.app M) (S.map (c2.inv.app M) _) = _
  refine hi'.trans ?_
  convert h2 using 1
  simp only [eqToHom_refl]
  rfl

-- Transporting the scalar map preserves the underlying pure tensor.
private theorem extendScalars_transport_one
    {R S : Type u} [CommRing R] [CommRing S]
    (phi psi : R →+* S) (h : phi = psi) (M : ModuleCat.{u} R) (x : M) :
    (eqToHom (congrArg (fun a : R →+* S ↦ (ModuleCat.extendScalars a).obj M) h))
      ((1 : S) ⊗ₜ[R, phi] x) = (1 : S) ⊗ₜ[R, psi] x := by
  subst psi
  rfl

-- A cast changing only the restriction-of-scalars map preserves component values.
private theorem restrictScalarsIso_cast_apply
    {R S : Type u} [CommRing R] [CommRing S]
    (phi psi : R →+* S) (h : phi = psi)
    (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (Q : CochainComplex (ModuleCat.{u} S) ℤ)
    (q : P ≅ ((ModuleCat.restrictScalars phi).mapHomologicalComplex (.up ℤ)).obj Q)
    (e : (P ≅ ((ModuleCat.restrictScalars phi).mapHomologicalComplex (.up ℤ)).obj Q) =
      (P ≅ ((ModuleCat.restrictScalars psi).mapHomologicalComplex (.up ℤ)).obj Q))
    (k : ℤ) (x : P.X k) :
    (cast e q).hom.f k x = q.hom.f k x := by
  subst psi
  rfl

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

-- Identifying the tensor model with stalk extension reduces scalar-change functors.
private theorem tensorStalkIso_one
    {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g) (z : X')
    (P : CochainComplex X.Modules ℤ) (k : ℤ) (x : (stalkComplex g' z P).X k) :
    let := leftAlgebra f g' z
    let := rightAlgebra f f' g g' sq z
    (tensorStalkIso f f' g g' sq z P).hom.f k
      ((1 : C z) ⊗ₜ[A g' z, (tensorMap f f' g g' sq z).comp
        (algebraMap (A g' z) (A g' z ⊗[R f g' z] B f' z))] x) =
      (Classical.choose (Scheme.Modules.exists_tensorPullback_stalk_iso g' z)).inv.app
        (P.X k) ((1 : X'.presheaf.stalk z) ⊗ₜ[_, (g'.stalkMap z).hom] x) := by
  dsimp only
  let := leftAlgebra f g' z
  let := rightAlgebra f f' g g' sq z
  change (Classical.choose (exists_tensorStalkIso f f' g g' sq z P)).hom.f k _ = _
  erw [Classical.choose_spec (exists_tensorStalkIso f f' g g' sq z P) k]
  exact congrArg
    (fun t ↦ (Classical.choose (Scheme.Modules.exists_tensorPullback_stalk_iso g' z)).inv.app
      (P.X k) t)
    (extendScalars_transport_one _ _
      (Classical.choose_spec (exists_tensorMap f f' g g' sq z)).1
      ((RingedSpace.moduleStalkFunctor X.toRingedSpace (g' z)).obj (P.X k)) x)

-- The extension-restriction unit is lifted through several complex functor isomorphisms.
private theorem canonicalSpectrumStalkComplexIso_one
    (X : Scheme.{u}) [IsAffine X] (x : X) (y : Spec Γ(X, ⊤))
    (h : x = X.isoSpec.inv y) (P : CochainComplex X.Modules ℤ)
    (k : ℤ) (t : (RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj (P.X k)) :
    (canonicalSpectrumStalkComplexIso X x y h P).hom.f k t =
      (Classical.choose
        (Scheme.Modules.exists_tensorPullback_stalk_iso X.isoSpec.inv y)).inv.app (P.X k)
        ((1 : (Spec Γ(X, ⊤)).presheaf.stalk y) ⊗ₜ[_, (X.isoSpec.inv.stalkMap y).hom]
          ((eqToHom (congrArg
            (TopCat.Presheaf.stalk (C := Ab.{u}) (X := X.toTopCat)
              (P.X k).val.presheaf) h)) t)) := by
  subst x
  have hr : (X.isoSpec.inv.stalkMap y).hom =
      (canonicalSpectrumStalkEquiv X (X.isoSpec.inv y) y rfl).toRingHom := by
    simp only [canonicalSpectrumStalkEquiv, eqToIso_refl, Iso.refl_trans,
      RingEquiv.toRingHom_eq_coe, Iso.commRingCatIsoToRingEquiv_toRingHom, asIso_hom]
  unfold canonicalSpectrumStalkComplexIso
  -- Apply the cast identity directly, avoiding a rewrite motive for the whole complex.
  refine (restrictScalarsIso_cast_apply _ _ hr _ _
    (isoPullbackModuleStalkComplexIso X.isoSpec.inv y P) _ k t).trans ?_
  dsimp [isoPullbackModuleStalkComplexIso]
  rfl

-- The fixed complex and its scalar-change functors require substantial reduction.
/-- The coefficient-one comparison for the canonical input chain coordinates.
Proof: represent x by the germ of a section s of P.X k. The original tensor-stalk
comparison takes 1 tensor x to the germ of the pullback adjunction unit on s.
The additive comparison along j takes this to the germ of its pullback along j:
this follows from restriction-stalk compatibility and adjunction uniqueness.
The inverse of alpha is the mate of the pushforward composition isomorphism.
The composite-adjunction unit identity therefore identifies this successive
pullback-unit germ with the germ obtained by pulling s first along X.isoSpec.inv
and then along Spec.map g'.appTop. By definition, the extension/restriction unit
sends x to 1 tensor x; applying the inverse pullback-stalk comparison yields
canonicalSpectrumStalkComplexIso.hom(x). The spectrum tensor-stalk comparison
sends 1 tensor this element to precisely the preceding germ. Cancel that last
comparison to obtain the asserted coefficient-one equation. Stalk elements all
have section-germ representatives, so this establishes the equation for all x.
The mapHomologicalComplex composition isomorphisms have identity components and
do not alter this calculation. Zero modules and empty spectra cause no exception.
Source: Stacks Project, Tags 0098, 0096, and 0DJ8.
(blueprint: lem-pc-affine-spectrum-canonical-tensor-comparison-one). -/
theorem canonicalSpectrum_tensor_comparison_one
    {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g)
    [IsAffine X] [IsAffine X'] [IsAffine S] [IsAffine S']
    (sq0 : IsPullback (Spec.map g'.appTop) (Spec.map f'.appTop)
      (Spec.map f.appTop) (Spec.map g.appTop))
    (z0 : Spec Γ(X', ⊤))
    (P : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :
    let z := X'.isoSpec.inv z0
    let P0 := ((Scheme.Modules.tensorPullback X.isoSpec.inv).mapHomologicalComplex
      (.up ℤ)).obj P
    letI := leftAlgebra f g' z
    letI := rightAlgebra f f' g g' sq z
    letI := (tensorMap f f' g g' sq z).toAlgebra
    letI := HasDerivedCategory.standard (ModuleCat.{u} (R f g' z))
    letI := HasDerivedCategory.standard (ModuleCat.{u} (B f' z))
    letI := leftAlgebra (Spec.map f.appTop) (Spec.map g'.appTop) z0
    letI := rightAlgebra (Spec.map f.appTop) (Spec.map f'.appTop)
      (Spec.map g.appTop) (Spec.map g'.appTop) sq0 z0
    letI := (tensorMap (Spec.map f.appTop) (Spec.map f'.appTop)
      (Spec.map g.appTop) (Spec.map g'.appTop) sq0 z0).toAlgebra
    letI := HasDerivedCategory.standard
      (ModuleCat.{u} (R (Spec.map f.appTop) (Spec.map g'.appTop) z0))
    letI := HasDerivedCategory.standard (ModuleCat.{u} (B (Spec.map f'.appTop) z0))
    let R0 := R (Spec.map f.appTop) (Spec.map g'.appTop) z0
    let A0 := A (Spec.map g'.appTop) z0
    let B0 := B (Spec.map f'.appTop) z0
    let Q := stalkComplex g' z P
    let Q0 := stalkComplex (Spec.map g'.appTop) z0 P0
    let H :=
      let z := X'.isoSpec.inv z0
      let P0 := ((Scheme.Modules.tensorPullback X.isoSpec.inv).mapHomologicalComplex
        (.up ℤ)).obj P
      let Pg := ((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj P
      let j := X'.isoSpec.inv
      let S0 := RingedSpace.moduleStalkFunctor (Spec Γ(X', ⊤)).toRingedSpace z0
      let F := forget₂ (ModuleCat.{u} (X'.presheaf.stalk z)) AddCommGrpCat.{u}
      let F0 := forget₂ (ModuleCat.{u} ((Spec Γ(X', ⊤)).presheaf.stalk z0))
        AddCommGrpCat.{u}
      let alpha := (NatIso.mapHomologicalComplex
        ((Scheme.Modules.tensorPullbackCompositionIso (Spec.map g'.appTop) X.isoSpec.inv
          ((Spec.map g'.appTop) ≫ X.isoSpec.inv) rfl).symm ≪≫
        Scheme.Modules.tensorPullbackCompositionIso j g'
          ((Spec.map g'.appTop) ≫ X.isoSpec.inv) (Scheme.isoSpec_inv_naturality g').symm)
        (.up ℤ)).app P
      let U :=
        letI : (Scheme.Modules.tensorPullback j).Additive := tensorPullbackAdditive j
        letI : (RingedSpace.moduleStalkFunctor (Spec Γ(X', ⊤)).toRingedSpace z0).Additive :=
          comparisonStalkAdditive (Spec Γ(X', ⊤)) z0
        let E := Scheme.Modules.tensorPullback j
        let S := RingedSpace.moduleStalkFunctor (Spec Γ(X', ⊤)).toRingedSpace z0 ⋙
          forget₂ (ModuleCat.{u} ((Spec Γ(X', ⊤)).presheaf.stalk z0)) AddCommGrpCat.{u}
        let SZ := RingedSpace.moduleStalkFunctor X'.toRingedSpace (j z0)
        let F := forget₂ (ModuleCat.{u} (X'.presheaf.stalk (j z0))) AddCommGrpCat.{u}
        let F0 := forget₂ (ModuleCat.{u} ((Spec Γ(X', ⊤)).presheaf.stalk z0)) AddCommGrpCat.{u}
        (Functor.mapHomologicalComplexCompIso (Iso.refl (SZ ⋙ F)) (.up ℤ)).app Pg ≪≫
          (NatIso.mapHomologicalComplex (isoPullbackAdditiveStalkIso j z0) (.up ℤ)).app Pg ≪≫
          (Functor.mapHomologicalComplexCompIso (Iso.refl (E ⋙ S)) (.up ℤ)).symm.app Pg ≪≫
          (Functor.mapHomologicalComplexCompIso
            (Iso.refl (RingedSpace.moduleStalkFunctor (Spec Γ(X', ⊤)).toRingedSpace z0 ⋙ F0))
            (.up ℤ)).symm.app ((E.mapHomologicalComplex (.up ℤ)).obj Pg)
      let H := (F.mapHomologicalComplex (.up ℤ)).mapIso
          (tensorStalkIso f f' g g' sq z P) ≪≫ U ≪≫
        (F0.mapHomologicalComplex (.up ℤ)).mapIso
          ((S0.mapHomologicalComplex (.up ℤ)).mapIso alpha.symm) ≪≫
        (F0.mapHomologicalComplex (.up ℤ)).mapIso
          (tensorStalkIso (Spec.map f.appTop) (Spec.map f'.appTop)
            (Spec.map g.appTop) (Spec.map g'.appTop) sq0 z0 P0).symm
      H
    let hA : g' z = X.isoSpec.inv ((Spec.map g'.appTop) z0) :=
      (congrArg (fun k : Spec Γ(X', ⊤) ⟶ X ↦ k z0)
        (Scheme.isoSpec_inv_naturality g')).symm
    let eA := canonicalSpectrumStalkEquiv X (g' z) ((Spec.map g'.appTop) z0) hA
    let q : Q ≅ ((ModuleCat.restrictScalars.{u} eA.toRingHom).mapHomologicalComplex
      (.up ℤ)).obj Q0 :=
      canonicalSpectrumStalkComplexIso X (g' z) ((Spec.map g'.appTop) z0) hA P
    (∀ (k : ℤ) (x : Q.X k),
        H.hom.f k ((1 : C z) ⊗ₜ[A g' z, (tensorMap f f' g g' sq z).comp
          (algebraMap (A g' z) (A g' z ⊗[R f g' z] B f' z))] x) =
        (1 : C z0) ⊗ₜ[A0, (tensorMap (Spec.map f.appTop) (Spec.map f'.appTop)
          (Spec.map g.appTop) (Spec.map g'.appTop) sq0 z0).comp
          (algebraMap A0 (A0 ⊗[R0] B0))] (show Q0.X k from q.hom.f k x)) := by
  dsimp only
  intro k x
  let z := X'.isoSpec.inv z0
  let P0 := ((Scheme.Modules.tensorPullback X.isoSpec.inv).mapHomologicalComplex
    (.up ℤ)).obj P
  let Pg := ((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj P
  let j := X'.isoSpec.inv
  let S0 := RingedSpace.moduleStalkFunctor (Spec Γ(X', ⊤)).toRingedSpace z0
  let alpha := (NatIso.mapHomologicalComplex
    ((Scheme.Modules.tensorPullbackCompositionIso (Spec.map g'.appTop) X.isoSpec.inv
      ((Spec.map g'.appTop) ≫ X.isoSpec.inv) rfl).symm ≪≫
    Scheme.Modules.tensorPullbackCompositionIso j g'
      ((Spec.map g'.appTop) ≫ X.isoSpec.inv) (Scheme.isoSpec_inv_naturality g').symm)
    (.up ℤ)).app P
  let a := (tensorStalkIso f f' g g' sq z P).hom.f k
  let b := (isoPullbackAdditiveStalkIso j z0).hom.app (Pg.X k)
  let c := (S0.mapHomologicalComplex (.up ℤ)).map alpha.inv |>.f k
  let t0 := tensorStalkIso (Spec.map f.appTop) (Spec.map f'.appTop)
    (Spec.map g.appTop) (Spec.map g'.appTop) sq0 z0 P0
  let hA : g' z = X.isoSpec.inv ((Spec.map g'.appTop) z0) :=
    (congrArg (fun t : Spec Γ(X', ⊤) ⟶ X ↦ t z0)
      (Scheme.isoSpec_inv_naturality g')).symm
  let q := canonicalSpectrumStalkComplexIso X (g' z) ((Spec.map g'.appTop) z0) hA P
  let := leftAlgebra f g' z
  let := rightAlgebra f f' g g' sq z
  let := leftAlgebra (Spec.map f.appTop) (Spec.map g'.appTop) z0
  let := rightAlgebra (Spec.map f.appTop) (Spec.map f'.appTop)
    (Spec.map g.appTop) (Spec.map g'.appTop) sq0 z0
  change t0.inv.f k (c (b (a ((1 : C z) ⊗ₜ[_, _] x)))) =
    (1 : C z0) ⊗ₜ[_, _] (show (stalkComplex (Spec.map g'.appTop) z0 P0).X k from
      q.hom.f k x)
  have ha := tensorStalkIso_one f f' g g' sq z P k x
  have hb := additive_one j z0 (Pg.X k)
    ((Classical.choose (Scheme.Modules.exists_tensorPullback_stalk_iso g' z)).inv.app
      (P.X k) ((1 : C z) ⊗ₜ[_, (g'.stalkMap z).hom] x))
  have hs := square_one g' j X.isoSpec.inv (Spec.map g'.appTop)
    (Scheme.isoSpec_inv_naturality g').symm z0 (P.X k) x
  have hq := canonicalSpectrumStalkComplexIso_one X (g' z)
    ((Spec.map g'.appTop) z0) hA P k x
  have he := tensorStalkIso_one (Spec.map f.appTop) (Spec.map f'.appTop)
    (Spec.map g.appTop) (Spec.map g'.appTop) sq0 z0 P0 k (q.hom.f k x)
  let p0 := Classical.choose
    (Scheme.Modules.exists_tensorPullback_stalk_iso (Spec.map g'.appTop) z0)
  have hf := (congrArg (fun t ↦ c (b t)) ha).trans
    ((congrArg (fun t ↦ c t) hb).trans
      (hs.trans ((congrArg (fun t ↦ p0.inv.app (P0.X k)
        ((1 : C z0) ⊗ₜ[_, ((Spec.map g'.appTop).stalkMap z0).hom] t)) hq).symm.trans
          he.symm)))
  have hi := congrArg (fun t ↦ t0.inv.f k t) hf
  exact hi.trans (Iso.hom_inv_id_apply
    ((HomologicalComplex.eval _ (.up ℤ) k).mapIso t0) _)

end AlgebraicGeometry.SingleComplexBaseChange
