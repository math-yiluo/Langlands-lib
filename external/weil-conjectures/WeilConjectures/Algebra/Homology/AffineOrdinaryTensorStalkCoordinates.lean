/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.AffineTensorPullbackStalkCoordinates

/-! # AffineOrdinaryTensorStalkCoordinates

Source: Stacks Project, Tag 0DJ8.
(blueprint: lem-pc-affine-ordinary-tensor-stalk-coordinates). -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w wM
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ChangeOfRings
noncomputable section
namespace AlgebraicGeometry

private theorem extendScalars_eqToHom_tmul {D F : Type u} [CommRing D] [CommRing F]
    (a b : D →+* F) (V : ModuleCat.{u} D) (h : a = b) (m : V) :
    eqToHom (congrArg (fun k => (ModuleCat.extendScalars k).obj V) h)
      ((1 : F) ⊗ₜ[D, a] m) = (1 : F) ⊗ₜ[D, b] m := by
  subst b
  rfl

private theorem mapIso_trans_apply {D : Type*} [Category D]
    {F : Type u} [CommRing F] (s : D ⥤ ModuleCat.{u} F)
    {X Y Z : D} (d : X ≅ Y) (e : Y ≅ Z) (x : s.obj X) :
    (s.mapIso (d ≪≫ e)).toLinearEquiv.toAddEquiv x =
      s.map e.hom (s.map d.hom x) := by
  change s.map (d.hom ≫ e.hom) x = _
  rw [s.map_comp, ModuleCat.comp_apply]

private theorem mapIso_three_apply {D : Type*} [Category D]
    {F : Type u} [CommRing F] (s : D ⥤ ModuleCat.{u} F)
    {X Y Z W : D} (d : X ≅ Y) (e : Y ≅ Z) (f : Z ≅ W) (x : s.obj X) :
    (s.mapIso (d ≪≫ e ≪≫ f)).toLinearEquiv.toAddEquiv x =
      s.map f.hom ((s.mapIso (d ≪≫ e)).toLinearEquiv.toAddEquiv x) := by
  rw [← Iso.trans_assoc]
  exact mapIso_trans_apply s (d ≪≫ e) f x

private theorem moduleStalk_map_germ (X : RingedSpace.{u}) (p : X)
    {F G : X.Modules} (a : F ⟶ G) (V : TopologicalSpace.Opens X.carrier)
    (hp : p ∈ V) (x : F.val.obj (Opposite.op V)) :
    (RingedSpace.moduleStalkFunctor X p).map a
        (TopCat.Presheaf.germ F.val.presheaf V p hp x) =
      TopCat.Presheaf.germ G.val.presheaf V p hp (a.val.app (Opposite.op V) x) := by
  exact TopCat.Presheaf.stalkFunctor_map_germ_apply V p hp
    ((PresheafOfModules.toPresheaf _).map a.val) x

private theorem complexIso_hom_inv_apply {D : Type u} [CommRing D]
    {K L : CochainComplex (ModuleCat.{u} D) ℤ} (e : K ≅ L) (j : ℤ) (x : K.X j) :
    e.inv.f j (e.hom.f j x) = x := by
  have h := congrArg (fun k => k.f j) e.hom_inv_id
  simpa only [HomologicalComplex.comp_f, HomologicalComplex.id_f,
    ModuleCat.comp_apply, ModuleCat.id_apply] using congrArg (fun k => k x) h

private theorem moduleIso_square_apply {D : Type u} [CommRing D]
    {X Y P Q : ModuleCat.{u} D} (eX : X ≅ P) (eY : Y ≅ Q)
    (a : X ⟶ Y) (b : P ⟶ Q) (h : a ≫ eY.hom = eX.hom ≫ b) (x : X) :
    a x = eY.inv (b (eX.hom x)) := by
  have h' : a = (eX.hom ≫ b) ≫ eY.inv := (eY.eq_comp_inv).2 h
  simpa only [ModuleCat.comp_apply] using congrArg (fun k => k x) h'

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

/-- Localization of ordinary cohomology into the stalk complex of its tilde.
Source: Stacks Project, Tags 01I9 and 01AG.
(blueprint: lem-pc-affine-ordinary-tensor-stalk-coordinates).
Constructed from the tilde stalk localization, exact tilde homology and exact stalks. -/
def affineTildeHomologyLocalization
    (D : Type u) [CommRing D] (C : CochainComplex (ModuleCat.{u} D) ℤ)
    (p : PrimeSpectrum D) (i : ℤ) :
    let TB : ModuleCat.{u} D ⥤
        SheafOfModules.{u} (moduleRings (Spec (.of D)).toRingedSpace) :=
      tilde.functor (.of D)
    letI : TB.PreservesZeroMorphisms := ⟨fun _ _ ↦ tilde.map_zero⟩
    let N := (TB.mapHomologicalComplex (.up ℤ)).obj C
    let s := RingedSpace.moduleStalkFunctor (Spec (.of D)).toRingedSpace p
    LocalizedModule p.asIdeal.primeCompl (C.homology i) ≃+
      ((s.mapHomologicalComplex (.up ℤ)).obj N).homology i := by
  let TB : ModuleCat.{u} D ⥤
      SheafOfModules.{u} (moduleRings (Spec (.of D)).toRingedSpace) := tilde.functor (.of D)
  let : TB.Additive := by
    constructor
    intro M N f g
    exact tilde.map_add (R := .of D) f g
  let : TB.PreservesZeroMorphisms := ⟨fun _ _ ↦ tilde.map_zero⟩
  let : TB.PreservesHomology := tilde_preservesHomology D
  let N := (TB.mapHomologicalComplex (.up ℤ)).obj C
  let s := RingedSpace.moduleStalkFunctor (Spec (.of D)).toRingedSpace p
  let Rs := ModuleCat.restrictScalars (StructureSheaf.toStalk D p).hom
  let t : C.homology i →ₗ[D] (Rs.obj (s.obj (TB.obj (C.homology i)))) :=
    StructureSheaf.toStalkₗ D (C.homology i) p
  have : IsLocalizedModule p.asIdeal.primeCompl t :=
    inferInstanceAs (IsLocalizedModule p.asIdeal.primeCompl
      (StructureSheaf.toStalkₗ D (C.homology i) p))
  let l := IsLocalizedModule.iso p.asIdeal.primeCompl t
  let H := DerivedCategory.homologyFunctor
    (SheafOfModules.{u} (moduleRings (Spec (.of D)).toRingedSpace)) i
  let d : TB.obj (C.homology i) ≅ H.obj (DerivedCategory.Q.obj N) :=
    ((C.sc i).mapHomologyIso TB).symm ≪≫
      ((DerivedCategory.homologyFunctorFactors _ i).app N).symm
  exact l.toAddEquiv.trans ((s.mapIso d).toLinearEquiv.toAddEquiv.trans
    (affineRepresentativeStalkIso (Spec (.of D)) p N i).toLinearEquiv.toAddEquiv)

private theorem affineTildeHomologyLocalization_apply
    (D : Type u) [CommRing D] (C : CochainComplex (ModuleCat.{u} D) ℤ)
    (p : PrimeSpectrum D) (i : ℤ) (y : LocalizedModule p.asIdeal.primeCompl (C.homology i)) :
    let TB : ModuleCat.{u} D ⥤
        SheafOfModules.{u} (moduleRings (Spec (.of D)).toRingedSpace) := tilde.functor (.of D)
    letI : TB.Additive := by
      constructor
      intro M N f g
      exact tilde.map_add (R := .of D) f g
    letI : TB.PreservesZeroMorphisms := ⟨fun _ _ ↦ tilde.map_zero⟩
    letI : TB.PreservesHomology := tilde_preservesHomology D
    let N := (TB.mapHomologicalComplex (.up ℤ)).obj C
    let s := RingedSpace.moduleStalkFunctor (Spec (.of D)).toRingedSpace p
    let H := DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings (Spec (.of D)).toRingedSpace)) i
    let d : TB.obj (C.homology i) ≅ H.obj (DerivedCategory.Q.obj N) :=
      ((C.sc i).mapHomologyIso TB).symm ≪≫
        ((DerivedCategory.homologyFunctorFactors _ i).app N).symm
    let l := IsLocalizedModule.iso p.asIdeal.primeCompl
      (StructureSheaf.toStalkₗ D (C.homology i) p)
    affineTildeHomologyLocalization D C p i y =
      (affineRepresentativeStalkIso (Spec (.of D)) p N i).hom (s.map d.hom (l y)) := by
  rfl

set_option maxHeartbeats 200000 in
-- Normalize the stalk, scalar-extension and homology functor identifications.
/-- The ordinary tensor target has canonical stalk-complex coordinates.
Source: Stacks Project, Tags 01I9, 01HV, 01AG and 0DJ8.
(blueprint: lem-pc-affine-ordinary-tensor-stalk-coordinates).

Proof: exact tilde homology and exact stalks give affineTildeHomologyLocalization.
The tensor-pullback/tilde natural isomorphism identifies T with tilde C. Take its
inverse on stalk complexes and compose with the inverse tensorStalkIso to obtain
τ. The unit equation of the tilde comparison and the pure-tensor equation of the
pullback-stalk comparison show its displayed action on germs. Germs of pure tensors
generate the localized modules, so these equations determine τ in each degree.
Naturality of exact stalk homology, followed by the homologyFunctorFactors equation,
identifies the resulting cohomology composite with the three factors in the
constructed affineTensorPullbackHomologyStalkIso. This gives the second equation.
The construction uses no derived source comparison or K-flatness and works for
zero complexes and identity maps; zero rings have no primes. -/
theorem exists_affineOrdinaryTensorStalkCoordinates
    (R A R' A' : Type u) [CommRing R] [CommRing A] [CommRing R'] [CommRing A']
    [Algebra R A] [Algebra R R'] [Algebra (A ⊗[R] R') A']
    (φg' : A →+* A') (φf' : R' →+* A')
    (hφg' : (algebraMap (A ⊗[R] R') A').comp
      (algebraMap A (A ⊗[R] R')) = φg')
    (hφf' : (algebraMap (A ⊗[R] R') A').comp
      Algebra.TensorProduct.includeRight.toRingHom = φf')
    (sq : IsPullback (Spec.map (CommRingCat.ofHom φg')) (Spec.map (CommRingCat.ofHom φf'))
      (Spec.map (CommRingCat.ofHom (algebraMap R A)))
      (Spec.map (CommRingCat.ofHom (algebraMap R R'))))
    (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (i : ℤ) :
    let P := ((@Functor.mapHomologicalComplex _ _ _ _ _ _ _
      (@id (ModuleCat.{u} A ⥤
        SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
          (tilde.functor (.of A))) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)).obj M)
    let T := ((Scheme.Modules.tensorPullback
      (Spec.map (CommRingCat.ofHom φg'))).mapHomologicalComplex (.up ℤ)).obj P
    let C := ((ModuleCat.extendScalars φg').mapHomologicalComplex (.up ℤ)).obj M
    (p : PrimeSpectrum A') →
      let f := Spec.map (CommRingCat.ofHom (algebraMap R A))
      let f' := Spec.map (CommRingCat.ofHom φf')
      let g := Spec.map (CommRingCat.ofHom (algebraMap R R'))
      let g' := Spec.map (CommRingCat.ofHom φg')
      letI := SingleComplexBaseChange.leftAlgebra f g' p
      letI := SingleComplexBaseChange.rightAlgebra f f' g g' sq p
      letI := (SingleComplexBaseChange.tensorMap f f' g g' sq p).toAlgebra
      letI := HasDerivedCategory.standard (ModuleCat.{u} (SingleComplexBaseChange.R f g' p))
      letI := HasDerivedCategory.standard (ModuleCat.{u} (SingleComplexBaseChange.B f' p))
      let N := ((@Functor.mapHomologicalComplex _ _ _ _ _ _ _
        (@id (ModuleCat.{u} A' ⥤
          SheafOfModules.{u} (moduleRings (Spec (.of A')).toRingedSpace))
            (tilde.functor (.of A'))) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)).obj C)
      let s := RingedSpace.moduleStalkFunctor (Spec (.of A')).toRingedSpace p
      let ρ := (SingleComplexBaseChange.tensorMap f f' g g' sq p).comp
        (algebraMap (SingleComplexBaseChange.A g' p)
          (SingleComplexBaseChange.A g' p ⊗[SingleComplexBaseChange.R f g' p]
            SingleComplexBaseChange.B f' p))
      ∃ τ : (s.mapHomologicalComplex (.up ℤ)).obj N ≅
          SingleComplexBaseChange.tensorComplex f f' g g' sq p P,
        (∀ (j : ℤ) (x : M.X j),
          τ.hom.f j (TopCat.Presheaf.germ (N.X j).val.presheaf ⊤ p trivial
            (tilde.toOpen (R := .of A') (C.X j) ⊤ ((1 : A') ⊗ₜ[A, φg'] x))) =
            (1 : (Spec (.of A')).presheaf.stalk p) ⊗ₜ[SingleComplexBaseChange.A g' p, ρ]
              (TopCat.Presheaf.germ (P.X j).val.presheaf ⊤ (g' p) trivial
                (tilde.toOpen (R := .of A) (M.X j) ⊤ x))) ∧
        ∀ y, affineTensorPullbackHomologyStalkIso A A' φg' M p i y =
          (affineRepresentativeStalkIso (Spec (.of A')) p T i).inv
            (HomologicalComplex.homologyMap
              (SingleComplexBaseChange.tensorStalkIso f f' g g' sq p P).hom i
                (HomologicalComplex.homologyMap τ.hom i
                  (affineTildeHomologyLocalization A' C p i y))) := by
  classical
  have _ := hφg'
  have _ := hφf'
  intro P T C p f f' g g' N s ρ
  let TA : ModuleCat.{u} A ⥤
      SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace) := tilde.functor (.of A)
  let TB : ModuleCat.{u} A' ⥤
      SheafOfModules.{u} (moduleRings (Spec (.of A')).toRingedSpace) := tilde.functor (.of A')
  let : TA.Additive := by
    constructor
    intro M N f g
    exact tilde.map_add (R := .of A) f g
  let : TB.Additive := by
    constructor
    intro M N f g
    exact tilde.map_add (R := .of A') f g
  let : TA.PreservesZeroMorphisms := ⟨fun _ _ ↦ tilde.map_zero⟩
  let : TB.PreservesZeroMorphisms := ⟨fun _ _ ↦ tilde.map_zero⟩
  let : TB.PreservesHomology := tilde_preservesHomology A'
  let E : SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings (Spec (.of A')).toRingedSpace) :=
    Scheme.Modules.tensorPullback g'
  let : E.Additive := SingleComplexBaseChange.tensorPullbackAdditive.{u, w} g'
  let S := s.mapHomologicalComplex (.up ℤ)
  let θ : TA ⋙ E ≅ ModuleCat.extendScalars φg' ⋙ TB :=
    Classical.choose (Scheme.Modules.exists_tensorPullback_tilde_iso (CommRingCat.ofHom φg'))
  let δ : T ≅ N := (Functor.mapHomologicalComplexCompIso θ (.up ℤ)).app M
  let t := SingleComplexBaseChange.tensorStalkIso f f' g g' sq p P
  let τ := S.mapIso δ.symm ≪≫ t.symm
  refine ⟨τ, ?_, ?_⟩
  · intro j x
    let := SingleComplexBaseChange.leftAlgebra f g' p
    let := SingleComplexBaseChange.rightAlgebra f f' g g' sq p
    let U := (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction g')).unit
    let v := (U.app (P.X j)).app ⊤ (tilde.toOpen (R := .of A) (M.X j) ⊤ x)
    let a := TopCat.Presheaf.germ (T.X j).val.presheaf ⊤ p trivial v
    let b := TopCat.Presheaf.germ (N.X j).val.presheaf ⊤ p trivial
      (tilde.toOpen (R := .of A') (C.X j) ⊤ ((1 : A') ⊗ₜ[A, φg'] x))
    have hd : (S.map δ.hom).f j a = b := by
      change s.map (θ.hom.app (M.X j)) a = b
      have hg := moduleStalk_map_germ (Spec (.of A')).toRingedSpace p
        (θ.hom.app (M.X j)) ⊤ trivial v
      have hu := Classical.choose_spec (Scheme.Modules.exists_tensorPullback_tilde_iso
        (CommRingCat.ofHom φg')) (M.X j) x
      exact hg.trans (congrArg
        (TopCat.Presheaf.germ (N.X j).val.presheaf ⊤ p trivial) hu)
    have hd' : (S.map δ.inv).f j b = a := by
      have h := congrArg (fun z => (S.map δ.inv).f j z) hd
      rw [← ModuleCat.comp_apply, ← HomologicalComplex.comp_f,
        ← Functor.map_comp, Iso.hom_inv_id, S.map_id, HomologicalComplex.id_f,
        ModuleCat.id_apply] at h
      exact h.symm
    have ht : t.hom.f j
        ((1 : SingleComplexBaseChange.C (X' := Spec (.of A')) p) ⊗ₜ[_,
          (SingleComplexBaseChange.tensorMap f f' g g' sq p).comp
            (algebraMap (SingleComplexBaseChange.A g' p)
              (SingleComplexBaseChange.A g' p ⊗[SingleComplexBaseChange.R f g' p]
                SingleComplexBaseChange.B f' p))]
          (TopCat.Presheaf.germ (P.X j).val.presheaf ⊤ (g' p) trivial
            (tilde.toOpen (R := .of A) (M.X j) ⊤ x))) = a := by
      rw [show t.hom.f j = _ from
        Classical.choose_spec (SingleComplexBaseChange.exists_tensorStalkIso
          f f' g g' sq p P) j]
      rw [ModuleCat.comp_apply]
      let m := TopCat.Presheaf.germ (P.X j).val.presheaf ⊤ (g' p) trivial
        (tilde.toOpen (R := .of A) (M.X j) ⊤ x)
      have hρ : ρ = (g'.stalkMap p).hom :=
        (Classical.choose_spec (SingleComplexBaseChange.exists_tensorMap f f' g g' sq p)).1
      have hc := extendScalars_eqToHom_tmul ρ (g'.stalkMap p).hom
        ((RingedSpace.moduleStalkFunctor (Spec (.of A)).toRingedSpace
          (g' p)).obj (P.X j)) hρ m
      let e := Classical.choose (Scheme.Modules.exists_tensorPullback_stalk_iso g' p)
      have he := Classical.choose_spec
        (Scheme.Modules.exists_tensorPullback_stalk_iso g' p)
        (P.X j) ⊤ trivial (tilde.toOpen (R := .of A) (M.X j) ⊤ x)
      have he' := congrArg (fun z => (e.inv.app (P.X j)) z) he
      rw [← ModuleCat.comp_apply, e.hom_inv_id_app, ModuleCat.id_apply] at he'
      have hc' := congrArg (fun z => (e.inv.app (P.X j)) z) hc
      exact hc'.trans he'.symm
    change (t.inv.f j) ((S.map δ.inv).f j b) = _
    rw [hd', ← ht]
    exact complexIso_hom_inv_apply t j _
  · intro y
    have ht : τ.hom ≫ t.hom = S.map δ.inv := by
      change (S.map δ.inv ≫ t.inv) ≫ t.hom = _
      rw [Category.assoc, t.inv_hom_id, Category.comp_id]
    have hh := congrArg (fun a => HomologicalComplex.homologyMap a i) ht
    rw [HomologicalComplex.homologyMap_comp] at hh
    have hn := affineRepresentativeStalkIso_naturality (Spec (.of A')) p δ.inv i
    let H := DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings (Spec (.of A')).toRingedSpace)) i
    let q : CochainComplex
        (SheafOfModules.{u} (moduleRings (Spec (.of A')).toRingedSpace)) ℤ ⥤
      DerivedCategory (SheafOfModules.{u} (moduleRings (Spec (.of A')).toRingedSpace)) :=
      DerivedCategory.Q
    let d : TB.obj (C.homology i) ≅ H.obj (DerivedCategory.Q.obj N) :=
      ((C.sc i).mapHomologyIso TB).symm ≪≫
        ((DerivedCategory.homologyFunctorFactors _ i).app N).symm
    let l := IsLocalizedModule.iso p.asIdeal.primeCompl
      (StructureSheaf.toStalkₗ A' (C.homology i) p)
    let z := s.map d.hom (l y)
    have hcoord : affineTensorPullbackHomologyStalkIso A A' φg' M p i y =
        s.map (H.map (DerivedCategory.Q.map δ.inv)) z := by
      let d₁ := ((C.sc i).mapHomologyIso TB).symm
      let d₂ := ((DerivedCategory.homologyFunctorFactors _ i).app N).symm
      change (s.mapIso (d₁ ≪≫ d₂ ≪≫ H.mapIso (q.mapIso δ).symm)).toLinearEquiv.toAddEquiv
        (l y) = _
      exact mapIso_three_apply s d₁ d₂ (H.mapIso (q.mapIso δ).symm) (l y)
    have hloc : affineTildeHomologyLocalization A' C p i y =
        (affineRepresentativeStalkIso (Spec (.of A')) p N i).hom z := by
      exact affineTildeHomologyLocalization_apply A' C p i y
    have hn' := moduleIso_square_apply
      (affineRepresentativeStalkIso (Spec (.of A')) p N i)
      (affineRepresentativeStalkIso (Spec (.of A')) p T i)
      (s.map (H.map (q.map δ.inv))) (HomologicalComplex.homologyMap (S.map δ.inv) i) hn z
    have hh' := congrArg (fun k =>
      (affineRepresentativeStalkIso (Spec (.of A')) p T i).inv
        (k ((affineRepresentativeStalkIso (Spec (.of A')) p N i).hom z))) hh
    have hl' := congrArg (fun v =>
      (affineRepresentativeStalkIso (Spec (.of A')) p T i).inv
        (HomologicalComplex.homologyMap t.hom i
          (HomologicalComplex.homologyMap τ.hom i v))) hloc
    exact hcoord.trans (hn'.trans (hh'.symm.trans hl'.symm))


end AlgebraicGeometry
