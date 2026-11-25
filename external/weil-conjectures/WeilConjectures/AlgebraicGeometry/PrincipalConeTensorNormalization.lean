/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.ProEtale.DerivedCompletion
import WeilConjectures.Algebra.Homology.ReductionIsoShift
import WeilConjectures.CategoryTheory.DerivedCategory.Complete.Defs
public import WeilConjectures.CategoryTheory.Monoidal.Closed.UnitEnd

/-! # Signed principal cones and derived tensor

Source: blueprint, derived Nakayama resolution, On X paragraph.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.PrincipalNormalization

attribute [local irreducible] upperStarFromPoint
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u})

/-- The standard shift on derived right tensor by the finite quotient.
Source: derived tensor localized from total tensor
(auxiliary; not a blueprint node). -/
abbrev tensorReductionShift (n : ℕ) :
    (DerivedNakayama.reductionFunctor l E X (n + 1)).CommShift ℤ := by
  change (tensorRight _).CommShift ℤ
  infer_instance

section ScalarTools
universe v
open Category BraidedCategory
namespace UnitEndScalars
variable (A : Type u) [Category.{v} A] [Preadditive A]
  [MonoidalCategory A] [MonoidalPreadditive A]
@[instance_reducible] private def scalarRing : CommRing (End (𝟙_ A)) :=
  { (inferInstance : Ring (End (𝟙_ A))) with
    mul_comm := fun a b ↦ by
      apply End.ext
      have h := unitEndAction_naturality a.asHom b
      simpa only [End.mul_asHom, unitEndAction_unit] using h }
-- A private copy fixes the scalar action on each Hom space.
private def Scalars := End (𝟙_ A)
private instance principalConeTensorNormalizationInst1 : CommRing (Scalars A) := scalarRing A
private def centerHom : Scalars A →+* CatCenter A where
  toFun a :=
    .of
      { app := fun X ↦ (unitEndAction X a).asHom
        naturality := fun _ _ f ↦ (unitEndAction_naturality f a).symm }
  map_one' := by
    apply CatCenter.ext
    intro X
    exact congrArg End.asHom (unitEndAction X).map_one
  map_mul' a b := by
    apply CatCenter.ext
    intro X
    exact congrArg End.asHom ((unitEndAction X).map_mul a b)
  map_zero' := by
    apply CatCenter.ext
    intro X
    exact congrArg End.asHom (unitEndRingHom X).map_zero
  map_add' a b := by
    apply CatCenter.ext
    intro X
    exact congrArg End.asHom ((unitEndRingHom X).map_add a b)
private instance (priority := 2000) scalarLinear : Linear (Scalars A) A :=
  Linear.ofRingMorphism (centerHom A)
private theorem unit_smul_id (a : Scalars A) : a • 𝟙 (𝟙_ A) = a.asHom := by
  change (unitEndAction (𝟙_ A) a).asHom ≫ 𝟙 _ = a.asHom
  rw [unitEndAction_unit, Category.comp_id]
private theorem smul_eq {X Y : A} (a : Scalars A) (f : X ⟶ Y) :
    a • f = (unitEndAction X a).asHom ≫ f := rfl
variable [BraidedCategory A]
omit [Preadditive A] [MonoidalPreadditive A] [BraidedCategory A] in
private theorem action_tensor_right (X Y : A) (a : End (𝟙_ A)) :
    X ◁ (unitEndAction Y a).asHom = (unitEndAction (X ⊗ Y) a).asHom := by
  simp only [unitEndAction_apply, whiskerLeft_comp]
  monoidal
omit [Preadditive A] [MonoidalPreadditive A] in
private theorem action_left (X : A) (a : End (𝟙_ A)) :
    (unitEndAction X a).asHom = (λ_ X).inv ≫ a.asHom ▷ X ≫ (λ_ X).hom := by
  apply (cancel_epi (λ_ X).hom).mp
  apply (cancel_mono (ρ_ X).inv).mp
  simpa only [unitEndAction_apply, Category.assoc, Iso.hom_inv_id_assoc,
    Iso.hom_inv_id, Category.comp_id, braiding_tensorUnit_left] using
    (braiding_naturality_left a.asHom X).symm
omit [Preadditive A] [MonoidalPreadditive A] in
private theorem action_tensor_left (X Y : A) (a : End (𝟙_ A)) :
    (unitEndAction X a).asHom ▷ Y = (unitEndAction (X ⊗ Y) a).asHom := by
  rw [action_left, action_left]
  simp only [comp_whiskerRight]
  monoidal
private instance (priority := 2000) scalarMonoidal :
    MonoidalLinear (Scalars A) A where
  whiskerLeft_smul X _ _ a f := by
    simp only [smul_eq, whiskerLeft_comp, action_tensor_right]
  smul_whiskerRight a _ _ f X := by
    simp only [smul_eq, comp_whiskerRight, action_tensor_left]
end UnitEndScalars
end ScalarTools

private def scalar (d : End (Mod.regular (DerivedNakayama.integerRing l E))) :
    UnitEndScalars.Scalars (AdicCompletion.Modules l E X) :=
  End.of ((DerivedNakayama.regularPullbackIso l E X).inv ≫
    (DerivedNakayama.pullback l E X).map d.asHom ≫
    (DerivedNakayama.regularPullbackIso l E X).hom)

private theorem scalar_complex (d : End (Mod.regular (DerivedNakayama.integerRing l E)))
    (M : CochainComplex (AdicCompletion.Modules l E X) ℤ) :
    DerivedNakayama.scalarOnComplex l E X d M = scalar l E X d • 𝟙 M := by
  apply HomologicalComplex.Hom.ext
  funext j
  change (λ_ (M.X j)).inv ≫ (scalar l E X d).asHom ▷ M.X j ≫ (λ_ (M.X j)).hom =
    scalar l E X d • 𝟙 (M.X j)
  rw [UnitEndScalars.smul_eq, Category.comp_id, UnitEndScalars.action_left]

private theorem coefficient_exact
    (d : End (Mod.regular (DerivedNakayama.integerRing l E)))
    (hd : ∀ (S : Profinite.{u}ᵒᵖ) (a : (DerivedNakayama.integerRing l E).obj.obj S)
      (s : S.unop), ((d.asHom.hom.hom.app S) a).down s =
        Padic.coefficientExtensionUniformizer l E * a.down s) (n : ℕ) :
    ∃ w : (scalar l E X (d ^ (n + 1)) • 𝟙 _) ≫
        AdicCompletion.finiteUnit l E X n = 0,
      (ShortComplex.mk _ _ w).ShortExact := by
  obtain ⟨d₀, hd₀, r, hr, i, q, hi, hq, hseq⟩ :=
    DerivedNakayama.derived_nakayama_resolution l E
  have he : d₀ = d := by
    let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
    apply End.ext
    apply Mod.hom_ext
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext S
    apply AddCommGrpCat.hom_ext
    ext a
    apply ULift.ext
    apply ContinuousMap.ext
    intro s
    exact (hd₀ S a s).trans (hd S a s).symm
  subst d₀
  obtain ⟨w, hw⟩ := (hseq X (n + 1) (by omega)).1
  have hr' : r (n + 1) = AdicCompletion.quotientUnit l E n :=
    Mod.hom_ext _ _ (hr (n + 1))
  simp only [hr'] at w hw
  let e := DerivedNakayama.regularPullbackIso l E X
  have hs : scalar l E X (d ^ (n + 1)) • 𝟙 (𝟙_ (AdicCompletion.Modules l E X)) =
      e.inv ≫ (DerivedNakayama.pullback l E X).map (d ^ (n + 1)).asHom ≫ e.hom :=
    UnitEndScalars.unit_smul_id _ _
  have w' : (scalar l E X (d ^ (n + 1)) • 𝟙 _) ≫
      AdicCompletion.finiteUnit l E X n = 0 := by
    rw [hs]
    dsimp only [AdicCompletion.finiteUnit]
    simp only [e, Category.assoc, Iso.hom_inv_id_assoc]
    rw [w, comp_zero]
  refine ⟨w', ShortComplex.shortExact_of_iso ?_ hw⟩
  refine ShortComplex.isoMk e e (Iso.refl _) ?_ ?_
  · dsimp
    rw [hs]
    simp
  · dsimp [AdicCompletion.finiteUnit, e]
    simp

private theorem scalar_mul
    (a b : End (Mod.regular (DerivedNakayama.integerRing l E))) :
    scalar l E X (a * b) = scalar l E X a * scalar l E X b := by
  apply End.ext
  change (DerivedNakayama.regularPullbackIso l E X).inv ≫
      (DerivedNakayama.pullback l E X).map (a * b).asHom ≫
      (DerivedNakayama.regularPullbackIso l E X).hom =
    ((DerivedNakayama.regularPullbackIso l E X).inv ≫
      (DerivedNakayama.pullback l E X).map b.asHom ≫
      (DerivedNakayama.regularPullbackIso l E X).hom) ≫
    (DerivedNakayama.regularPullbackIso l E X).inv ≫
      (DerivedNakayama.pullback l E X).map a.asHom ≫
      (DerivedNakayama.regularPullbackIso l E X).hom
  rw [End.mul_asHom, Functor.map_comp]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

section Generic
universe v z
variable {A : Type*} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{v} A]
  [HasDerivedCategory.{v} A] [MonoidalCategory A] [MonoidalClosed A]
  [MonoidalPreadditive A] [BraidedCategory A] [Abelian.HasFunctorialFlatResolution A]
  {B : Type z} [CommRing B] [Linear B A] [MonoidalLinear B A]
attribute [local instance] instHasColimitsOfSize_weilConjectures

private def scalarNat (b : B) : 𝟭 (CochainComplex A ℤ) ⟶ 𝟭 _ where
  app M := b • 𝟙 M
  naturality _ _ f := by simp

private def coneOf (τ : 𝟭 (CochainComplex A ℤ) ⟶ 𝟭 _) :
    CochainComplex A ℤ ⥤ DerivedCategory A where
  obj M := DerivedCategory.Q.obj (CochainComplex.mappingCone (τ.app M))
  map f := DerivedCategory.Q.map
    (CochainComplex.mappingCone.map _ _ f f (τ.naturality f).symm)
  map_id M := by
    trans DerivedCategory.Q.map (𝟙 _)
    · exact DerivedCategory.Q.congr_map (CochainComplex.mappingCone.map_id (τ.app M))
    · exact DerivedCategory.Q.map_id _
  map_comp f g := by rw [CochainComplex.mappingCone.map_comp, Functor.map_comp]

omit [IsGrothendieckAbelian A] [MonoidalCategory A] [MonoidalClosed A]
    [MonoidalPreadditive A] [BraidedCategory A] [Abelian.HasFunctorialFlatResolution A] in
private theorem single_map {U V : A} (f : U ⟶ V) :
    (DerivedCategory.singleFunctor A 0).map f =
      DerivedCategory.Q.map ((HomologicalComplex.single A (.up ℤ) 0).map f) := by
  rfl

private theorem normalize
    (b : ℕ → B) (s : B) (hb : ∀ n, b n * s = b (n + 1))
    (N : ℕ → A) (p : ∀ n, 𝟙_ A ⟶ N n)
    (w : ∀ n, (b n • 𝟙 (𝟙_ A)) ≫ p n = 0)
    (hw : ∀ n, (ShortComplex.mk _ _ (w n)).ShortExact)
    (q : ∀ n, N (n + 1) ⟶ N n) (hq : ∀ n, p (n + 1) ≫ q n = p n)
    (τ : ℕ → (𝟭 (CochainComplex A ℤ) ⟶ 𝟭 _))
    (hτ : τ = fun n ↦ scalarNat (b n))
    (σ : 𝟭 (CochainComplex A ℤ) ⟶ 𝟭 _) (hσ : σ = scalarNat s)
    (hshift : ∀ n t (M : CochainComplex A ℤ),
      (τ n).app (M⟦t⟧) = ((τ n).app M)⟦t⟧')
    (hs : ∀ n M, (τ (n + 1)).app M = σ.app M ≫ (τ n).app M) :
    ∃ κ : ∀ n, coneOf (τ n) ≅
        DerivedCategory.Q ⋙ tensorRight ((DerivedCategory.singleFunctor A 0).obj (N n)),
      (∀ n M, DerivedCategory.Q.map
        (CochainComplex.mappingCone.map ((τ (n + 1)).app M) ((τ n).app M)
          (σ.app M) (𝟙 M) ((Category.comp_id _).trans (hs n M))) ≫
          (κ n).hom.app M = (κ (n + 1)).hom.app M ≫
            DerivedCategory.Q.obj M ◁ DerivedCategory.Q.map
              ((HomologicalComplex.single A (.up ℤ) 0).map (q n))) ∧
      (∀ n M, DerivedCategory.Q.map (CochainComplex.mappingCone.inr ((τ n).app M)) ≫
        (κ n).hom.app M = (ρ_ (DerivedCategory.Q.obj M)).inv ≫
          DerivedCategory.Q.obj M ◁ (Functor.LaxMonoidal.ε DerivedCategory.Q ≫
            DerivedCategory.Q.map ((HomologicalComplex.single A (.up ℤ) 0).map (p n)))) ∧
      (∀ n t M, DerivedCategory.Q.map
          (eqToHom (congrArg (fun f : M⟦t⟧ ⟶ M⟦t⟧ ↦ CochainComplex.mappingCone f)
            (hshift n t M)) ≫
            (CochainComplex.mappingCone.shiftIso ((τ n).app M) t).inv) ≫
          (DerivedCategory.Q.commShiftIso t).hom.app
            (CochainComplex.mappingCone ((τ n).app M)) ≫ ((κ n).hom.app M)⟦t⟧' =
        (κ n).hom.app (M⟦t⟧) ≫
          (tensorRight ((DerivedCategory.singleFunctor A 0).obj (N n))).map
            ((DerivedCategory.Q.commShiftIso t).hom.app M) ≫
          ((tensorRight ((DerivedCategory.singleFunctor A 0).obj (N n))).commShiftIso t).hom.app
            (DerivedCategory.Q.obj M)) := by
  subst τ σ
  let κ : ∀ n, coneOf (scalarNat (b n)) ≅
      DerivedCategory.Q ⋙ tensorRight ((DerivedCategory.singleFunctor A 0).obj (N n)) :=
    fun n ↦ NatIso.ofComponents
      (fun M ↦ (DerivedCategory.reductionIso (w n) (hw n) M).symm) (by
        intro M P f
        change DerivedCategory.Q.map _ ≫ _ = _ ≫ (DerivedCategory.Q.map f ▷ _)
        rw [← cancel_epi (DerivedCategory.reductionIso (w n) (hw n) M).hom,
          ← cancel_mono (DerivedCategory.reductionIso (w n) (hw n) P).hom]
        simpa only [scalarNat, Iso.symm_hom, DerivedCategory.Q_obj_single_obj, Category.assoc,
          Iso.hom_inv_id_assoc, Iso.inv_hom_id, Category.comp_id] using
          (DerivedCategory.reductionIso_hom_naturality (w n) (hw n) f).symm)
  refine ⟨κ, ?_, ?_, ?_⟩
  · intro n M
    change DerivedCategory.Q.map _ ≫ (DerivedCategory.reductionIso (w n) (hw n) M).inv =
      (DerivedCategory.reductionIso (w (n + 1)) (hw (n + 1)) M).inv ≫ _
    rw [← cancel_epi (DerivedCategory.reductionIso (w (n + 1)) (hw (n + 1)) M).hom,
      ← cancel_mono (DerivedCategory.reductionIso (w n) (hw n) M).hom]
    simpa only [scalarNat, Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id,
      Category.comp_id] using
      (DerivedCategory.whiskerLeft_reductionIso_hom (hb n)
        (w (n + 1)) (w n) (hw (n + 1)) (hw n) (q n) (hq n) M).symm
  · intro n M
    change DerivedCategory.Q.map _ ≫ (DerivedCategory.reductionIso (w n) (hw n) M).inv = _
    rw [← cancel_mono (DerivedCategory.reductionIso (w n) (hw n) M).hom]
    simpa only [scalarNat, Category.assoc, Iso.inv_hom_id, Category.comp_id] using
      (DerivedCategory.reduction_reductionIso_hom (w n) (hw n) M).symm
  · intro n t M
    simpa only [κ, NatIso.ofComponents_hom_app, Iso.symm_hom,
      scalarNat, eqToHom_refl, Category.id_comp] using
      DerivedCategory.reductionIso_inv_signed_shift (w n) (hw n) M t
end Generic

/-- The scalar cone comparison with derived tensor preserves quotient maps, the
specified tensor unit and the signed shift. No change of coefficient category is involved.

Source: blueprint derived Nakayama resolution, On X paragraph, and first reduction,
Cones paragraph; original normalization proof steps 1, 3 and 4.
(auxiliary; not a blueprint node).

Proof: equality on profinite sections identifies d with the specified uniformizer.
The exact coefficient sequence gives the augmentation from its two-term free
resolution to the finite quotient in degree zero. The resolution is K-flat, so
its total tensor with any complex computes the derived tensor. Compose the inverse
of the standard tensor-cone interchange with this augmentation and the localization
comparison. The interchange is natural in the input complex, hence gives a natural
isomorphism. The quotient map is lifted on the two-term resolutions by (d,id);
the supplied power equation is its chain-map equation. Naturality of tensor-cone
interchange and of the augmentation proves the transition equation. The cone
inclusion becomes the right unitor inverse followed by the degree-zero quotient
map, which is the stated tensor unit. Shifting the two-term tensor multiplies the
shifted input summand by (-1)^r. Thus the comparison uses the inverse of the standard
mappingCone.shiftIso. The derived tensor shift was localized from this total-tensor
shift; the same square therefore holds after localization. All degrees and
unbounded input complexes are covered, including the zero complex. -/
theorem principal_cone_tensor_normalization
    (d : End (Mod.regular (DerivedNakayama.integerRing l E)))
    (hd : ∀ (S : Profinite.{u}ᵒᵖ) (a : (DerivedNakayama.integerRing l E).obj.obj S)
      (s : S.unop), ((d.asHom.hom.hom.app S) a).down s =
        Padic.coefficientExtensionUniformizer l E * a.down s)
    (hs : ∀ (n : ℕ) (M : CochainComplex (AdicCompletion.Modules l E X) ℤ),
      DerivedNakayama.scalarOnComplex l E X (d ^ (n + 1 + 1)) M =
        DerivedNakayama.scalarOnComplex l E X d M ≫
          DerivedNakayama.scalarOnComplex l E X (d ^ (n + 1)) M) :
    ∃ (κ : ∀ n : ℕ, DerivedNakayama.coneFunctor l E X (d ^ (n + 1)) ≅
        DerivedCategory.Q ⋙ DerivedNakayama.reductionFunctor l E X (n + 1)),
      (∀ (n : ℕ) (M : CochainComplex (AdicCompletion.Modules l E X) ℤ),
        DerivedCategory.Q.map (CochainComplex.mappingCone.map
          (DerivedNakayama.scalarOnComplex l E X (d ^ (n + 1 + 1)) M)
          (DerivedNakayama.scalarOnComplex l E X (d ^ (n + 1)) M)
          (DerivedNakayama.scalarOnComplex l E X d M) (𝟙 M)
          ((Category.comp_id _).trans (hs n M))) ≫ (κ n).hom.app M =
            (κ (n + 1)).hom.app M ≫
              (DerivedNakayama.reductionMap l E X
                (AdicCompletion.quotientStep l E n)).app (DerivedCategory.Q.obj M)) ∧
      (∀ (n : ℕ) (M : CochainComplex (AdicCompletion.Modules l E X) ℤ),
        DerivedCategory.Q.map (CochainComplex.mappingCone.inr
          (DerivedNakayama.scalarOnComplex l E X (d ^ (n + 1)) M)) ≫
            (κ n).hom.app M =
          (ρ_ (DerivedCategory.Q.obj M)).inv ≫ DerivedCategory.Q.obj M ◁
            (Functor.LaxMonoidal.ε DerivedCategory.Q ≫ DerivedCategory.Q.map
              ((HomologicalComplex.single _ (.up ℤ) 0).map
                (AdicCompletion.finiteUnit l E X n)))) ∧
      (∀ (n : ℕ) (r : ℤ) (M : CochainComplex (AdicCompletion.Modules l E X) ℤ),
        DerivedCategory.Q.map
            (CochainComplex.mappingCone.shiftIso
              (DerivedNakayama.scalarOnComplex l E X (d ^ (n + 1)) M) r).inv ≫
            (DerivedCategory.Q.commShiftIso r).hom.app
              (CochainComplex.mappingCone
                (DerivedNakayama.scalarOnComplex l E X (d ^ (n + 1)) M)) ≫
            ((κ n).hom.app M)⟦r⟧' =
          (κ n).hom.app (M⟦r⟧) ≫
            (DerivedNakayama.reductionFunctor l E X (n + 1)).map
              ((DerivedCategory.Q.commShiftIso r).hom.app M) ≫
            (Functor.commShiftIso (self := tensorReductionShift l E X n)
              (DerivedNakayama.reductionFunctor l E X (n + 1)) r).hom.app
              (DerivedCategory.Q.obj M)) := by
  classical
  choose w hw using coefficient_exact l E X d hd
  let τ : ℕ → (𝟭 (CochainComplex (AdicCompletion.Modules l E X) ℤ) ⟶ 𝟭 _) := fun n ↦
    NatTrans.mapHomologicalComplex
      (DerivedNakayama.scalarOnModules l E X (d ^ (n + 1))) (.up ℤ)
  let σ : 𝟭 (CochainComplex (AdicCompletion.Modules l E X) ℤ) ⟶ 𝟭 _ :=
    NatTrans.mapHomologicalComplex (DerivedNakayama.scalarOnModules l E X d) (.up ℤ)
  have hτ : τ = fun n ↦ scalarNat (scalar l E X (d ^ (n + 1))) := by
    funext n
    apply NatTrans.ext
    funext M
    exact scalar_complex l E X (d ^ (n + 1)) M
  have hσ : σ = scalarNat (scalar l E X d) := by
    apply NatTrans.ext
    funext M
    exact scalar_complex l E X d M
  have hb (n : ℕ) : scalar l E X (d ^ (n + 1)) * scalar l E X d =
      scalar l E X (d ^ (n + 1 + 1)) := by
    rw [← scalar_mul, ← pow_succ]
  have hq (n : ℕ) : AdicCompletion.finiteUnit l E X (n + 1) ≫
      (DerivedNakayama.pullback l E X).map (AdicCompletion.quotientStep l E n) =
      AdicCompletion.finiteUnit l E X n := by
    dsimp only [AdicCompletion.finiteUnit]
    rw [Category.assoc, ← Functor.map_comp]
    congr 2
  dsimp only [DerivedNakayama.reductionFunctor, CondensedRing.derivedTensor]
  simpa only [τ, σ, coneOf, DerivedNakayama.coneFunctor,
    DerivedNakayama.scalarOnComplex, DerivedNakayama.reductionMap,
    CondensedRing.derivedTensor, Functor.flip_map_app, curriedTensor, tensorRight,
    Functor.flip, single_map, AdicCompletion.Modules,
    eqToHom_refl, Category.id_comp] using
    normalize (fun n ↦ scalar l E X (d ^ (n + 1))) (scalar l E X d) hb
    (AdicCompletion.finiteModule l E X) (AdicCompletion.finiteUnit l E X) w hw
    (fun n ↦ (DerivedNakayama.pullback l E X).map (AdicCompletion.quotientStep l E n)) hq
      τ hτ σ hσ (fun _ _ _ ↦ rfl) hs

end AlgebraicGeometry.ProEtale.PrincipalNormalization
