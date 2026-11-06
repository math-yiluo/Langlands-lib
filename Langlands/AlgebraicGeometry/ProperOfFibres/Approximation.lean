import Mathlib
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_exists_fg_subalgebra_isPullback_of_locallyOfFinitePresentation
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_exists_fg_subalgebra_hom_pullback_of_hom_pullback_of_locallyOfFinitePresentation
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_exists_fg_subalgebra_pullback_fst_comp_eq_of_locallyOfFiniteType
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Smooth_exists_fg_subalgebra_of_smooth_pullback_snd
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_IsProper_exists_fg_subalgebra_of_isProper_pullback_snd
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_IsSeparated_exists_fg_subalgebra_of_isSeparated_pullback_snd
import Langlands.AlgebraicGeometry.NoetherianApproximation.NormalFiniteTypeSubalgebraProof

/-! # Finite-type models of a monomorphism into a proper scheme -/

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.ProperOfFibres

/-- The spectra of the maps of a scalar tower compose. -/
theorem specMap_algebraMap_comp (R R' V : Type u) [CommRing R] [CommRing R'] [CommRing V]
    [Algebra R R'] [Algebra R' V] [Algebra R V] [IsScalarTower R R' V] :
    Spec.map (CommRingCat.ofHom (algebraMap R' V)) ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')) =
      Spec.map (CommRingCat.ofHom (algebraMap R V)) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]

/-- If `X` is the base change of `X₁` along `ι : Y ⟶ B` and `ι` factors through `κ : B' ⟶ B`,
then `X` is the base change of `X₁ ×_B B'` along the factor `Y ⟶ B'`. -/
theorem isPullback_lift_of_fac {X X₁ Y B B' : Scheme.{u}} {π : X ⟶ X₁} {g : X ⟶ Y}
    {f : X₁ ⟶ B} {ι : Y ⟶ B} (sq : IsPullback π g f ι) (κ : B' ⟶ B) (ι' : Y ⟶ B')
    (hι : ι' ≫ κ = ι) (w : π ≫ f = (g ≫ ι') ≫ κ) :
    IsPullback (pullback.lift π (g ≫ ι') w) g (pullback.snd f κ) ι' := by
  refine IsPullback.of_right (h₁₂ := pullback.fst f κ) (v₁₃ := f) (h₂₂ := κ) ?_
    (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback f κ)
  rw [pullback.lift_fst, hι]
  exact sq

variable {V : Type u} [CommRing V]

/-- A *model* of `f : X ⟶ Spec V` over a ring `R` with an `R`-algebra structure on `V`: a
morphism `f₀ : X₀ ⟶ Spec R` that is locally of finite presentation, quasi-compact and
quasi-separated, whose base change along `Spec V ⟶ Spec R` is `f`. -/
structure SchemeModel {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of V)) (R : Type u)
    [CommRing R] [Algebra R V] where
  /-- The model scheme. -/
  X₀ : Scheme.{u}
  /-- The model morphism. -/
  f₀ : X₀ ⟶ Spec (CommRingCat.of R)
  /-- The projection from `X` to the model. -/
  π : X ⟶ X₀
  isPullback : IsPullback π f f₀ (Spec.map (CommRingCat.ofHom (algebraMap R V)))
  [locallyOfFinitePresentation : LocallyOfFinitePresentation f₀]
  [quasiCompact : QuasiCompact f₀]
  [quasiSeparated : QuasiSeparated f₀]

attribute [instance] SchemeModel.locallyOfFinitePresentation SchemeModel.quasiCompact
  SchemeModel.quasiSeparated

namespace SchemeModel

variable {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of V)} {R : Type u} [CommRing R]
  [Algebra R V]

/-- The base change of a model along a ring map `R ⟶ R'` through which `R ⟶ V` factors. -/
def baseChange (M : SchemeModel f R) (R' : Type u) [CommRing R'] [Algebra R R'] [Algebra R' V]
    [IsScalarTower R R' V] : SchemeModel f R' where
  X₀ := pullback M.f₀ (Spec.map (CommRingCat.ofHom (algebraMap R R')))
  f₀ := pullback.snd _ _
  π := pullback.lift M.π (f ≫ Spec.map (CommRingCat.ofHom (algebraMap R' V)))
    (by rw [Category.assoc, specMap_algebraMap_comp]; exact M.isPullback.w)
  isPullback := isPullback_lift_of_fac M.isPullback _ _ (specMap_algebraMap_comp R R' V) _

/-- A property of `f` stable under isomorphisms holds for the base change of the model to `V`. -/
theorem prop_pullback_snd (M : SchemeModel f R) (P : MorphismProperty Scheme.{u})
    [P.RespectsIso] (hf : P f) :
    P (pullback.snd M.f₀ (Spec.map (CommRingCat.ofHom (algebraMap R V)))) := by
  rw [← M.isPullback.isoPullback_inv_snd]
  exact (P.cancel_left_of_respectsIso _ _).mpr hf

/-- Every quasi-compact, quasi-separated morphism of finite presentation to `Spec V` has a model
over a finitely generated subalgebra of `V`. -/
theorem exists_subalgebra (R : Type u) [CommRing R] [Algebra R V]
    (f : X ⟶ Spec (CommRingCat.of V)) [QuasiCompact f] [QuasiSeparated f]
    [LocallyOfFinitePresentation f] :
    ∃ T : Subalgebra R V, T.FG ∧ Nonempty (SchemeModel f T) := by
  obtain ⟨T, hT, -, X₀, f₀, π, h₁, h₂, h₃, sq⟩ :=
    AlgebraicGeometry.exists_fg_subalgebra_isPullback_of_locallyOfFinitePresentation
      (A₀ := R) f (∅ : Finset V)
  exact ⟨T, hT, ⟨{ X₀ := X₀, f₀ := f₀, π := π, isPullback := sq }⟩⟩

end SchemeModel

/-- A *model* of a factorization `j ≫ g = f` of morphisms to `Spec V` over `R`: models of `f`
and `g` over `R` together with a model `j₀` of `j` over `Spec R`. -/
structure Model {X Y : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of V))
    (g : Y ⟶ Spec (CommRingCat.of V)) (j : X ⟶ Y) (R : Type u) [CommRing R] [Algebra R V] where
  /-- The model of the source. -/
  MX : SchemeModel f R
  /-- The model of the target. -/
  MY : SchemeModel g R
  /-- The model of `j`. -/
  j₀ : MX.X₀ ⟶ MY.X₀
  fac : j₀ ≫ MY.f₀ = MX.f₀
  comm : j ≫ MY.π = MX.π ≫ j₀

namespace Model

variable {X Y : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of V)} {g : Y ⟶ Spec (CommRingCat.of V)}
  {j : X ⟶ Y} {R : Type u} [CommRing R] [Algebra R V]

/-- The base change of a model along a ring map `R ⟶ R'` through which `R ⟶ V` factors. -/
def baseChange (M : Model f g j R) (hfac : j ≫ g = f) (R' : Type u) [CommRing R'] [Algebra R R']
    [Algebra R' V] [IsScalarTower R R' V] : Model f g j R' where
  MX := M.MX.baseChange R'
  MY := M.MY.baseChange R'
  j₀ := pullback.map _ _ _ _ M.j₀ (𝟙 _) (𝟙 _) (by rw [Category.comp_id, M.fac])
    (by rw [Category.comp_id, Category.id_comp])
  fac := by
    change pullback.map _ _ _ _ _ _ _ _ _ ≫ pullback.snd _ _ = pullback.snd _ _
    rw [pullback.lift_snd, Category.comp_id]
  comm := by
    apply pullback.hom_ext
    · simp only [SchemeModel.baseChange, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc,
        M.comm]
    · simp only [SchemeModel.baseChange, Category.assoc, pullback.lift_snd,
        Category.comp_id, reassoc_of% hfac]

variable (M : Model f g j R) (hfac : j ≫ g = f) (R' : Type u) [CommRing R'] [Algebra R R']
  [Algebra R' V] [IsScalarTower R R' V]

theorem baseChange_MX_f₀ :
    (M.baseChange hfac R').MX.f₀ =
      pullback.snd M.MX.f₀ (Spec.map (CommRingCat.ofHom (algebraMap R R'))) := rfl

theorem baseChange_MY_f₀ :
    (M.baseChange hfac R').MY.f₀ =
      pullback.snd M.MY.f₀ (Spec.map (CommRingCat.ofHom (algebraMap R R'))) := rfl

instance smooth_baseChange [Smooth M.MX.f₀] : Smooth (M.baseChange hfac R').MX.f₀ :=
  inferInstanceAs (Smooth (pullback.snd _ _))

instance isProper_baseChange [IsProper M.MY.f₀] : IsProper (M.baseChange hfac R').MY.f₀ :=
  inferInstanceAs (IsProper (pullback.snd _ _))

instance isSeparated_baseChange [IsSeparated M.MY.f₀] :
    IsSeparated (M.baseChange hfac R').MY.f₀ :=
  inferInstanceAs (IsSeparated (pullback.snd _ _))

/-- If the kernel pair of `j₀` has equal projections after base change along `κ`, then the base
change of `j₀` along `κ` is a monomorphism. -/
theorem mono_pullbackMap_of_kernelPair {X₀ Y₀ S S' : Scheme.{u}} (j₀ : X₀ ⟶ Y₀) (f₀ : X₀ ⟶ S)
    (g₀ : Y₀ ⟶ S) (h₀ : j₀ ≫ g₀ = f₀) (κ : S' ⟶ S)
    (hab : pullback.fst (pullback.fst j₀ j₀ ≫ f₀) κ ≫ pullback.fst j₀ j₀ =
      pullback.fst (pullback.fst j₀ j₀ ≫ f₀) κ ≫ pullback.snd j₀ j₀) :
    Mono (pullback.map f₀ κ g₀ κ j₀ (𝟙 _) (𝟙 _) (by rw [Category.comp_id, h₀])
      (by rw [Category.comp_id, Category.id_comp])) := by
  constructor
  intro W c d hcd
  have h₁ : (c ≫ pullback.fst f₀ κ) ≫ j₀ = (d ≫ pullback.fst f₀ κ) ≫ j₀ := by
    have := congrArg (· ≫ pullback.fst g₀ κ) hcd
    simpa only [Category.assoc, pullback.lift_fst] using this
  have h₂ : c ≫ pullback.snd f₀ κ = d ≫ pullback.snd f₀ κ := by
    have := congrArg (· ≫ pullback.snd g₀ κ) hcd
    simpa only [Category.assoc, pullback.lift_snd, Category.comp_id] using this
  let e := pullback.lift (c ≫ pullback.fst f₀ κ) (d ≫ pullback.fst f₀ κ) h₁
  let e' : W ⟶ pullback (pullback.fst j₀ j₀ ≫ f₀) κ :=
    pullback.lift e (c ≫ pullback.snd f₀ κ)
      (by simp only [e, pullback.lift_fst_assoc, Category.assoc, pullback.condition])
  have h₃ : c ≫ pullback.fst f₀ κ = d ≫ pullback.fst f₀ κ := by
    have := congrArg (e' ≫ ·) hab
    simpa only [e', e, pullback.lift_fst_assoc, pullback.lift_fst, pullback.lift_snd] using this
  exact pullback.hom_ext h₃ h₂

include hfac in
/-- Over `V` itself, the kernel pair of the model `j₀` of a monomorphism `j` has equal
projections. -/
theorem kernelPair_eq_of_mono [Mono j] :
    pullback.fst (pullback.fst M.j₀ M.j₀ ≫ M.MX.f₀)
        (Spec.map (CommRingCat.ofHom (algebraMap R V))) ≫ pullback.fst M.j₀ M.j₀ =
      pullback.fst (pullback.fst M.j₀ M.j₀ ≫ M.MX.f₀)
        (Spec.map (CommRingCat.ofHom (algebraMap R V))) ≫ pullback.snd M.j₀ M.j₀ := by
  set σ := Spec.map (CommRingCat.ofHom (algebraMap R V))
  set f₁ := pullback.fst M.j₀ M.j₀ ≫ M.MX.f₀
  set u := pullback.fst f₁ σ ≫ pullback.fst M.j₀ M.j₀
  set v := pullback.fst f₁ σ ≫ pullback.snd M.j₀ M.j₀
  have hb : pullback.snd M.j₀ M.j₀ ≫ M.MX.f₀ = f₁ := by
    show _ = pullback.fst M.j₀ M.j₀ ≫ M.MX.f₀
    rw [← M.fac, pullback.condition_assoc]
  have hu : u ≫ M.MX.f₀ = pullback.snd f₁ σ ≫ σ := by
    simp only [u, Category.assoc]; exact pullback.condition
  have hv : v ≫ M.MX.f₀ = pullback.snd f₁ σ ≫ σ := by
    simp only [v, Category.assoc, hb]; exact pullback.condition
  have huv : u ≫ M.j₀ = v ≫ M.j₀ := by
    simp only [u, v, Category.assoc, pullback.condition]
  let u' := M.MX.isPullback.lift u (pullback.snd f₁ σ) hu
  let v' := M.MX.isPullback.lift v (pullback.snd f₁ σ) hv
  have hj : u' ≫ j = v' ≫ j := by
    refine M.MY.isPullback.hom_ext ?_ ?_
    · rw [Category.assoc, Category.assoc, M.comm, ← Category.assoc, ← Category.assoc,
        M.MX.isPullback.lift_fst, M.MX.isPullback.lift_fst, huv]
    · rw [Category.assoc, Category.assoc, hfac, M.MX.isPullback.lift_snd,
        M.MX.isPullback.lift_snd]
  have huv' : u' = v' := (cancel_mono j).mp hj
  calc u = u' ≫ M.MX.π := (M.MX.isPullback.lift_fst _ _ _).symm
    _ = v' ≫ M.MX.π := by rw [huv']
    _ = v := M.MX.isPullback.lift_fst _ _ _

instance mono_baseChange [Mono M.j₀] : Mono (M.baseChange hfac R').j₀ :=
  mono_pullbackMap_of_kernelPair M.j₀ M.MX.f₀ M.MY.f₀ M.fac _
    (congrArg (pullback.fst (pullback.fst M.j₀ M.j₀ ≫ M.MX.f₀) _ ≫ ·)
      ((cancel_mono M.j₀).1 pullback.condition))

/-- Models of the source and the target over `R` give, over a finitely generated enlargement
of `R`, a model of the factorization `j ≫ g = f`. -/
theorem exists_of_models (MX : SchemeModel f R) (MY : SchemeModel g R) (hfac : j ≫ g = f) :
    ∃ T : Subalgebra R V, T.FG ∧ Nonempty (Model f g j T) := by
  let eX := MX.isPullback.isoPullback
  let eY := MY.isPullback.isoPullback
  have hg : (eX.inv ≫ j ≫ eY.hom) ≫ pullback.snd MY.f₀ _ = pullback.snd MX.f₀ _ := by
    rw [Category.assoc, Category.assoc, IsPullback.isoPullback_hom_snd, hfac,
      IsPullback.isoPullback_inv_snd]
  obtain ⟨T, hT, -, j₀, hj₀, hq⟩ :=
    AlgebraicGeometry.exists_fg_subalgebra_hom_pullback_of_hom_pullback_of_locallyOfFinitePresentation
      MX.f₀ MY.f₀ (eX.inv ≫ j ≫ eY.hom) hg (∅ : Finset V)
  refine ⟨T, hT, ⟨⟨MX.baseChange T, MY.baseChange T, j₀, hj₀, ?_⟩⟩⟩
  have hval : Spec.map (CommRingCat.ofHom T.val.toRingHom) =
      Spec.map (CommRingCat.ofHom (algebraMap T V)) := rfl
  have h := hq (eX.inv ≫ (MX.baseChange T).π) (eY.inv ≫ (MY.baseChange T).π)
    (by simp only [SchemeModel.baseChange, Category.assoc]; rw [pullback.lift_fst]
        exact IsPullback.isoPullback_inv_fst _)
    (by simp only [SchemeModel.baseChange, Category.assoc]; rw [pullback.lift_snd, hval]
        exact IsPullback.isoPullback_inv_snd_assoc _ _)
    (by simp only [SchemeModel.baseChange, Category.assoc]; rw [pullback.lift_fst]
        exact IsPullback.isoPullback_inv_fst _)
    (by simp only [SchemeModel.baseChange, Category.assoc]; rw [pullback.lift_snd, hval]
        exact IsPullback.isoPullback_inv_snd_assoc _ _)
  rw [← cancel_epi eX.inv]
  have e : eX.inv ≫ j ≫ (MY.baseChange T).π =
      (eX.inv ≫ j ≫ eY.hom) ≫ eY.inv ≫ (MY.baseChange T).π := by
    rw [Category.assoc, Category.assoc, Iso.hom_inv_id_assoc]
  exact e.trans (h.symm.trans (Category.assoc _ _ _))

/-- Smoothness of `f` descends to a finitely generated enlargement of the base of a model. -/
theorem exists_smooth [Smooth f] :
    ∃ T : Subalgebra R V, T.FG ∧ Smooth (M.baseChange hfac T).MX.f₀ := by
  have : MorphismProperty.RespectsIso @Smooth.{u} :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have : Smooth (pullback.snd M.MX.f₀ (Spec.map (CommRingCat.ofHom (algebraMap R V)))) :=
    M.MX.prop_pullback_snd @Smooth ‹_›
  obtain ⟨T, hT, -, h⟩ :=
    AlgebraicGeometry.Smooth.exists_fg_subalgebra_of_smooth_pullback_snd (A := V) M.MX.f₀
      (∅ : Finset V)
  exact ⟨T, hT, h⟩

/-- Separatedness of `g` descends to a finitely generated enlargement of the base of a model. -/
theorem exists_isSeparated [IsSeparated g] :
    ∃ T : Subalgebra R V, T.FG ∧ IsSeparated (M.baseChange hfac T).MY.f₀ := by
  have : IsSeparated (pullback.snd M.MY.f₀ (Spec.map (CommRingCat.ofHom (algebraMap R V)))) :=
    M.MY.prop_pullback_snd @IsSeparated ‹_›
  obtain ⟨T, hT, -, h⟩ :=
    AlgebraicGeometry.IsSeparated.exists_fg_subalgebra_of_isSeparated_pullback_snd (A := V)
      M.MY.f₀ (∅ : Finset V)
  exact ⟨T, hT, h⟩

/-- Over a noetherian base, properness of `g` descends to a finitely generated enlargement of the
base of a model with separated target. -/
theorem exists_isProper [IsNoetherianRing R] [IsSeparated M.MY.f₀] [IsProper g] :
    ∃ T : Subalgebra R V, T.FG ∧ IsProper (M.baseChange hfac T).MY.f₀ := by
  have : IsProper (pullback.snd M.MY.f₀ (Spec.map (CommRingCat.ofHom (algebraMap R V)))) :=
    M.MY.prop_pullback_snd @IsProper ‹_›
  obtain ⟨T, hT, -, h⟩ :=
    AlgebraicGeometry.IsProper.exists_fg_subalgebra_of_isProper_pullback_snd (A := V)
      M.MY.f₀ (∅ : Finset V)
  exact ⟨T, hT, h⟩

/-- If `j` is a monomorphism, then so is the model of `j` over a finitely generated enlargement
of the base. -/
theorem exists_mono [Mono j] :
    ∃ T : Subalgebra R V, T.FG ∧ Mono (M.baseChange hfac T).j₀ := by
  have : QuasiCompact M.j₀ := by
    have : QuasiCompact (M.j₀ ≫ M.MY.f₀) := by rw [M.fac]; infer_instance
    exact QuasiCompact.of_comp M.j₀ M.MY.f₀
  have hb : pullback.snd M.j₀ M.j₀ ≫ M.MX.f₀ = pullback.fst M.j₀ M.j₀ ≫ M.MX.f₀ := by
    rw [← M.fac, pullback.condition_assoc]
  obtain ⟨T, hT, -, h⟩ :=
    AlgebraicGeometry.exists_fg_subalgebra_pullback_fst_comp_eq_of_locallyOfFiniteType
      (A := V) (pullback.fst M.j₀ M.j₀ ≫ M.MX.f₀) M.MX.f₀ (pullback.fst M.j₀ M.j₀)
      (pullback.snd M.j₀ M.j₀) rfl hb (M.kernelPair_eq_of_mono hfac) (∅ : Finset V)
  exact ⟨T, hT, mono_pullbackMap_of_kernelPair M.j₀ M.MX.f₀ M.MY.f₀ M.fac _ h⟩

end Model

/-- A finitely generated subalgebra over a ring of finite type over `ℤ` is of finite type
over `ℤ`. -/
theorem finiteType_int_of_fg {R : Type u} [CommRing R] [Algebra R V] [Algebra.FiniteType ℤ R]
    (T : Subalgebra R V) (hT : T.FG) : Algebra.FiniteType ℤ T :=
  Algebra.FiniteType.trans (S := R) ‹_› ((Subalgebra.fg_iff_finiteType T).mp hT)

section exists_model

variable {X Y : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of V)} {g : Y ⟶ Spec (CommRingCat.of V)}
  {j : X ⟶ Y}

/-- Last stage of `exists_model`: make the model of `j` a monomorphism. -/
theorem exists_model_of_isProper {R : Type u} [CommRing R] [Algebra R V]
    [Algebra.FiniteType ℤ R] (M : Model f g j R) (hfac : j ≫ g = f) [Mono j]
    [Smooth M.MX.f₀] [IsProper M.MY.f₀] :
    ∃ (R : Type u) (_ : CommRing R) (_ : Algebra R V), Algebra.FiniteType ℤ R ∧
      ∃ M : Model f g j R, Smooth M.MX.f₀ ∧ Mono M.j₀ ∧ IsProper M.MY.f₀ := by
  obtain ⟨T, hT, h⟩ := M.exists_mono hfac
  exact ⟨T, inferInstance, inferInstance, finiteType_int_of_fg T hT, M.baseChange hfac T,
    inferInstance, h, inferInstance⟩

/-- Third stage of `exists_model`: make the model of `g` proper. -/
theorem exists_model_of_isSeparated {R : Type u} [CommRing R] [Algebra R V]
    [Algebra.FiniteType ℤ R] (M : Model f g j R) (hfac : j ≫ g = f) [Mono j] [IsProper g]
    [Smooth M.MX.f₀] [IsSeparated M.MY.f₀] :
    ∃ (R : Type u) (_ : CommRing R) (_ : Algebra R V), Algebra.FiniteType ℤ R ∧
      ∃ M : Model f g j R, Smooth M.MX.f₀ ∧ Mono M.j₀ ∧ IsProper M.MY.f₀ := by
  have : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing ℤ R
  obtain ⟨T, hT, h⟩ := M.exists_isProper hfac
  have := finiteType_int_of_fg T hT
  exact exists_model_of_isProper (M.baseChange hfac T) hfac

/-- Second stage of `exists_model`: make the model of `g` separated. -/
theorem exists_model_of_smooth {R : Type u} [CommRing R] [Algebra R V]
    [Algebra.FiniteType ℤ R] (M : Model f g j R) (hfac : j ≫ g = f) [Mono j] [IsProper g]
    [Smooth M.MX.f₀] :
    ∃ (R : Type u) (_ : CommRing R) (_ : Algebra R V), Algebra.FiniteType ℤ R ∧
      ∃ M : Model f g j R, Smooth M.MX.f₀ ∧ Mono M.j₀ ∧ IsProper M.MY.f₀ := by
  obtain ⟨T, hT, h⟩ := M.exists_isSeparated hfac
  have := finiteType_int_of_fg T hT
  exact exists_model_of_isSeparated (M.baseChange hfac T) hfac

/-- First stage of `exists_model`: make the model of `f` smooth. -/
theorem exists_model_of_model {R : Type u} [CommRing R] [Algebra R V]
    [Algebra.FiniteType ℤ R] (M : Model f g j R) (hfac : j ≫ g = f) [Smooth f] [Mono j]
    [IsProper g] :
    ∃ (R : Type u) (_ : CommRing R) (_ : Algebra R V), Algebra.FiniteType ℤ R ∧
      ∃ M : Model f g j R, Smooth M.MX.f₀ ∧ Mono M.j₀ ∧ IsProper M.MY.f₀ := by
  obtain ⟨T, hT, h⟩ := M.exists_smooth hfac
  have := finiteType_int_of_fg T hT
  exact exists_model_of_smooth (M.baseChange hfac T) hfac

/-- Models of the source and the target give a model of the factorization. -/
theorem exists_model_of_schemeModels {R : Type u} [CommRing R] [Algebra R V]
    [Algebra.FiniteType ℤ R] (MX : SchemeModel f R) (MY : SchemeModel g R) (hfac : j ≫ g = f)
    [Smooth f] [Mono j] [IsProper g] :
    ∃ (R : Type u) (_ : CommRing R) (_ : Algebra R V), Algebra.FiniteType ℤ R ∧
      ∃ M : Model f g j R, Smooth M.MX.f₀ ∧ Mono M.j₀ ∧ IsProper M.MY.f₀ := by
  obtain ⟨T, hT, ⟨M⟩⟩ := Model.exists_of_models MX MY hfac
  have := finiteType_int_of_fg T hT
  exact exists_model_of_model M hfac

/-- A model of the source gives a model of the factorization. -/
theorem exists_model_of_schemeModel {R : Type u} [CommRing R] [Algebra R V]
    [Algebra.FiniteType ℤ R] (MX : SchemeModel f R) (hfac : j ≫ g = f) [Smooth f] [Mono j]
    [IsProper g] [LocallyOfFinitePresentation g] :
    ∃ (R : Type u) (_ : CommRing R) (_ : Algebra R V), Algebra.FiniteType ℤ R ∧
      ∃ M : Model f g j R, Smooth M.MX.f₀ ∧ Mono M.j₀ ∧ IsProper M.MY.f₀ := by
  obtain ⟨T, hT, ⟨MY⟩⟩ := SchemeModel.exists_subalgebra R g
  have := finiteType_int_of_fg T hT
  exact exists_model_of_schemeModels (MX.baseChange T) MY hfac

end exists_model

/-- A smooth quasi-compact `f = j ≫ g` with `j` a monomorphism and `g` proper of finite
presentation has a model over a ring of finite type over `ℤ` in which the model of `f` is smooth,
the model of `j` is a monomorphism and the model of `g` is proper. -/
theorem exists_model {X Y : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of V))
    (g : Y ⟶ Spec (CommRingCat.of V)) (j : X ⟶ Y) (hfac : j ≫ g = f) [Smooth f]
    [QuasiCompact f] [IsProper g] [LocallyOfFinitePresentation g] [Mono j] :
    ∃ (R : Type u) (_ : CommRing R) (_ : Algebra R V), Algebra.FiniteType ℤ R ∧
      ∃ M : Model f g j R, Smooth M.MX.f₀ ∧ Mono M.j₀ ∧ IsProper M.MY.f₀ := by
  have : QuasiSeparated f := by
    have : QuasiSeparated (j ≫ g) := inferInstance
    rwa [hfac] at this
  have : Algebra.FiniteType ℤ (⊥ : Subalgebra ℤ V) :=
    (Subalgebra.fg_iff_finiteType _).mp Subalgebra.fg_bot
  obtain ⟨T, hT, ⟨MX⟩⟩ := SchemeModel.exists_subalgebra (⊥ : Subalgebra ℤ V) f
  have := finiteType_int_of_fg T hT
  exact exists_model_of_schemeModel MX hfac

/-- Over an integrally closed domain, the model of `exists_model` can be taken over a finitely
generated integrally closed subring of `V`. -/
theorem exists_normal_model [IsDomain V] [IsIntegrallyClosed V] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of V)) (g : Y ⟶ Spec (CommRingCat.of V)) (j : X ⟶ Y)
    (hfac : j ≫ g = f) [Smooth f] [QuasiCompact f] [IsProper g] [LocallyOfFinitePresentation g]
    [Mono j] :
    ∃ N : Subalgebra ℤ V, N.FG ∧ IsIntegrallyClosed N ∧
      ∃ M : Model f g j N, Smooth M.MX.f₀ ∧ Mono M.j₀ ∧ IsProper M.MY.f₀ := by
  classical
  obtain ⟨R, _, _, hR, M, hM₁, hM₂, hM₃⟩ := exists_model f g j hfac
  obtain ⟨s, hs⟩ := hR.out
  obtain ⟨N, hN, hsN, hNi, -⟩ :=
    NoetherianApproximation.normalFiniteTypeSubalgebra V (s.image (algebraMap R V))
  let φ : R →ₐ[ℤ] V := (algebraMap R V).toIntAlgHom
  have hle : Algebra.adjoin ℤ (s : Set R) ≤ N.comap φ := by
    refine Algebra.adjoin_le fun x hx => hsN ?_
    exact Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hx)
  have hmem : ∀ r : R, φ r ∈ N := fun r => hle (hs.symm ▸ Algebra.mem_top)
  let : Algebra R N := (φ.codRestrict N hmem).toRingHom.toAlgebra
  have : IsScalarTower R N V := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact ⟨N, hN, hNi, M.baseChange hfac N, inferInstance, inferInstance, inferInstance⟩

end Langlands.AlgebraicGeometry.ProperOfFibres
