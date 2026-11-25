/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.LeftResolution.Reduced
public import Mathlib.CategoryTheory.Abelian.Refinements
public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
public import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitude
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.FromJoel.Algebra.Homology.LeftResolution.CochainComplexMinus
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal

/-!

# Bounded flat models of objects of finite Tor amplitude

Let `C` be a closed braided monoidal Grothendieck abelian category with functorial flat
resolutions, so that its derived category `D(C)` carries the derived tensor product
`- ⊗ᴸ -`. This file shows that an object `K` of `D(C)` has Tor amplitude in `[a, b]`
(`DerivedCategory.torAmplitudeIn`) exactly when it is represented by a complex of flat objects
concentrated in degrees `[a, b]`.

* If `P` is a complex of flat objects in degrees `[a, b]`, it is K-flat, so `P ⊗ᴸ F[0]` is
  computed by the tensor product of complexes `P ⊗ F`, which lives in degrees `[a, b]`.
* Conversely, `K` is concentrated in `[a, b]` (test against the unit), so it is represented by
  a complex `P` of flat objects vanishing above `b`, a bounded above flat resolution. The
  truncation `τ^{≥ a} P` still represents `K`; its terms are those of `P` except in degree `a`,
  where it is the cokernel `P^a / d(P^{a-1})`. That cokernel is flat by the Tor criterion
  `CategoryTheory.ObjectProperty.flat_opcycles_of_exactAt`, since
  `H^{a-1}(P ⊗ F) = H^{a-1}(K ⊗ᴸ F[0]) = 0` for every `F`.

## Main results

- `CategoryTheory.ObjectProperty.flat_opcycles_of_exactAt`: the Tor criterion for the
  flatness of a cokernel `P^a / d(P^{a-1})` of a map of flat objects.
- `CochainComplex.exists_quasiIso_flat_of_isStrictlyLE`: a bounded above complex has a
  bounded above flat resolution.
- `DerivedCategory.QObjTensorSingleFunctorObjIso`: for a K-flat complex `P`, the isomorphism
  `P ⊗ᴸ F[0] ≅ P ⊗ F`.
- `DerivedCategory.torAmplitudeIn_Q_obj_of_flat`: a complex of flat objects in degrees
  `[a, b]` has Tor amplitude in `[a, b]`.
- `DerivedCategory.exists_iso_Q_obj_flat_of_torAmplitudeIn` and
  `DerivedCategory.torAmplitudeIn_iff_exists_iso_Q_obj_flat`: an object has Tor amplitude in
  `[a, b]` exactly when it is represented by a complex of flat objects in degrees `[a, b]`.
- `DerivedCategory.torAmplitudeIn_tensor`: Tor amplitudes add under the derived tensor
  product.

-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory

universe w v u

namespace CategoryTheory.ObjectProperty

variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C] [BraidedCategory C]
  [MonoidalClosed C] [MonoidalPreadditive C]

/-- **Tor criterion for flatness.** Let `P` be a cochain complex whose terms `P^{a-1}` and `P^a`
are flat. If for every object `F` the complex `P ⊗ F` is exact in degree `a - 1`, then the
cokernel `P^a / d(P^{a-1})` (the opcycles of `P` in degree `a`) is flat.

Tensoring with it is right exact, and a diagram chase shows that it preserves monomorphisms:
for a short exact sequence `F' ⟶ F ⟶ F''` the obstruction is a cycle of `P ⊗ F''` in
degree `a - 1`, which is a boundary by hypothesis. -/
lemma flat_opcycles_of_exactAt (P : CochainComplex C ℤ) (a : ℤ)
    (h₁ : flat (P.X (a - 1))) (h₂ : flat (P.X a))
    (hP : ∀ F : C, (((tensorRight F).mapHomologicalComplex (.up ℤ)).obj P).ExactAt (a - 1)) :
    flat (P.opcycles a) := by
  have := h₁.tensorLeft.preservesFiniteLimits
  have := h₂.tensorLeft.preservesFiniteLimits
  rw [flat_iff_preservesFiniteLimits,
    Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono]
  intro S hS
  refine ⟨hS.exact.map_of_epi_of_preservesCokernel _ hS.epi_g inferInstance, ?_⟩
  have := hS.mono_f
  have := hS.epi_g
  dsimp
  set d := P.d (a - 1) a
  set d' := P.d (a - 1 - 1) (a - 1)
  set p := P.pOpcycles a
  have hdp : d ≫ p = 0 := P.d_pOpcycles _ _
  have (F : C) : PreservesColimitsOfSize.{0, 0} (tensorRight F) :=
    preservesColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight F)
  -- the cokernel sequence `P^{a-1} ⟶ P^a ⟶ C ⟶ 0`, tensored with any object, stays exact
  have hcok (F : C) : (ShortComplex.mk (d ▷ F) (p ▷ F)
      (by rw [← comp_whiskerRight, hdp, MonoidalPreadditive.zero_whiskerRight])).Exact := by
    have h : (ShortComplex.mk d p hdp).Exact :=
      ShortComplex.exact_of_g_is_cokernel _ (P.opcyclesIsCokernel _ _ (by simp))
    exact h.map_of_epi_of_preservesCokernel (tensorRight F) (by dsimp; infer_instance)
      inferInstance
  have hpe (F : C) : Epi (p ▷ F) := (tensorRight F).map_epi p
  have hge (X : C) : Epi (X ◁ S.g) := (tensorLeft X).map_epi S.g
  refine Preadditive.mono_of_cancel_zero _ (fun {T} x hx ↦ ?_)
  -- lift `x` to `P^a ⊗ S.X₁`
  obtain ⟨T₁, π₁, _, y, hy⟩ := surjective_up_to_refinements_of_epi (p ▷ S.X₁) x
  -- its image in `P^a ⊗ S.X₂` dies in `C ⊗ S.X₂`, so it comes from `P^{a-1} ⊗ S.X₂`
  obtain ⟨T₂, π₂, _, z, hz⟩ :=
      (hcok S.X₂).exact_up_to_refinements (y ≫ P.X a ◁ S.f) (by
    dsimp
    rw [Category.assoc, whisker_exchange, ← Category.assoc, ← hy, Category.assoc,
      hx, comp_zero])
  -- the image of `z` in `P^{a-1} ⊗ S.X₃` is a cycle, hence a boundary
  have hex := (HomologicalComplex.exactAt_iff' _ (a - 1 - 1) (a - 1) a (by simp)
    (by simp)).1 (hP S.X₃)
  obtain ⟨T₃, π₃, _, w, hw⟩ := hex.exact_up_to_refinements (z ≫ P.X (a - 1) ◁ S.g) (by
    change (z ≫ P.X (a - 1) ◁ S.g) ≫ d ▷ S.X₃ = 0
    dsimp at hz
    rw [Category.assoc, whisker_exchange, ← Category.assoc, ← hz, Category.assoc,
      Category.assoc, ← MonoidalCategory.whiskerLeft_comp, S.zero,
      MonoidalPreadditive.whiskerLeft_zero, comp_zero, comp_zero])
  let w₀ : T₃ ⟶ P.X (a - 1 - 1) ⊗ S.X₃ := w
  have hw₂ : π₃ ≫ z ≫ P.X (a - 1) ◁ S.g = w₀ ≫ d' ▷ S.X₃ := hw
  obtain ⟨T₄, π₄, _, w', hw'⟩ :=
    surjective_up_to_refinements_of_epi (P.X (a - 1 - 1) ◁ S.g) w₀
  dsimp at hz
  -- correcting `z` by a boundary, it comes from `P^{a-1} ⊗ S.X₁`
  have hz' : (π₄ ≫ π₃ ≫ z - w' ≫ d' ▷ S.X₂) ≫ P.X (a - 1) ◁ S.g = 0 := by
    rw [Preadditive.sub_comp, Category.assoc, Category.assoc, hw₂, Category.assoc,
      ← whisker_exchange, ← reassoc_of% hw', sub_self]
  have hex₁ : (S.map (tensorLeft (P.X (a - 1)))).Exact := hS.exact.map _
  have : Mono (S.map (tensorLeft (P.X (a - 1)))).f :=
    (tensorLeft (P.X (a - 1))).map_mono S.f
  have : Mono (P.X a ◁ S.f) := (tensorLeft (P.X a)).map_mono S.f
  let v : T₄ ⟶ P.X (a - 1) ⊗ S.X₁ := hex₁.lift _ hz'
  have hv : v ≫ P.X (a - 1) ◁ S.f = π₄ ≫ π₃ ≫ z - w' ≫ d' ▷ S.X₂ :=
    hex₁.lift_f _ hz'
  have hvy : v ≫ d ▷ S.X₁ = π₄ ≫ π₃ ≫ π₂ ≫ y := by
    rw [← cancel_mono (P.X a ◁ S.f)]
    simp only [Category.assoc]
    rw [← whisker_exchange, reassoc_of% hv,
      Preadditive.sub_comp, Category.assoc, Category.assoc, ← hz, Category.assoc,
      ← comp_whiskerRight, P.d_comp_d, MonoidalPreadditive.zero_whiskerRight, comp_zero,
      sub_zero]
  rw [← cancel_epi (π₄ ≫ π₃ ≫ π₂ ≫ π₁), comp_zero]
  simp only [Category.assoc]
  rw [hy, ← reassoc_of% hvy, ← comp_whiskerRight, hdp,
    MonoidalPreadditive.zero_whiskerRight, comp_zero]

end CategoryTheory.ObjectProperty

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
  [Abelian.HasFunctorialFlatResolution C]

/-- A complex `L` vanishing above degree `b` has a flat resolution vanishing above degree `b`:
a quasi-isomorphism `P ⟶ L` from a complex `P` of flat objects with `P^n = 0` for `n > b`. It
is the total complex of the functorial flat resolutions of the terms of `L`. -/
lemma exists_quasiIso_flat_of_isStrictlyLE (L : CochainComplex C ℤ) (b : ℤ)
    [L.IsStrictlyLE b] :
    ∃ (P : CochainComplex C ℤ) (_ : P.IsStrictlyLE b) (π : P ⟶ L),
      QuasiIso π ∧ ∀ n, ObjectProperty.flat (P.X n) := by
  let Λ := (Classical.arbitrary (Abelian.LeftResolution
    (ObjectProperty.flat.ι : _ ⥤ C))).reduced
  let K : CochainComplex.Minus C := ⟨L, b, inferInstance⟩
  have : HasFiniteCoproducts (ObjectProperty.flat (A := C)).FullSubcategory := inferInstance
  have : HasZeroObject (ObjectProperty.flat (A := C)).FullSubcategory := inferInstance
  exact ⟨_, inferInstance, Λ.totalπ K, inferInstance, fun n ↦ (((Λ.bicomplexFunctor.obj
    K.obj).total (.up ℤ)).X n).property⟩

/-- Every complex has a K-flat resolution by a complex of flat objects: the functorial flat
resolution of an unbounded complex is a colimit of bounded above complexes of flat objects. -/
lemma exists_quasiIso_flat_kFlat (L : CochainComplex C ℤ) :
    ∃ (P : CochainComplex C ℤ) (π : P ⟶ L), QuasiIso π ∧ (∀ n, ObjectProperty.flat (P.X n)) ∧
      (HomologicalComplex.quasiIso C (.up ℤ)).kFlat P := by
  have (X : C) : PreservesColimitsOfShape ℤ ((curriedTensor C).flip.obj X) :=
    preservesColimitsOfShape_of_natIso (F := tensorLeft X)
      (NatIso.ofComponents (fun Y ↦ β_ X Y) (by intros; simp [curriedTensor]))
  let Λ := (Classical.arbitrary (Abelian.LeftResolution
    (ObjectProperty.flat.ι : _ ⥤ C))).reduced
  have hι : (ObjectProperty.flat.ι : _ ⥤ C).essImage ≤ ObjectProperty.flat := by
    rintro X ⟨Y, ⟨e⟩⟩
    exact ObjectProperty.prop_of_iso _ e Y.property
  refine ⟨Λ.resolutionFunctor.obj L, Λ.resolutionNatTrans.app L, inferInstance, fun n ↦ ?_,
    Λ.kFlat_resolutionFunctor_obj hι L⟩
  have := CochainComplex.closedUnderColimitsOfShape_flat C ℤ
  let c := Λ.colimitOfShapeResolutionFunctorObj L
  exact ObjectProperty.prop_of_isColimit _
    (isColimitOfPreserves (HomologicalComplex.eval C (.up ℤ) n) c.isColimit)
    (fun i ↦ hι _ ((c.prop_diag_obj i).1 n))

end CochainComplex

namespace DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
  [HasDerivedCategory.{w} C] [Abelian.HasFunctorialFlatResolution C]

/-- For a K-flat complex `P` and an object `F`, the derived tensor product `P ⊗ᴸ F[0]` is
the tensor product of complexes `P ⊗ F`, that is, `F` tensored onto each term of `P`. -/
noncomputable def QObjTensorSingleFunctorObjIso (P : CochainComplex C ℤ)
    (hP : (HomologicalComplex.quasiIso C (.up ℤ)).kFlat P) (F : C) :
    Q.obj P ⊗ (singleFunctor C 0).obj F ≅
      Q.obj (((tensorRight F).mapHomologicalComplex _).obj P) :=
  have hP' : (HomotopyCategory.quasiIso C (.up ℤ)).kFlat
      ((HomotopyCategory.quotient C (.up ℤ)).obj P) :=
    (HomotopyCategory.kFlat_quotient_obj_iff _).2 hP
  have := isIso_tensorLeftCounit _ hP'
  tensorIso ((quotientCompQhIso C).symm.app P)
      ((singleFunctorIsoCompQ C 0).app F ≪≫ (quotientCompQhIso C).symm.app _) ≪≫
    (asIso (tensorLeftCounit ((HomotopyCategory.quotient C (.up ℤ)).obj P))).app
      ((HomotopyCategory.quotient C (.up ℤ)).obj
        ((HomologicalComplex.single C (.up ℤ) 0).obj F)) ≪≫
    Qh.mapIso (Functor.Monoidal.μIso (HomotopyCategory.quotient C (.up ℤ)) _ _) ≪≫
    Qh.mapIso ((HomotopyCategory.quotient C (.up ℤ)).mapIso
      ((CochainComplex.map₂HomologicalComplexFlipObjSingleIso (curriedTensor C) F).app P)) ≪≫
    (quotientCompQhIso C).app _

variable (C) in
/-- The monoidal unit of `D(C)` is the unit object of `C` placed in degree `0`. -/
noncomputable def singleFunctorObjUnitIso :
    (singleFunctor C 0).obj (𝟙_ C) ≅ 𝟙_ (DerivedCategory C) :=
  have : IsIso (Functor.LaxMonoidal.ε (Qh (C := C))) :=
    inferInstanceAs (IsIso (Functor.LaxMonoidal.ε (toDerivedMonoidal Qh
      (HomotopyCategory.quasiIso C (.up ℤ)))))
  (singleFunctorIsoCompQ C 0).app _ ≪≫ (quotientCompQhIso C).symm.app _ ≪≫
    Qh.mapIso ((Functor.Monoidal.εIso (HomotopyCategory.quotient C (.up ℤ))).symm :
        (HomotopyCategory.quotient C (.up ℤ)).obj (𝟙_ (CochainComplex C ℤ)) ≅ _) ≪≫
    (asIso (Functor.LaxMonoidal.ε Qh)).symm

/-- An object of Tor amplitude in `[a, b]` has homology concentrated in `[a, b]`: test the Tor
amplitude against the unit. -/
lemma homologyConcentratedIn_of_torAmplitudeIn {a b : ℤ} {K : DerivedCategory C}
    (hK : torAmplitudeIn C a b K) : homologyConcentratedIn a b K := by
  obtain ⟨h₁, h₂⟩ := hK (𝟙_ C)
  have e : K ⊗ (singleFunctor C 0).obj (𝟙_ C) ≅ K :=
    whiskerLeftIso K (singleFunctorObjUnitIso C) ≪≫ ρ_ K
  exact ⟨TStructure.t.isGE_of_iso e a, TStructure.t.isLE_of_iso e b⟩

/-- A complex of flat objects concentrated in degrees `[a, b]` has Tor amplitude in `[a, b]`:
it is K-flat, so its derived tensor product with `F[0]` is the tensor product of complexes,
which is concentrated in degrees `[a, b]`. -/
lemma torAmplitudeIn_Q_obj_of_flat (P : CochainComplex C ℤ) (a b : ℤ)
    [P.IsStrictlyGE a] [P.IsStrictlyLE b] (hP : ∀ n, ObjectProperty.flat (P.X n)) :
    torAmplitudeIn C a b (Q.obj P) := fun F ↦ by
  have hP' := CochainComplex.kFlat_of_bounded_of_flat P a b hP
  rw [homologyConcentratedIn_iff]
  exact ⟨TStructure.t.isGE_of_iso (QObjTensorSingleFunctorObjIso P hP' F).symm a,
    TStructure.t.isLE_of_iso (QObjTensorSingleFunctorObjIso P hP' F).symm b⟩

/-- **Bounded flat model.** An object of Tor amplitude in `[a, b]` is represented by a complex
of flat objects concentrated in degrees `[a, b]`.

The object is concentrated in `[a, b]`, so it has a flat resolution `P` vanishing above `b`
(`CochainComplex.exists_quasiIso_flat_of_isStrictlyLE`). Its truncation `τ^{≥ a} P` still
represents it, and its term in degree `a`, the cokernel of `P^{a-1} ⟶ P^a`, is flat by the Tor
criterion `CategoryTheory.ObjectProperty.flat_opcycles_of_exactAt`, as
`H^{a-1}(P ⊗ F) = H^{a-1}(K ⊗ᴸ F[0])` vanishes for every `F`. -/
lemma exists_iso_Q_obj_flat_of_torAmplitudeIn {a b : ℤ} {K : DerivedCategory C}
    (hK : torAmplitudeIn C a b K) :
    ∃ (P : CochainComplex C ℤ) (_ : P.IsStrictlyGE a) (_ : P.IsStrictlyLE b),
      (∀ n, ObjectProperty.flat (P.X n)) ∧ Nonempty (Q.obj P ≅ K) := by
  obtain ⟨hGE, hLE⟩ := homologyConcentratedIn_of_torAmplitudeIn hK
  have : K.IsLE b := hLE
  have : K.IsGE a := hGE
  obtain ⟨L, _, ⟨e⟩⟩ := K.exists_iso_Q_obj_of_isLE b
  obtain ⟨P, _, π, _, hP⟩ := L.exists_quasiIso_flat_of_isStrictlyLE b
  have : IsIso (Q.map π) := by rwa [isIso_Q_map_iff_quasiIso]
  let e' : Q.obj P ≅ K := asIso (Q.map π) ≪≫ e.symm
  have hPk : (HomologicalComplex.quasiIso C (.up ℤ)).kFlat P :=
    CochainComplex.kFlat_of_isStrictlyLE_of_flat P b hP
  have : P.IsGE a := by
    rw [← isGE_Q_obj_iff]
    exact TStructure.t.isGE_of_iso e'.symm a
  -- `H^{a-1}(P ⊗ F) = H^{a-1}(K ⊗ᴸ F[0]) = 0`
  have hex (F : C) :
      (((tensorRight F).mapHomologicalComplex (.up ℤ)).obj P).ExactAt (a - 1) := by
    have := (hK F).1
    have : (Q.obj (((tensorRight F).mapHomologicalComplex (.up ℤ)).obj P)).IsGE a :=
      TStructure.t.isGE_of_iso
        ((whiskerRightIso e' _).symm ≪≫ QObjTensorSingleFunctorObjIso P hPk F) a
    rw [isGE_Q_obj_iff] at this
    exact CochainComplex.exactAt_of_isGE _ a _
  have hop := ObjectProperty.flat_opcycles_of_exactAt P a (hP _) (hP _) hex
  refine ⟨P.truncGE a, inferInstance, ?_, fun n ↦ ?_,
    ⟨(asIso (Q.map (P.πTruncGE a))).symm ≪≫ e'⟩⟩
  · rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    obtain hi' | rfl | hi' := lt_trichotomy i a
    · exact CochainComplex.isZero_of_isStrictlyGE _ a i hi'
    · exact (P.truncGEXIsoOpcycles i).isZero_iff.2
        (IsZero.of_epi (P.pOpcycles i) (P.isZero_of_isStrictlyLE b i hi))
    · exact (P.truncGEXIso a i hi').isZero_iff.2 (P.isZero_of_isStrictlyLE b i hi)
  · obtain hn | rfl | hn := lt_trichotomy n a
    · exact ObjectProperty.flat_of_isZero (CochainComplex.isZero_of_isStrictlyGE _ a n hn)
    · exact ObjectProperty.prop_of_iso _ (P.truncGEXIsoOpcycles n).symm hop
    · exact ObjectProperty.prop_of_iso _ (P.truncGEXIso a n hn).symm (hP n)

/-- An object of `D(C)` has Tor amplitude in `[a, b]` exactly when it is represented by a
complex of flat objects concentrated in degrees `[a, b]`. -/
lemma torAmplitudeIn_iff_exists_iso_Q_obj_flat (a b : ℤ) (K : DerivedCategory C) :
    torAmplitudeIn C a b K ↔
      ∃ (P : CochainComplex C ℤ) (_ : P.IsStrictlyGE a) (_ : P.IsStrictlyLE b),
        (∀ n, ObjectProperty.flat (P.X n)) ∧ Nonempty (Q.obj P ≅ K) := by
  refine ⟨exists_iso_Q_obj_flat_of_torAmplitudeIn, ?_⟩
  rintro ⟨P, _, _, hP, ⟨e⟩⟩
  exact (torAmplitudeIn C a b).prop_of_iso e (torAmplitudeIn_Q_obj_of_flat P a b hP)

/-- A flat object placed in degree `0` has Tor amplitude in `[0, 0]`: the single complex is its
own flat model. -/
lemma torAmplitudeIn_singleFunctor_obj_of_flat {F : C} (hF : ObjectProperty.flat F) :
    torAmplitudeIn C 0 0 ((singleFunctor C 0).obj F) := by
  refine (torAmplitudeIn_iff_exists_iso_Q_obj_flat 0 0 _).2
    ⟨(HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj F, inferInstance, inferInstance,
      fun n ↦ ?_, ⟨((singleFunctorIsoCompQ C 0).app F).symm⟩⟩
  by_cases hn : n = 0
  · subst hn
    exact ObjectProperty.prop_of_iso _ (HomologicalComplex.singleObjXSelf _ 0 F).symm hF
  · exact ObjectProperty.flat_of_isZero (HomologicalComplex.isZero_single_obj_X _ _ _ _ hn)

/-- For a K-flat complex `P` and any complex `L`, the derived tensor product `P ⊗ᴸ L` is the
tensor product of complexes `P ⊗ L`. -/
noncomputable def QObjTensorQObjIsoOfKFlatLeft (P L : CochainComplex C ℤ)
    (hP : (HomologicalComplex.quasiIso C (.up ℤ)).kFlat P) :
    Q.obj P ⊗ Q.obj L ≅ Q.obj (P ⊗ L) :=
  have hP' : (HomotopyCategory.quasiIso C (.up ℤ)).kFlat
      ((HomotopyCategory.quotient C (.up ℤ)).obj P) :=
    (HomotopyCategory.kFlat_quotient_obj_iff _).2 hP
  have := isIso_tensorLeftCounit _ hP'
  tensorIso ((quotientCompQhIso C).symm.app P) ((quotientCompQhIso C).symm.app L) ≪≫
    (asIso (tensorLeftCounit ((HomotopyCategory.quotient C (.up ℤ)).obj P))).app
      ((HomotopyCategory.quotient C (.up ℤ)).obj L) ≪≫
    Qh.mapIso (Functor.Monoidal.μIso (HomotopyCategory.quotient C (.up ℤ)) _ _) ≪≫
    (quotientCompQhIso C).app _

/-- For any complex `L` and a K-flat complex `P`, the derived tensor product `L ⊗ᴸ P` is the
tensor product of complexes `L ⊗ P`. -/
noncomputable def QObjTensorQObjIsoOfKFlatRight (L P : CochainComplex C ℤ)
    (hP : (HomologicalComplex.quasiIso C (.up ℤ)).kFlat P) :
    Q.obj L ⊗ Q.obj P ≅ Q.obj (L ⊗ P) :=
  have hP' : (HomotopyCategory.quasiIso C (.up ℤ)).kFlat
      ((HomotopyCategory.quotient C (.up ℤ)).obj P) :=
    (HomotopyCategory.kFlat_quotient_obj_iff _).2 hP
  have := isIso_tensorRightCounit _ hP'
  tensorIso ((quotientCompQhIso C).symm.app L) ((quotientCompQhIso C).symm.app P) ≪≫
    (asIso (tensorRightCounit ((HomotopyCategory.quotient C (.up ℤ)).obj P))).app
      ((HomotopyCategory.quotient C (.up ℤ)).obj L) ≪≫
    Qh.mapIso (Functor.Monoidal.μIso (HomotopyCategory.quotient C (.up ℤ)) _ _) ≪≫
    (quotientCompQhIso C).app _

/-- The isomorphism `L ⊗ᴸ P ≅ L ⊗ P` for a K-flat complex `P` is natural in `L`: for
`f : L ⟶ L'` the square
```
  Q(L) ⊗ᴸ Q(P) ──≅──▶ Q(L ⊗ P)
       │                  │
  Q(f) ▷ Q(P)          Q(f ▷ P)
       ▼                  ▼
  Q(L') ⊗ᴸ Q(P) ─≅──▶ Q(L' ⊗ P)
```
commutes. -/
@[reassoc]
lemma qObjTensorQObjIsoOfKFlatRight_hom_naturality {L L' : CochainComplex C ℤ} (f : L ⟶ L')
    (P : CochainComplex C ℤ) (hP : (HomologicalComplex.quasiIso C (.up ℤ)).kFlat P) :
    Q.map f ▷ Q.obj P ≫ (QObjTensorQObjIsoOfKFlatRight L' P hP).hom =
      (QObjTensorQObjIsoOfKFlatRight L P hP).hom ≫ Q.map (f ▷ P) := by
  have h₁ := (tensorRightCounit ((HomotopyCategory.quotient C (.up ℤ)).obj P)).naturality
    ((HomotopyCategory.quotient C (.up ℤ)).map f)
  have h₂ := Functor.LaxMonoidal.μ_natural_left (HomotopyCategory.quotient C (.up ℤ)) f P
  have h₃ := (quotientCompQhIso C).hom.naturality (f ▷ P)
  have h₄ := (quotientCompQhIso C).inv.naturality f
  dsimp at h₁ h₂ h₃ h₄
  simp only [QObjTensorQObjIsoOfKFlatRight, Iso.trans_hom, tensorIso_hom, Iso.app_hom,
    Iso.symm_hom, asIso_hom, Functor.mapIso_hom, Category.assoc]
  have key : Q.map f ▷ Q.obj P ≫
      ((quotientCompQhIso C).inv.app L' ⊗ₘ (quotientCompQhIso C).inv.app P) =
      ((quotientCompQhIso C).inv.app L ⊗ₘ (quotientCompQhIso C).inv.app P) ≫
        Qh.map ((HomotopyCategory.quotient C (.up ℤ)).map f) ▷ _ := by
    rw [← tensorHom_id, ← tensorHom_id, tensorHom_comp_tensorHom, tensorHom_comp_tensorHom, h₄,
      Category.comp_id, Category.id_comp]
  rw [reassoc_of% key, reassoc_of% h₁, ← h₃, Functor.Monoidal.μIso_hom, ← Qh.map_comp_assoc,
    h₂, Qh.map_comp_assoc, Functor.Monoidal.μIso_hom]

/-- If `K` has Tor amplitude in `[a, b]` and `N` has homology concentrated in `[c, d]`, then
`K ⊗ᴸ N` has homology concentrated in `[a + c, b + d]`: represent `K` by a complex of flat
objects in degrees `[a, b]` and `N` by a complex in degrees `[c, d]`. -/
lemma homologyConcentratedIn_tensor_of_torAmplitudeIn_left {a b c d : ℤ}
    {K N : DerivedCategory C}
    (hK : torAmplitudeIn C a b K) (hN : homologyConcentratedIn c d N) :
    homologyConcentratedIn (a + c) (b + d) (K ⊗ N) := by
  obtain ⟨P, _, _, hP, ⟨e⟩⟩ := exists_iso_Q_obj_flat_of_torAmplitudeIn hK
  have : N.IsGE c := hN.1
  have : N.IsLE d := hN.2
  obtain ⟨L, _, _, ⟨e'⟩⟩ := N.exists_iso_Q_obj_of_isGE_of_isLE c d
  have hPk := CochainComplex.kFlat_of_bounded_of_flat P a b hP
  have := CochainComplex.isStrictlyGE_tensorObj P L a c
  have := CochainComplex.isStrictlyLE_tensorObj P L b d
  have e'' : K ⊗ N ≅ Q.obj (P ⊗ L) :=
    tensorIso e.symm e' ≪≫ QObjTensorQObjIsoOfKFlatLeft P L hPk
  exact ⟨TStructure.t.isGE_of_iso e''.symm _, TStructure.t.isLE_of_iso e''.symm _⟩

/-- If `N` has homology concentrated in `[c, d]` and `M` has Tor amplitude in `[a, b]`, then
`N ⊗ᴸ M` has homology concentrated in `[c + a, d + b]`. -/
lemma homologyConcentratedIn_tensor_of_torAmplitudeIn_right {a b c d : ℤ}
    {N M : DerivedCategory C} (hN : homologyConcentratedIn c d N)
    (hM : torAmplitudeIn C a b M) :
    homologyConcentratedIn (c + a) (d + b) (N ⊗ M) := by
  obtain ⟨P, _, _, hP, ⟨e⟩⟩ := exists_iso_Q_obj_flat_of_torAmplitudeIn hM
  have : N.IsGE c := hN.1
  have : N.IsLE d := hN.2
  obtain ⟨L, _, _, ⟨e'⟩⟩ := N.exists_iso_Q_obj_of_isGE_of_isLE c d
  have hPk := CochainComplex.kFlat_of_bounded_of_flat P a b hP
  have := CochainComplex.isStrictlyGE_tensorObj L P c a
  have := CochainComplex.isStrictlyLE_tensorObj L P d b
  have e'' : N ⊗ M ≅ Q.obj (L ⊗ P) :=
    tensorIso e' e.symm ≪≫ QObjTensorQObjIsoOfKFlatRight L P hPk
  exact ⟨TStructure.t.isGE_of_iso e''.symm _, TStructure.t.isLE_of_iso e''.symm _⟩

/-- **Tor amplitudes add under the derived tensor product.** If `K` and `M` have Tor amplitude
in `[a, b]` and `[c, d]`, then `K ⊗ᴸ M` has Tor amplitude in `[a + c, b + d]`. -/
lemma torAmplitudeIn_tensor {a b c d : ℤ} {K M : DerivedCategory C}
    (hK : torAmplitudeIn C a b K) (hM : torAmplitudeIn C c d M) :
    torAmplitudeIn C (a + c) (b + d) (K ⊗ M) := fun F ↦ by
  obtain ⟨h₁, h₂⟩ := homologyConcentratedIn_tensor_of_torAmplitudeIn_left hK (hM F)
  exact ⟨TStructure.t.isGE_of_iso (α_ K M _).symm _,
    TStructure.t.isLE_of_iso (α_ K M _).symm _⟩

/-- If `K` has Tor amplitude in `[a, b]` and `N` vanishes above `d`, then `K ⊗ᴸ N` vanishes
above `b + d`. -/
lemma isLE_tensor_of_torAmplitudeIn {a b : ℤ} {K : DerivedCategory C}
    (hK : torAmplitudeIn C a b K) (N : DerivedCategory C) (d : ℤ) [N.IsLE d] :
    (K ⊗ N).IsLE (b + d) := by
  obtain ⟨P, _, _, hP, ⟨e⟩⟩ := exists_iso_Q_obj_flat_of_torAmplitudeIn hK
  obtain ⟨L, _, ⟨e'⟩⟩ := N.exists_iso_Q_obj_of_isLE d
  have := CochainComplex.isStrictlyLE_tensorObj P L b d
  exact TStructure.t.isLE_of_iso (tensorIso e.symm e' ≪≫
    QObjTensorQObjIsoOfKFlatLeft P L (CochainComplex.kFlat_of_bounded_of_flat P a b hP)).symm _

/-- The derived tensor product of an object vanishing above `b` and one vanishing above `d`
vanishes above `b + d`: represent the first by a bounded above complex of flat objects. -/
lemma isLE_tensor (K N : DerivedCategory C) (b d : ℤ) [K.IsLE b] [N.IsLE d] :
    (K ⊗ N).IsLE (b + d) := by
  obtain ⟨L, _, ⟨e⟩⟩ := K.exists_iso_Q_obj_of_isLE b
  obtain ⟨P, _, π, _, hP⟩ := L.exists_quasiIso_flat_of_isStrictlyLE b
  have : IsIso (Q.map π) := by rwa [isIso_Q_map_iff_quasiIso]
  obtain ⟨M, _, ⟨e'⟩⟩ := N.exists_iso_Q_obj_of_isLE d
  have := CochainComplex.isStrictlyLE_tensorObj P M b d
  exact TStructure.t.isLE_of_iso (tensorIso (e ≪≫ (asIso (Q.map π)).symm) e' ≪≫
    QObjTensorQObjIsoOfKFlatLeft P M (CochainComplex.kFlat_of_isStrictlyLE_of_flat P b hP)).symm _

/-- If `K` has Tor amplitude in `[a, b]` and `N` vanishes below `c`, then `K ⊗ᴸ N` vanishes
below `a + c`. -/
lemma isGE_tensor_of_torAmplitudeIn {a b : ℤ} {K : DerivedCategory C}
    (hK : torAmplitudeIn C a b K) (N : DerivedCategory C) (c : ℤ) [N.IsGE c] :
    (K ⊗ N).IsGE (a + c) := by
  obtain ⟨P, _, _, hP, ⟨e⟩⟩ := exists_iso_Q_obj_flat_of_torAmplitudeIn hK
  obtain ⟨L, _, ⟨e'⟩⟩ := N.exists_iso_Q_obj_of_isGE c
  have := CochainComplex.isStrictlyGE_tensorObj P L a c
  exact TStructure.t.isGE_of_iso (tensorIso e.symm e' ≪≫
    QObjTensorQObjIsoOfKFlatLeft P L (CochainComplex.kFlat_of_bounded_of_flat P a b hP)).symm _

/-- **The dual of an object of Tor amplitude in `[a, b]` has Tor amplitude in `[-b, -a]`.**
If `L` is dual to `K` on both sides, maps `G ⟶ L ⊗ᴸ F[0]` correspond to maps
`K ⊗ᴸ G ⟶ F[0]`, and maps `L ⊗ᴸ F[0] ⟶ G` to maps `F[0] ⟶ K ⊗ᴸ G`; the Tor amplitude of `K`
makes these vanish for `G` above `-b - 1`, respectively below `-a + 1`. -/
lemma torAmplitudeIn_of_exactPairing {a b : ℤ} {K L : DerivedCategory C} [ExactPairing L K]
    [ExactPairing K L] (hK : torAmplitudeIn C a b K) : torAmplitudeIn C (-b) (-a) L := by
  intro F
  refine ⟨(TStructure.t.isGE_iff_orthogonal (-b - 1) (-b) (by omega) _).2 fun Y f hY ↦ ?_,
    (TStructure.t.isLE_iff_orthogonal (-a) (-a + 1) rfl _).2 fun Y f hY ↦ ?_⟩
  · have : Y.IsLE (-b - 1) := hY
    have := isLE_tensor_of_torAmplitudeIn hK Y (-b - 1)
    obtain ⟨g, rfl⟩ := (tensorLeftHomEquiv Y L K ((singleFunctor C 0).obj F)).surjective f
    rw [TStructure.t.zero g (b + (-b - 1)) 0 (by omega)]
    simp [tensorLeftHomEquiv]
  · have : Y.IsGE (-a + 1) := hY
    have := isGE_tensor_of_torAmplitudeIn hK Y (-a + 1)
    have h := TStructure.t.zero
      (tensorLeftHomEquiv ((singleFunctor C 0).obj F) K L Y f) 0 (a + (-a + 1)) (by omega)
    rw [← (tensorLeftHomEquiv ((singleFunctor C 0).obj F) K L Y).symm_apply_apply f, h]
    simp [tensorLeftHomEquiv]

/-- A right adjoint `G` of `K ⊗ᴸ -`, for `K` vanishing above `b`, sends an object vanishing below
`c` to one vanishing below `c - b`: maps `Y ⟶ G M` correspond to maps `K ⊗ᴸ Y ⟶ M`, which vanish
for `Y` vanishing above `c - b - 1`, since `K ⊗ᴸ Y` then vanishes above `c - 1`. In particular
this applies to the internal hom `RHom(K, -)`. -/
lemma isGE_obj_of_adjunction {K : DerivedCategory C} {G : DerivedCategory C ⥤ DerivedCategory C}
    (adj : tensorLeft K ⊣ G) (M : DerivedCategory C) (b c : ℤ) [K.IsLE b] [M.IsGE c] :
    (G.obj M).IsGE (c - b) := by
  refine (TStructure.t.isGE_iff_orthogonal (c - b - 1) (c - b) (by omega) _).2 fun Y f hY ↦ ?_
  have : Y.IsLE (c - b - 1) := hY
  have : TStructure.t.IsLE ((tensorLeft K).obj Y) (b + (c - b - 1)) := isLE_tensor K Y b _
  obtain ⟨g, rfl⟩ := (adj.homEquiv Y M).surjective f
  rw [TStructure.t.zero g (b + (c - b - 1)) c (by omega)]
  have : G.IsRightAdjoint := adj.isRightAdjoint
  rw [Adjunction.homEquiv_unit, Functor.map_zero, Limits.comp_zero]

end DerivedCategory
