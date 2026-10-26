import Langlands.Cohomology.AcyclicResolution.Lift
import Langlands.Cohomology.AcyclicResolution.Statement

/-!
# Comparison of right resolutions with right derived functors

Let `F : C ⥤ D` be an additive functor between abelian categories, where `C` has injective
resolutions, and let `ε : A[0] ⟶ K` be a right resolution of `A` (a quasi-isomorphism from
`A` in degree zero to a cochain complex `K` indexed by `ℕ`).

* `comparison F I φ n` is the map `Hⁿ(F K) ⟶ Rⁿ F A` induced by a cochain map
  `φ : K ⟶ I` to an injective resolution `I` of `A`: the homology map of `F φ`, followed by
  the inverse of Mathlib's identification `I.isoRightDerivedObj F n`.
* `comparison_eq`: for lifts compatible with the augmentations, the map depends neither on
  the injective resolution nor on the lift. `resolutionComparison F ε n` is the map for
  Mathlib's chosen resolution `injectiveResolution A` and the lift `lift ε (𝟙 A)`.
* `comparison_naturality`, `resolutionComparison_naturality`: naturality with respect to
  maps of resolutions lying over a map `A ⟶ B`.
* `toRightDerivedZero_eq_comparison`, `comparison_zero`: in degree zero the comparison is
  compatible with `F.toRightDerivedZero`; for left exact `F` it is the composite of
  `homologyZeroIso F ε : H⁰(F K) ≅ F A` with `F.rightDerivedZeroIsoSelf.inv`.
* `comparisonNatTrans F 𝒦 e he n`: for a functorial right resolution
  `e : single₀ C ⟶ 𝒦` whose components are quasi-isomorphisms, the natural transformation
  `𝒦 ⋙ F.mapHomologicalComplex _ ⋙ homologyFunctor D _ n ⟶ F.rightDerived n` whose
  component at `A` is `comparison F I φ n` for every compatible `(I, φ)`
  (`comparisonNatTrans_app`). In degree zero and for left exact `F` it is an isomorphism
  (`comparisonNatTrans_zero`).
* `comparisonNatIso`: given the separate theorem obligation
  `AcyclicResolutionComparisonStatement` as a hypothesis, and `F`-acyclicity of every term of
  every `𝒦.obj A`, the transformation is a natural isomorphism. The obligation is not
  proved here.

This is the comparison of Cartan–Eilenberg, Chapter V, Proposition 1.1a and §3, for a
covariant functor.
-/

open CategoryTheory CategoryTheory.Limits HomologicalComplex

noncomputable section

namespace Langlands.Cohomology.AcyclicResolution

universe v u v' u'

variable {C : Type u} [Category.{v} C] [Abelian C] [HasInjectiveResolutions C]
  {D : Type u'} [Category.{v'} D] [Abelian D] (F : C ⥤ D) [F.Additive]

section Comparison

variable {A : C} {K : CochainComplex C ℕ}

/-- The degree-`n` comparison map `Hⁿ(F K) ⟶ Rⁿ F A` induced by a cochain map `φ` from `K`
to an injective resolution `I` of `A`: the homology map of `F φ` followed by the inverse of
Mathlib's identification of `Rⁿ F A` with the homology of `F I`. -/
def comparison (I : InjectiveResolution A) (φ : K ⟶ I.cocomplex) (n : ℕ) :
    (F.mapHomologicalComplex _ ⋙ HomologicalComplex.homologyFunctor D _ n).obj K ⟶
      (F.rightDerived n).obj A :=
  (F.mapHomologicalComplex _ ⋙ HomologicalComplex.homologyFunctor D _ n).map φ ≫
    (I.isoRightDerivedObj F n).inv

variable (ε : (CochainComplex.single₀ C).obj A ⟶ K) [QuasiIso ε]

omit [HasInjectiveResolutions C] in
/-- The lift of `ε` into an injective resolution of `A` over the identity of `A` is compatible
with the augmentations. -/
lemma comp_lift_id (I : InjectiveResolution A) : ε ≫ lift ε (𝟙 A) I.ι = I.ι := by
  rw [comp_lift, CategoryTheory.Functor.map_id, Category.id_comp]

/-- The comparison map does not depend on the injective resolution or on the
augmentation-compatible lift. -/
theorem comparison_eq {I J : InjectiveResolution A} (φ : K ⟶ I.cocomplex)
    (ψ : K ⟶ J.cocomplex) (hφ : ε ≫ φ = I.ι) (hψ : ε ≫ ψ = J.ι) (n : ℕ) :
    comparison F I φ n = comparison F J ψ n := by
  let h := InjectiveResolution.desc (𝟙 A) J I
  have hh : Homotopy (φ ≫ h) ψ := homotopyOfComp ε _ _ (by
    rw [← Category.assoc, hφ, InjectiveResolution.desc_commutes, CategoryTheory.Functor.map_id,
      Category.id_comp, hψ])
  have key : (F.mapHomologicalComplex _ ⋙ HomologicalComplex.homologyFunctor D _ n).map ψ =
      (F.mapHomologicalComplex _ ⋙ HomologicalComplex.homologyFunctor D _ n).map φ ≫
        (F.mapHomologicalComplex _ ⋙ HomologicalComplex.homologyFunctor D _ n).map h := by
    rw [← Functor.map_comp]
    exact ((F.mapHomotopy hh).homologyMap_eq n).symm
  rw [comparison, comparison, key, Category.assoc,
    ← InjectiveResolution.isoRightDerivedObj_inv_naturality (𝟙 A) I J h
      (InjectiveResolution.desc_commutes_zero (𝟙 A) J I) F n,
    CategoryTheory.Functor.map_id, Category.comp_id]

/-- The comparison map of the right resolution `ε`, computed with Mathlib's chosen injective
resolution of `A` and the lift of `ε` over the identity. -/
def resolutionComparison (n : ℕ) :
    (F.mapHomologicalComplex _ ⋙ HomologicalComplex.homologyFunctor D _ n).obj K ⟶
      (F.rightDerived n).obj A :=
  comparison F (injectiveResolution A) (lift ε (𝟙 A) (injectiveResolution A).ι) n

/-- The comparison map of `ε` is the comparison map of every augmentation-compatible lift to
every injective resolution. -/
theorem resolutionComparison_eq (I : InjectiveResolution A) (φ : K ⟶ I.cocomplex)
    (hφ : ε ≫ φ = I.ι) (n : ℕ) :
    resolutionComparison F ε n = comparison F I φ n :=
  comparison_eq F ε _ φ (comp_lift_id ε _) hφ n

/-- Comparison maps commute with maps of right resolutions lying over a map `f : A ⟶ B`. -/
@[reassoc]
theorem comparison_naturality {B : C} {L : CochainComplex C ℕ}
    (η : (CochainComplex.single₀ C).obj B ⟶ L) (f : A ⟶ B) (g : K ⟶ L)
    (hg : ε ≫ g = (CochainComplex.single₀ C).map f ≫ η)
    {I : InjectiveResolution A} {J : InjectiveResolution B}
    (φ : K ⟶ I.cocomplex) (ψ : L ⟶ J.cocomplex) (hφ : ε ≫ φ = I.ι) (hψ : η ≫ ψ = J.ι)
    (n : ℕ) :
    (F.mapHomologicalComplex _ ⋙ HomologicalComplex.homologyFunctor D _ n).map g ≫
        comparison F J ψ n =
      comparison F I φ n ≫ (F.rightDerived n).map f := by
  let h := InjectiveResolution.desc f J I
  have hh : Homotopy (g ≫ ψ) (φ ≫ h) := homotopyOfComp ε _ _ (by
    rw [← Category.assoc, hg, Category.assoc, hψ, ← Category.assoc, hφ,
      InjectiveResolution.desc_commutes])
  have key : (F.mapHomologicalComplex _ ⋙ HomologicalComplex.homologyFunctor D _ n).map g ≫
        (F.mapHomologicalComplex _ ⋙ HomologicalComplex.homologyFunctor D _ n).map ψ =
      (F.mapHomologicalComplex _ ⋙ HomologicalComplex.homologyFunctor D _ n).map φ ≫
        (F.mapHomologicalComplex _ ⋙ HomologicalComplex.homologyFunctor D _ n).map h := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact (F.mapHomotopy hh).homologyMap_eq n
  have key' := reassoc_of% key
  rw [comparison, comparison, Category.assoc,
    InjectiveResolution.isoRightDerivedObj_inv_naturality f I J h
      (InjectiveResolution.desc_commutes_zero f J I) F n]
  exact key' _

/-- Comparison maps of right resolutions commute with maps of right resolutions lying over a
map `f : A ⟶ B`. -/
@[reassoc]
theorem resolutionComparison_naturality {B : C} {L : CochainComplex C ℕ}
    (η : (CochainComplex.single₀ C).obj B ⟶ L) [QuasiIso η] (f : A ⟶ B) (g : K ⟶ L)
    (hg : ε ≫ g = (CochainComplex.single₀ C).map f ≫ η) (n : ℕ) :
    (F.mapHomologicalComplex _ ⋙ HomologicalComplex.homologyFunctor D _ n).map g ≫
        resolutionComparison F η n =
      resolutionComparison F ε n ≫ (F.rightDerived n).map f :=
  comparison_naturality F ε η f g hg _ _ (comp_lift_id ε _) (comp_lift_id η _) n

end Comparison

section Zero

variable {A : C} {K : CochainComplex C ℕ} (ε : (CochainComplex.single₀ C).obj A ⟶ K)

omit [HasInjectiveResolutions C] in
/-- The morphism from `F A` to the degree-zero cycles of `F K` induced by the augmentation. -/
def toCyclesZero : F.obj A ⟶ ((F.mapHomologicalComplex _).obj K).cycles 0 :=
  ((F.mapHomologicalComplex _).obj K).liftCycles (F.map (ε.f 0)) 1 (by simp) (by
    exact (F.map_comp _ _).symm.trans ((congrArg F.map (f_zero_comp_d ε)).trans (F.map_zero _ _)))

omit [HasInjectiveResolutions C] in
/-- The morphism `toCyclesZero F ε` followed by the inclusion of cycles is `F` applied to the
degree-zero component of `ε`. -/
@[reassoc (attr := simp)]
lemma toCyclesZero_iCycles :
    toCyclesZero F ε ≫ ((F.mapHomologicalComplex _).obj K).iCycles 0 = F.map (ε.f 0) := by
  simp [toCyclesZero]

/-- In degree zero, `F.toRightDerivedZero` factors through the comparison map of any
augmentation-compatible lift. No exactness of `F` is needed. -/
theorem toRightDerivedZero_eq_comparison (I : InjectiveResolution A) (φ : K ⟶ I.cocomplex)
    (hφ : ε ≫ φ = I.ι) :
    F.toRightDerivedZero.app A =
      toCyclesZero F ε ≫ ((F.mapHomologicalComplex _).obj K).homologyπ 0 ≫
        comparison F I φ 0 := by
  have h : toCyclesZero F ε ≫ HomologicalComplex.cyclesMap ((F.mapHomologicalComplex _).map φ) 0 =
      I.toRightDerivedZero' F := by
    rw [← cancel_mono (HomologicalComplex.iCycles _ 0), Category.assoc,
      HomologicalComplex.cyclesMap_i, toCyclesZero_iCycles_assoc,
      InjectiveResolution.toRightDerivedZero'_comp_iCycles, Functor.mapHomologicalComplex_map_f]
    exact (F.map_comp _ _).symm.trans (congrArg (fun g => F.map (HomologicalComplex.Hom.f g 0)) hφ)
  rw [I.toRightDerivedZero_eq F, ← h, Category.assoc]
  congr 1
  exact (HomologicalComplex.homologyπ_naturality_assoc _ 0 _).symm

variable [QuasiIso ε] [PreservesFiniteLimits F]

omit [HasInjectiveResolutions C] in
/-- For left exact `F`, `F A` is the degree-zero cycles of `F K`. -/
def cyclesZeroIso : F.obj A ≅ ((F.mapHomologicalComplex _).obj K).cycles 0 :=
  IsLimit.conePointUniqueUpToIso (KernelFork.mapIsLimit _ (isLimitKernelFork ε) F)
    (((F.mapHomologicalComplex _).obj K).cyclesIsKernel 0 1 (by simp))

omit [HasInjectiveResolutions C] in
/-- The identification `cyclesZeroIso F ε` is the morphism `toCyclesZero F ε`. -/
lemma cyclesZeroIso_hom : (cyclesZeroIso F ε).hom = toCyclesZero F ε := by
  rw [← cancel_mono (HomologicalComplex.iCycles _ 0), toCyclesZero_iCycles]
  exact IsLimit.conePointUniqueUpToIso_hom_comp
    (KernelFork.mapIsLimit _ (isLimitKernelFork ε) F)
    (((F.mapHomologicalComplex _).obj K).cyclesIsKernel 0 1 (by simp)) WalkingParallelPair.zero

omit [HasInjectiveResolutions C] in
/-- For left exact `F`, the degree-zero cohomology of `F K` is `F A`. -/
def homologyZeroIso :
    (F.mapHomologicalComplex _ ⋙ HomologicalComplex.homologyFunctor D _ 0).obj K ≅ F.obj A :=
  (cyclesZeroIso F ε ≪≫ CochainComplex.isoHomologyπ₀ _).symm

/-- For left exact `F`, the degree-zero comparison map of any augmentation-compatible lift is
the identification of `H⁰(F K)` with `F A`, followed by `F A ≅ R⁰ F A`. -/
theorem comparison_zero (I : InjectiveResolution A) (φ : K ⟶ I.cocomplex)
    (hφ : ε ≫ φ = I.ι) :
    comparison F I φ 0 = (homologyZeroIso F ε).hom ≫ F.rightDerivedZeroIsoSelf.inv.app A := by
  change _ = _ ≫ F.toRightDerivedZero.app A
  rw [toRightDerivedZero_eq_comparison F ε I φ hφ, ← cyclesZeroIso_hom, homologyZeroIso,
    Iso.symm_hom, Iso.trans_inv]
  have e1 := Iso.inv_hom_id_assoc (cyclesZeroIso F ε)
    (((F.mapHomologicalComplex _).obj K).homologyπ 0 ≫ comparison F I φ 0)
  have e2 := Iso.inv_hom_id_assoc
    (CochainComplex.isoHomologyπ₀ ((F.mapHomologicalComplex _).obj K)) (comparison F I φ 0)
  exact ((Category.assoc _ _ _).trans
    ((congrArg (fun x => (CochainComplex.isoHomologyπ₀ _).inv ≫ x) e1).trans e2)).symm

end Zero

section Functorial

variable (𝒦 : C ⥤ CochainComplex C ℕ) (e : CochainComplex.single₀ C ⟶ 𝒦)
  (he : ∀ A, QuasiIso (e.app A))

/-- The comparison transformation of a functorial right resolution `e : single₀ C ⟶ 𝒦`, from
the cohomology of `F` applied to `𝒦` to the right derived functors of `F`. -/
def comparisonNatTrans (n : ℕ) :
    𝒦 ⋙ F.mapHomologicalComplex _ ⋙ HomologicalComplex.homologyFunctor D _ n ⟶
      F.rightDerived n where
  app A := have := he A; resolutionComparison F (e.app A) n
  naturality A B f := by
    have := he A
    have := he B
    exact resolutionComparison_naturality F (e.app A) (e.app B) f (𝒦.map f)
      (e.naturality f).symm n

/-- Each component of the comparison transformation is the comparison map of every
augmentation-compatible lift to every injective resolution. -/
theorem comparisonNatTrans_app (A : C) (I : InjectiveResolution A)
    (φ : (𝒦.obj A) ⟶ I.cocomplex) (hφ : e.app A ≫ φ = I.ι) (n : ℕ) :
    (comparisonNatTrans F 𝒦 e he n).app A = comparison F I φ n :=
  have := he A
  resolutionComparison_eq F (e.app A) I φ hφ n

variable [PreservesFiniteLimits F]

/-- For left exact `F`, the degree-zero cohomology of `F` applied to a functorial right
resolution is `F`. -/
def homologyZeroNatIso :
    𝒦 ⋙ F.mapHomologicalComplex _ ⋙ HomologicalComplex.homologyFunctor D _ 0 ≅ F :=
  NatIso.ofComponents (fun A => have := he A; homologyZeroIso F (e.app A)) (fun {A B} f => by
    have := he A
    have := he B
    have h : ∀ X, (homologyZeroIso F (e.app X)).hom =
        (comparisonNatTrans F 𝒦 e he 0).app X ≫ F.rightDerivedZeroIsoSelf.hom.app X := by
      intro X
      have := he X
      rw [comparisonNatTrans_app F 𝒦 e he X _ _ (comp_lift_id (e.app X) (injectiveResolution X)),
        comparison_zero F (e.app X) _ _ (comp_lift_id (e.app X) (injectiveResolution X)),
        Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
    rw [h, h, (comparisonNatTrans F 𝒦 e he 0).naturality_assoc,
      F.rightDerivedZeroIsoSelf.hom.naturality, Category.assoc])

/-- For left exact `F`, the degree-zero comparison transformation is the identification of
degree-zero cohomology with `F`, followed by `F ≅ R⁰ F`. -/
theorem comparisonNatTrans_zero :
    comparisonNatTrans F 𝒦 e he 0 =
      (homologyZeroNatIso F 𝒦 e he).hom ≫ F.rightDerivedZeroIsoSelf.inv := by
  ext A
  have := he A
  rw [NatTrans.comp_app, comparisonNatTrans_app F 𝒦 e he A _ _
      (comp_lift_id (e.app A) (injectiveResolution A)),
    comparison_zero F (e.app A) _ _ (comp_lift_id (e.app A) (injectiveResolution A))]
  rfl

/-- For left exact `F`, the degree-zero comparison transformation is an isomorphism. -/
instance isIso_comparisonNatTrans_zero : IsIso (comparisonNatTrans F 𝒦 e he 0) := by
  rw [comparisonNatTrans_zero]
  infer_instance

/-- If every term of every `𝒦.obj A` is `F`-acyclic, the separate theorem obligation
`AcyclicResolutionComparisonStatement` (taken as a hypothesis, not proved here) makes the
comparison transformation a natural isomorphism. -/
def comparisonNatIso
    (hcomp : AcyclicResolutionComparisonStatement.{u, v, u', v'})
    (hacyc : ∀ (A : C) (i n : ℕ), IsZero ((F.rightDerived (n + 1)).obj ((𝒦.obj A).X i)))
    (n : ℕ) :
    𝒦 ⋙ F.mapHomologicalComplex _ ⋙ HomologicalComplex.homologyFunctor D _ n ≅
      F.rightDerived n :=
  have : ∀ A, IsIso ((comparisonNatTrans F 𝒦 e he n).app A) := fun A =>
    (hcomp C D F A (𝒦.obj A) (e.app A) (he A) (hacyc A) (injectiveResolution A) _
      (comp_lift_id (e.app A) (injectiveResolution A))).2 n
  have := NatIso.isIso_of_isIso_app (comparisonNatTrans F 𝒦 e he n)
  asIso (comparisonNatTrans F 𝒦 e he n)

/-- The natural isomorphism `comparisonNatIso` is the comparison transformation. -/
@[simp]
lemma comparisonNatIso_hom
    (hcomp : AcyclicResolutionComparisonStatement.{u, v, u', v'})
    (hacyc : ∀ (A : C) (i n : ℕ), IsZero ((F.rightDerived (n + 1)).obj ((𝒦.obj A).X i)))
    (n : ℕ) :
    (comparisonNatIso F 𝒦 e he hcomp hacyc n).hom = comparisonNatTrans F 𝒦 e he n :=
  rfl

end Functorial

end Langlands.Cohomology.AcyclicResolution
