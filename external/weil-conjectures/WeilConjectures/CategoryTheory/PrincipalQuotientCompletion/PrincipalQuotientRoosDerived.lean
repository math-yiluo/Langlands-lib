/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.PrincipalQuotientCompletion.PrincipalQuotientCompletionModel
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import WeilConjectures.CategoryTheory.Strict.StrictRoosHomotopyFunctor
import WeilConjectures.Algebra.Homology.TotalTensorSigns.TotalTensorHomotopyConeSigns
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedPointwiseKanBridge
import WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy
import Mathlib.CategoryTheory.Limits.Final
import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit

/-! # Deriving the principal quotient Roos functor

Source: Stacks Project, sites-cohomology.tex, Tags 06YS, 06YT and 0941.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u v r w u' v'
open CategoryTheory CategoryTheory.Limits Opposite
section TensorHomotopy
open HomologicalComplex
variable {A : Type*} [Category A] [Preadditive A]
  (F : A ⥤ A ⥤ A) [F.Additive] [∀ M, (F.obj M).Additive]
  [∀ (K L : CochainComplex A ℤ), HasMapBifunctor K L F (.up ℤ)]

-- The total tensor homotopy in the second variable is natural in the first one.
private theorem tensorHomotopy_natural
    {K L X Y : CochainComplex A ℤ} (a : K ⟶ L) {f g : X ⟶ Y}
    (h : Homotopy f g) (i j : ℤ) :
    (((F.map₂CochainComplex.map a).app X).f i) ≫
        (mapBifunctorMapHomotopy₂ (𝟙 L) h F (.up ℤ)).hom i j =
      (mapBifunctorMapHomotopy₂ (𝟙 K) h F (.up ℤ)).hom i j ≫
        (((F.map₂CochainComplex.map a).app Y).f j) := by
  change (mapBifunctorMap a (𝟙 X) F (.up ℤ)).f i ≫
      mapBifunctorMapHomotopy.hom₂ (𝟙 L) h F (.up ℤ) i j =
    mapBifunctorMapHomotopy.hom₂ (𝟙 K) h F (.up ℤ) i j ≫
      (mapBifunctorMap a (𝟙 Y) F (.up ℤ)).f j
  ext p q hpq
  simp only [ι_mapBifunctorMap_assoc,
    mapBifunctorMapHomotopy.ιMapBifunctor_hom₂,
    mapBifunctorMapHomotopy.ιMapBifunctor_hom₂_assoc,
    HomologicalComplex.id_f, Linear.comp_units_smul, Linear.units_smul_comp,
    Category.assoc]
  by_cases he : ComplexShape.π (.up ℤ) (.up ℤ) (.up ℤ) (p, (ComplexShape.up ℤ).prev q) = j
  · rw [ιMapBifunctorOrZero_eq _ _ _ _ _ _ _ he,
      ιMapBifunctorOrZero_eq _ _ _ _ _ _ _ he, ι_mapBifunctorMap]
    simp only [HomologicalComplex.id_f, CategoryTheory.Functor.map_id, NatTrans.id_app,
      Category.id_comp]
    congr 1
    exact ((F.map (a.f p)).naturality_assoc
      (h.hom q ((ComplexShape.up ℤ).prev q)) _).symm
  · rw [ιMapBifunctorOrZero_eq_zero _ _ _ _ _ _ _ he,
      ιMapBifunctorOrZero_eq_zero _ _ _ _ _ _ _ he]
    simp

end TensorHomotopy

-- A full, essentially surjective functor is initial: every comma object maps
-- to a fixed lift of the target, giving a zigzag between any two objects.
private theorem initial_of_full_essSurj
    {A B : Type*} [Category A] [Category B] (F : A ⥤ B) [F.Full] [F.EssSurj] :
    F.Initial := by
  classical
  constructor
  intro Y
  let e := F.objObjPreimageIso Y
  let Z : CostructuredArrow F Y := CostructuredArrow.mk e.hom
  have lift (X : CostructuredArrow F Y) : Nonempty (X ⟶ Z) := by
    refine ⟨CostructuredArrow.homMk (F.preimage (X.hom ≫ e.inv)) ?_⟩
    simp [Z, e]
  let : Nonempty (CostructuredArrow F Y) := ⟨Z⟩
  apply zigzag_isConnected
  intro X X'
  exact (Zigzag.of_hom (lift X).some).trans (Zigzag.of_inv (lift X').some)

-- The induced functor on structured arrows is also full and essentially
-- surjective, so restricting the defining limit cone preserves its limit.
private noncomputable def pointwise_precomp_full
    {A C D H : Type*} [Category A] [Category C] [Category D] [Category H]
    (P : A ⥤ C) [P.Full] [P.EssSurj] (Q : C ⥤ D) (F : C ⥤ H) (L : D ⥤ H)
    (α : Q ⋙ L ⟶ F)
    (h : (Functor.RightExtension.mk L α).IsPointwiseRightKanExtension) :
    (Functor.RightExtension.mk L
      ((Functor.associator P Q L).hom ≫ Functor.whiskerLeft P α)).IsPointwiseRightKanExtension := by
  intro Y
  let p := StructuredArrow.pre Y P Q
  let : p.Initial := initial_of_full_essSurj p
  apply Limits.IsLimit.ofIsoLimit ((Functor.Initial.isLimitWhiskerEquiv p _).symm (h Y))
  refine Limits.Cone.ext (Iso.refl _) ?_
  intro X
  dsimp [Functor.RightExtension.coneAt, Functor.RightExtension.mk, p]
  simp

-- Transport the defining limit cone through an equivalence of structured
-- arrow categories and the prescribed isomorphism of diagram functors.
private noncomputable def pointwise_change_iso
    {C D H : Type*} [Category C] [Category D] [Category H]
    {Q Q' : C ⥤ D} {F F' : C ⥤ H} (L : D ⥤ H)
    (i : Q ≅ Q') (j : F ≅ F') (α : Q ⋙ L ⟶ F)
    (h : (Functor.RightExtension.mk L α).IsPointwiseRightKanExtension) :
    (Functor.RightExtension.mk L
      (Functor.whiskerRight i.inv L ≫ α ≫ j.hom)).IsPointwiseRightKanExtension := by
  intro Y
  let Φ : StructuredArrow Y Q' ≌ StructuredArrow Y Q := Comma.mapRightIso _ i.symm
  let k : Φ.functor ⋙ StructuredArrow.proj Y Q ⋙ F ≅
      StructuredArrow.proj Y Q' ⋙ F' :=
    NatIso.ofComponents (fun X ↦ j.app X.right) (by
      intro X X' f
      exact j.hom.naturality f.right)
  apply Limits.IsLimit.ofIsoLimit
    ((Limits.IsLimit.postcomposeHomEquiv k _).symm ((h Y).whiskerEquivalence Φ))
  refine Limits.Cone.ext (Iso.refl _) ?_
  intro X
  dsimp [Functor.RightExtension.coneAt, Functor.RightExtension.mk, Φ, k]
  simp [Category.assoc]

private theorem resolving_class_left_derived
    (A : Type u) [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    (D : Type u') [Category.{v'} D]
    (F : HomotopyCategory A (.up ℤ) ⥤ D)
    (P : Set (HomotopyCategory A (.up ℤ)))
    (hres : ∀ X : HomotopyCategory A (.up ℤ),
      ∃ (Y : HomotopyCategory A (.up ℤ)) (s : Y ⟶ X),
        Y ∈ P ∧ HomotopyCategory.quasiIso A (.up ℤ) s)
    (hinv : ∀ (X Y : HomotopyCategory A (.up ℤ)) (s : X ⟶ Y),
      X ∈ P → Y ∈ P → HomotopyCategory.quasiIso A (.up ℤ) s → IsIso (F.map s)) :
    F.HasPointwiseLeftDerivedFunctor (HomotopyCategory.quasiIso A (.up ℤ)) ∧
      ∃ (L : DerivedCategory A ⥤ D) (ε : DerivedCategory.Qh ⋙ L ⟶ F),
        L.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso A (.up ℤ)) ∧
        ∀ X, X ∈ P → IsIso (ε.app X) := by
  classical
  let W := HomotopyCategory.quasiIso A (ComplexShape.up ℤ)
  let Q := DerivedCategory.Qh (C := A)
  obtain ⟨hleft, hright, htri, hsat, htwo, _, _, _, _⟩ :=
    HomotopyCategory.quasiIso_saturated_triangulated A
  let : W.HasRightCalculusOfFractions := hright
  let : W.HasTwoOutOfThreeProperty := htwo
  have hwitness := Functor.resolvingClass_essentialConstancy W F P hres hinv
  have hpw : F.HasPointwiseLeftDerivedFunctor W := by
    intro X
    obtain ⟨Y, u, hc, hr, _⟩ := hwitness X
    have hb := leftDerived_defined_pointwiseKan_bridge W Q F X Y hc u hr
    exact (F.hasPointwiseLeftDerivedFunctorAt_iff Q W X).2 hb.1
  let : F.HasPointwiseLeftDerivedFunctor W := hpw
  let LF := F.totalLeftDerived Q W
  let ε := F.totalLeftDerivedCounit Q W
  have hLF : LF.IsLeftDerivedFunctor ε W := inferInstance
  refine ⟨hpw, LF, ε, hLF, ?_⟩
  · intro X hX
    obtain ⟨Y, u, hc, hr, hu⟩ := hwitness X
    obtain ⟨_, π, ⟨hπ⟩, _, hidentity⟩ :=
      leftDerived_defined_pointwiseKan_bridge W Q F X Y hc u hr
    let hcanonical :=
      Functor.isPointwiseRightKanExtensionOfHasPointwiseLeftDerivedFunctor LF ε W (Q.obj X)
    let e := hcanonical.conePointUniqueUpToIso hπ
    have hid : W (𝟙 X) := W.id_mem X
    have : IsIso (u.app (⟨Over.mk (𝟙 X), hid⟩ : W.Over ⊤ X)) := hu hid hX
    have : IsIso (π.app (StructuredArrow.mk (𝟙 (Q.obj X)))) := by
      rw [hidentity hid]
      infer_instance
    have he := hcanonical.conePointUniqueUpToIso_hom_comp hπ
      (StructuredArrow.mk (𝟙 (Q.obj X)))
    have he' : e.hom ≫ π.app (StructuredArrow.mk (𝟙 (Q.obj X))) = ε.app X := by
      simpa [Functor.RightExtension.coneAt] using he
    rw [← he']
    infer_instance

private theorem roos_map_quasiIso
    {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory.{w} A]
    [HasCountableProducts A] [HasExactLimitsOfShape (Discrete ℕ) A]
    {X Y : CochainComplex (ℕᵒᵖ ⥤ A) ℤ} (f : X ⟶ Y) [hf : QuasiIso f] :
    QuasiIso (roosF.map f) := by
  have (n : Discrete ℕ) : QuasiIso
      ((Discrete.natTrans (F := Discrete.functor (fun n : ℕ ↦ X.asFunctor.obj (op n)))
        (G := Discrete.functor (fun n : ℕ ↦ Y.asFunctor.obj (op n)))
        (fun n ↦ (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map f).app
          (op n.as))).app n) :=
    (HomologicalComplex.quasiIso_iff_evaluation f).mp hf (op n.as)
  have hp : QuasiIso (roosPmap f) := HomologicalComplex.quasiIso_limMap _
  let τ := CochainComplex.mappingCone.triangleMap (roosU X) (roosU Y)
    (roosPmap f) (roosPmap f) (roosU_natural f)
  have hc : IsIso (DerivedCategory.Q.map (roosConeFunctor.map f)) :=
    CategoryTheory.Pretriangulated.isIso₃_of_isIso₁₂
      (DerivedCategory.Q.mapTriangle.map τ)
      (DerivedCategory.mappingCone_triangle_distinguished (roosU X))
      (DerivedCategory.mappingCone_triangle_distinguished (roosU Y))
      (inferInstance : IsIso (DerivedCategory.Q.map (roosPmap f)))
      (inferInstance : IsIso (DerivedCategory.Q.map (roosPmap f)))
  have : QuasiIso (roosConeFunctor.map f) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mp hc
  change QuasiIso ((roosConeFunctor.map f)⟦(-1 : ℤ)⟧')
  infer_instance

-- Derive an arbitrary homotopy-invariant functor using a class of cochain resolutions.
private theorem cochain_resolving_derived
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    (G : CochainComplex A ℤ ⥤ DerivedCategory.{w} A)
    (P : Set (CochainComplex A ℤ))
    (hhom : ∀ {X Y : CochainComplex A ℤ} {f g : X ⟶ Y},
      Homotopy f g → G.map f = G.map g)
    (hres : ∀ X, ∃ (Y : CochainComplex A ℤ) (s : Y ⟶ X), Y ∈ P ∧ QuasiIso s)
    (hinv : ∀ {X Y : CochainComplex A ℤ} (s : X ⟶ Y),
      X ∈ P → Y ∈ P → QuasiIso s → IsIso (G.map s)) :
    ∃ (L : DerivedCategory.{w} A ⥤ DerivedCategory.{w} A)
      (ε : DerivedCategory.Q ⋙ L ⟶ G),
      L.IsLeftDerivedFunctor ε (HomologicalComplex.quasiIso A (.up ℤ)) ∧
        ∀ X, X ∈ P → IsIso (ε.app X) := by
  classical
  let q := HomotopyCategory.quotient A (.up ℤ)
  let F : HomotopyCategory A (.up ℤ) ⥤ DerivedCategory.{w} A :=
    CategoryTheory.Quotient.lift _ G (fun X Y f g ⟨h⟩ ↦ hhom h)
  let j : q ⋙ F ≅ G := CategoryTheory.Quotient.lift.isLift _ _ _
  let S : Set (HomotopyCategory A (.up ℤ)) := fun X ↦
    ∃ K : CochainComplex A ℤ, K ∈ P ∧ q.obj K = X
  have hres' : ∀ X : HomotopyCategory A (.up ℤ),
      ∃ (Y : HomotopyCategory A (.up ℤ)) (s : Y ⟶ X),
        Y ∈ S ∧ HomotopyCategory.quasiIso A (.up ℤ) s := by
    intro X
    obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
    obtain ⟨L, f, hL, hf⟩ := hres K
    exact ⟨q.obj L, q.map f, ⟨L, hL, rfl⟩,
      (HomotopyCategory.quotient_map_mem_quasiIso_iff f).2 hf⟩
  have hinv' : ∀ (X Y : HomotopyCategory A (.up ℤ)) (s : X ⟶ Y),
      X ∈ S → Y ∈ S → HomotopyCategory.quasiIso A (.up ℤ) s →
        IsIso (F.map s) := by
    rintro X Y s ⟨K, hK, rfl⟩ ⟨L, hL, rfl⟩ hs
    obtain ⟨f, rfl⟩ := q.map_surjective s
    exact hinv f hK hL ((HomotopyCategory.quotient_map_mem_quasiIso_iff f).1 hs)
  obtain ⟨hpw, L, ε, huniv, hcomp⟩ :=
    resolving_class_left_derived A _ F S hres' hinv'
  let : F.HasPointwiseLeftDerivedFunctor (HomotopyCategory.quasiIso A (.up ℤ)) := hpw
  let : L.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso A (.up ℤ)) := huniv
  let α := (Functor.associator q DerivedCategory.Qh L).hom ≫ Functor.whiskerLeft q ε
  have hα := pointwise_precomp_full q DerivedCategory.Qh F L ε
    (Functor.isPointwiseRightKanExtensionOfHasPointwiseLeftDerivedFunctor L ε
      (HomotopyCategory.quasiIso A (.up ℤ)))
  let i := DerivedCategory.quotientCompQhIso A
  let β : DerivedCategory.Q ⋙ L ⟶ G :=
    Functor.whiskerRight i.inv L ≫ α ≫ j.hom
  have hβ := pointwise_change_iso L i j α hα
  refine ⟨L, β, ⟨hβ.isRightKanExtension⟩, ?_⟩
  intro X hX
  have := hcomp (q.obj X) ⟨X, hX, rfl⟩
  dsimp [β, α]
  infer_instance

namespace CategoryTheory.PrincipalQuotientCompletion

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [HasSheafify J AddCommGrpCat.{r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
    (R : Sheaf J CommRingCat.{r})

attribute [local instance] SheafOfModules.isMonoidal_W_independentCoefficients
  SheafOfModules.monoidalCategory
  SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients

private noncomputable def quotientTowerHomotopy
    (t : (SheafOfModules.unit
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)).sections)
    {X Y : CochainComplex (ringedSiteModules.{r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)) ℤ}
    {f g : X ⟶ Y} (h : Homotopy f g) :
    Homotopy ((quotientTower R t).map f) ((quotientTower R t).map g) := by
  let instPresheafCoproducts (I : Type r) : HasColimitsOfShape (Discrete I)
      (PresheafOfModules.{r} (SheafOfModules.derivedChangeRingIndependentCoefficients J R).obj) :=
    PresheafOfModules.hasColimitsOfShape _ _
  exact
    { hom i j :=
        { app n := (HomologicalComplex.mapBifunctorMapHomotopy₂
            (𝟙 ((principalReductionTower R t).obj n)) h
            (MonoidalCategory.curriedTensor _) (.up ℤ)).hom i j
          naturality n m a := tensorHomotopy_natural _
            ((principalReductionTower R t).map a) h i j }
      zero i j hij := by
        apply NatTrans.ext
        funext n
        exact (HomologicalComplex.mapBifunctorMapHomotopy₂
          (𝟙 ((principalReductionTower R t).obj n)) h
          (MonoidalCategory.curriedTensor _) (.up ℤ)).zero i j hij
      comm i := by
        apply NatTrans.ext
        funext n
        exact (HomologicalComplex.mapBifunctorMapHomotopy₂
          (𝟙 ((principalReductionTower R t).obj n)) h
          (MonoidalCategory.curriedTensor _) (.up ℤ)).comm i }

variable [HasDerivedCategory.{w}
  (ringedSiteModules.{r} (SheafOfModules.derivedChangeRingIndependentCoefficients J R))]

/-- The quotient Roos functor has a universal left derived functor, computed
on every K-flat cochain complex.

Source: Stacks Project, sites-cohomology.tex, Tags 06YS, 06YT and 0941, and
Derived Categories, Tag 06XN (blueprint: lem-pur-principal-quotient-roos-derived).

Proof: Tensor homotopies with the fixed quotient complexes. Naturality in their
transition maps assembles these homotopies on the tower. Products and the signed
cone carry them to homotopies of the Roos complexes by the existing strict Roos
compatible-homotopy theorem, giving a functor on the homotopy category. If a map
between K-flat complexes is a quasi-isomorphism,
resolve each fixed quotient by a K-flat complex and use the tensor square and
two-out-of-three to see that tensoring the map with that quotient is a
quasi-isomorphism. Exact countable products preserve these maps, and the cone
triangle makes their Roos map a quasi-isomorphism. K-flat resolutions give a
resolving class on the homotopy category. The resolving-class essential-constancy
criterion and its pointwise Kan-extension bridge give the total left derived
functor; using the identity resolution shows its counit invertible on every
K-flat object. Precompose its universal counit with the full, essentially
surjective homotopy quotient and transport along quotientCompQhIso. This gives
the asserted cochain universal pair and preserves all computation isomorphisms.
No unit augmentation is involved in this construction. -/
theorem exists_derivedQuotientRoos
    (t : (SheafOfModules.unit
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)).sections)
    [HasExactLimitsOfShape (Discrete ℕ)
      (ringedSiteModules.{r} (SheafOfModules.derivedChangeRingIndependentCoefficients J R))] :
    ∃ (L : DerivedCategory.{w} (ringedSiteModules.{r}
        (SheafOfModules.derivedChangeRingIndependentCoefficients J R)) ⥤
        DerivedCategory.{w} (ringedSiteModules.{r}
          (SheafOfModules.derivedChangeRingIndependentCoefficients J R)))
      (ε : DerivedCategory.Q ⋙ L ⟶ quotientRoos R t ⋙ DerivedCategory.Q),
      L.IsLeftDerivedFunctor ε (HomologicalComplex.quasiIso _ (.up ℤ)) ∧
        ∀ P, CochainComplex.IsKFlatIndependentCoefficients (R := R) P →
          IsIso (ε.app P) := by
  classical
  let A := ringedSiteModules.{r}
    (SheafOfModules.derivedChangeRingIndependentCoefficients J R)
  let G := quotientRoos R t ⋙ DerivedCategory.Q.{w}
  let P : Set (CochainComplex A ℤ) := fun K ↦
    CochainComplex.IsKFlatIndependentCoefficients (R := R) K
  have htensor :=
    (SheafOfModules.TotalTensorSigns.totalTensorHomotopyConeSigns R).2.2.2.2.2.2.1
  apply cochain_resolving_derived G P
  · intro X Y f g h
    obtain ⟨H, _⟩ := (roosF_homotopy_functor.{_, _, 0} (A := A)).2.1 _ _ _ _
      (quotientTowerHomotopy R t h)
    exact DerivedCategory.Q_map_eq_of_homotopy A H
  · intro X
    obtain ⟨K, p, hK, _, hp, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients (R := R) X
    exact ⟨K, p, hK, hp⟩
  · intro X Y f hX hY hf
    have hlevel (B : CochainComplex A ℤ) :
        QuasiIso (((SheafOfModules.TotalTensorSigns.total R).obj B).map f) := by
      obtain ⟨K, p, hK, _, hp, _⟩ :=
        CochainComplex.exists_isKFlatResolutionIndependentCoefficients (R := R) B
      let T := SheafOfModules.TotalTensorSigns.total R
      have h₁ : QuasiIso ((T.map p).app X) :=
        ((htensor X hX).1 _ _ p hp).2
      have h₂ : QuasiIso ((T.map p).app Y) :=
        ((htensor Y hY).1 _ _ p hp).2
      have h₃ : QuasiIso ((T.obj K).map f) :=
        ((htensor K hK).1 _ _ f hf).1
      rw [← quasiIso_iff_comp_left ((T.map p).app X),
        ← (T.map p).naturality f]
      infer_instance
    have ht : QuasiIso ((quotientTower R t).map f) := by
      apply (HomologicalComplex.quasiIso_iff_evaluation _).2
      intro n
      exact hlevel ((principalReductionTower R t).obj n)
    have hr : QuasiIso ((quotientRoos R t).map f) := roos_map_quasiIso _
    exact (DerivedCategory.isIso_Q_map_iff_quasiIso A _).2 hr

end CategoryTheory.PrincipalQuotientCompletion
