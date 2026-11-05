import Langlands.Algebra.RenardEndomorphismLocalizationSource

/-! # The explicit target functor and the chosen canonical-arrow comparison -/

set_option autoImplicit false

universe u v w

open CategoryTheory Polynomial Langlands.Algebra.PolynomialEndomorphism

noncomputable section

namespace Langlands.Renard.EndomorphismLocalization.ChosenComparison

variable (R : Type u) [CommRing R]

/-- Conjugate the published localized automorphism through the actual native R-linear lift. -/
def liftedLocalizedEquiv (A : EndomorphismCat.{u, v} R) :
    ULift.{w} (Localized (endomorphism R A)) ≃ₗ[R]
      ULift.{w} (Localized (endomorphism R A)) :=
  (ULift.moduleEquiv (R := R)).trans
    ((localizedEquiv (endomorphism R A)).trans (ULift.moduleEquiv (R := R)).symm)

@[simp] theorem liftedLocalizedEquiv_up (A : EndomorphismCat.{u, v} R)
    (z : Localized (endomorphism R A)) :
    liftedLocalizedEquiv.{u, v, w} R A (ULift.up z) =
      ULift.up (localizedEnd (endomorphism R A) z) := rfl

@[simp] theorem liftedLocalizedEquiv_symm_up (A : EndomorphismCat.{u, v} R)
    (z : Localized (endomorphism R A)) :
    (liftedLocalizedEquiv.{u, v, w} R A).symm (ULift.up z) =
      ULift.up (localizedInv (endomorphism R A) z) := rfl

@[simp] theorem liftedLocalizedEquiv_apply_symm (A : EndomorphismCat.{u, v} R)
    (z : ULift.{w} (Localized (endomorphism R A))) :
    liftedLocalizedEquiv.{u, v, w} R A ((liftedLocalizedEquiv R A).symm z) = z :=
  (liftedLocalizedEquiv R A).apply_symm_apply z

@[simp] theorem liftedLocalizedEquiv_symm_apply (A : EndomorphismCat.{u, v} R)
    (z : ULift.{w} (Localized (endomorphism R A))) :
    (liftedLocalizedEquiv.{u, v, w} R A).symm (liftedLocalizedEquiv R A z) = z :=
  (liftedLocalizedEquiv R A).symm_apply_apply z

/-- The explicit localized pair, using its native R-module action. -/
def explicitObject (A : EndomorphismCat.{u, v} R) :
    InvertibleEndomorphismCat.{u, max u v w} R :=
  ⟨{ a := ModuleCat.of R (ULift.{w} (Localized (endomorphism R A)))
     str := ModuleCat.ofHom (liftedLocalizedEquiv.{u, v, w} R A).toLinearMap }, by
    change IsUnit (liftedLocalizedEquiv.{u, v, w} R A).toLinearMap
    rw [Module.End.isUnit_iff]
    exact (liftedLocalizedEquiv.{u, v, w} R A).bijective⟩

@[simp] theorem explicitObject_str_up (A : EndomorphismCat.{u, v} R)
    (z : Localized (endomorphism R A)) :
    (explicitObject.{u, v, w} R A).obj.str (ULift.up z) =
      ULift.up (localizedEnd (endomorphism R A) z) := rfl

/-- The actual polynomial-linear localized map of the published polynomial intertwiner. -/
def localizedPolynomialMap {A B : EndomorphismCat.{u, v} R} (f : A ⟶ B) :
    Localized (endomorphism R A) →ₗ[R[X]] Localized (endomorphism R B) :=
  IsLocalizedModule.map (powersX R)
    (LocalizedModule.mkLinearMap (powersX R) ((toPolynomial R).obj A))
    (LocalizedModule.mkLinearMap (powersX R) ((toPolynomial R).obj B))
    (toPolynomialMap R f).hom

@[simp] theorem localizedPolynomialMap_mk {A B : EndomorphismCat.{u, v} R}
    (f : A ⟶ B) (m : Module.AEval' (endomorphism R A)) (s : powersX R) :
    localizedPolynomialMap R f (LocalizedModule.mk m s) =
      LocalizedModule.mk ((toPolynomial R).map f m) s :=
  IsLocalizedModule.map_LocalizedModules (powersX R) (toPolynomialMap R f).hom m s

/-- Restrict the actual localized polynomial map to R and conjugate through the native lifts. -/
def explicitLinearMap {A B : EndomorphismCat.{u, v} R} (f : A ⟶ B) :
    (explicitObject.{u, v, w} R A).obj.a →ₗ[R] (explicitObject.{u, v, w} R B).obj.a :=
  (ULift.moduleEquiv (R := R) (M := Localized (endomorphism R B))).symm.toLinearMap.comp
    (((localizedPolynomialMap R f).restrictScalars R).comp
      (ULift.moduleEquiv (R := R) (M := Localized (endomorphism R A))).toLinearMap)

/-- The explicit target retains each original intertwiner through its actual localized map. -/
def explicitMap {A B : EndomorphismCat.{u, v} R} (f : A ⟶ B) :
    explicitObject.{u, v, w} R A ⟶ explicitObject.{u, v, w} R B :=
  ObjectProperty.homMk
    { f := ModuleCat.ofHom (explicitLinearMap.{u, v, w} R f)
      h := (intertwining_iff R _ _ _).mpr (fun z => by
        change ULift.up (localizedPolynomialMap R f
            (localizedEnd (endomorphism R A) z.down)) =
          ULift.up (localizedEnd (endomorphism R B) (localizedPolynomialMap R f z.down))
        exact congrArg ULift.up ((localizedPolynomialMap R f).map_smul (X : R[X]) z.down)) }

/-- The underlying map is the actual IsLocalizedModule.map, restricted and conjugated. -/
theorem explicitMap_hom {A B : EndomorphismCat.{u, v} R} (f : A ⟶ B) :
    (explicitMap.{u, v, w} R f).hom.f.hom = explicitLinearMap.{u, v, w} R f := rfl

@[simp] theorem explicitMap_up_mk {A B : EndomorphismCat.{u, v} R}
    (f : A ⟶ B) (m : Module.AEval' (endomorphism R A)) (s : powersX R) :
    (explicitMap.{u, v, w} R f).hom.f (ULift.up (LocalizedModule.mk m s)) =
      ULift.up (LocalizedModule.mk ((toPolynomial R).map f m) s) :=
  congrArg ULift.up (localizedPolynomialMap_mk R f m s)

@[simp] theorem explicitMap_id (A : EndomorphismCat.{u, v} R) :
    explicitMap.{u, v, w} R (𝟙 A) = 𝟙 (explicitObject.{u, v, w} R A) := by
  apply ObjectProperty.hom_ext
  apply Endofunctor.Algebra.Hom.ext
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rcases x with ⟨z⟩
  induction z using LocalizedModule.induction_on with
  | _ m s => exact explicitMap_up_mk R (𝟙 A) m s

@[simp] theorem explicitMap_comp {A B C : EndomorphismCat.{u, v} R}
    (f : A ⟶ B) (g : B ⟶ C) :
    explicitMap.{u, v, w} R (f ≫ g) = explicitMap R f ≫ explicitMap R g := by
  apply ObjectProperty.hom_ext
  apply Endofunctor.Algebra.Hom.ext
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rcases x with ⟨z⟩
  induction z using LocalizedModule.induction_on with
  | _ m s =>
    change (explicitMap.{u, v, w} R (f ≫ g)).hom.f (ULift.up (LocalizedModule.mk m s)) =
      (explicitMap R g).hom.f ((explicitMap R f).hom.f (ULift.up (LocalizedModule.mk m s)))
    exact (explicitMap_up_mk.{u, v, w} R (f ≫ g) m s).trans
      ((explicitMap_up_mk.{u, v, w} R g ((toPolynomial R).map f m) s).symm.trans
        (congrArg (fun y => (explicitMap.{u, v, w} R g).hom.f y)
          (explicitMap_up_mk.{u, v, w} R f m s).symm))

/-- Functor on the exact published explicit localization models. -/
def explicitFunctor :
    EndomorphismCat.{u, v} R ⥤ InvertibleEndomorphismCat.{u, max u v w} R where
  obj := explicitObject R
  map := explicitMap R
  map_id := explicitMap_id R
  map_comp := explicitMap_comp R

/-- The formula on each lifted denominator representative retains the original intertwiner. -/
@[simp] theorem explicitFunctor_map_up_mk {A B : EndomorphismCat.{u, v} R}
    (f : A ⟶ B) (x : A.a) (s : powersX R) :
    ((explicitFunctor.{u, v, w} R).map f).hom.f
        (ULift.up (LocalizedModule.mk (Module.AEval'.of (endomorphism R A) x) s)) =
      ULift.up (LocalizedModule.mk (Module.AEval'.of (endomorphism R B) (f.f x)) s) :=
  explicitMap_up_mk R f _ s

@[simp] theorem explicitFunctor_map_up_frac {A B : EndomorphismCat.{u, v} R}
    (f : A ⟶ B) (x : A.a) (n : ℕ) :
    ((explicitFunctor.{u, v, w} R).map f).hom.f (ULift.up (frac (endomorphism R A) x n)) =
      ULift.up (frac (endomorphism R B) (f.f x) n) :=
  explicitFunctor_map_up_mk R f x (Submonoid.pow X n)

/-- Identity of quotient carriers, with restricted and native coefficient actions compared. -/
def targetLinearEquiv (A : EndomorphismCat.{u, v} R) :
    ((chosenFunctor.{u, v, w} R).obj A).obj.a ≃ₗ[R]
      ((explicitFunctor.{u, v, w} R).obj A).obj.a where
  toFun z := ULift.up z.down
  invFun z := ULift.up z.down
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' r z := by
    change ULift.up ((C r : R[X]) • (show Localized (endomorphism R A) from z.down)) =
      ULift.up (r • (show Localized (endomorphism R A) from z.down))
    exact congrArg ULift.up (smul_eq_C_smul (endomorphism R A) r
      (show Localized (endomorphism R A) from z.down)).symm

/-- The recovered X-action is precisely the native published localizedEnd. -/
theorem targetLinearEquiv_intertwines (A : EndomorphismCat.{u, v} R)
    (z : ((chosenFunctor.{u, v, w} R).obj A).obj.a) :
    targetLinearEquiv.{u, v, w} R A (((chosenFunctor.{u, v, w} R).obj A).obj.str z) =
      ((explicitFunctor.{u, v, w} R).obj A).obj.str (targetLinearEquiv R A z) := rfl

/-- The comparison alpha at the actual invertible pairs. -/
def targetIso (A : EndomorphismCat.{u, v} R) :
    (chosenFunctor.{u, v, w} R).obj A ≅ (explicitFunctor.{u, v, w} R).obj A :=
  ObjectProperty.isoMk _
    (Endofunctor.Algebra.isoMk (targetLinearEquiv.{u, v, w} R A).toModuleIso (by
      ext z
      rfl))

/-- The target comparison is natural for every original intertwiner. -/
def targetComparison : chosenFunctor.{u, v, w} R ≅ explicitFunctor.{u, v, w} R :=
  NatIso.ofComponents (targetIso R) (fun _ => by
    apply ObjectProperty.hom_ext
    ext z
    rfl)

@[simp] theorem targetComparison_hom_up (A : EndomorphismCat.{u, v} R)
    (z : Localized (endomorphism R A)) :
    ((targetComparison.{u, v, w} R).hom.app A).hom.f (ULift.up z) = ULift.up z := rfl

@[simp] theorem targetComparison_inv_up (A : EndomorphismCat.{u, v} R)
    (z : Localized (endomorphism R A)) :
    ((targetComparison.{u, v, w} R).inv.app A).hom.f (ULift.up z) = ULift.up z := rfl

@[simp] theorem targetComparison_hom_inv (A : EndomorphismCat.{u, v} R) :
    (targetComparison.{u, v, w} R).hom.app A ≫ (targetComparison R).inv.app A =
      𝟙 ((chosenFunctor.{u, v, w} R).obj A) :=
  (targetComparison R).hom_inv_id_app A

@[simp] theorem targetComparison_inv_hom (A : EndomorphismCat.{u, v} R) :
    (targetComparison.{u, v, w} R).inv.app A ≫ (targetComparison R).hom.app A =
      𝟙 ((explicitFunctor.{u, v, w} R).obj A) :=
  (targetComparison R).inv_hom_id_app A

/-- Naturality in the actual full subcategory, without any condition on the intertwiner. -/
theorem targetComparison_naturality {A B : EndomorphismCat.{u, v} R} (f : A ⟶ B) :
    (chosenFunctor.{u, v, w} R).map f ≫ (targetComparison R).hom.app B =
      (targetComparison R).hom.app A ≫ (explicitFunctor R).map f :=
  (targetComparison R).hom.naturality f

/-- The canonical map into the explicit native localization, conjugated through the lifts. -/
def explicitArrowComponent (A : EndomorphismCat.{u, v} R) :
    (raisedFunctor.{u, v, w} R).obj A ⟶
      (invertibleEndomorphismInclusion R).obj ((explicitFunctor.{u, v, w} R).obj A) where
  f := ModuleCat.ofHom <|
    (ULift.moduleEquiv (R := R) (M := Localized (endomorphism R A))).symm.toLinearMap.comp
      ((iota (endomorphism R A)).comp
        (ULift.moduleEquiv (R := R) (M := A.a)).toLinearMap)
  h := (intertwining_iff R _ _ _).mpr (fun x =>
    congrArg ULift.up (iota_intertwines (endomorphism R A) x.down))

@[simp] theorem explicitArrowComponent_up (A : EndomorphismCat.{u, v} R) (x : A.a) :
    (explicitArrowComponent.{u, v, w} R A).f (ULift.up x) =
      ULift.up (iota (endomorphism R A) x) := rfl

/-- The explicit canonical maps form a natural transformation iota. -/
def explicitArrow :
    raisedFunctor.{u, v, w} R ⟶
      explicitFunctor.{u, v, w} R ⋙ invertibleEndomorphismInclusion R where
  app := explicitArrowComponent R
  naturality {A B} f := by
    apply Endofunctor.Algebra.Hom.ext
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rcases x with ⟨x⟩
    change ULift.up (iota (endomorphism R B) (f.f x)) =
      ((explicitFunctor.{u, v, w} R).map f).hom.f (ULift.up (iota (endomorphism R A) x))
    exact (explicitFunctor_map_up_mk R f x 1).symm

/-- The exact canonical-arrow equation beta; theta; J(alpha) = iota. -/
theorem arrow_comparison (A : EndomorphismCat.{u, v} R) :
    (sourceComparison.{u, v, w} R).hom.app A ≫ (polynomialArrow R).app A ≫
        (invertibleEndomorphismInclusion R).map ((targetComparison R).hom.app A) =
      (explicitArrow.{u, v, w} R).app A := by
  ext x
  rfl

/-- The component equation with lambda as the chosen source arrow. -/
theorem chosenArrow_comparison (A : EndomorphismCat.{u, v} R) :
    (chosenArrow.{u, v, w} R).app A ≫
        (invertibleEndomorphismInclusion R).map ((targetComparison R).hom.app A) =
      (explicitArrow.{u, v, w} R).app A := by
  simpa only [chosenArrow, NatTrans.comp_app, Category.assoc] using arrow_comparison R A

/-- The comparison holds as an equality of the actual natural transformations. -/
theorem canonicalArrowComparison :
    chosenArrow.{u, v, w} R ≫
        Functor.whiskerRight (targetComparison R).hom (invertibleEndomorphismInclusion R) =
      explicitArrow.{u, v, w} R := by
  apply NatTrans.ext
  funext A
  exact chosenArrow_comparison R A

/-- The chosen arrow as an actual structured-arrow object. -/
def chosenStructuredArrow (A : EndomorphismCat.{u, v} R) :
    StructuredArrow ((raisedFunctor.{u, v, w} R).obj A)
      (invertibleEndomorphismInclusion.{u, max u v w} R) :=
  StructuredArrow.mk ((chosenArrow.{u, v, w} R).app A)

/-- The explicit canonical arrow as an actual structured-arrow object. -/
def explicitStructuredArrow (A : EndomorphismCat.{u, v} R) :
    StructuredArrow ((raisedFunctor.{u, v, w} R).obj A)
      (invertibleEndomorphismInclusion.{u, max u v w} R) :=
  StructuredArrow.mk ((explicitArrow.{u, v, w} R).app A)

/-- The two chosen canonical arrows are isomorphic, with target component alpha. -/
def structuredArrowComparison (A : EndomorphismCat.{u, v} R) :
    chosenStructuredArrow.{u, v, w} R A ≅ explicitStructuredArrow.{u, v, w} R A :=
  StructuredArrow.isoMk ((targetComparison.{u, v, w} R).app A) (by
    change (chosenArrow.{u, v, w} R).app A ≫
        (invertibleEndomorphismInclusion R).map ((targetComparison R).hom.app A) =
      (explicitArrow.{u, v, w} R).app A
    exact chosenArrow_comparison R A)

@[simp] theorem structuredArrowComparison_hom_right (A : EndomorphismCat.{u, v} R) :
    (structuredArrowComparison.{u, v, w} R A).hom.right =
      (targetComparison.{u, v, w} R).hom.app A := rfl

@[simp] theorem structuredArrowComparison_inv_right (A : EndomorphismCat.{u, v} R) :
    (structuredArrowComparison.{u, v, w} R A).inv.right =
      (targetComparison.{u, v, w} R).inv.app A := rfl

/-- Projection of the arrow isomorphism is the actual target isomorphism alpha. -/
@[simp] theorem structuredArrowComparison_proj (A : EndomorphismCat.{u, v} R) :
    (StructuredArrow.proj ((raisedFunctor.{u, v, w} R).obj A)
      (invertibleEndomorphismInclusion R)).mapIso (structuredArrowComparison R A) =
        (targetComparison.{u, v, w} R).app A := rfl

/-- The exact comparison for an arbitrary field and arbitrary-dimensional vector spaces. -/
abbrev fieldStructuredArrowComparison (k : Type u) [Field k]
    (A : EndomorphismCat.{u, v} k) :
    chosenStructuredArrow.{u, v, w} k A ≅ explicitStructuredArrow.{u, v, w} k A :=
  structuredArrowComparison k A

end Langlands.Renard.EndomorphismLocalization.ChosenComparison
