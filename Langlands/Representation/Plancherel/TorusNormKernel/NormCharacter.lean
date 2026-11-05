import Langlands.GroupScheme.AffineCorepresented
import Langlands.GroupScheme.Torus.WeilRestrictionNorm
import Langlands.GroupScheme.GaloisPointRational
import Langlands.GroupScheme.MultiplicativePointTopology

/-!
# Norms of characters after a finite field extension

Let `E / F` be a finite field extension and `T` an affine group scheme over `F`. A character
`χ` of the base change `T_E` gives a rational character of `T` whose value at an `F`-point `t`
is the field norm of `χ(t_E)`. It is constructed as a homomorphism to the Weil restriction
`Res_{E/F} 𝔾ₘ` followed by the norm.
-/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped TensorProduct CategoryTheory.MonObj

namespace Langlands.Plancherel.TorusNormKernel

open Langlands.GroupScheme

variable (F E : Type u) [Field F] [Field E] [Algebra F E]

/-- The base morphism `Spec E ⟶ Spec F`. -/
abbrev baseMap : Spec (CommRingCat.of E) ⟶ Spec (CommRingCat.of F) :=
  GaloisPointComparison.baseMap F E

section Coefficients

variable (D : Type u) [CommRing D] [Algebra F D] [Algebra E D] [IsScalarTower F E D]

/-- An `E`-algebra spectrum regarded over `F` is the `F`-algebra spectrum. -/
def specRestrictIso :
    (Over.map (baseMap F E)).obj ((algSpec (CommRingCat.of E)).obj (op (CommAlgCat.of E D))) ≅
      (algSpec (CommRingCat.of F)).obj (op (CommAlgCat.of F D)) :=
  Over.isoMk (Iso.refl _) (by
    change 𝟙 _ ≫ Spec.map (CommRingCat.ofHom (algebraMap F D)) =
      Spec.map (CommRingCat.ofHom (algebraMap E D)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap F E))
    rw [Category.id_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← IsScalarTower.algebraMap_eq])

variable (T : GroupScheme (Spec (CommRingCat.of F)))

/-- Points of `T` with coefficients in an `E`-algebra are points of the base change `T_E`. -/
def pointE :
    T.affinePoints (CommAlgCat.of F D) ≃*
      (GaloisPointComparison.baseChanged F E T).affinePoints (CommAlgCat.of E D) :=
  (T.points.mapIso (specRestrictIso F E D).op).groupIsoToMulEquiv.trans
    (baseChangePointsEquiv (baseMap F E) T
      ((algSpec (CommRingCat.of E)).obj (op (CommAlgCat.of E D)))).symm

theorem baseChangePointsEquiv_pointE (y : T.affinePoints (CommAlgCat.of F D)) :
    baseChangePointsEquiv (baseMap F E) T
        ((algSpec (CommRingCat.of E)).obj (op (CommAlgCat.of E D))) (pointE F E D T y) =
      (specRestrictIso F E D).hom ≫ y := by
  exact (baseChangePointsEquiv (baseMap F E) T
    ((algSpec (CommRingCat.of E)).obj (op (CommAlgCat.of E D)))).apply_symm_apply
      ((specRestrictIso F E D).hom ≫ y)

variable {D} {D' : Type u} [CommRing D'] [Algebra F D'] [Algebra E D'] [IsScalarTower F E D']

/-- Changing coefficients along an `E`-algebra map commutes with the base-change comparison. -/
theorem pointE_naturality (g : D →ₐ[E] D') (y : T.affinePoints (CommAlgCat.of F D)) :
    pointE F E D' T (T.affinePointMap (CommAlgCat.ofHom (g.restrictScalars F)) y) =
      (GaloisPointComparison.baseChanged F E T).affinePointMap (CommAlgCat.ofHom g)
        (pointE F E D T y) := by
  apply (baseChangePointsEquiv (baseMap F E) T
    ((algSpec (CommRingCat.of E)).obj (op (CommAlgCat.of E D')))).injective
  rw [baseChangePointsEquiv_pointE, affinePointMap_apply, affinePointMap_apply,
    baseChangePointsEquiv_naturality, baseChangePointsEquiv_pointE, ← Category.assoc,
    ← Category.assoc]
  congr 1

end Coefficients

section Values

variable {F E}
variable {T : GroupScheme (Spec (CommRingCat.of F))}
variable (χ : rationalCharacters (GaloisPointComparison.baseChanged F E T))
variable (D : Type u) [CommRing D] [Algebra F D] [Algebra E D] [IsScalarTower F E D]

/-- The value of an `E`-character at a point of `T` with coefficients in an `E`-algebra. -/
def valueE : T.affinePoints (CommAlgCat.of F D) →* Dˣ :=
  (Gm.affineUnitsEquiv (CommRingCat.of E) (CommAlgCat.of E D)).toMonoidHom.comp
    (((GaloisPointComparison.baseChanged F E T).affinePointsTarget χ.toMul
      (CommAlgCat.of E D)).comp (pointE F E D T).toMonoidHom)

theorem valueE_apply (y : T.affinePoints (CommAlgCat.of F D)) :
    valueE χ D y = Gm.affineUnitsEquiv (CommRingCat.of E) (CommAlgCat.of E D)
      (pointE F E D T y ≫ χ.toMul.hom.hom) :=
  rfl

variable {D} {D' : Type u} [CommRing D'] [Algebra F D'] [Algebra E D'] [IsScalarTower F E D']

/-- The value is natural in the coefficient algebra. -/
theorem valueE_naturality (g : D →ₐ[E] D') (y : T.affinePoints (CommAlgCat.of F D)) :
    valueE χ D' (T.affinePointMap (CommAlgCat.ofHom (g.restrictScalars F)) y) =
      Units.map g.toMonoidHom (valueE χ D y) := by
  rw [valueE_apply, valueE_apply, pointE_naturality]
  have h := congrArg (fun φ => φ (pointE F E D T y))
    ((GaloisPointComparison.baseChanged F E T).affinePointsTarget_naturality χ.toMul
      (CommAlgCat.ofHom g))
  simp only [MonoidHom.comp_apply, affinePointsTarget_apply] at h
  rw [← h, Gm.affineUnitsEquiv_naturality]
  rfl

end Values

section Weil

variable {F E}
variable {T : GroupScheme (Spec (CommRingCat.of F))} [IsAffine T.X.left]

/-- Points of the corepresented coordinate model, regarded as points of `T`. -/
def coordinatePoints (C : CommAlgCat.{u} F) :
    (AffineCoordinates.functor T).obj C →* T.affinePoints C :=
  ((Corepresented.groupScheme (AffineCoordinates.functor T)
      (AffineCoordinates.corepresentation T)).affinePointsTarget
      (AffineCoordinates.groupSchemeIso T).hom C).comp
    (Corepresented.affinePointsEquiv (AffineCoordinates.functor T)
      (AffineCoordinates.corepresentation T) C).symm.toMonoidHom

theorem coordinatePoints_naturality {C C' : CommAlgCat.{u} F} (φ : C ⟶ C')
    (f : (AffineCoordinates.functor T).obj C) :
    coordinatePoints C' ((AffineCoordinates.functor T).map φ f) =
      T.affinePointMap φ (coordinatePoints C f) := by
  have h := Corepresented.affinePointsEquiv_naturality (AffineCoordinates.functor T)
    (AffineCoordinates.corepresentation T) φ
    ((Corepresented.affinePointsEquiv (AffineCoordinates.functor T)
      (AffineCoordinates.corepresentation T) C).symm f)
  rw [MulEquiv.apply_symm_apply] at h
  change ((Corepresented.affinePointsEquiv (AffineCoordinates.functor T)
      (AffineCoordinates.corepresentation T) C').symm ((AffineCoordinates.functor T).map φ f)) ≫
        (AffineCoordinates.groupSchemeIso T).hom.hom.hom =
    (algSpec (CommRingCat.of F)).map φ.op ≫
      ((Corepresented.affinePointsEquiv (AffineCoordinates.functor T)
        (AffineCoordinates.corepresentation T) C).symm f ≫
          (AffineCoordinates.groupSchemeIso T).hom.hom.hom)
  rw [← h, MulEquiv.symm_apply_apply, Category.assoc]

variable (χ : rationalCharacters (GaloisPointComparison.baseChanged F E T))

/-- The Weil-restriction value of an `E`-character on coordinate points. -/
def weilApp (C : CommAlgCat.{u} F) :
    (AffineCoordinates.functor T).obj C →* (E ⊗[F] C)ˣ :=
  (valueE χ (E ⊗[F] C)).comp
    ((T.affinePointMap (CommAlgCat.ofHom
      (Algebra.TensorProduct.includeRight : C →ₐ[F] E ⊗[F] C))).comp (coordinatePoints C))

theorem weilApp_naturality {C C' : CommAlgCat.{u} F} (φ : C ⟶ C')
    (f : (AffineCoordinates.functor T).obj C) :
    weilApp χ C' ((AffineCoordinates.functor T).map φ f) =
      Units.map (Algebra.TensorProduct.lTensor (S := E) E φ.hom).toMonoidHom
        (weilApp χ C f) := by
  simp only [weilApp, MonoidHom.comp_apply, coordinatePoints_naturality]
  rw [← valueE_naturality, affinePointMap_apply, affinePointMap_apply, affinePointMap_apply,
    affinePointMap_apply, ← Category.assoc, ← Category.assoc, ← Functor.map_comp,
    ← Functor.map_comp]
  congr 3

/-- The natural transformation to the Weil-restriction functor. -/
def weilNatTrans : AffineCoordinates.functor T ⟶ WeilGm.functor (CommRingCat.of F) E where
  app C := GrpCat.ofHom (weilApp χ C)
  naturality C C' φ := by
    ext f
    exact weilApp_naturality χ φ f

variable [FiniteDimensional F E]

/-- The homomorphism from `T` to `Res_{E/F} 𝔾ₘ` determined by an `E`-character. -/
def weilHom : T ⟶ WeilGm.groupScheme (CommRingCat.of F) E :=
  (AffineCoordinates.groupSchemeIso T).inv ≫
    Corepresented.groupSchemeMap (AffineCoordinates.corepresentation T)
      (WeilGm.corepresentableBy (CommRingCat.of F) E) (weilNatTrans χ)

/-- The rational character of `T` obtained as the norm of an `E`-character. -/
def normCharacter : rationalCharacters T :=
  Additive.ofMul (weilHom χ ≫ WeilGm.norm (CommRingCat.of F) E)

end Weil

section Evaluation

variable {F E} [FiniteDimensional F E]

/-- On affine test schemes, the Weil-restriction norm is the tensor norm of the
corepresented coordinates. -/
theorem weilNorm_affinePoints (A : CommAlgCat.{u} F)
    (z : (WeilGm.groupScheme (CommRingCat.of F) E).affinePoints A) :
    Gm.affineUnitsEquiv (CommRingCat.of F) A (z ≫ (WeilGm.norm (CommRingCat.of F) E).hom.hom) =
      Langlands.Algebra.tensorNormUnits (CommRingCat.of F) E A
        (Corepresented.affinePointsEquiv (WeilGm.functor (CommRingCat.of F) E)
          (WeilGm.corepresentableBy (CommRingCat.of F) E) A z) := by
  set P := (algSpec (CommRingCat.of F)).obj (op A)
  set g := (Corepresented.affineSectionsIso (R := CommRingCat.of F) A).hom.hom
  set w := WeilGm.pointsEquiv (CommRingCat.of F) E P z
  rw [← Corepresented.map_affineSectionsIso_pointsEquiv]
  have h := Langlands.Algebra.tensorNormUnits_naturality g w
  have hval := congrArg Units.val h
  apply Units.ext
  change (Scheme.ΓSpecIso (CommRingCat.of A)).hom
      (Gm.pointsEquiv _ P (z ≫ (WeilGm.norm (CommRingCat.of F) E).hom.hom)).val = _
  rw [WeilGm.norm_points]
  refine Eq.trans ?_ hval.symm
  have hr := congrArg (fun φ => φ ((Langlands.Algebra.tensorNormUnits (CommRingCat.of F) E
      ((algΓ (CommRingCat.of F)).obj P).unop w :
        ((algΓ (CommRingCat.of F)).obj P).unop)))
    (Corepresented.affineSectionsIso_hom_ringHom (R := CommRingCat.of F) A)
  exact hr.symm

variable {T : GroupScheme (Spec (CommRingCat.of F))} [IsAffine T.X.left]
variable (χ : rationalCharacters (GaloisPointComparison.baseChanged F E T))

/-- On affine test schemes, the norm character is the tensor norm of the extended value. -/
theorem normCharacter_affinePoints (A : CommAlgCat.{u} F) (y : T.affinePoints A) :
    Gm.affineUnitsEquiv (CommRingCat.of F) A (y ≫ (normCharacter χ).toMul.hom.hom) =
      Langlands.Algebra.tensorNormUnits (CommRingCat.of F) E A
        (valueE χ (E ⊗[F] A) (T.affinePointMap (CommAlgCat.ofHom
          (Algebra.TensorProduct.includeRight : A →ₐ[F] E ⊗[F] A)) y)) := by
  have hz : y ≫ (normCharacter χ).toMul.hom.hom =
      (y ≫ (weilHom χ).hom.hom) ≫ (WeilGm.norm (CommRingCat.of F) E).hom.hom := by
    rw [Category.assoc]
    rfl
  rw [hz, weilNorm_affinePoints]
  have hw : y ≫ (weilHom χ).hom.hom =
      (y ≫ (AffineCoordinates.groupSchemeIso T).inv.hom.hom) ≫
        (Corepresented.groupSchemeMap (AffineCoordinates.corepresentation T)
          (WeilGm.corepresentableBy (CommRingCat.of F) E) (weilNatTrans χ)).hom.hom := by
    rw [Category.assoc]
    rfl
  rw [hw, Corepresented.groupSchemeMap_affinePoints]
  congr 1
  change weilApp χ A _ = _
  rw [weilApp, MonoidHom.comp_apply, MonoidHom.comp_apply]
  congr 2
  change (Corepresented.affinePointsEquiv (AffineCoordinates.functor T)
      (AffineCoordinates.corepresentation T) A).symm
      ((Corepresented.affinePointsEquiv (AffineCoordinates.functor T)
        (AffineCoordinates.corepresentation T) A)
          (y ≫ (AffineCoordinates.groupSchemeIso T).inv.hom.hom)) ≫
      (AffineCoordinates.groupSchemeIso T).hom.hom.hom = y
  rw [MulEquiv.symm_apply_apply, Category.assoc]
  change y ≫ ((AffineCoordinates.groupSchemeIso T).inv ≫
    (AffineCoordinates.groupSchemeIso T).hom).hom.hom = y
  rw [Iso.inv_hom_id]
  rfl

omit [FiniteDimensional F E] [IsAffine T.X.left] in
/-- The rational-point and affine-point conventions agree with postcomposition. -/
theorem rationalCoeffEquiv_comp {G H : GroupScheme (Spec (CommRingCat.of F))} (f : G ⟶ H)
    (x : rationalPoints G) :
    GaloisPointComparison.rationalCoeffEquiv F H (x ≫ f.hom.hom) =
      GaloisPointComparison.rationalCoeffEquiv F G x ≫ f.hom.hom := by
  apply Over.OverMorphism.ext
  rw [GaloisPointComparison.rationalCoeffEquiv_left, Over.comp_left, Over.comp_left,
    GaloisPointComparison.rationalCoeffEquiv_left]
  rfl

omit [FiniteDimensional F E] [IsAffine T.X.left] in
/-- The rational-point convention is precomposition with the canonical test isomorphism. -/
theorem rationalCoeffEquiv_eq_comp {G : GroupScheme (Spec (CommRingCat.of E))}
    (x : rationalPoints G) :
    GaloisPointComparison.rationalCoeffEquiv E G x =
      (Langlands.AlgebraicGeometry.PointTopology.ringTestSelfIso E).hom ≫ x := by
  apply Over.OverMorphism.ext
  rw [GaloisPointComparison.rationalCoeffEquiv_left, Over.comp_left]
  exact (Category.id_comp _).symm

omit [FiniteDimensional F E] [IsAffine T.X.left] in
/-- The base-change comparison of rational points is the coefficient comparison of `pointE`. -/
theorem pointE_baseChangeCoeffEquiv
    (s : rationalPoints (GaloisPointComparison.baseChanged F E T)) :
    pointE F E E T (GaloisPointComparison.baseChangeCoeffEquiv F E T s) =
      GaloisPointComparison.rationalCoeffEquiv E (GaloisPointComparison.baseChanged F E T) s := by
  apply Over.OverMorphism.ext
  apply CategoryTheory.Limits.pullback.hom_ext
  · have h := baseChangePointsEquiv_left (baseMap F E) T
      ((algSpec (CommRingCat.of E)).obj (op (CommAlgCat.of E E)))
      (pointE F E E T (GaloisPointComparison.baseChangeCoeffEquiv F E T s))
    rw [baseChangePointsEquiv_pointE] at h
    change ((specRestrictIso F E E).hom ≫
      GaloisPointComparison.baseChangeCoeffEquiv F E T s).left = _ at h
    refine h.symm.trans ?_
    rw [Over.comp_left, GaloisPointComparison.rationalCoeffEquiv_left,
      GaloisPointComparison.baseChangeCoeffEquiv_left]
    exact Category.id_comp _
  · have h1 := Over.w (pointE F E E T (GaloisPointComparison.baseChangeCoeffEquiv F E T s))
    have h2 := Over.w
      (GaloisPointComparison.rationalCoeffEquiv E (GaloisPointComparison.baseChanged F E T) s)
    exact h1.trans h2.symm

omit [FiniteDimensional F E] [IsAffine T.X.left] in
/-- On rational points of `T_E`, the coefficient value is the rational character value. -/
theorem valueE_baseChangeCoeffEquiv
    (s : rationalPoints (GaloisPointComparison.baseChanged F E T)) :
    valueE χ E (GaloisPointComparison.baseChangeCoeffEquiv F E T s) =
      rationalCharacterEval χ s := by
  rw [valueE_apply, pointE_baseChangeCoeffEquiv, ← rationalCoeffEquiv_comp,
    GaloisPoint.gm_units_rationalCoeffEquiv]
  rfl

/-- **Norm character formula.** At a rational point `t`, the norm character takes the field
norm of the value of `χ` at the extended point. -/
theorem normCharacter_eval (t : rationalPoints T) :
    ((rationalCharacterEval (normCharacter χ) t : Fˣ) : F) =
      Algebra.norm F ((rationalCharacterEval χ
        (GaloisPointComparison.rationalExtend F E T t) : Eˣ) : E) := by
  set y₀ := GaloisPointComparison.rationalCoeffEquiv F T t
  have h1 : rationalCharacterEval (normCharacter χ) t =
      Gm.affineUnitsEquiv (CommRingCat.of F) (CommAlgCat.of F F)
        (y₀ ≫ (normCharacter χ).toMul.hom.hom) := by
    rw [rationalCharacterEval_apply, ← GaloisPoint.gm_units_rationalCoeffEquiv,
      rationalCoeffEquiv_comp]
  rw [h1, normCharacter_affinePoints]
  set v := valueE χ (E ⊗[F] F) (T.affinePointMap (CommAlgCat.ofHom
    (Algebra.TensorProduct.includeRight : F →ₐ[F] E ⊗[F] F)) y₀)
  have hext : Units.map (Algebra.TensorProduct.rid F E E).toAlgHom.toMonoidHom v =
      rationalCharacterEval χ (GaloisPointComparison.rationalExtend F E T t) := by
    rw [← valueE_baseChangeCoeffEquiv, GaloisPointComparison.baseChangeCoeffEquiv_rationalExtend,
      ← valueE_naturality]
    congr 1
    have hcomp : CommAlgCat.ofHom (Algebra.TensorProduct.includeRight : F →ₐ[F] E ⊗[F] F) ≫
        CommAlgCat.ofHom ((Algebra.TensorProduct.rid F E E).toAlgHom.restrictScalars F) =
          CommAlgCat.ofHom (Algebra.ofId F E) := by
      ext
    have h := DFunLike.congr_fun (T.affinePointMap_comp
      (CommAlgCat.ofHom (Algebra.TensorProduct.includeRight : F →ₐ[F] E ⊗[F] F))
      (CommAlgCat.ofHom ((Algebra.TensorProduct.rid F E E).toAlgHom.restrictScalars F))) y₀
    rw [MonoidHom.comp_apply] at h
    rw [← h, hcomp]
    rfl
  rw [← hext]
  change Algebra.norm F (Algebra.TensorProduct.comm F E F (v : E ⊗[F] F)) =
    Algebra.norm F (Algebra.TensorProduct.rid F E E (v : E ⊗[F] F))
  rw [← Algebra.norm_eq_of_algEquiv (Algebra.TensorProduct.lid F E)]
  congr 1
  induction (v : E ⊗[F] F) using TensorProduct.inductionOn with
  | tmul a b => simp [Algebra.smul_def, mul_comm]
  | add a b ha hb => simp only [map_add, ha, hb]

end Evaluation

end Langlands.Plancherel.TorusNormKernel
