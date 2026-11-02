import Langlands.GroupScheme.Reductive.GeneralLinearDiagonal
import Mathlib.Algebra.DualNumber
import Mathlib.Tactic.LinearCombination

/-! # The diagonal torus of `GL_n` is a maximal torus -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.GeneralLinear

/-! ### Dual numbers -/

section DualNumbers

variable (A : Type*) [CommRing A]

/-- The unit `1 + ε` of the dual numbers, with inverse `1 - ε`. -/
def onePlusEps : (DualNumber A)ˣ where
  val := 1 + DualNumber.eps
  inv := 1 - DualNumber.eps
  val_inv := by linear_combination (-1 : DualNumber A) * (DualNumber.eps_mul_eps (R := A))
  inv_val := by linear_combination (-1 : DualNumber A) * (DualNumber.eps_mul_eps (R := A))

variable {A}

theorem eq_zero_of_eps_mul_inl {m : A}
    (h : (DualNumber.eps : DualNumber A) * TrivSqZeroExt.inl m = 0) : m = 0 := by
  have h' := congrArg TrivSqZeroExt.snd h
  simpa using h'

end DualNumbers

variable {n : Type} [Fintype n] [DecidableEq n] {R : CommRingCat.{u}}

/-- Affine coordinates are the global-section coordinates transported along the section
isomorphism. -/
theorem affinePointsEquiv_eq_map_pointsEquiv (S : CommAlgCat.{u} R)
    (x : (algSpec R).obj (op S) ⟶ (groupScheme n R).X) :
    affinePointsEquiv n R S x =
      Matrix.GeneralLinearGroup.map (Corepresented.affineSectionsIso S).hom.hom.toRingHom
        (pointsEquiv n R _ x) := by
  rw [pointsEquiv_eq_affinePointsEquiv]
  ext i j
  exact (ConcreteCategory.congr_hom (Corepresented.affineSectionsIso S).inv_hom_id _).symm

/-! ### Points commuting with the diagonal torus are diagonal -/

section Commuting

variable {T' : CommGroupScheme (Spec R)} (i' : T'.toGrp ⟶ groupScheme n R)
  (f : (splitTorus.commGroupScheme (Spec R) (ULift.{u} n)).toGrp ⟶ T'.toGrp)

/-- If the diagonal torus factors as `f ≫ i'` through a commutative group scheme `T'`, then
every affine point of `T'` maps to a diagonal matrix: it commutes with `diag(1, …, 1 + ε, …, 1)`
over the dual numbers. -/
theorem isDiagonalGL_affinePointsEquiv (hf : f ≫ i' = diagonalTorus n R) (B : CommAlgCat.{u} R)
    (y : (algSpec R).obj (op B) ⟶ T'.X) :
    IsDiagonalGL (affinePointsEquiv n R B (y ≫ i'.hom.hom)) := by
  intro a b hab
  let B' : CommAlgCat.{u} R := CommAlgCat.of R (DualNumber B)
  let inl : B ⟶ B' := CommAlgCat.ofHom (TrivSqZeroExt.inlAlgHom R B B)
  let U' := (algSpec R).obj (op B')
  let y' : U' ⟶ T'.X := (algSpec R).map inl.op ≫ y
  let e : Γ(U'.left, ⊤)ˣ :=
    Units.map (Corepresented.affineSectionsIso B').inv.hom.toRingHom.toMonoidHom (onePlusEps B)
  let t : U' ⟶ (splitTorus (Spec R) (ULift.{u} n)).X :=
    (splitTorus.pointsEquiv (ULift.{u} n) U').symm (Pi.mulSingle ⟨a⟩ e)
  have hcomm : y' * (t ≫ f.hom.hom) = (t ≫ f.hom.hom) * y' := mul_comm _ _
  have hy' : affinePointsEquiv n R B' (y' ≫ i'.hom.hom) =
      Matrix.GeneralLinearGroup.map inl.hom.toRingHom
        (affinePointsEquiv n R B (y ≫ i'.hom.hom)) := by
    rw [Category.assoc, affinePointsEquiv_naturality]
  let φ := (Corepresented.affineSectionsIso B').hom.hom
  have hM' : φ ((pointsEquiv n R U' (y' ≫ i'.hom.hom) : Matrix n n Γ(U'.left, ⊤)) a b) =
      TrivSqZeroExt.inl ((affinePointsEquiv n R B (y ≫ i'.hom.hom) : Matrix n n B) a b) := by
    have h := congrArg (fun M : GL n B' => (M : Matrix n n B') a b)
      ((affinePointsEquiv_eq_map_pointsEquiv B' (y' ≫ i'.hom.hom)).symm.trans hy')
    exact h
  have he : φ (e : Γ(U'.left, ⊤)) = 1 + DualNumber.eps :=
    ConcreteCategory.congr_hom (Corepresented.affineSectionsIso B').inv_hom_id _
  have hD : pointsEquiv n R U' ((t ≫ f.hom.hom) ≫ i'.hom.hom) =
      diagonalTorusUnits n Γ(U'.left, ⊤) (Pi.mulSingle ⟨a⟩ e) := by
    rw [Category.assoc, ← Grp.comp_hom_hom, hf, pointsEquiv_diagonalTorus]
    exact congrArg _ (MulEquiv.apply_symm_apply _ _)
  have h1 := congrArg (pointsEquiv n R U') (congrArg (· ≫ i'.hom.hom) hcomm)
  simp only [MonObj.mul_comp, map_mul, hD] at h1
  have h2 := congrArg (fun M : GL n Γ(U'.left, ⊤) => (M : Matrix n n Γ(U'.left, ⊤)) a b) h1
  simp only [Units.val_mul, coe_diagonalTorusUnits, Matrix.mul_diagonal,
    Matrix.diagonal_mul] at h2
  have hba : (⟨b⟩ : ULift.{u} n) ≠ ⟨a⟩ := fun h => hab (congrArg ULift.down h).symm
  rw [Pi.mulSingle_eq_of_ne hba, Pi.mulSingle_eq_same, Units.val_one, mul_one] at h2
  set m := (affinePointsEquiv n R B (y ≫ i'.hom.hom) : Matrix n n B) a b
  have key : (TrivSqZeroExt.inl m : DualNumber B) =
      (1 + DualNumber.eps) * TrivSqZeroExt.inl m := by
    calc (TrivSqZeroExt.inl m : DualNumber B)
        = φ ((pointsEquiv n R U' (y' ≫ i'.hom.hom) : Matrix n n Γ(U'.left, ⊤)) a b) := hM'.symm
      _ = φ ((e : Γ(U'.left, ⊤)) *
          (pointsEquiv n R U' (y' ≫ i'.hom.hom) : Matrix n n Γ(U'.left, ⊤)) a b) :=
          congrArg φ h2
      _ = φ (e : Γ(U'.left, ⊤)) *
          φ ((pointsEquiv n R U' (y' ≫ i'.hom.hom) : Matrix n n Γ(U'.left, ⊤)) a b) :=
          map_mul φ _ _
      _ = (1 + DualNumber.eps) * TrivSqZeroExt.inl m := by rw [he, hM']
  apply eq_zero_of_eps_mul_inl (A := B)
  linear_combination -1 * key

/-- Under the same hypotheses, and if `T'` is affine, every point of `T'` maps to a diagonal
matrix. The proof reduces to the universal point, which is affine. -/
theorem isDiagonalGL_universal (hf : f ≫ i' = diagonalTorus n R) [IsAffine T'.X.left] :
    IsDiagonalGL (pointsEquiv n R T'.X i'.hom.hom) := by
  obtain ⟨D, ⟨e⟩⟩ := (essImage_algSpec (G := T'.X)).mpr inferInstance
  have h : i'.hom.hom = e.inv ≫ (e.hom ≫ i'.hom.hom) := by
    rw [Iso.inv_hom_id_assoc]
  rw [h, pointsEquiv_naturality, pointsEquiv_eq_affinePointsEquiv]
  exact ((isDiagonalGL_affinePointsEquiv i' f hf D.unop e.hom).map _).map _

/-- The factorization of `i'` through the diagonal torus on the universal point. -/
def universalLift (hf : f ≫ i' = diagonalTorus n R) [IsAffine T'.X.left] :
    T'.X ⟶ (splitTorus (Spec R) (ULift.{u} n)).X :=
  (splitTorus.pointsEquiv (ULift.{u} n) T'.X).symm (diagUnits (isDiagonalGL_universal i' f hf))

theorem universalLift_comp (hf : f ≫ i' = diagonalTorus n R) [IsAffine T'.X.left] :
    universalLift i' f hf ≫ (diagonalTorus n R).hom.hom = i'.hom.hom := by
  apply (pointsEquiv n R _).injective
  rw [pointsEquiv_diagonalTorus, universalLift, MulEquiv.apply_symm_apply,
    diagonalTorusUnits_diagUnits]

/-- The points of the homomorphism `T' ⟶ D_n` through which `i'` factors. -/
def liftPoints (hf : f ≫ i' = diagonalTorus n R) [IsAffine T'.X.left] (U : Over (Spec R)) :
    (U ⟶ T'.X) →* (U ⟶ (splitTorus (Spec R) (ULift.{u} n)).X) where
  toFun x := x ≫ universalLift i' f hf
  map_one' := by
    rw [← cancel_mono (diagonalTorus n R).hom.hom, Category.assoc, universalLift_comp,
      MonObj.one_comp, MonObj.one_comp]
  map_mul' x y := by
    rw [← cancel_mono (diagonalTorus n R).hom.hom, Category.assoc, universalLift_comp,
      MonObj.mul_comp, MonObj.mul_comp, Category.assoc, Category.assoc, universalLift_comp]

theorem liftPoints_apply (hf : f ≫ i' = diagonalTorus n R) [IsAffine T'.X.left]
    (U : Over (Spec R)) (x : U ⟶ T'.X) : liftPoints i' f hf U x = x ≫ universalLift i' f hf :=
  rfl

theorem liftPoints_naturality (hf : f ≫ i' = diagonalTorus n R) [IsAffine T'.X.left]
    {U U' : Over (Spec R)} (a : U' ⟶ U) (x : U ⟶ T'.X) :
    liftPoints i' f hf U' (a ≫ x) = a ≫ liftPoints i' f hf U x := by
  rw [liftPoints_apply, liftPoints_apply, Category.assoc]

/-- The homomorphism `T' ⟶ D_n` through which `i'` factors. -/
def liftHom (hf : f ≫ i' = diagonalTorus n R) [IsAffine T'.X.left] :
    T'.toGrp ⟶ (splitTorus.commGroupScheme (Spec R) (ULift.{u} n)).toGrp :=
  homOfPoints (liftPoints i' f hf) (fun {_ _} a x => liftPoints_naturality i' f hf a x)

theorem liftHom_comp (hf : f ≫ i' = diagonalTorus n R) [IsAffine T'.X.left] :
    liftHom i' f hf ≫ diagonalTorus n R = i' := by
  apply hom_ext_points
  intro U x
  rw [Grp.comp_hom_hom, ← Category.assoc, liftHom, comp_homOfPoints, liftPoints_apply,
    Category.assoc, universalLift_comp]

/-- If the diagonal torus factors as `f ≫ i'` with `i'` a closed subgroup from a commutative
group scheme, then `f` is an isomorphism. -/
theorem isIso_of_comp_eq_diagonalTorus (hf : f ≫ i' = diagonalTorus n R)
    (hi' : IsClosedSubgroup i') : IsIso f := by
  have : IsClosedImmersion i'.hom.hom.left := hi'
  have : IsAffine T'.X.left := isAffine_of_isAffineHom i'.hom.hom.left
  have : Mono i'.hom.hom := Over.mono_of_mono_left _
  refine ⟨liftHom i' f hf, ?_, ?_⟩
  · apply Grp.hom_ext
    rw [← cancel_mono (diagonalTorus n R).hom.hom, Grp.comp_hom_hom, Category.assoc,
      ← Grp.comp_hom_hom, liftHom_comp, ← Grp.comp_hom_hom, hf, Grp.id_hom_hom, Category.id_comp]
  · apply Grp.hom_ext
    rw [← cancel_mono i'.hom.hom, Grp.comp_hom_hom, Category.assoc, ← Grp.comp_hom_hom, hf,
      ← Grp.comp_hom_hom, liftHom_comp, Grp.id_hom_hom, Category.id_comp]

end Commuting

/-! ### Maximality -/

/-- The diagonal torus of `GL_n` over a field is a maximal torus (Milne, Example 17.88). -/
theorem isMaximalTorus_diagonalTorus (k : Type u) [Field k] :
    IsMaximalTorus (diagonalTorus n (CommRingCat.of k)) :=
  ⟨IsSplitTorus.isTorus (isSplitTorus_splitTorus _), isClosedSubgroup_diagonalTorus n _,
    fun _ i' f _ hi' hf => isIso_of_comp_eq_diagonalTorus i' f hf hi'⟩

end Langlands.GroupScheme.GeneralLinear
