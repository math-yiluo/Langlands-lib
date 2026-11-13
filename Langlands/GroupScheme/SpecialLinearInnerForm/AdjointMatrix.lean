import Langlands.GroupScheme.SpecialLinearInnerForm.ConjugationDescent
import Langlands.GroupScheme.SpecialLinearInnerForm.MatrixExtension
import Langlands.GroupScheme.Adjoint.InnerAction
import Langlands.GroupScheme.SpecialLinear
import Langlands.AlgebraicGeometry.Modules.UnitCocycleDescent.FunctionDescent
import Langlands.AlgebraicGeometry.PointTopology.ProductRingPoints

/-! # The matrix algebra action of a supplied adjoint quotient of SL -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SpecialLinearInnerForm

open Langlands.AlgebraicGeometry.PointTopology

variable {K : Type u} [Field K] {n : Type} [Fintype n] [DecidableEq n]
    {M A : GroupScheme (Spec (CommRingCat.of K))}

/-- Matrix coordinates on every test scheme, transported through the supplied
special-linear presentation. -/
def pointMatrix (i : M ≅ SpecialLinear.groupScheme n (CommRingCat.of K))
    (T : Over (Spec (CommRingCat.of K))) :
    (T ⟶ M.X) ≃* Matrix.SpecialLinearGroup n Γ(T.left, ⊤) :=
  (((yonedaGrp.mapIso i).app (op T)).groupIsoToMulEquiv).trans
    (SpecialLinear.pointsEquiv n (CommRingCat.of K) T)

@[simp] theorem pointMatrix_apply
    (i : M ≅ SpecialLinear.groupScheme n (CommRingCat.of K))
    (T : Over (Spec (CommRingCat.of K))) (g : T ⟶ M.X) :
    pointMatrix i T g =
      SpecialLinear.pointsEquiv n (CommRingCat.of K) T (g ≫ i.hom.hom.hom) := rfl

theorem pointMatrix_naturality
    (i : M ≅ SpecialLinear.groupScheme n (CommRingCat.of K))
    {T V : Over (Spec (CommRingCat.of K))} (b : V ⟶ T) (g : T ⟶ M.X) :
    pointMatrix i V (b ≫ g) =
      Matrix.SpecialLinearGroup.map b.left.appTop.hom (pointMatrix i T g) := by
  simp only [pointMatrix_apply, Category.assoc]
  exact SpecialLinear.pointsEquiv_naturality b _

/-- The affine test scheme associated to a coefficient algebra. -/
abbrev matrixTest (L : Type u) [CommRing L] [Algebra K L] :
    Over (Spec (CommRingCat.of K)) :=
  (algSpec (CommRingCat.of K)).obj (op (CommAlgCat.of (CommRingCat.of K) L))

/-- Affine matrix coordinates with coefficients in the test algebra itself. -/
def affineMatrix (i : M ≅ SpecialLinear.groupScheme n (CommRingCat.of K))
    (L : Type u) [CommRing L] [Algebra K L] :
    (matrixTest (K := K) L ⟶ M.X) ≃* Matrix.SpecialLinearGroup n L :=
  (((yonedaGrp.mapIso i).app (op (matrixTest (K := K) L))).groupIsoToMulEquiv).trans
    (SpecialLinear.affinePointsEquiv n (CommRingCat.of K)
      (CommAlgCat.of (CommRingCat.of K) L))

/-- Affine matrix coordinates commute with coefficient change. -/
theorem affineMatrix_naturality
    (i : M ≅ SpecialLinear.groupScheme n (CommRingCat.of K))
    {L B : Type u} [CommRing L] [CommRing B] [Algebra K L] [Algebra K B]
    (f : L →ₐ[K] B) (g : matrixTest (K := K) L ⟶ M.X) :
    affineMatrix i B (ringTestMap K f ≫ g) =
      Matrix.SpecialLinearGroup.map f.toRingHom (affineMatrix i L g) := by
  have hb : ringTestMap K f = (algSpec (CommRingCat.of K)).map
      (CommAlgCat.ofHom (R := CommRingCat.of K) f).op := by
    ext1
    rfl
  rw [hb]
  change SpecialLinear.affinePointsEquiv _ _ _ ((_ ≫ g) ≫ i.hom.hom.hom) = _
  rw [Category.assoc]
  exact Corepresented.affinePointsEquiv_naturality _ _
    (CommAlgCat.ofHom (R := CommRingCat.of K) f) _

/-- Pullback of coefficients along an arbitrary test over the affine coefficient
scheme. -/
def sectionMap {L : Type u} [CommRing L] [Algebra K L]
    {V : Over (Spec (CommRingCat.of K))} (s : V ⟶ matrixTest (K := K) L) :
    L →+* Γ(V.left, ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of L)).inv ≫ s.left.appTop).hom

theorem sectionMap_comp {L : Type u} [CommRing L] [Algebra K L]
    {V W : Over (Spec (CommRingCat.of K))} (b : W ⟶ V)
    (s : V ⟶ matrixTest (K := K) L) :
    sectionMap (b ≫ s) = b.left.appTop.hom.comp (sectionMap s) := by
  ext r
  change (b.left ≫ s.left).appTop ((Scheme.ΓSpecIso (CommRingCat.of L)).inv r) = _
  rw [Scheme.Hom.comp_appTop]
  rfl

/-- Pullback of coefficients along the spectrum of an algebra map is composition
with that algebra map. -/
theorem sectionMap_ringTestMap_comp
    {L B : Type u} [CommRing L] [CommRing B] [Algebra K L] [Algebra K B]
    (f : L →ₐ[K] B) {V : Over (Spec (CommRingCat.of K))}
    (s : V ⟶ matrixTest (K := K) B) :
    sectionMap (s ≫ ringTestMap K f) = (sectionMap s).comp f.toRingHom := by
  change ((Scheme.ΓSpecIso (CommRingCat.of L)).inv ≫
    (s.left ≫ Spec.map (CommRingCat.ofHom f.toRingHom)).appTop).hom = _
  rw [Scheme.Hom.comp_appTop, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality]
  rfl

theorem pointMatrix_affine
    (i : M ≅ SpecialLinear.groupScheme n (CommRingCat.of K))
    {L : Type u} [CommRing L] [Algebra K L]
    (g : matrixTest (K := K) L ⟶ M.X) :
    pointMatrix i (matrixTest (K := K) L) g =
      Matrix.SpecialLinearGroup.map (Scheme.ΓSpecIso (CommRingCat.of L)).inv.hom
        (affineMatrix i L g) := by
  exact Corepresented.pointsEquiv_eq_affinePointsEquiv (SpecialLinear.functor n _)
    (SpecialLinear.corepresentableBy n _) _ _

theorem pointMatrix_comp_affine
    (i : M ≅ SpecialLinear.groupScheme n (CommRingCat.of K))
    {L : Type u} [CommRing L] [Algebra K L]
    {V : Over (Spec (CommRingCat.of K))} (s : V ⟶ matrixTest (K := K) L)
    (g : matrixTest (K := K) L ⟶ M.X) :
    pointMatrix i V (s ≫ g) =
      Matrix.SpecialLinearGroup.map (sectionMap s) (affineMatrix i L g) := by
  rw [pointMatrix_naturality, pointMatrix_affine]
  apply Subtype.ext
  rfl

variable {q : M ⟶ A}

/-- The universal local lift of a point through the supplied quotient. -/
def liftTest {T : Over (Spec (CommRingCat.of K))} (c : T ⟶ A.X) :
    Over (Spec (CommRingCat.of K)) :=
  Over.mk (pullback.fst c.left q.hom.hom.left ≫ T.hom)

def liftBase {T : Over (Spec (CommRingCat.of K))} (c : T ⟶ A.X) :
    liftTest (q := q) c ⟶ T :=
  Over.homMk (pullback.fst c.left q.hom.hom.left) rfl

def liftPoint {T : Over (Spec (CommRingCat.of K))} (c : T ⟶ A.X) :
    liftTest (q := q) c ⟶ M.X :=
  Over.homMk (pullback.snd c.left q.hom.hom.left) (by
    change pullback.snd c.left q.hom.hom.left ≫ M.X.hom =
      pullback.fst c.left q.hom.hom.left ≫ T.hom
    rw [← Over.w q.hom.hom, ← Category.assoc, ← pullback.condition,
      Category.assoc, Over.w c])

theorem lift_condition {T : Over (Spec (CommRingCat.of K))} (c : T ⟶ A.X) :
    liftBase (q := q) c ≫ c = liftPoint (q := q) c ≫ q.hom.hom :=
  Over.OverMorphism.ext pullback.condition

/-- The universal lifts are functorial under change of test scheme. -/
def liftTestMap {T V : Over (Spec (CommRingCat.of K))} (s : V ⟶ T)
    (c : T ⟶ A.X) : liftTest (q := q) (s ≫ c) ⟶ liftTest (q := q) c :=
  Over.homMk (pullback.lift
    (pullback.fst (s ≫ c).left q.hom.hom.left ≫ s.left)
    (pullback.snd (s ≫ c).left q.hom.hom.left)
    (by
      change (pullback.fst (s ≫ c).left q.hom.hom.left ≫ s.left) ≫ c.left = _
      rw [Category.assoc]
      exact pullback.condition))
    (by
      change pullback.lift _ _ _ ≫ (pullback.fst _ _ ≫ T.hom) = _
      rw [pullback.lift_fst_assoc, Category.assoc, Over.w s]
      rfl)

@[simp] theorem liftTestMap_base
    {T V : Over (Spec (CommRingCat.of K))} (s : V ⟶ T) (c : T ⟶ A.X) :
    liftTestMap (q := q) s c ≫ liftBase (q := q) c =
      liftBase (q := q) (s ≫ c) ≫ s := by
  apply Over.OverMorphism.ext
  exact pullback.lift_fst _ _ _

@[simp] theorem liftTestMap_point
    {T V : Over (Spec (CommRingCat.of K))} (s : V ⟶ T) (c : T ⟶ A.X) :
    liftTestMap (q := q) s c ≫ liftPoint (q := q) c =
      liftPoint (q := q) (s ≫ c) := by
  apply Over.OverMorphism.ext
  exact pullback.lift_snd _ _ _

theorem liftBase_epi (hq : IsAdjointQuotient q)
    {T : Over (Spec (CommRingCat.of K))} (c : T ⟶ A.X) :
    Epi (liftBase (q := q) c).left := by
  let := hq.flat
  let := hq.surjective
  change Epi (pullback.fst c.left q.hom.hom.left)
  exact Flat.epi_of_flat_of_surjective _

theorem sectionMap_lift_injective (hq : IsAdjointQuotient q)
    {L : Type u} [CommRing L] [Algebra K L]
    (c : matrixTest (K := K) L ⟶ A.X) :
    Function.Injective (sectionMap (liftBase (q := q) c)) := by
  let := liftBase_epi hq c
  exact (Langlands.Scheme.UnitCocycleDescent.appTop_injective_of_epi
    (liftBase (q := q) c).left).comp
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of L)).inv).1

/-- Over the local lift, the given inner action is the usual conjugation of
determinant-one matrices. -/
theorem pointMatrix_inner_lift (hq : IsAdjointQuotient q)
    (i : M ≅ SpecialLinear.groupScheme n (CommRingCat.of K))
    {T : Over (Spec (CommRingCat.of K))} (c : T ⟶ A.X) (g : T ⟶ M.X) :
    pointMatrix i (liftTest (q := q) c)
        (liftBase (q := q) c ≫ hq.innerAction.act c g) =
      pointMatrix i _ (liftPoint (q := q) c) *
        pointMatrix i _ (liftBase (q := q) c ≫ g) *
        (pointMatrix i _ (liftPoint (q := q) c))⁻¹ := by
  rw [hq.innerAction.naturality, lift_condition, hq.innerAction_act_lift]
  simp only [map_mul, map_inv]

/-- The local conjugation preserves the coefficient image on all special-linear
matrices. -/
theorem conjugation_image_specialLinear (hq : IsAdjointQuotient q)
    (i : M ≅ SpecialLinear.groupScheme n (CommRingCat.of K))
    {L : Type u} [CommRing L] [Algebra K L]
    (c : matrixTest (K := K) L ⟶ A.X) (g : Matrix.SpecialLinearGroup n L) :
    ∃ y : Matrix n n L, y.map (sectionMap (liftBase (q := q) c)) =
      (pointMatrix i _ (liftPoint (q := q) c) : Matrix n n _) *
        (g : Matrix n n L).map (sectionMap (liftBase (q := q) c)) *
        (((pointMatrix i _ (liftPoint (q := q) c))⁻¹ :
          Matrix.SpecialLinearGroup n _) : Matrix n n _) := by
  let x := (affineMatrix i L).symm g
  refine ⟨affineMatrix i L (hq.innerAction.act c x), ?_⟩
  have he := pointMatrix_inner_lift hq i c x
  rw [pointMatrix_comp_affine, pointMatrix_comp_affine, MulEquiv.apply_symm_apply] at he
  exact congrArg Subtype.val he

/-- An adjoint point acts by an algebra endomorphism on the matrix algebra.
The construction uses its universal fpqc lift and injective coefficient pullback. -/
def adjointMatrixHom (hq : IsAdjointQuotient q)
    (i : M ≅ SpecialLinear.groupScheme n (CommRingCat.of K))
    {L : Type u} [CommRing L] [Algebra K L]
    (c : matrixTest (K := K) L ⟶ A.X) :
    Matrix n n L →ₐ[L] Matrix n n L := by
  let B := Γ((liftTest (q := q) c).left, ⊤)
  letI : Algebra L B := (sectionMap (liftBase (q := q) c)).toAlgebra
  let φ : Matrix n n L →ₐ[L] Matrix n n B := (Algebra.ofId L B).mapMatrix
  let H := (pointMatrix i _ (liftPoint (q := q) c)).toGL
  let ψ := (conjugationAlgHom (R := L) H).comp φ
  refine descendMatrixAlgHom φ ψ ?_ ?_
  · intro g
    exact conjugation_image_specialLinear hq i c g
  · intro X Y h
    ext a b
    exact sectionMap_lift_injective hq c (congrFun (congrFun h a) b)

/-- The matrix action is conjugation after pullback to the universal lift. -/
theorem adjointMatrixHom_map (hq : IsAdjointQuotient q)
    (i : M ≅ SpecialLinear.groupScheme n (CommRingCat.of K))
    {L : Type u} [CommRing L] [Algebra K L]
    (c : matrixTest (K := K) L ⟶ A.X) (X : Matrix n n L) :
    (adjointMatrixHom hq i c X).map (sectionMap (liftBase (q := q) c)) =
      (pointMatrix i _ (liftPoint (q := q) c) : Matrix n n _) *
        X.map (sectionMap (liftBase (q := q) c)) *
        (((pointMatrix i _ (liftPoint (q := q) c))⁻¹ :
          Matrix.SpecialLinearGroup n _) : Matrix n n _) := by
  let B := Γ((liftTest (q := q) c).left, ⊤)
  let : Algebra L B := (sectionMap (liftBase (q := q) c)).toAlgebra
  let φ : Matrix n n L →ₐ[L] Matrix n n B := (Algebra.ofId L B).mapMatrix
  let H := (pointMatrix i _ (liftPoint (q := q) c)).toGL
  let ψ := (conjugationAlgHom (R := L) H).comp φ
  exact map_descendMatrixAlgHom φ ψ (conjugation_image_specialLinear hq i c)
    (fun X Y h => by
      ext a b
      exact sectionMap_lift_injective hq c (congrFun (congrFun h a) b)) X

/-- On determinant-one matrices the algebra action is the supplied inner action. -/
theorem adjointMatrixHom_specialLinear (hq : IsAdjointQuotient q)
    (i : M ≅ SpecialLinear.groupScheme n (CommRingCat.of K))
    {L : Type u} [CommRing L] [Algebra K L]
    (c : matrixTest (K := K) L ⟶ A.X) (g : matrixTest (K := K) L ⟶ M.X) :
    adjointMatrixHom hq i c (affineMatrix i L g) =
      (affineMatrix i L (hq.innerAction.act c g) : Matrix n n L) := by
  have hα := adjointMatrixHom_map hq i c (affineMatrix i L g)
  have he := pointMatrix_inner_lift hq i c g
  rw [pointMatrix_comp_affine, pointMatrix_comp_affine] at he
  exact Matrix.map_injective (sectionMap_lift_injective hq c)
    (hα.trans (congrArg Subtype.val he).symm)

/-- The descended algebra action remains conjugation after any pullback of
the universal lift. -/
theorem adjointMatrixHom_map_lift (hq : IsAdjointQuotient q)
    (i : M ≅ SpecialLinear.groupScheme n (CommRingCat.of K))
    {L : Type u} [CommRing L] [Algebra K L]
    (c : matrixTest (K := K) L ⟶ A.X)
    {V : Over (Spec (CommRingCat.of K))} (s : V ⟶ matrixTest (K := K) L)
    (X : Matrix n n L) :
    (adjointMatrixHom hq i c X).map
        (sectionMap (liftBase (q := q) (s ≫ c) ≫ s)) =
      (pointMatrix i _ (liftPoint (q := q) (s ≫ c)) : Matrix n n _) *
        X.map (sectionMap (liftBase (q := q) (s ≫ c) ≫ s)) *
        (((pointMatrix i _ (liftPoint (q := q) (s ≫ c)))⁻¹ :
          Matrix.SpecialLinearGroup n _) : Matrix n n _) := by
  let b := liftTestMap (q := q) s c
  have hf : sectionMap (liftBase (q := q) (s ≫ c) ≫ s) =
      b.left.appTop.hom.comp (sectionMap (liftBase (q := q) c)) := by
    rw [← liftTestMap_base s c, sectionMap_comp]
  have hH := pointMatrix_naturality i b (liftPoint (q := q) c)
  simp only [b, liftTestMap_point] at hH
  have hHmat := congrArg Subtype.val hH
  have hHimat := congrArg (fun z : Matrix.SpecialLinearGroup n
      Γ((liftTest (q := q) (s ≫ c)).left, ⊤) => (z⁻¹).val) hH
  have hmapinv := congrArg Subtype.val
    ((Matrix.SpecialLinearGroup.map b.left.appTop.hom).map_inv
      (pointMatrix i _ (liftPoint (q := q) c))).symm
  have hHimat' := hHimat.trans hmapinv
  change _ = (pointMatrix i _ (liftPoint (q := q) c) : Matrix n n _).map
    b.left.appTop.hom at hHmat
  change _ = (((pointMatrix i _ (liftPoint (q := q) c))⁻¹ :
    Matrix.SpecialLinearGroup n _) : Matrix n n _).map b.left.appTop.hom at hHimat'
  have he := congrArg (fun Y : Matrix n n Γ((liftTest (q := q) c).left, ⊤) =>
    Y.map b.left.appTop.hom) (adjointMatrixHom_map hq i c X)
  simpa only [Matrix.map_mul, Matrix.map_map, ← RingHom.coe_comp, ← hf,
    ← hHmat, ← hHimat'] using he

/-- On every test over the affine coefficient scheme, the given inner action is
the coefficient extension of the descended matrix algebra action. -/
theorem pointMatrix_innerAction (hq : IsAdjointQuotient q)
    (i : M ≅ SpecialLinear.groupScheme n (CommRingCat.of K))
    {L : Type u} [CommRing L] [Algebra K L]
    (c : matrixTest (K := K) L ⟶ A.X)
    {V : Over (Spec (CommRingCat.of K))} (s : V ⟶ matrixTest (K := K) L)
    (g : V ⟶ M.X) :
    (pointMatrix i V (hq.innerAction.act (s ≫ c) g) : Matrix n n _) =
      extendMatrix (sectionMap s) (adjointMatrixHom hq i c).toLinearMap
        (pointMatrix i V g) := by
  let p := liftBase (q := q) (s ≫ c)
  let := liftBase_epi hq (s ≫ c)
  let B := Γ((liftTest (q := q) (s ≫ c)).left, ⊤)
  let H := (pointMatrix i _ (liftPoint (q := q) (s ≫ c))).toGL
  have hC : extendMatrix (sectionMap (p ≫ s)) (adjointMatrixHom hq i c).toLinearMap =
      (conjugationAlgHom (R := B) H).toLinearMap := by
    apply extendMatrix_eq
    intro X
    exact (adjointMatrixHom_map_lift hq i c s X).symm
  have hm :
      (pointMatrix i V (hq.innerAction.act (s ≫ c) g) : Matrix n n _).map
          p.left.appTop.hom =
        conjugationAlgHom (R := B) H
          ((pointMatrix i V g : Matrix n n _).map p.left.appTop.hom) := by
    have he := pointMatrix_inner_lift hq i (s ≫ c) g
    rw [pointMatrix_naturality, pointMatrix_naturality] at he
    exact congrArg Subtype.val he
  have hext :
      (extendMatrix (sectionMap s) (adjointMatrixHom hq i c).toLinearMap
        (pointMatrix i V g)).map p.left.appTop.hom =
        conjugationAlgHom (R := B) H
          ((pointMatrix i V g : Matrix n n _).map p.left.appTop.hom) := by
    rw [map_extendMatrix, ← sectionMap_comp]
    exact LinearMap.congr_fun hC _
  exact Matrix.map_injective
    (Langlands.Scheme.UnitCocycleDescent.appTop_injective_of_epi p.left)
      (hm.trans hext.symm)

/-- The identity adjoint point acts trivially on matrices. -/
theorem adjointMatrixHom_one (hq : IsAdjointQuotient q)
    (i : M ≅ SpecialLinear.groupScheme n (CommRingCat.of K))
    (L : Type u) [CommRing L] [Algebra K L] :
    adjointMatrixHom hq i (1 : matrixTest (K := K) L ⟶ A.X) = AlgHom.id L _ := by
  have he : (adjointMatrixHom hq i (1 : matrixTest (K := K) L ⟶ A.X)).toLinearMap =
      (AlgHom.id L (Matrix n n L)).toLinearMap := by
    apply linearMap_ext_specialLinear
    intro x
    change adjointMatrixHom hq i (1 : matrixTest (K := K) L ⟶ A.X) x =
      (x : Matrix n n L)
    let g := (affineMatrix i L).symm x
    have h := adjointMatrixHom_specialLinear hq i
      (1 : matrixTest (K := K) L ⟶ A.X) g
    simpa only [AutomorphicAction.act_one_left, g, MulEquiv.apply_symm_apply] using h
  exact AlgHom.ext fun X => LinearMap.congr_fun he X

/-- Multiplication of adjoint points corresponds to composition of matrix maps. -/
theorem adjointMatrixHom_mul (hq : IsAdjointQuotient q)
    (i : M ≅ SpecialLinear.groupScheme n (CommRingCat.of K))
    {L : Type u} [CommRing L] [Algebra K L]
    (c d : matrixTest (K := K) L ⟶ A.X) (X : Matrix n n L) :
    adjointMatrixHom hq i (c * d) X =
      adjointMatrixHom hq i c (adjointMatrixHom hq i d X) := by
  have he : (adjointMatrixHom hq i (c * d)).toLinearMap =
      ((adjointMatrixHom hq i c).comp (adjointMatrixHom hq i d)).toLinearMap := by
    apply linearMap_ext_specialLinear
    intro x
    let g := (affineMatrix i L).symm x
    have hx : x = affineMatrix i L g := (MulEquiv.apply_symm_apply _ _).symm
    change adjointMatrixHom hq i (c * d) x =
      adjointMatrixHom hq i c (adjointMatrixHom hq i d x)
    rw [hx, adjointMatrixHom_specialLinear, adjointMatrixHom_specialLinear,
      adjointMatrixHom_specialLinear, AutomorphicAction.act_mul_left]
  exact LinearMap.congr_fun he X

/-- The matrix action commutes with every change of coefficient algebra. -/
theorem adjointMatrixHom_naturality (hq : IsAdjointQuotient q)
    (i : M ≅ SpecialLinear.groupScheme n (CommRingCat.of K))
    {L B : Type u} [CommRing L] [CommRing B] [Algebra K L] [Algebra K B]
    (f : L →ₐ[K] B) (c : matrixTest (K := K) L ⟶ A.X) (X : Matrix n n L) :
    (adjointMatrixHom hq i c X).map f =
      adjointMatrixHom hq i (ringTestMap K f ≫ c) (X.map f) := by
  let : Algebra L B := f.toRingHom.toAlgebra
  let F : Matrix n n L →ₗ[L] Matrix n n B :=
    ((Algebra.ofId L B).mapMatrix).toLinearMap
  have he : F.comp (adjointMatrixHom hq i c).toLinearMap =
      ((adjointMatrixHom hq i (ringTestMap K f ≫ c)).toLinearMap.restrictScalars L).comp F := by
    apply linearMap_ext_specialLinear
    intro x
    let g := (affineMatrix i L).symm x
    have hx : x = affineMatrix i L g := (MulEquiv.apply_symm_apply _ _).symm
    change (adjointMatrixHom hq i c x).map f =
      adjointMatrixHom hq i (ringTestMap K f ≫ c) ((x : Matrix n n L).map f)
    rw [hx, adjointMatrixHom_specialLinear]
    have hn := congrArg Subtype.val (affineMatrix_naturality i f g)
    change (affineMatrix i B (ringTestMap K f ≫ g) : Matrix n n B) =
      (affineMatrix i L g : Matrix n n L).map f at hn
    rw [← hn, adjointMatrixHom_specialLinear,
      ← hq.innerAction.naturality, affineMatrix_naturality]
    rfl
  exact LinearMap.congr_fun he X

end Langlands.GroupScheme.SpecialLinearInnerForm
