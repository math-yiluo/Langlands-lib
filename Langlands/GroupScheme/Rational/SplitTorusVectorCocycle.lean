import Langlands.GroupScheme.AutomorphicAction.Cocycles
import Langlands.GroupScheme.ProductProperties
import Langlands.GroupScheme.Rational.VectorLinearAction
import Langlands.GroupScheme.Torus.TranslatedUniversalPoint

/-! # Vector cocycles for split tori -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory

namespace Langlands.GroupScheme

namespace AutomorphicAction.Cocycle

variable {S : Scheme.{u}} {H V : GroupScheme S} {a : AutomorphicAction H V}

/-- The unique map from a relative test scheme to the base. -/
def baseMap (T : Over S) : T ⟶ Over.mk (𝟙 S) :=
  Over.homMk T.hom (by simp)

theorem baseMap_unique {T : Over S} (b : T ⟶ Over.mk (𝟙 S)) : b = baseMap T := by
  apply Over.OverMorphism.ext
  change b.left = T.hom
  simpa using b.w

theorem comp_baseMap {T W : Over S} (f : W ⟶ T) : f ≫ baseMap T = baseMap W :=
  baseMap_unique _

/-- A cocycle parametrized by the base is an actual morphism from the acting group. -/
def baseHom (c : a.Cocycle (Over.mk (𝟙 S))) : H.X ⟶ V.X :=
  lift (baseMap H.X) (𝟙 H.X) ≫ c.hom

theorem eval_eq_comp_baseHom (c : a.Cocycle (Over.mk (𝟙 S)))
    {T : Over S} (b : T ⟶ Over.mk (𝟙 S)) (h : T ⟶ H.X) :
    c.eval b h = h ≫ c.baseHom := by
  simp only [baseHom, eval, ← Category.assoc, comp_lift, comp_baseMap, Category.comp_id]
  rw [baseMap_unique b]

variable {R : CommRingCat.{u}} {H V : GroupScheme (Spec R)}
    {a : AutomorphicAction H V}

/-- Evaluation of a base cocycle on an actual affine test point. -/
def affineEval (c : a.Cocycle (Over.mk (𝟙 (Spec R))))
    {A : Type u} [CommRing A] [Algebra R A] (h : Lie.AffinePoints H A) :
    Lie.AffinePoints V A := c.eval (baseMap _) h

theorem affineEval_naturality (c : a.Cocycle (Over.mk (𝟙 (Spec R))))
    {A B : Type u} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]
    (f : A →ₐ[R] B) (h : Lie.AffinePoints H A) :
    Lie.affineMap V f (c.affineEval h) = c.affineEval (Lie.affineMap H f h) := by
  simp only [affineEval, Lie.affineMap_apply, eval_eq_comp_baseHom, Category.assoc]

theorem affineEval_mul (c : a.Cocycle (Over.mk (𝟙 (Spec R))))
    {A : Type u} [CommRing A] [Algebra R A] (h h' : Lie.AffinePoints H A) :
    c.affineEval (h * h') = c.affineEval h * a.act h (c.affineEval h') :=
  c.eval_mul _ h h'

theorem affineEval_ext [IsAffine H.X.left]
    {c d : a.Cocycle (Over.mk (𝟙 (Spec R)))}
    (h : ∀ (A : CommAlgCat.{u} R) (t : H.affinePoints A),
      c.affineEval t = d.affineEval t) : c = d := by
  have hi : (algSpec R).essImage H.X := by
    rw [essImage_algSpec]
    infer_instance
  have hh : c.baseHom = d.baseHom := by
    apply (cancel_epi hi.getIso.hom).1
    simpa only [affineEval, eval_eq_comp_baseHom] using h hi.witness.unop hi.getIso.hom
  apply eval_ext
  intro T b t
  rw [eval_eq_comp_baseHom, eval_eq_comp_baseHom, hh]

end AutomorphicAction.Cocycle

namespace AutomorphicAction

variable {k : Type u} [Field k]
    {H V : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom V.X.hom] (a : AutomorphicAction H V) {d : ℕ}
    (c : Lie.FiniteCoordinates V d)

/-- Coefficients commute with the extension of an actual finite-coordinate action. -/
theorem coordinateAction_coeff {A : Type u} [CommRing A] [Algebra k A]
    {M : Type u} [AddCommMonoid M] (h : Lie.AffinePoints H A)
    (x : Fin d → AddMonoidAlgebra A M) (m : M) :
    (fun j => (a.coordinateAction c (CommAlgCat.of k (AddMonoidAlgebra A M))
      (Lie.affineMap H (IsScalarTower.toAlgHom k A (AddMonoidAlgebra A M)) h) x j).coeff m) =
      a.coordinateAction c (CommAlgCat.of k A) h (fun j => (x j).coeff m) := by
  classical
  let f : CommAlgCat.of k A ⟶ CommAlgCat.of k (AddMonoidAlgebra A M) :=
    CommAlgCat.ofHom (IsScalarTower.toAlgHom k A (AddMonoidAlgebra A M))
  have hm := a.coordinateMatrix_naturality c f h
  rw [← a.coordinateMatrix_mulVec, ← a.coordinateMatrix_mulVec]
  funext j
  change ((∑ l, (a.coordinateMatrix c _ (H.affinePointMap f h)) j l * x l).coeff m) = _
  rw [hm]
  simp only [Matrix.GeneralLinearGroup.map_apply]
  change ((∑ l, AddMonoidAlgebra.single 0 ((a.coordinateMatrix c _ h) j l) * x l).coeff m) = _
  simp only [AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
    AddMonoidAlgebra.coeff_single_zero_mul, Matrix.mulVec, dotProduct]

end AutomorphicAction

namespace Lie

/-- The affine self-algebra represents the base test scheme. -/
def affineSelfTestIso (R : CommRingCat.{u}) :
    (algSpec R).obj (op (CommAlgCat.of R R)) ≅ Over.mk (𝟙 (Spec R)) :=
  Over.isoMk (Iso.refl _) (by
    change 𝟙 _ ≫ 𝟙 _ = Spec.map (𝟙 R)
    simp)

/-- The affine coefficient inclusion is the structure map to the base. -/
theorem baseMap_comp_affineSelfTestIso_inv (R : CommRingCat.{u})
    (A : Type u) [CommRing A] [Algebra R A] :
    AutomorphicAction.Cocycle.baseMap
        ((algSpec R).obj (op (CommAlgCat.of R A))) ≫ (affineSelfTestIso R).inv =
      (algSpec R).map (CommAlgCat.ofHom (Algebra.ofId R A)).op := by
  apply Over.OverMorphism.ext
  change (Spec.map _) ≫ 𝟙 _ = Spec.map _
  exact Category.comp_id _

end Lie

namespace splitTorus

open RelativeRoot

variable {k : Type u} [Field k] (I : Type u) [Fintype I] [DecidableEq I]
    {V : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom V.X.hom]
    (a : AutomorphicAction (splitTorus (Spec (CommRingCat.of k)) I) V)
    {d : ℕ}
    (e : ∀ T : Over (Spec (CommRingCat.of k)),
      (T ⟶ V.X) ≃* Multiplicative (Fin d → Γ(T.left, ⊤)))
    (he : IsLinearVectorCoordinates a e)
    (c : a.Cocycle (Over.mk (𝟙 (Spec (CommRingCat.of k)))))

/-- The coordinate vector of an actual cocycle on an affine test. -/
def cocycleCoordinates {A : Type u} [CommRing A] [Algebra k A]
    (t : Lie.AffinePoints (splitTorus (Spec (CommRingCat.of k)) I) A) : Fin d → A :=
  (vectorAffineCoordinates e A (c.affineEval t)).toAdd

omit [DecidableEq I] [IsAffineHom V.X.hom] in
include he in
/-- Cocycle coordinates commute with extension of coefficients. -/
theorem cocycleCoordinates_naturality
    {A B : Type u} [CommRing A] [Algebra k A] [CommRing B] [Algebra k B]
    (f : A →ₐ[k] B) (t : Lie.AffinePoints (splitTorus (Spec (CommRingCat.of k)) I) A) :
    cocycleCoordinates I a e c (Lie.affineMap _ f t) =
      fun j => f (cocycleCoordinates I a e c t j) := by
  simp only [cocycleCoordinates, ← c.affineEval_naturality,
    he.1.vectorAffineCoordinates_naturality]

omit [DecidableEq I] in
include he in
/-- The actual cocycle equation in finite vector coordinates. -/
theorem cocycleCoordinates_mul {A : Type u} [CommRing A] [Algebra k A]
    (t s : Lie.AffinePoints (splitTorus (Spec (CommRingCat.of k)) I) A) :
    cocycleCoordinates I a e c (t * s) = cocycleCoordinates I a e c t +
      a.coordinateAction (finiteLieCoordinatesOfVector e he.1) (CommAlgCat.of k A) t
        (cocycleCoordinates I a e c s) := by
  rw [he.coordinateAction_eq]
  simp only [cocycleCoordinates, c.affineEval_mul, map_mul, toAdd_mul,
    ofAdd_toAdd, MulEquiv.symm_apply_apply]

/-- The constant Laurent coefficient of the cocycle at the universal torus point. -/
def cocycleConstant : Fin d → k :=
  fun j => (cocycleCoordinates I a e c (universalPoint (R := CommRingCat.of k) I) j).coeff 0

omit [IsAffineHom V.X.hom] in
include he in
/-- Translation preserves the constant Laurent coefficient of the cocycle. -/
theorem cocycleCoordinates_translated_constant
    {A : Type u} [CommRing A] [Algebra k A] (t : I → Aˣ) :
    (fun j => (cocycleCoordinates I a e c
      (Lie.affineMap _ (translatedEvaluation (R := CommRingCat.of k) I t)
        (universalPoint (R := CommRingCat.of k) I)) j).coeff 0) =
      fun j => algebraMap k A (cocycleConstant I a e c j) := by
  rw [cocycleCoordinates_naturality I a e he]
  funext j
  change ((translatedEvaluation (R := CommRingCat.of k) I t)
    (cocycleCoordinates I a e c (universalPoint (R := CommRingCat.of k) I) j)).coeff 0 = _
  rw [coeff_translatedEvaluation]
  simp [cocycleConstant, exponentValue]

include he in
/-- The constant Laurent coefficient gives the coboundary formula on every affine test. -/
theorem cocycleCoordinates_eq_constant_sub_action
    {A : Type u} [CommRing A] [Algebra k A]
    (t : Lie.AffinePoints (splitTorus (Spec (CommRingCat.of k)) I) A) :
    cocycleCoordinates I a e c t =
      (fun j => algebraMap k A (cocycleConstant I a e c j)) -
        a.coordinateAction (finiteLieCoordinatesOfVector e he.1) (CommAlgCat.of k A) t
          (fun j => algebraMap k A (cocycleConstant I a e c j)) := by
  let f : A →ₐ[k] AddMonoidAlgebra A (I → ℤ) :=
    IsScalarTower.toAlgHom k A (AddMonoidAlgebra A (I → ℤ))
  let g : AddMonoidAlgebra k (I → ℤ) →ₐ[k] AddMonoidAlgebra A (I → ℤ) :=
    AddMonoidAlgebra.mapAlgHom (I → ℤ) (Algebra.ofId k A)
  let s := universalPoint (R := CommRingCat.of k) I
  have ht := cocycleCoordinates_translated_constant I a e he c (algebraPointsEquiv I A t)
  rw [universalPoint_translatedEvaluation, MulEquiv.symm_apply_apply] at ht
  have hfirst : (fun j => (cocycleCoordinates I a e c (Lie.affineMap _ f t) j).coeff 0) =
      cocycleCoordinates I a e c t := by
    rw [cocycleCoordinates_naturality I a e he]
    funext j
    change (AddMonoidAlgebra.single 0 (cocycleCoordinates I a e c t j)).coeff 0 = _
    simp
  have hsecond :
      (fun j => (cocycleCoordinates I a e c (Lie.affineMap _ g s) j).coeff 0) =
        fun j => algebraMap k A (cocycleConstant I a e c j) := by
    rw [cocycleCoordinates_naturality I a e he]
    funext j
    exact AddMonoidAlgebra.coeff_mapAlgHom (Algebra.ofId k A) _ 0
  have hmul := congrArg
    (fun x : Fin d → AddMonoidAlgebra A (I → ℤ) => fun j => (x j).coeff 0)
    (cocycleCoordinates_mul I a e he c (Lie.affineMap _ f t) (Lie.affineMap _ g s))
  change _ = (fun j => (cocycleCoordinates I a e c (Lie.affineMap _ f t) j).coeff 0) +
    (fun j => (a.coordinateAction (finiteLieCoordinatesOfVector e he.1)
      (CommAlgCat.of k (AddMonoidAlgebra A (I → ℤ))) (Lie.affineMap _ f t)
        (cocycleCoordinates I a e c (Lie.affineMap _ g s)) j).coeff 0) at hmul
  rw [ht, hfirst, a.coordinateAction_coeff, hsecond] at hmul
  exact (eq_sub_iff_add_eq).2 hmul.symm

/-- The actual rational point given by the constant Laurent coefficient. -/
def cocycleConjugator : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ V.X :=
  (Lie.affineSelfTestIso (CommRingCat.of k)).inv ≫
    (vectorAffineCoordinates e k).symm (Multiplicative.ofAdd (cocycleConstant I a e c))

omit [IsAffineHom V.X.hom] in
include he in
/-- The rational conjugator restricts to the scalar extension of its constant vector. -/
theorem cocycleConjugator_coordinates {A : Type u} [CommRing A] [Algebra k A] :
    (vectorAffineCoordinates e A
      (AutomorphicAction.Cocycle.baseMap _ ≫ cocycleConjugator I a e c)).toAdd =
      fun j => algebraMap k A (cocycleConstant I a e c j) := by
  rw [cocycleConjugator, ← Category.assoc, Lie.baseMap_comp_affineSelfTestIso_inv]
  change (vectorAffineCoordinates e A (Lie.affineMap V (Algebra.ofId k A) _)).toAdd = _
  rw [he.1.vectorAffineCoordinates_naturality, MulEquiv.apply_symm_apply]
  rfl

include he in
/-- Every actual cocycle for a split torus acting linearly on a vector group is
an actual rational coboundary. -/
theorem cocycle_eq_coboundary : c = a.coboundary (cocycleConjugator I a e c) := by
  have : MorphismProperty.IsStableUnderComposition
      (@IsAffineHom : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsMultiplicative.toIsStableUnderComposition
  have : MorphismProperty.ContainsIdentities (@IsAffineHom : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsMultiplicative.toContainsIdentities
  have : MorphismProperty.RespectsIso (@IsAffineHom : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have : IsAffineHom Gm.overSpecZ.{u}.hom := by
    change IsAffineHom
      (Spec.map (CommRingCat.ofHom (LaurentPolynomial.C (R := ULift.{u} ℤ))))
    infer_instance
  have hgm : IsAffineHom (Gm (Spec (CommRingCat.of k))).X.hom := by
    change IsAffineHom (CategoryTheory.Limits.pullback.snd Gm.overSpecZ.hom _)
    infer_instance
  have : IsAffineHom (splitTorus (Spec (CommRingCat.of k)) I).X.hom :=
    prop_pi_hom (@IsAffineHom : MorphismProperty Scheme.{u}) (fun _ : I =>
      (Gm (Spec (CommRingCat.of k))).toGrp) (fun _ => hgm)
  have : IsAffine (splitTorus (Spec (CommRingCat.of k)) I).X.left :=
    isAffine_of_isAffineHom (splitTorus (Spec (CommRingCat.of k)) I).X.hom
  apply AutomorphicAction.Cocycle.affineEval_ext
  intro A t
  apply (vectorAffineCoordinates e A).injective
  apply Multiplicative.toAdd.injective
  have hq := cocycleConjugator_coordinates I a e he c (A := A)
  have hc := cocycleCoordinates_eq_constant_sub_action I a e he c t
  rw [he.coordinateAction_eq, ← hq] at hc
  simp only [ofAdd_toAdd, MulEquiv.symm_apply_apply] at hc
  simpa only [cocycleCoordinates, AutomorphicAction.Cocycle.affineEval,
    AutomorphicAction.eval_coboundary, a.act_inv, map_mul, map_inv, toAdd_mul,
    toAdd_inv, hq, sub_eq_add_neg] using hc

end splitTorus

end Langlands.GroupScheme
