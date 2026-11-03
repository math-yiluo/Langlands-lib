import Langlands.AlgebraicGeometry.ClosedFactorizationLocusStatement
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Mathlib.AlgebraicGeometry.Pullbacks

/-! # Base change of full-product factorization -/

noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.ClosedFactorizationBaseChange

variable {S S' : Scheme.{u}} (f : S' ⟶ S)

/-- The underlying pullback associativity isomorphism. -/
def schemeProductIso (X : Over S) (T : Over S') :
    pullback (pullback.snd X.hom f) T.hom ≅ pullback X.hom (T.hom ≫ f) where
  hom := pullback.lift
    (pullback.fst _ _ ≫ pullback.fst X.hom f) (pullback.snd _ _)
    (by rw [Category.assoc, pullback.condition, ← Category.assoc, pullback.condition, Category.assoc])
  inv := pullback.lift
    (pullback.lift (pullback.fst X.hom (T.hom ≫ f))
      (pullback.snd X.hom (T.hom ≫ f) ≫ T.hom) (by
        rw [Category.assoc, pullback.condition]))
    (pullback.snd X.hom (T.hom ≫ f)) (by rw [pullback.lift_snd])
  hom_inv_id := by
    apply pullback.hom_ext
    · apply pullback.hom_ext
      · simp only [Category.assoc, pullback.lift_fst, Category.id_comp]
      · simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.lift_snd_assoc,
          Category.id_comp, pullback.condition]
    · simp only [Category.assoc, pullback.lift_snd, Category.id_comp]
  inv_hom_id := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, Category.id_comp]
    · simp only [Category.assoc, pullback.lift_snd, Category.id_comp]

/-- Forgetting the changed base commutes with taking a product with a
base-changed first factor. -/
def productIso (X : Over S) (T : Over S') :
    (Over.map f).obj ((Over.pullback f).obj X ⊗ T) ≅
      X ⊗ (Over.map f).obj T :=
  Over.isoMk (schemeProductIso f X T) (by
    dsimp [schemeProductIso]
    simp only [Category.assoc, pullback.condition,
      pullback.lift_snd_assoc])

@[reassoc (attr := simp)]
theorem productIso_hom_fst (X : Over S) (T : Over S') :
    (productIso f X T).hom.left ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ pullback.fst X.hom f := by
  exact pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem productIso_hom_snd (X : Over S) (T : Over S') :
    (productIso f X T).hom.left ≫ pullback.snd _ _ = pullback.snd _ _ := by
  exact pullback.lift_snd _ _ _

/-- The closed immersion after base change, placed in the product of the
base-changed schemes. -/
def baseChangedMap {X Y D : Over S} (d : D ⟶ X ⊗ Y) :
    (Over.pullback f).obj D ⟶ (Over.pullback f).obj X ⊗ (Over.pullback f).obj Y :=
  (Over.pullback f).map d ≫ (Functor.Monoidal.μIso (Over.pullback f) X Y).inv

instance {X Y D : Over S} (d : D ⟶ X ⊗ Y) [IsClosedImmersion d.left] :
    IsClosedImmersion (baseChangedMap f d).left := by
  have : IsClosedImmersion ((Over.pullback f).map d).left :=
    MorphismProperty.overPullbackMap (P := @IsClosedImmersion) f d inferInstance
  have : IsIso (Functor.Monoidal.μIso (Over.pullback f) X Y).inv.left :=
    inferInstanceAs (IsIso ((Over.forget S').map
      (Functor.Monoidal.μIso (Over.pullback f) X Y).inv))
  dsimp only [baseChangedMap, Over.comp_left]
  infer_instance

/-- An arrow to a base-changed target, considered over the original base. -/
def originalMap {Y : Over S} {T : Over S'} (t : T ⟶ (Over.pullback f).obj Y) :
    (Over.map f).obj T ⟶ Y :=
  ((Over.mapPullbackAdj f).homEquiv T Y).symm t

@[simp]
theorem originalMap_left {Y : Over S} {T : Over S'}
    (t : T ⟶ (Over.pullback f).obj Y) :
    (originalMap f t).left = t.left ≫ pullback.fst Y.hom f := rfl

@[reassoc]
theorem originalMap_comp {A : Over S'} {D E : Over S}
    (q : A ⟶ (Over.pullback f).obj D) (d : D ⟶ E) :
    originalMap f (q ≫ (Over.pullback f).map d) = originalMap f q ≫ d :=
  (Over.mapPullbackAdj f).homEquiv_naturality_right_symm q d

@[reassoc (attr := simp)]
theorem tensorComparison_fst (X Y : Over S) :
    (Functor.Monoidal.μIso (Over.pullback f) X Y).hom.left ≫
      pullback.fst _ _ ≫ pullback.fst X.hom Y.hom =
        pullback.fst _ _ ≫ pullback.fst X.hom f :=
  Over.μ_pullback_left_fst_fst X Y

@[reassoc (attr := simp)]
theorem tensorComparison_snd (X Y : Over S) :
    (Functor.Monoidal.μIso (Over.pullback f) X Y).hom.left ≫
      pullback.fst _ _ ≫ pullback.snd X.hom Y.hom =
        pullback.snd _ _ ≫ pullback.fst Y.hom f :=
  Over.μ_pullback_left_fst_snd X Y

/-- The product comparison is compatible with the map specified by a test. -/
theorem originalMap_whisker {X Y : Over S} {T : Over S'}
    (t : T ⟶ (Over.pullback f).obj Y) :
    originalMap f (((Over.pullback f).obj X ◁ t) ≫
      (Functor.Monoidal.μIso (Over.pullback f) X Y).hom) =
        (productIso f X T).hom ≫ (X ◁ originalMap f t) := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · simp only [originalMap_left, Over.comp_left, Category.assoc,
      tensorComparison_fst, Over.whiskerLeft_left_fst_assoc,
      Over.whiskerLeft_left_fst, productIso_hom_fst]
  · simp only [originalMap_left, Over.comp_left, Category.assoc,
      tensorComparison_snd, Over.whiskerLeft_left_snd_assoc,
      Over.whiskerLeft_left_snd, productIso_hom_snd_assoc]

/-- Full-product factorization over the changed base is equivalent to the
original factorization property on the corresponding test. -/
theorem factors_iff {X Y D : Over S} (d : D ⟶ X ⊗ Y)
    {T : Over S'} (t : T ⟶ (Over.pullback f).obj Y) :
    (∃ q : (Over.pullback f).obj X ⊗ T ⟶ (Over.pullback f).obj D,
      q ≫ baseChangedMap f d = ((Over.pullback f).obj X ◁ t)) ↔
    ∃ q : X ⊗ (Over.map f).obj T ⟶ D, q ≫ d = (X ◁ originalMap f t) := by
  let e := productIso f X T
  let μ := Functor.Monoidal.μIso (Over.pullback f) X Y
  constructor
  · rintro ⟨q, hq⟩
    have hq' : q ≫ (Over.pullback f).map d =
        ((Over.pullback f).obj X ◁ t) ≫ μ.hom := by
      calc
        q ≫ (Over.pullback f).map d = (q ≫ baseChangedMap f d) ≫ μ.hom := by
          simp [baseChangedMap, μ]
        _ = _ := by rw [hq]
    have h := congrArg (originalMap f) hq'
    rw [originalMap_comp, originalMap_whisker] at h
    refine ⟨e.inv ≫ originalMap f q, ?_⟩
    simp only [Category.assoc, h, e, Iso.inv_hom_id_assoc]
  · rintro ⟨q, hq⟩
    let q' := (Over.mapPullbackAdj f).homEquiv _ _ (e.hom ≫ q)
    have hq' : q' ≫ (Over.pullback f).map d =
        ((Over.pullback f).obj X ◁ t) ≫ μ.hom := by
      apply ((Over.mapPullbackAdj f).homEquiv _ _).symm.injective
      change originalMap f (q' ≫ (Over.pullback f).map d) =
        originalMap f (((Over.pullback f).obj X ◁ t) ≫
          (Functor.Monoidal.μIso (Over.pullback f) X Y).hom)
      rw [originalMap_comp, originalMap_whisker]
      change ((Over.mapPullbackAdj f).homEquiv _ _).symm
        ((Over.mapPullbackAdj f).homEquiv _ _ (e.hom ≫ q)) ≫ d = _
      simp only [Equiv.symm_apply_apply, Category.assoc, hq, e]
    refine ⟨q', ?_⟩
    change q' ≫ (Over.pullback f).map d ≫ μ.inv = _
    rw [← Category.assoc, hq']
    simp

end Langlands.AlgebraicGeometry.ClosedFactorizationBaseChange
