import Langlands.GroupScheme.Rational.CoordinateAction
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-! # Actual pointed affine schemes and equivariant coordinate pullback -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory Opposite AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.PointedCoordinateWeights

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}

/-- An actual scheme action with a fixed rational point. No group structure on
the target scheme is required. -/
structure PointedAction (S : CommGroupScheme (Spec (CommRingCat.of k)))
    (V : Over (Spec (CommRingCat.of k))) where
  hom : S.X ⊗ V ⟶ V
  origin : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ V
  one_left : ∀ {T : Over (Spec (CommRingCat.of k))} (v : T ⟶ V),
    lift (1 : T ⟶ S.X) v ≫ hom = v
  mul_left : ∀ {T : Over (Spec (CommRingCat.of k))} (s t : T ⟶ S.X) (v : T ⟶ V),
    lift (s * t) v ≫ hom = lift s (lift t v ≫ hom) ≫ hom
  origin_fixed : ∀ {T : Over (Spec (CommRingCat.of k))} (s : T ⟶ S.X),
    lift s (toUnit T ≫ origin) ≫ hom = toUnit T ≫ origin

namespace PointedAction

variable {V : Over (Spec (CommRingCat.of k))} (a : PointedAction S V)

/-- The action on all scheme-valued points is induced by the actual morphism. -/
def act {T : Over (Spec (CommRingCat.of k))} (s : T ⟶ S.X) (v : T ⟶ V) : T ⟶ V :=
  lift s v ≫ a.hom

@[simp] theorem act_one_left {T : Over (Spec (CommRingCat.of k))} (v : T ⟶ V) :
    a.act 1 v = v := a.one_left v

theorem act_mul_left {T : Over (Spec (CommRingCat.of k))} (s t : T ⟶ S.X) (v : T ⟶ V) :
    a.act (s * t) v = a.act s (a.act t v) := a.mul_left s t v

@[simp] theorem act_origin {T : Over (Spec (CommRingCat.of k))} (s : T ⟶ S.X) :
    a.act s (toUnit T ≫ a.origin) = toUnit T ≫ a.origin := a.origin_fixed s

theorem naturality {T T' : Over (Spec (CommRingCat.of k))} (f : T' ⟶ T)
    (s : T ⟶ S.X) (v : T ⟶ V) :
    f ≫ a.act s v = a.act (f ≫ s) (f ≫ v) := by
  unfold act
  rw [← Category.assoc, comp_lift]

variable {G : GroupScheme (Spec (CommRingCat.of k))}

/-- Stability of the actual image on all tests, without requiring it to be a subgroup. -/
def IsStableInclusion (b : AutomorphicAction S.toGrp G) (i : V ⟶ G.X) : Prop :=
  ∀ (T : Over (Spec (CommRingCat.of k))) (s : T ⟶ S.X) (v : T ⟶ V),
    ∃ w : T ⟶ V, w ≫ i = b.act s (v ≫ i)

/-- Restrict the actual action to a stable pointed subscheme using its
monomorphic inclusion. This construction does not impose a group law on V. -/
def ofStableInclusion (b : AutomorphicAction S.toGrp G) (i : V ⟶ G.X) [Mono i]
    (e : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ V) (he : e ≫ i = η[G.X])
    (hstable : IsStableInclusion b i) : PointedAction S V := by
  let h : S.X ⊗ V ⟶ V := Classical.choose (hstable _ (fst _ _) (snd _ _))
  have hh : h ≫ i = b.act (fst _ _) (snd _ _ ≫ i) :=
    Classical.choose_spec (hstable _ (fst _ _) (snd _ _))
  have hact {T : Over (Spec (CommRingCat.of k))} (s : T ⟶ S.X) (v : T ⟶ V) :
      (lift s v ≫ h) ≫ i = b.act s (v ≫ i) := by
    rw [Category.assoc, hh, b.naturality, lift_fst, lift_snd_assoc]
  exact
    { hom := h
      origin := e
      one_left := fun v => by
        apply (cancel_mono i).1
        rw [hact, b.act_one_left]
      mul_left := fun s t v => by
        apply (cancel_mono i).1
        rw [hact, hact, hact, b.act_mul_left]
      origin_fixed := fun s => by
        apply (cancel_mono i).1
        rw [hact, Category.assoc, he, ← Hom.one_def, b.act_one] }

theorem ofStableInclusion_act_comp (b : AutomorphicAction S.toGrp G)
    (i : V ⟶ G.X) [Mono i]
    (e : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ V) (he : e ≫ i = η[G.X])
    (hstable : IsStableInclusion b i)
    {T : Over (Spec (CommRingCat.of k))} (s : T ⟶ S.X) (v : T ⟶ V) :
    (ofStableInclusion b i e he hstable).act s v ≫ i = b.act s (v ≫ i) := by
  change (lift s v ≫ Classical.choose (hstable _ (fst _ _) (snd _ _))) ≫ i = _
  rw [Category.assoc, Classical.choose_spec (hstable _ (fst _ _) (snd _ _)),
    b.naturality, lift_fst, lift_snd_assoc]

/-- Forget the group structure on the target of an existing automorphic action. -/
def ofGroup {G : GroupScheme (Spec (CommRingCat.of k))}
    (b : AutomorphicAction S.toGrp G) : PointedAction S G.X where
  hom := b.hom
  origin := η[G.X]
  one_left := b.one_left
  mul_left := b.mul_left
  origin_fixed s := by
    simpa only [← Hom.one_def, AutomorphicAction.act] using b.act_one s

@[simp] theorem ofGroup_act {G : GroupScheme (Spec (CommRingCat.of k))}
    (b : AutomorphicAction S.toGrp G) {T : Over (Spec (CommRingCat.of k))}
    (s : T ⟶ S.X) (g : T ⟶ G.X) : (ofGroup b).act s g = b.act s g := rfl

end PointedAction

variable {V W Z : Over (Spec (CommRingCat.of k))}

/-- Coordinates of an actual affine scheme over the field. -/
def coordinatePresentation (V : Over (Spec (CommRingCat.of k))) [IsAffineHom V.hom] :
    Σ C : CommAlgCat (CommRingCat.of k), (algSpec (CommRingCat.of k)).obj (op C) ≅ V :=
  Classical.choice (by
    have h : IsAffine V.left := isAffine_of_isAffineHom V.hom
    obtain ⟨C, ⟨e⟩⟩ := (essImage_algSpec (G := V)).mpr h
    exact ⟨⟨C.unop, e⟩⟩)

abbrev Coord (V : Over (Spec (CommRingCat.of k))) [IsAffineHom V.hom] :=
  (coordinatePresentation V).1

def coordinateIso (V : Over (Spec (CommRingCat.of k))) [IsAffineHom V.hom] :
    (algSpec (CommRingCat.of k)).obj (op (Coord V)) ≅ V :=
  (coordinatePresentation V).2

abbrev Points (V : Over (Spec (CommRingCat.of k))) (A : Type u) [CommRing A] [Algebra k A] :=
  (algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of (CommRingCat.of k) A)) ⟶ V

variable [IsAffineHom V.hom] [IsAffineHom W.hom] [IsAffineHom Z.hom]

/-- Actual affine points are the algebra maps in the chosen coordinates. -/
def pointCoordinates {A : Type u} [CommRing A] [Algebra k A] :
    Points V A ≃ (Coord V →ₐ[k] A) where
  toFun v := (algSpec.fullyFaithful.preimage (v ≫ (coordinateIso V).inv)).unop.hom
  invFun f := (algSpec (CommRingCat.of k)).map (CommAlgCat.ofHom f).op ≫ (coordinateIso V).hom
  left_inv v := by simp
  right_inv f := by
    change (algSpec.fullyFaithful.preimage
      ((algSpec (CommRingCat.of k)).map (CommAlgCat.ofHom f).op ≫
        (coordinateIso V).hom ≫ (coordinateIso V).inv)).unop.hom = f
    simp

def pointsMap {A B : Type u} [CommRing A] [Algebra k A] [CommRing B] [Algebra k B]
    (f : A →ₐ[k] B) (v : Points V A) : Points V B :=
  (algSpec (CommRingCat.of k)).map (CommAlgCat.ofHom f).op ≫ v

@[simp] theorem pointCoordinates_naturality
    {A B : Type u} [CommRing A] [Algebra k A] [CommRing B] [Algebra k B]
    (f : A →ₐ[k] B) (v : Points V A) :
    pointCoordinates (pointsMap f v) = f.comp (pointCoordinates v) := by
  have h : CommAlgCat.ofHom (R := CommRingCat.of k) (pointCoordinates (pointsMap f v)) =
      CommAlgCat.ofHom (R := CommRingCat.of k) (f.comp (pointCoordinates v)) := by
    apply Quiver.Hom.op_inj
    apply (algSpec.fullyFaithful (R := CommRingCat.of k)).map_injective
    simp [pointCoordinates, pointsMap]
  exact congrArg CommAlgCat.Hom.hom h

def universalPoint (V : Over (Spec (CommRingCat.of k))) [IsAffineHom V.hom] :
    Points V (Coord V) := pointCoordinates.symm (AlgHom.id _ _)

@[simp] theorem coordinates_universalPoint :
    pointCoordinates (universalPoint V) = AlgHom.id k (Coord V) :=
  pointCoordinates.apply_symm_apply _

/-- The actual coordinate pullback of a morphism of affine schemes. -/
def pullback (f : V ⟶ W) : Coord W →ₐ[k] Coord V :=
  pointCoordinates (universalPoint V ≫ f)

@[simp] theorem coordinates_comp {A : Type u} [CommRing A] [Algebra k A]
    (f : V ⟶ W) (v : Points V A) :
    pointCoordinates (v ≫ f) = (pointCoordinates v).comp (pullback f) := by
  have hv : pointsMap (pointCoordinates v) (universalPoint V) = v := by
    apply pointCoordinates.injective
    rw [pointCoordinates_naturality, coordinates_universalPoint, AlgHom.comp_id]
  change _ = (pointCoordinates v).comp (pointCoordinates (universalPoint V ≫ f))
  rw [← pointCoordinates_naturality]
  exact congrArg pointCoordinates (congrArg (· ≫ f) hv.symm)

@[simp] theorem pullback_id : pullback (𝟙 V) = AlgHom.id k (Coord V) := by
  simpa only [pullback, Category.comp_id] using (coordinates_universalPoint (V := V))

@[simp] theorem pullback_comp (f : V ⟶ W) (g : W ⟶ Z) :
    pullback (f ≫ g) = (pullback f).comp (pullback g) := by
  rw [pullback, ← Category.assoc, coordinates_comp]
  rfl

/-- Evaluation at the specified fixed point of the actual scheme. -/
def coordinateOrigin (a : PointedAction S V) : Coord V →ₐ[k] k :=
  pointCoordinates (toUnit _ ≫ a.origin : Points V k)

theorem pointCoordinates_origin (a : PointedAction S V)
    {A : Type u} [CommRing A] [Algebra k A] :
    pointCoordinates (toUnit _ ≫ a.origin : Points V A) =
      (Algebra.ofId k A).comp (coordinateOrigin a) := by
  rw [coordinateOrigin, ← pointCoordinates_naturality]
  simp only [pointsMap, comp_toUnit_assoc]

/-- Evaluation of base-changed actual coordinates. -/
def evaluate {A : Type u} [CommRing A] [Algebra k A] (v : Points V A) :
    A ⊗[k] Coord V →ₐ[A] A :=
  AlgHom.liftEquiv k A (Coord V) A (pointCoordinates v)

/-- The actual action applied to the universal point over A tensor O(V). -/
def actionCoordinates (a : PointedAction S V)
    {A : Type u} [CommRing A] [Algebra k A] (s : Lie.AffinePoints S.toGrp A) :
    Coord V →ₐ[k] A ⊗[k] Coord V :=
  pointCoordinates (a.act (Lie.affineMap S.toGrp Algebra.TensorProduct.includeLeft s)
    (pointCoordinates.symm Algebra.TensorProduct.includeRight))

/-- The actual A-algebra action on A tensor O(V). -/
def actionPullback (a : PointedAction S V)
    {A : Type u} [CommRing A] [Algebra k A] (s : Lie.AffinePoints S.toGrp A) :
    A ⊗[k] Coord V →ₐ[A] A ⊗[k] Coord V :=
  AlgHom.liftEquiv k A (Coord V) (A ⊗[k] Coord V) (actionCoordinates a s)

@[simp] theorem actionPullback_tmul (a : PointedAction S V)
    {A : Type u} [CommRing A] [Algebra k A] (s : Lie.AffinePoints S.toGrp A)
    (c : A) (z : Coord V) :
    actionPullback a s (c ⊗ₜ[k] z) = c • actionCoordinates a s z := rfl

/-- CGP's convention for actual pointed schemes after every algebra change. -/
theorem evaluate_actionCoordinates (a : PointedAction S V)
    {A : Type u} [CommRing A] [Algebra k A] (s : Lie.AffinePoints S.toGrp A)
    (v : Points V A) :
    ((evaluate v).restrictScalars k).comp (actionCoordinates a s) =
      pointCoordinates (a.act s v) := by
  unfold actionCoordinates
  rw [← pointCoordinates_naturality, pointsMap, a.naturality]
  have hs : Lie.affineMap S.toGrp ((evaluate v).restrictScalars k)
      (Lie.affineMap S.toGrp Algebra.TensorProduct.includeLeft s) = s := by
    rw [← Lie.affineMap_comp]
    have he : ((evaluate v).restrictScalars k).comp
        (Algebra.TensorProduct.includeLeft : A →ₐ[k] A ⊗[k] Coord V) = AlgHom.id k A := by
      ext c
      simp [evaluate]
    rw [he, Lie.affineMap_id]
  have hv : pointsMap ((evaluate v).restrictScalars k)
      (pointCoordinates.symm Algebra.TensorProduct.includeRight : Points V (A ⊗[k] Coord V)) =
      v := by
    apply pointCoordinates.injective
    rw [pointCoordinates_naturality, Equiv.apply_symm_apply]
    exact (AlgHom.liftEquiv k A (Coord V) A).symm_apply_apply _
  change pointCoordinates (a.act
    (Lie.affineMap S.toGrp ((evaluate v).restrictScalars k)
      (Lie.affineMap S.toGrp Algebra.TensorProduct.includeLeft s))
    (pointsMap ((evaluate v).restrictScalars k)
      (pointCoordinates.symm Algebra.TensorProduct.includeRight))) = _
  rw [hs, hv]

theorem evaluate_actionPullback (a : PointedAction S V)
    {A : Type u} [CommRing A] [Algebra k A] (s : Lie.AffinePoints S.toGrp A)
    (v : Points V A) (c : A) (z : Coord V) :
    evaluate v (actionPullback a s (c ⊗ₜ[k] z)) =
      c * pointCoordinates (a.act s v) z := by
  change evaluate v (c • actionCoordinates a s z) = _
  rw [map_smul]
  exact congrArg (c * ·) (DFunLike.congr_fun (evaluate_actionCoordinates a s v) z)

/-- The coordinate action fixes the coefficient factor and extended acting points. -/
theorem actionPullback_actingPoint (a : PointedAction S V)
    {A : Type u} [CommRing A] [Algebra k A] (s t : Lie.AffinePoints S.toGrp A) :
    Lie.affineMap S.toGrp ((actionPullback a t).restrictScalars k)
      (Lie.affineMap S.toGrp (Algebra.TensorProduct.includeLeft :
        A →ₐ[k] A ⊗[k] Coord V) s) =
      Lie.affineMap S.toGrp Algebra.TensorProduct.includeLeft s := by
  rw [← Lie.affineMap_comp]
  have he : ((actionPullback a t).restrictScalars k).comp
      (Algebra.TensorProduct.includeLeft : A →ₐ[k] A ⊗[k] Coord V) =
      Algebra.TensorProduct.includeLeft := by
    ext c
    simp [actionPullback, Algebra.TensorProduct.includeLeft_apply,
      Algebra.TensorProduct.one_def, TensorProduct.smul_tmul', smul_eq_mul]
  rw [he]

/-- The universal target point is sent to its actual translate. -/
theorem actionPullback_universalPoint (a : PointedAction S V)
    {A : Type u} [CommRing A] [Algebra k A] (s : Lie.AffinePoints S.toGrp A) :
    pointsMap ((actionPullback a s).restrictScalars k)
      (pointCoordinates.symm Algebra.TensorProduct.includeRight :
        Points V (A ⊗[k] Coord V)) =
      a.act (Lie.affineMap S.toGrp Algebra.TensorProduct.includeLeft s)
        (pointCoordinates.symm Algebra.TensorProduct.includeRight) := by
  apply pointCoordinates.injective
  rw [pointCoordinates_naturality, Equiv.apply_symm_apply]
  exact (AlgHom.liftEquiv k A (Coord V) (A ⊗[k] Coord V)).symm_apply_apply _

@[simp] theorem actionPullback_coordinates (a : PointedAction S V)
    {A : Type u} [CommRing A] [Algebra k A] (s : Lie.AffinePoints S.toGrp A) :
    ((actionPullback a s).restrictScalars k).comp Algebra.TensorProduct.includeRight =
      actionCoordinates a s :=
  (AlgHom.liftEquiv k A (Coord V) (A ⊗[k] Coord V)).symm_apply_apply _

@[simp] theorem actionPullback_one (a : PointedAction S V)
    {A : Type u} [CommRing A] [Algebra k A] :
    actionPullback a (1 : Lie.AffinePoints S.toGrp A) = AlgHom.id A (A ⊗[k] Coord V) := by
  apply Algebra.TensorProduct.ext_ring
  ext z
  simp [actionPullback, actionCoordinates, Algebra.TensorProduct.includeRight_apply]

/-- The positive pullback convention reverses composition. -/
theorem actionPullback_mul (a : PointedAction S V)
    {A : Type u} [CommRing A] [Algebra k A] (s t : Lie.AffinePoints S.toGrp A) :
    actionPullback a (s * t) = (actionPullback a t).comp (actionPullback a s) := by
  apply Algebra.TensorProduct.ext_ring
  change ((actionPullback a (s * t)).restrictScalars k).comp
      Algebra.TensorProduct.includeRight =
    (((actionPullback a t).restrictScalars k).comp
      ((actionPullback a s).restrictScalars k)).comp Algebra.TensorProduct.includeRight
  rw [AlgHom.comp_assoc, actionPullback_coordinates, actionPullback_coordinates]
  unfold actionCoordinates
  rw [← pointCoordinates_naturality, pointsMap, a.naturality]
  change _ = pointCoordinates (a.act
    (Lie.affineMap S.toGrp ((actionPullback a t).restrictScalars k)
      (Lie.affineMap S.toGrp Algebra.TensorProduct.includeLeft s))
    (pointsMap ((actionPullback a t).restrictScalars k)
      (pointCoordinates.symm Algebra.TensorProduct.includeRight)))
  rw [actionPullback_actingPoint, actionPullback_universalPoint, map_mul, a.act_mul_left]

/-- Actual base-changed coordinate automorphisms for a pointed affine action. -/
def actionAut (a : PointedAction S V)
    {A : Type u} [CommRing A] [Algebra k A] (s : Lie.AffinePoints S.toGrp A) :
    A ⊗[k] Coord V ≃ₐ[A] A ⊗[k] Coord V :=
  AlgEquiv.ofAlgHom (actionPullback a s) (actionPullback a s⁻¹)
    (by rw [← actionPullback_mul, inv_mul_cancel, actionPullback_one])
    (by rw [← actionPullback_mul, mul_inv_cancel, actionPullback_one])

theorem action_preserves_origin (a : PointedAction S V)
    {A : Type u} [CommRing A] [Algebra k A] (s : Lie.AffinePoints S.toGrp A) :
    ((evaluate (toUnit _ ≫ a.origin : Points V A)).restrictScalars k).comp
      (actionCoordinates a s) = (Algebra.ofId k A).comp (coordinateOrigin a) := by
  rw [evaluate_actionCoordinates, a.act_origin, pointCoordinates_origin]

/-- The actual ideal of the distinguished rational point. -/
def augmentationIdeal (a : PointedAction S V) : Ideal (Coord V) :=
  RingHom.ker (coordinateOrigin a).toRingHom

/-- The same ideal regarded as a vector subspace. -/
def augmentation (a : PointedAction S V) : Submodule k (Coord V) :=
  LinearMap.ker (coordinateOrigin a).toLinearMap

@[simp] theorem mem_augmentation (a : PointedAction S V) {z : Coord V} :
    z ∈ augmentation a ↔ coordinateOrigin a z = 0 := Iff.rfl

/-- CGP's coordinate eigencondition on every coefficient algebra and every point. -/
def IsEigenfunction (a : PointedAction S V) (χ : characterLattice S) (z : Coord V) : Prop :=
  ∀ (A : Type u) [CommRing A] [Algebra k A] (s : Lie.AffinePoints S.toGrp A)
    (v : Points V A),
    pointCoordinates (a.act s v) z =
      (Lie.characterValue χ s : A) * pointCoordinates v z

def weightSpace (a : PointedAction S V) (χ : characterLattice S) : Submodule k (Coord V) where
  carrier := IsEigenfunction a χ
  zero_mem' := by intro A _ _ s v; simp
  add_mem' := by
    intro x y hx hy A _ _ s v
    simp only [map_add, hx A s v, hy A s v, mul_add]
  smul_mem' := by
    intro c z hz A _ _ s v
    change pointCoordinates (a.act s v) (c • z) = _
    rw [map_smul, map_smul, hz A s v]
    simp only [Algebra.smul_def, mul_left_comm]

def augmentationWeightSpace (a : PointedAction S V) (χ : characterLattice S) :
    Submodule k (augmentation a) := (weightSpace a χ).comap (augmentation a).subtype

/-- The support consists of weights of nonzero functions in the augmentation
ideal, without adding a zero character. -/
def support (a : PointedAction S V) : Set (characterLattice S) :=
  {χ | ∃ z : augmentation a, z ≠ 0 ∧ z ∈ augmentationWeightSpace a χ}

@[simp] theorem ofGroup_weightSpace {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] (b : AutomorphicAction S.toGrp G) (χ : characterLattice S) :
    weightSpace (PointedAction.ofGroup b) χ = CoordinateWeights.weightSpace b χ := rfl

@[simp] theorem ofGroup_augmentationIdeal {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] (b : AutomorphicAction S.toGrp G) :
    augmentationIdeal (PointedAction.ofGroup b) = CoordinateWeights.augmentationIdeal G := rfl

@[simp] theorem ofGroup_augmentation {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] (b : AutomorphicAction S.toGrp G) :
    augmentation (PointedAction.ofGroup b) = CoordinateWeights.augmentation G := rfl

@[simp] theorem ofGroup_support {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] (b : AutomorphicAction S.toGrp G) :
    support (PointedAction.ofGroup b) = CoordinateWeights.support b := rfl

/-- Equivariance and preservation of the distinguished rational point. -/
def IsPointedEquivariant (a : PointedAction S V) (b : PointedAction S W)
    (f : V ⟶ W) : Prop :=
  (∀ (T : Over (Spec (CommRingCat.of k))) (s : T ⟶ S.X) (v : T ⟶ V),
    a.act s v ≫ f = b.act s (v ≫ f)) ∧ a.origin ≫ f = b.origin

omit [IsAffineHom V.hom] in
theorem stableInclusion_isPointedEquivariant
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (b : AutomorphicAction S.toGrp G) (i : V ⟶ G.X) [Mono i]
    (e : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ V) (he : e ≫ i = η[G.X])
    (hstable : PointedAction.IsStableInclusion b i) :
    IsPointedEquivariant (PointedAction.ofStableInclusion b i e he hstable)
      (PointedAction.ofGroup b) i :=
  ⟨fun _ s v => PointedAction.ofStableInclusion_act_comp b i e he hstable s v, he⟩

omit [IsAffineHom V.hom] [IsAffineHom W.hom] in
/-- The inverse isomorphism preserves the actual action and its fixed point. -/
theorem isPointedEquivariant_inv (a : PointedAction S V) (b : PointedAction S W)
    (e : V ≅ W) (he : IsPointedEquivariant a b e.hom) :
    IsPointedEquivariant b a e.inv := by
  constructor
  · intro T s w
    apply (cancel_mono e.hom).1
    rw [Category.assoc, he.1 T s (w ≫ e.inv), Category.assoc,
      e.inv_hom_id, Category.comp_id, Category.comp_id]
  · apply (cancel_mono e.hom).1
    rw [Category.assoc, e.inv_hom_id, Category.comp_id, he.2]

theorem pullback_mem_weightSpace (a : PointedAction S V) (b : PointedAction S W)
    (f : V ⟶ W) (hf : IsPointedEquivariant a b f) (χ : characterLattice S)
    {z : Coord W} (hz : z ∈ weightSpace b χ) :
    pullback f z ∈ weightSpace a χ := by
  intro A _ _ s v
  have he := congrArg (fun p : Points W A => (pointCoordinates p) z) (hf.1 _ s v)
  rw [coordinates_comp, hz A s (v ≫ f), coordinates_comp] at he
  exact he

/-- An equivariant pointed isomorphism preserves and reflects each weight. -/
theorem pullback_weightSpace_iso (a : PointedAction S V) (b : PointedAction S W)
    (e : V ≅ W) (he : IsPointedEquivariant a b e.hom)
    (χ : characterLattice S) (z : Coord W) :
    pullback e.hom z ∈ weightSpace a χ ↔ z ∈ weightSpace b χ := by
  constructor
  · intro hz
    have hh := pullback_mem_weightSpace b a e.inv (isPointedEquivariant_inv a b e he) χ hz
    have hp : (pullback e.inv).comp (pullback e.hom) = AlgHom.id k (Coord W) := by
      rw [← pullback_comp, e.inv_hom_id, pullback_id]
    simpa only [← AlgHom.comp_apply, hp, AlgHom.id_apply] using hh
  · exact pullback_mem_weightSpace a b e.hom he χ

/-- Pullback along an actual isomorphism is an algebra equivalence. -/
def pullbackEquiv (e : V ≅ W) : Coord W ≃ₐ[k] Coord V :=
  AlgEquiv.ofAlgHom (pullback e.hom) (pullback e.inv)
    (by rw [← pullback_comp, e.hom_inv_id, pullback_id])
    (by rw [← pullback_comp, e.inv_hom_id, pullback_id])

theorem pullback_origin (a : PointedAction S V) (b : PointedAction S W)
    (f : V ⟶ W) (hf : IsPointedEquivariant a b f) :
    (coordinateOrigin a).comp (pullback f) = coordinateOrigin b := by
  rw [coordinateOrigin, ← coordinates_comp, Category.assoc, hf.2]
  rfl

def augmentationPullback (a : PointedAction S V) (b : PointedAction S W)
    (f : V ⟶ W) (hf : IsPointedEquivariant a b f) :
    augmentation b →ₗ[k] augmentation a :=
  ((pullback f).toLinearMap.comp (augmentation b).subtype).codRestrict _ (by
    intro z
    change coordinateOrigin a (pullback f z.val) = 0
    rw [← AlgHom.comp_apply, pullback_origin a b f hf]
    exact z.property)

theorem augmentationPullback_mem (a : PointedAction S V) (b : PointedAction S W)
    (f : V ⟶ W) (hf : IsPointedEquivariant a b f) (χ : characterLattice S)
    {z : augmentation b} (hz : z ∈ augmentationWeightSpace b χ) :
    augmentationPullback a b f hf z ∈ augmentationWeightSpace a χ :=
  pullback_mem_weightSpace a b f hf χ hz

theorem support_subset_of_injective (a : PointedAction S V) (b : PointedAction S W)
    (f : V ⟶ W) (hf : IsPointedEquivariant a b f)
    (hinj : Function.Injective (pullback f)) : support b ⊆ support a := by
  rintro χ ⟨z, hz, hχ⟩
  refine ⟨augmentationPullback a b f hf z, ?_, augmentationPullback_mem a b f hf χ hχ⟩
  intro he
  apply hz
  apply Subtype.ext
  apply hinj
  have hh := congrArg (fun x : augmentation a => x.val) he
  exact hh.trans (map_zero _).symm

/-- Weightwise lifting is the precise quotient property needed for support
transport. It is not part of the definition of an action or a closed immersion. -/
def HasWeightwiseLifts (a : PointedAction S V) (b : PointedAction S W)
    (f : V ⟶ W) (hf : IsPointedEquivariant a b f) : Prop :=
  ∀ (χ : characterLattice S) (z : augmentation a),
    z ∈ augmentationWeightSpace a χ →
      ∃ y : augmentation b, y ∈ augmentationWeightSpace b χ ∧
        augmentationPullback a b f hf y = z

theorem support_subset_of_weightwise_lifts (a : PointedAction S V) (b : PointedAction S W)
    (f : V ⟶ W) (hf : IsPointedEquivariant a b f)
    (hlift : HasWeightwiseLifts a b f hf) : support a ⊆ support b := by
  rintro χ ⟨z, hz, hχ⟩
  obtain ⟨y, hy, he⟩ := hlift χ z hχ
  refine ⟨y, ?_, hy⟩
  intro hy0
  apply hz
  rw [← he, hy0, map_zero]

/-- Actual equivariant pointed isomorphisms preserve augmentation support. -/
theorem support_eq_of_iso (a : PointedAction S V) (b : PointedAction S W)
    (e : V ≅ W) (he : IsPointedEquivariant a b e.hom) : support a = support b := by
  apply Set.Subset.antisymm
  · exact support_subset_of_injective b a e.inv (isPointedEquivariant_inv a b e he)
      (pullbackEquiv e.symm).injective
  · exact support_subset_of_injective a b e.hom he (pullbackEquiv e).injective


end Langlands.GroupScheme.PointedCoordinateWeights
