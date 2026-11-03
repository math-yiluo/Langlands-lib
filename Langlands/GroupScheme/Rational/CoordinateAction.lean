import Langlands.GroupScheme.Rational.CharacterUnits
import Langlands.GroupScheme.Lie.AffineCoordinates
import Langlands.GroupScheme.Rational.ActionWeightComparisonProof
import Mathlib.RingTheory.TensorProduct.Basic

/-! # Actual affine coordinate actions and augmentation eigenspaces -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.CoordinateWeights

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G H K : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [IsAffineHom H.X.hom] [IsAffineHom K.X.hom]

/-- Pullback along an actual morphism over the base. -/
def pullback (f : G.X ⟶ H.X) : CharacterUnits.Coord H →ₐ[k] CharacterUnits.Coord G :=
  Lie.pointCoordinates H (CharacterUnits.universalPoint G ≫ f)

@[simp] theorem coordinates_comp {A : Type u} [CommRing A] [Algebra k A]
    (f : G.X ⟶ H.X) (g : Lie.AffinePoints G A) :
    Lie.pointCoordinates H (g ≫ f) = (Lie.pointCoordinates G g).comp (pullback f) := by
  have hg : Lie.affineMap G (Lie.pointCoordinates G g) (CharacterUnits.universalPoint G) = g := by
    apply (Lie.pointCoordinates G).injective
    rw [Lie.pointCoordinates_naturality]
    change (Lie.pointCoordinates G g).comp
      ((Lie.pointCoordinates G) ((Lie.pointCoordinates G).symm (AlgHom.id k (CharacterUnits.Coord G)))) = _
    rw [Equiv.apply_symm_apply, AlgHom.comp_id]
  change _ = (Lie.pointCoordinates G g).comp
    (Lie.pointCoordinates H (CharacterUnits.universalPoint G ≫ f))
  rw [← Lie.pointCoordinates_naturality]
  congr 1
  change g ≫ f = ((algSpec _).map
    (CommAlgCat.ofHom (Lie.pointCoordinates G g)).op ≫ CharacterUnits.universalPoint G) ≫ f
  exact congrArg (· ≫ f) hg.symm

@[simp] theorem pullback_id : pullback (𝟙 G.X) = AlgHom.id k (CharacterUnits.Coord G) := by
  change (Lie.pointCoordinates G)
    ((Lie.pointCoordinates G).symm (AlgHom.id k (CharacterUnits.Coord G))) = _
  exact (Lie.pointCoordinates G).apply_symm_apply _

@[simp] theorem pullback_comp (f : G.X ⟶ H.X) (g : H.X ⟶ K.X) :
    pullback (f ≫ g) = (pullback f).comp (pullback g) := by
  rw [pullback, ← Category.assoc, coordinates_comp]
  rfl

/-- Evaluation of base-changed coordinates at an actual point. -/
def evaluate {A : Type u} [CommRing A] [Algebra k A] (g : Lie.AffinePoints G A) :
    A ⊗[k] CharacterUnits.Coord G →ₐ[A] A :=
  AlgHom.liftEquiv k A (CharacterUnits.Coord G) A (Lie.pointCoordinates G g)

@[simp] theorem evaluate_tmul {A : Type u} [CommRing A] [Algebra k A]
    (g : Lie.AffinePoints G A) (a : A) (f : CharacterUnits.Coord G) :
    evaluate g (a ⊗ₜ[k] f) = a * Lie.pointCoordinates G g f := rfl

/-- Translate the universal point after the arbitrary coefficient extension A/k. -/
def actionCoordinates (b : AutomorphicAction S.toGrp G)
    {A : Type u} [CommRing A] [Algebra k A] (s : Lie.AffinePoints S.toGrp A) :
    CharacterUnits.Coord G →ₐ[k] A ⊗[k] CharacterUnits.Coord G :=
  Lie.pointCoordinates G (b.act
    (Lie.affineMap S.toGrp Algebra.TensorProduct.includeLeft s)
    ((Lie.pointCoordinates G).symm Algebra.TensorProduct.includeRight))

/-- The A-algebra pullback on A ⊗ O(G) for the specified actual A-point of S. -/
def actionPullback (b : AutomorphicAction S.toGrp G)
    {A : Type u} [CommRing A] [Algebra k A] (s : Lie.AffinePoints S.toGrp A) :
    A ⊗[k] CharacterUnits.Coord G →ₐ[A] A ⊗[k] CharacterUnits.Coord G :=
  AlgHom.liftEquiv k A (CharacterUnits.Coord G) (A ⊗[k] CharacterUnits.Coord G) (actionCoordinates b s)

@[simp] theorem actionPullback_tmul (b : AutomorphicAction S.toGrp G)
    {A : Type u} [CommRing A] [Algebra k A] (s : Lie.AffinePoints S.toGrp A)
    (a : A) (f : CharacterUnits.Coord G) :
    actionPullback b s (a ⊗ₜ[k] f) = a • actionCoordinates b s f := rfl

/-- CGP's convention on every coefficient algebra and every actual point. -/
theorem evaluate_actionCoordinates (b : AutomorphicAction S.toGrp G)
    {A : Type u} [CommRing A] [Algebra k A] (s : Lie.AffinePoints S.toGrp A)
    (g : Lie.AffinePoints G A) :
    ((evaluate g).restrictScalars k).comp (actionCoordinates b s) =
      Lie.pointCoordinates G (b.act s g) := by
  unfold actionCoordinates
  rw [← Lie.pointCoordinates_naturality G ((evaluate g).restrictScalars k),
    RelativeRoot.act_affineMap]
  have hs : Lie.affineMap S.toGrp ((evaluate g).restrictScalars k)
      (Lie.affineMap S.toGrp Algebra.TensorProduct.includeLeft s) = s := by
    rw [← Lie.affineMap_comp]
    have he : ((evaluate g).restrictScalars k).comp
        (Algebra.TensorProduct.includeLeft : A →ₐ[k] A ⊗[k] CharacterUnits.Coord G) = AlgHom.id k A := by
      ext a
      simp [evaluate]
    rw [he, Lie.affineMap_id]
  have hg : Lie.affineMap G ((evaluate g).restrictScalars k)
      ((Lie.pointCoordinates G).symm Algebra.TensorProduct.includeRight) = g := by
    apply (Lie.pointCoordinates G).injective
    rw [Lie.pointCoordinates_naturality, Equiv.apply_symm_apply]
    exact (AlgHom.liftEquiv k A (CharacterUnits.Coord G) A).symm_apply_apply _
  rw [hs, hg]

/-- Evaluation of translated base-changed functions is evaluation at b.act s g. -/
theorem evaluate_actionPullback (b : AutomorphicAction S.toGrp G)
    {A : Type u} [CommRing A] [Algebra k A] (s : Lie.AffinePoints S.toGrp A)
    (g : Lie.AffinePoints G A) (a : A) (f : CharacterUnits.Coord G) :
    evaluate g (actionPullback b s (a ⊗ₜ[k] f)) =
      a * Lie.pointCoordinates G (b.act s g) f := by
  rw [actionPullback_tmul, map_smul]
  exact congrArg (a * ·) (DFunLike.congr_fun (evaluate_actionCoordinates b s g) f)

/-- The pullback fixes the coefficient factor, hence every extended acting point. -/
theorem actionPullback_actingPoint (b : AutomorphicAction S.toGrp G)
    {A : Type u} [CommRing A] [Algebra k A] (s t : Lie.AffinePoints S.toGrp A) :
    Lie.affineMap S.toGrp ((actionPullback b t).restrictScalars k)
      (Lie.affineMap S.toGrp (Algebra.TensorProduct.includeLeft :
        A →ₐ[k] A ⊗[k] CharacterUnits.Coord G) s) =
      Lie.affineMap S.toGrp Algebra.TensorProduct.includeLeft s := by
  rw [← Lie.affineMap_comp]
  have he : ((actionPullback b t).restrictScalars k).comp
      (Algebra.TensorProduct.includeLeft : A →ₐ[k] A ⊗[k] CharacterUnits.Coord G) =
      Algebra.TensorProduct.includeLeft := by
    ext a
    simp [actionPullback, Algebra.TensorProduct.includeLeft_apply,
      Algebra.TensorProduct.one_def, TensorProduct.smul_tmul', smul_eq_mul]
  rw [he]

/-- The pullback sends the universal point to its actual translate. -/
theorem actionPullback_universalPoint (b : AutomorphicAction S.toGrp G)
    {A : Type u} [CommRing A] [Algebra k A] (s : Lie.AffinePoints S.toGrp A) :
    Lie.affineMap G ((actionPullback b s).restrictScalars k)
      ((Lie.pointCoordinates G).symm Algebra.TensorProduct.includeRight) =
      b.act (Lie.affineMap S.toGrp Algebra.TensorProduct.includeLeft s)
        ((Lie.pointCoordinates G).symm Algebra.TensorProduct.includeRight) := by
  apply (Lie.pointCoordinates G).injective
  rw [Lie.pointCoordinates_naturality, Equiv.apply_symm_apply]
  exact (AlgHom.liftEquiv k A (CharacterUnits.Coord G) (A ⊗[k] CharacterUnits.Coord G)).symm_apply_apply _

@[simp] theorem actionPullback_coordinates (b : AutomorphicAction S.toGrp G)
    {A : Type u} [CommRing A] [Algebra k A] (s : Lie.AffinePoints S.toGrp A) :
    ((actionPullback b s).restrictScalars k).comp Algebra.TensorProduct.includeRight =
      actionCoordinates b s :=
  (AlgHom.liftEquiv k A (CharacterUnits.Coord G) (A ⊗[k] CharacterUnits.Coord G)).symm_apply_apply _

/-- The identity acting point induces the identity algebra map. -/
@[simp] theorem actionPullback_one (b : AutomorphicAction S.toGrp G)
    {A : Type u} [CommRing A] [Algebra k A] :
    actionPullback b (1 : Lie.AffinePoints S.toGrp A) = AlgHom.id A (A ⊗[k] CharacterUnits.Coord G) := by
  apply Algebra.TensorProduct.ext_ring
  ext z
  simp [actionPullback, actionCoordinates, Algebra.TensorProduct.includeRight_apply]

/-- Pullback reverses composition. Since S is commutative, this is also a left action. -/
theorem actionPullback_mul (b : AutomorphicAction S.toGrp G)
    {A : Type u} [CommRing A] [Algebra k A] (s t : Lie.AffinePoints S.toGrp A) :
    actionPullback b (s * t) = (actionPullback b t).comp (actionPullback b s) := by
  apply Algebra.TensorProduct.ext_ring
  change ((actionPullback b (s * t)).restrictScalars k).comp
      Algebra.TensorProduct.includeRight =
    (((actionPullback b t).restrictScalars k).comp
      ((actionPullback b s).restrictScalars k)).comp Algebra.TensorProduct.includeRight
  rw [AlgHom.comp_assoc,
    actionPullback_coordinates, actionPullback_coordinates]
  unfold actionCoordinates
  rw [← Lie.pointCoordinates_naturality G ((actionPullback b t).restrictScalars k),
    RelativeRoot.act_affineMap, actionPullback_actingPoint, actionPullback_universalPoint,
    map_mul, b.act_mul_left]

/-- The actual base-changed coordinate action is an algebra automorphism. -/
def actionAut (b : AutomorphicAction S.toGrp G)
    {A : Type u} [CommRing A] [Algebra k A] (s : Lie.AffinePoints S.toGrp A) :
    A ⊗[k] CharacterUnits.Coord G ≃ₐ[A] A ⊗[k] CharacterUnits.Coord G :=
  AlgEquiv.ofAlgHom (actionPullback b s) (actionPullback b s⁻¹)
    (by rw [← actionPullback_mul, inv_mul_cancel, actionPullback_one])
    (by rw [← actionPullback_mul, mul_inv_cancel, actionPullback_one])

/-- The actual augmentation ideal at the group identity. -/
def augmentationIdeal (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom] :
    Ideal (CharacterUnits.Coord G) := RingHom.ker (Lie.coordinateOrigin G).toRingHom

/-- The same augmentation ideal as a k-vector subspace of actual coordinates. -/
def augmentation (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom] :
    Submodule k (CharacterUnits.Coord G) := LinearMap.ker (Lie.coordinateOrigin G).toLinearMap

@[simp] theorem mem_augmentation {f : CharacterUnits.Coord G} :
    f ∈ augmentation G ↔ Lie.coordinateOrigin G f = 0 := Iff.rfl

/-- The augmentation is stable under every base-changed actual action. -/
theorem action_preserves_origin (b : AutomorphicAction S.toGrp G)
    {A : Type u} [CommRing A] [Algebra k A] (s : Lie.AffinePoints S.toGrp A) :
    ((evaluate (1 : Lie.AffinePoints G A)).restrictScalars k).comp
      (actionCoordinates b s) = (Algebra.ofId k A).comp (Lie.coordinateOrigin G) := by
  rw [evaluate_actionCoordinates, b.act_one, Lie.pointCoordinates_one]

/-- Equivariance on all tests for a morphism of the underlying actual schemes. -/
def IsEquivariant (b : AutomorphicAction S.toGrp G) (c : AutomorphicAction S.toGrp H)
    (f : G.X ⟶ H.X) : Prop :=
  ∀ (T : Over (Spec (CommRingCat.of k))) (s : T ⟶ S.X) (g : T ⟶ G.X),
    b.act s g ≫ f = c.act s (g ≫ f)

/-- A coordinate is a χ-eigenfunction in CGP's all-algebra convention. -/
def IsEigenfunction (b : AutomorphicAction S.toGrp G) (χ : characterLattice S)
    (f : CharacterUnits.Coord G) : Prop :=
  ∀ (A : Type u) [CommRing A] [Algebra k A] (s : Lie.AffinePoints S.toGrp A)
    (g : Lie.AffinePoints G A),
    Lie.pointCoordinates G (b.act s g) f =
      (Lie.characterValue χ s : A) * Lie.pointCoordinates G g f

/-- Eigenspaces in the actual coordinate algebra, with no chosen abstract grading. -/
def weightSpace (b : AutomorphicAction S.toGrp G) (χ : characterLattice S) :
    Submodule k (CharacterUnits.Coord G) where
  carrier := IsEigenfunction b χ
  zero_mem' := by intro A _ _ s g; simp
  add_mem' := by
    intro f g hf hg A _ _ s x
    simp only [map_add, hf A s x, hg A s x, mul_add]
  smul_mem' := by
    intro a f hf A _ _ s x
    change Lie.pointCoordinates G (b.act s x) (a • f) = _
    rw [map_smul, map_smul, hf A s x]
    simp only [Algebra.smul_def, mul_left_comm]

/-- The eigenspace in the actual augmentation ideal. -/
def augmentationWeightSpace (b : AutomorphicAction S.toGrp G) (χ : characterLattice S) :
    Submodule k (augmentation G) := (weightSpace b χ).comap (augmentation G).subtype

/-- Weights of nonzero augmentation eigenfunctions; the zero character is allowed
exactly when it occurs, and is never inserted by definition. -/
def support (b : AutomorphicAction S.toGrp G) : Set (characterLattice S) :=
  {χ | ∃ f : augmentation G, f ≠ 0 ∧ f ∈ augmentationWeightSpace b χ}

/-- Pullback preserves actual eigenfunctions under an equivariant morphism. -/
theorem pullback_mem_weightSpace (b : AutomorphicAction S.toGrp G)
    (c : AutomorphicAction S.toGrp H) (f : G.X ⟶ H.X) (hf : IsEquivariant b c f)
    (χ : characterLattice S) {z : CharacterUnits.Coord H} (hz : z ∈ weightSpace c χ) :
    pullback f z ∈ weightSpace b χ := by
  intro A _ _ s g
  have he := congrArg (fun p => Lie.pointCoordinates H p z) (hf _ s g)
  rw [coordinates_comp, hz A s (g ≫ f), coordinates_comp] at he
  exact he

/-- An actual group homomorphism preserves the augmentation. -/
theorem pullback_origin (f : G ⟶ H) :
    (Lie.coordinateOrigin G).comp (pullback f.hom.hom) = Lie.coordinateOrigin H := by
  simpa only [Lie.coordinateOrigin, MonObj.one_comp] using
    (coordinates_comp f.hom.hom (1 : Lie.AffinePoints G k)).symm

/-- The pullback on actual augmentation ideals. -/
def augmentationPullback (f : G ⟶ H) : augmentation H →ₗ[k] augmentation G :=
  ((pullback f.hom.hom).toLinearMap.comp (augmentation H).subtype).codRestrict _ (by
    intro z
    change Lie.coordinateOrigin G (pullback f.hom.hom z.val) = 0
    rw [← AlgHom.comp_apply, pullback_origin]
    exact z.property)

/-- Every equivariant isomorphism preserves and reflects coordinate eigenspaces. -/
theorem pullback_weightSpace_iso (b : AutomorphicAction S.toGrp G)
    (c : AutomorphicAction S.toGrp H) (e : G.X ≅ H.X)
    (he : IsEquivariant b c e.hom) (χ : characterLattice S) (z : CharacterUnits.Coord H) :
    pullback e.hom z ∈ weightSpace b χ ↔ z ∈ weightSpace c χ := by
  constructor
  · intro hz
    have hi : IsEquivariant c b e.inv := by
      intro T s h
      apply (cancel_mono e.hom).1
      rw [Category.assoc, he T s (h ≫ e.inv), Category.assoc,
        e.inv_hom_id, Category.comp_id, Category.comp_id]
    have hh := pullback_mem_weightSpace c b e.inv hi χ hz
    have hp : (pullback e.inv).comp (pullback e.hom) = AlgHom.id k (CharacterUnits.Coord H) := by
      rw [← pullback_comp, e.inv_hom_id, pullback_id]
    simpa only [← AlgHom.comp_apply, hp, AlgHom.id_apply] using hh
  · exact pullback_mem_weightSpace b c e.hom he χ

/-- Equivariant pullback on augmentation eigenspaces. -/
theorem augmentationPullback_mem (b : AutomorphicAction S.toGrp G)
    (c : AutomorphicAction S.toGrp H) (f : G ⟶ H)
    (hf : IsEquivariant b c f.hom.hom) (χ : characterLattice S)
    {z : augmentation H} (hz : z ∈ augmentationWeightSpace c χ) :
    augmentationPullback f z ∈ augmentationWeightSpace b χ :=
  pullback_mem_weightSpace b c f.hom.hom hf χ hz

/-- An injective equivariant pullback includes the augmentation weight support. -/
theorem support_subset_of_injective (b : AutomorphicAction S.toGrp G)
    (c : AutomorphicAction S.toGrp H) (f : G ⟶ H)
    (hf : IsEquivariant b c f.hom.hom) (hinj : Function.Injective (pullback f.hom.hom)) :
    support c ⊆ support b := by
  rintro χ ⟨z, hz, hχ⟩
  refine ⟨augmentationPullback f z, ?_, augmentationPullback_mem b c f hf χ hχ⟩
  intro he
  apply hz
  apply Subtype.ext
  apply hinj
  have hh := congrArg (fun x : augmentation G => x.val) he
  exact hh.trans (map_zero _).symm

omit [IsAffineHom G.X.hom] [IsAffineHom H.X.hom] in
/-- The representing inclusion is equivariant for the existing restricted action. -/
theorem represented_inclusion_equivariant (b : AutomorphicAction S.toGrp G)
    {F : SubgroupFunctor G} (i : H ⟶ G) (hi : F.IsRepresentedBy i) (hF : b.IsStable F) :
    IsEquivariant (b.onRepresentedSubgroup i hi hF) b i.hom.hom :=
  fun _ s h => b.onRepresentedSubgroup_act_comp i hi hF s h

end Langlands.GroupScheme.CoordinateWeights
