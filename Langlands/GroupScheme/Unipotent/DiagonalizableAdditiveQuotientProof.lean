import Langlands.GroupScheme.Unipotent.DiagonalizableAdditiveQuotientStatement
import Langlands.GroupScheme.Unipotent.AlgebraicallyClosedSplit
import Langlands.GroupScheme.Rational.FppfQuotientSmooth
import Langlands.GroupScheme.Rational.VectorGroupCoordinates
import Langlands.GroupScheme.Rational.VectorLieCoordinates
import Langlands.GroupScheme.Lie.SmoothDifferential
import Langlands.GroupScheme.Lie.SurjectiveDifferentialProof
import Langlands.GroupScheme.Torus.DiagonalizableVectorCocycle
import Langlands.GroupScheme.Torus.DiagonalizableCharacterProof
import Langlands.GroupScheme.CorepresentedAffineComparison
import Langlands.GroupScheme.Rational.SplitTorusVectorExtension
import Langlands.GroupScheme.Torus.DiagonalizableGeometry

/-! # Equivariant smooth additive quotients of smooth connected unipotent groups -/

noncomputable section
universe u
open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory

namespace Langlands.GroupScheme.diagonalizableAdditiveQuotient
open RelativeRoot PointedCoordinateWeights

variable {k : Type u} [Field k]

local notation "𝔾ₐ" => VectorGroup.groupScheme (CommRingCat.of k) 1

/-- The additive group is affine over the base. -/
local instance : IsAffineHom (𝔾ₐ).X.hom := by
  change IsAffineHom (Spec.map (CommRingCat.ofHom (algebraMap k (MvPolynomial (Fin 1) k))))
  infer_instance

section Split

/-- A nontrivial smooth connected unipotent group over an algebraically closed field has a
smooth homomorphism to `𝔾ₐ`: the last quotient of a split series. -/
theorem exists_smooth_hom [IsAlgClosed k] (U : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth U.X.hom] [IsAffineHom U.X.hom] (hc : ConnectedSpace U.X.left)
    (hU : IsUnipotent U) (hne : SubgroupFunctor.range (𝟙 U) ≠ ⊥) :
    ∃ g : U ⟶ 𝔾ₐ, Smooth g.hom.hom.left := by
  obtain ⟨n, hn⟩ := Unipotent.algebraicallyClosedSplit k U hc hU
  cases n with
  | zero => exact absurd hn hne
  | succ n =>
    obtain ⟨K, V, j, q, hj, hK, -, -, hq, hV, -⟩ := hn
    have : IsClosedImmersion j.hom.hom.left := hj
    have : Mono j.hom.hom := Over.mono_of_mono_left _
    have : IsAffineHom V.X.hom := hV.isAffineHom
    have : QuasiCompact (q.hom.hom.left ≫ V.X.hom) := by
      rw [Over.w q.hom.hom]
      infer_instance
    have : QuasiCompact q.hom.hom.left := QuasiCompact.of_comp _ V.X.hom
    have hjrep : (SubgroupFunctor.range j).IsRepresentedBy j := ⟨inferInstance, rfl⟩
    have hqs : Smooth q.hom.hom.left := hq.smooth_of_smooth_kernel hjrep hK
    refine ⟨q ≫ hV.iso.hom, ?_⟩
    have : IsIso hV.iso.hom.hom.hom.left :=
      (inferInstance : IsIso (((Grp.forget _) ⋙ Over.forget _).map hV.iso.hom))
    change Smooth (q.hom.hom.left ≫ hV.iso.hom.hom.hom.left)
    infer_instance

end Split

section Components

variable (Λ : Type u) [AddCommGroup Λ] {U : GroupScheme (Spec (CommRingCat.of k))}
    (a : AutomorphicAction (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp U)
    (g : U ⟶ VectorGroup.groupScheme (CommRingCat.of k) 1)

local notation "𝔻" => CommGroupScheme.toGrp (Diagonalizable.groupScheme (CommRingCat.of k) Λ)
local notation "eₐ" => VectorGroup.coordinates (CommRingCat.of k) 1

variable {A : Type u} [CommRing A] [Algebra k A]

/-- The coordinate of an affine point of `𝔾ₐ`. -/
def coord (x : Lie.AffinePoints (R := CommRingCat.of k) (𝔾ₐ) A) : A :=
  (vectorAffineCoordinates (k := k) eₐ A x).toAdd 0

/-- The affine point of `𝔾ₐ` with a given coordinate. -/
def ofCoord (c : A) : Lie.AffinePoints (𝔾ₐ) A :=
  (vectorAffineCoordinates eₐ A).symm (Multiplicative.ofAdd fun _ => c)

@[simp] theorem coord_ofCoord (c : A) : coord (k := k) (ofCoord c) = c := by
  simp [coord, ofCoord]

theorem coord_injective : Function.Injective (coord (k := k) (A := A)) := by
  intro x y h
  apply (vectorAffineCoordinates eₐ A).injective
  apply Multiplicative.toAdd.injective
  funext j
  rw [Subsingleton.elim j 0]
  exact h

@[simp] theorem coord_mul (x y : Lie.AffinePoints (𝔾ₐ) A) :
    coord (x * y) = coord x + coord y := by
  simp [coord]

theorem coord_naturality {B : Type u} [CommRing B] [Algebra k B] (φ : A →ₐ[k] B)
    (x : Lie.AffinePoints (𝔾ₐ) A) :
    coord (Lie.affineMap _ φ x) = φ (coord x) := by
  simp only [coord]
  rw [VectorGroup.isNaturalVectorCoordinates.vectorAffineCoordinates_naturality]

/-- The value of `g` at the universal translate `P · u` of a point `u`, in `A[Λ]`. -/
def coaction (u : Lie.AffinePoints U A) : AddMonoidAlgebra A Λ :=
  coord (k := k) (a.act (Diagonalizable.Averaging.point (CommRingCat.of k) Λ A)
    (Lie.affineMap U (Diagonalizable.Averaging.const (CommRingCat.of k) Λ A) u) ≫ g.hom.hom)

theorem coaction_naturality {B : Type u} [CommRing B] [Algebra k B] (φ : A →ₐ[k] B)
    (u : Lie.AffinePoints U A) :
    coaction Λ a g (Lie.affineMap U φ u) =
      AddMonoidAlgebra.mapAlgHom Λ φ (coaction Λ a g u) := by
  have hc : (AddMonoidAlgebra.mapAlgHom Λ φ).comp
      (Diagonalizable.Averaging.const (CommRingCat.of k) Λ A) =
      (Diagonalizable.Averaging.const (CommRingCat.of k) Λ B).comp φ := by
    ext x
    simp [AddMonoidAlgebra.coe_algebraMap]
  have hl : (AddMonoidAlgebra.mapAlgHom Λ φ).comp
      (Diagonalizable.Averaging.scalars (CommRingCat.of k) Λ A) =
      Diagonalizable.Averaging.scalars (CommRingCat.of k) Λ B := by
    rw [Diagonalizable.Averaging.scalars, Diagonalizable.Averaging.scalars,
      ← AddMonoidAlgebra.mapRangeAlgHom_comp]
    exact congrArg _ (Subsingleton.elim _ _)
  have hd : a.act (Diagonalizable.Averaging.point (CommRingCat.of k) Λ B)
      (Lie.affineMap U (Diagonalizable.Averaging.const (CommRingCat.of k) Λ B)
        (Lie.affineMap U φ u)) =
      Lie.affineMap U (AddMonoidAlgebra.mapAlgHom Λ φ)
        (a.act (Diagonalizable.Averaging.point (CommRingCat.of k) Λ A)
          (Lie.affineMap U (Diagonalizable.Averaging.const (CommRingCat.of k) Λ A) u)) := by
    rw [Lie.affineMap_apply U (AddMonoidAlgebra.mapAlgHom Λ φ), a.naturality,
      ← Lie.affineMap_apply (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp,
      ← Lie.affineMap_apply U]
    congr 1
    · rw [Diagonalizable.Averaging.point, Diagonalizable.Averaging.point,
        ← Lie.affineMap_comp, hl]
    · rw [← Lie.affineMap_comp, ← Lie.affineMap_comp, hc]
  rw [coaction, coaction, hd, Lie.affineMap_apply U, Category.assoc,
    ← Lie.affineMap_apply (VectorGroup.groupScheme (CommRingCat.of k) 1), coord_naturality]

/-- The weight-`m` component of `g` on affine points. -/
def component (m : Λ) (u : Lie.AffinePoints U A) : Lie.AffinePoints (𝔾ₐ) A :=
  ofCoord ((coaction Λ a g u).coeff m)

theorem coord_component (m : Λ) (u : Lie.AffinePoints U A) :
    coord (k := k) (component Λ a g m u) = (coaction Λ a g u).coeff m :=
  coord_ofCoord _

theorem component_naturality {B : Type u} [CommRing B] [Algebra k B] (φ : A →ₐ[k] B)
    (m : Λ) (u : Lie.AffinePoints U A) :
    Lie.affineMap _ φ (component Λ a g m u) = component Λ a g m (Lie.affineMap U φ u) := by
  apply coord_injective
  rw [coord_naturality, coord_component, coord_component, coaction_naturality,
    AddMonoidAlgebra.coeff_mapAlgHom]

/-- The coaction is additive in the point. -/
theorem coaction_mul (u v : Lie.AffinePoints U A) :
    coaction Λ a g (u * v) = coaction Λ a g u + coaction Λ a g v := by
  rw [coaction, coaction, coaction, map_mul, a.act_mul_right, MonObj.mul_comp, coord_mul]

theorem component_mul (m : Λ) (u v : Lie.AffinePoints U A) :
    component Λ a g m (u * v) = component Λ a g m u * component Λ a g m v := by
  apply coord_injective
  rw [coord_mul, coord_component, coord_component, coord_component, coaction_mul,
    AddMonoidAlgebra.coeff_add, Finsupp.add_apply]

/-- The augmentation `A[Λ] → A`, sending every monomial `e_λ` to `1`. -/
def augmentation : AddMonoidAlgebra A Λ →ₐ[k] A :=
  (AddMonoidAlgebra.lift A A Λ 1).restrictScalars k

theorem augmentation_apply (x : AddMonoidAlgebra A Λ) :
    augmentation (k := k) Λ x = x.coeff.sum fun _ b => b := by
  simp [augmentation, AddMonoidAlgebra.lift_apply]

theorem augmentation_const (x : A) :
    augmentation (k := k) Λ (Diagonalizable.Averaging.const (CommRingCat.of k) Λ A x) = x := by
  simp [augmentation]

theorem affineMap_augmentation_point :
    Lie.affineMap _ (augmentation (k := k) Λ (A := A))
      (Diagonalizable.Averaging.point (CommRingCat.of k) Λ A) = 1 := by
  apply (Diagonalizable.Averaging.pointsEquiv (CommRingCat.of k) Λ A).injective
  rw [map_one, Diagonalizable.Averaging.point, ← Lie.affineMap_comp,
    Diagonalizable.Averaging.pointsEquiv_naturality,
    Diagonalizable.Averaging.pointsEquiv_universalPoint]
  ext m
  simp [augmentation]

/-- The value of `g` is the sum of all coefficients of the coaction. -/
theorem coord_comp_eq_augmentation (u : Lie.AffinePoints U A) :
    coord (k := k) (u ≫ g.hom.hom) = augmentation (k := k) Λ (coaction Λ a g u) := by
  have hc : Lie.affineMap U (augmentation (k := k) Λ (A := A))
      (Lie.affineMap U (Diagonalizable.Averaging.const (CommRingCat.of k) Λ A) u) = u := by
    rw [← Lie.affineMap_comp]
    convert Lie.affineMap_id U u
    ext x
    exact augmentation_const (k := k) Λ x
  have h : Lie.affineMap U (augmentation (k := k) Λ (A := A))
      (a.act (Diagonalizable.Averaging.point (CommRingCat.of k) Λ A)
        (Lie.affineMap U (Diagonalizable.Averaging.const (CommRingCat.of k) Λ A) u)) = u := by
    rw [Lie.affineMap_apply U, a.naturality,
      ← Lie.affineMap_apply (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp,
      ← Lie.affineMap_apply U, affineMap_augmentation_point, hc, a.act_one_left]
  rw [coaction, ← coord_naturality, Lie.affineMap_apply (VectorGroup.groupScheme _ 1),
    ← Category.assoc, ← Lie.affineMap_apply U, h]

/-- Translating the point by `d` multiplies the coaction by the character values of `d`. -/
theorem coaction_act (d : Lie.AffinePoints (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp A)
    (u : Lie.AffinePoints U A) :
    coaction Λ a g (a.act d u) =
      Diagonalizable.Averaging.translation Λ
        (Diagonalizable.Averaging.pointsEquiv (CommRingCat.of k) Λ A d) (coaction Λ a g u) := by
  set r := Diagonalizable.Averaging.pointsEquiv (CommRingCat.of k) Λ A d
  set τ := (Diagonalizable.Averaging.translation Λ r).restrictScalars (CommRingCat.of k)
  set P := Diagonalizable.Averaging.point (CommRingCat.of k) Λ A
  set c := Diagonalizable.Averaging.const (CommRingCat.of k) Λ A
  have h1 : Lie.affineMap U c (a.act d u) =
      a.act (Lie.affineMap _ c d) (Lie.affineMap U c u) := by
    rw [Lie.affineMap_apply U, a.naturality]
    rfl
  have hcomm : P * Lie.affineMap _ c d = Lie.affineMap _ c d * P := by
    apply (Diagonalizable.Averaging.pointsEquiv (CommRingCat.of k) Λ
      (AddMonoidAlgebra A Λ)).injective
    rw [map_mul, map_mul]
    exact mul_comm (G := Multiplicative Λ →* (AddMonoidAlgebra A Λ)ˣ) _ _
  have h2 : a.act (Lie.affineMap _ τ P) (Lie.affineMap U τ (Lie.affineMap U c u)) =
      Lie.affineMap U τ (a.act P (Lie.affineMap U c u)) := by
    rw [Lie.affineMap_apply U τ (a.act _ _), a.naturality]
    rfl
  have hL : a.act (Lie.affineMap _ c d * P) (Lie.affineMap U c u) =
      Lie.affineMap U τ (a.act P (Lie.affineMap U c u)) := by
    rw [← Diagonalizable.Averaging.translation_point (CommRingCat.of k) Λ d, ← h2,
      Diagonalizable.Averaging.translation_const]
  rw [coaction, coaction, h1, ← a.act_mul_left, hcomm, hL,
    Lie.affineMap_apply U, Category.assoc,
    ← Lie.affineMap_apply (VectorGroup.groupScheme (CommRingCat.of k) 1), coord_naturality]
  rfl

/-- The coordinate of the action through a character is the character value times the
coordinate. -/
theorem coord_weightAction_act
    (χ : characterLattice (Diagonalizable.groupScheme (CommRingCat.of k) Λ))
    (d : Lie.AffinePoints (𝔻) A) (w : Lie.AffinePoints (VectorGroup.groupScheme (CommRingCat.of k) 1) A) :
    coord (k := k) ((VectorGroup.weightAction (n := 1) χ).act d w) =
      (Scheme.ΓSpecIso (CommRingCat.of A)).hom (VectorGroup.charValue χ _ d) *
        coord (k := k) w := by
  change (Scheme.ΓSpecIso (CommRingCat.of A)).hom
      ((VectorGroup.coordinates (CommRingCat.of k) 1 _
        ((VectorGroup.weightAction (n := 1) χ).act d w)).toAdd 0) =
    (Scheme.ΓSpecIso (CommRingCat.of A)).hom (VectorGroup.charValue χ _ d) *
      (Scheme.ΓSpecIso (CommRingCat.of A)).hom
        ((VectorGroup.coordinates (CommRingCat.of k) 1 _ w).toAdd 0)
  rw [VectorGroup.coordinates_weightAction_act, Pi.smul_apply, smul_eq_mul]
  exact map_mul _ _ _

/-- The value of the evaluation character at an affine point is the corresponding unit. -/
theorem charValue_evalCharacter (m : Λ) (d : Lie.AffinePoints (𝔻) A) :
    (Scheme.ΓSpecIso (CommRingCat.of A)).hom
        (VectorGroup.charValue (DiagonalizableCharacter.evalCharacter (CommRingCat.of k) Λ m)
          _ d) =
      (Diagonalizable.Averaging.pointsEquiv (CommRingCat.of k) Λ A d (.ofAdd m) : A) := by
  rw [VectorGroup.charValue, DiagonalizableCharacter.evalCharacter_apply]
  unfold Diagonalizable.characterPointsEquiv
  erw [Corepresented.pointsEquiv_eq_affinePointsEquiv]
  exact Iso.inv_hom_id_apply (Scheme.ΓSpecIso (CommRingCat.of A)) _

section Morphism

variable [IsAffineHom U.X.hom]

/-- The weight-`m` component of `g` as a morphism of schemes. -/
def componentMor (m : Λ) : U.X ⟶ (VectorGroup.groupScheme (CommRingCat.of k) 1).X :=
  homOfAffinePoints fun _ _ _ u => component Λ a g m u

theorem comp_componentMor (m : Λ) (u : Lie.AffinePoints U A) :
    u ≫ componentMor Λ a g m = component Λ a g m u :=
  comp_homOfAffinePoints _ (fun _ _ _ _ _ _ f v => component_naturality Λ a g f m v) u

/-- The component is multiplicative on the universal pair of points. -/
theorem componentMor_mul_universal (m : Λ) :
    (fst U.X U.X * snd U.X U.X) ≫ componentMor Λ a g m =
      (fst U.X U.X ≫ componentMor Λ a g m) * (snd U.X U.X ≫ componentMor Λ a g m) := by
  apply affine_hom_ext
  intro A _ _ v
  simp only [← Category.assoc, MonObj.comp_mul, comp_componentMor]
  exact component_mul Λ a g m _ _

theorem componentMor_mul (m : Λ) {T : Over (Spec (CommRingCat.of k))} (x y : T ⟶ U.X) :
    (x * y) ≫ componentMor Λ a g m =
      (x ≫ componentMor Λ a g m) * (y ≫ componentMor Λ a g m) := by
  have hxy : x * y = lift x y ≫ (fst U.X U.X * snd U.X U.X) := by
    rw [MonObj.comp_mul, lift_fst, lift_snd]
  rw [hxy, Category.assoc, componentMor_mul_universal, MonObj.comp_mul]
  simp only [← Category.assoc, lift_fst, lift_snd]

/-- The weight-`m` component of `g` as a homomorphism. -/
def componentHom (m : Λ) : U ⟶ VectorGroup.groupScheme (CommRingCat.of k) 1 :=
  homOfPoints (fun _ => MonoidHom.mk' (· ≫ componentMor Λ a g m) (componentMor_mul Λ a g m))
    (fun _ _ => by simp only [MonoidHom.mk'_apply, Category.assoc])

theorem componentHom_hom (m : Λ) : (componentHom Λ a g m).hom.hom = componentMor Λ a g m := by
  have h := comp_homOfPoints
    (fun _ => MonoidHom.mk' (· ≫ componentMor Λ a g m) (componentMor_mul Λ a g m))
    (fun _ _ => by simp only [MonoidHom.mk'_apply, Category.assoc]) U.X (𝟙 U.X)
  unfold componentHom
  simpa only [Category.id_comp, MonoidHom.mk'_apply] using h

/-- Equivariance of the weight-`m` component on the universal pair of points. -/
theorem componentMor_equivariant_universal (m : Λ) :
    a.act (fst (𝔻).X U.X) (snd (𝔻).X U.X) ≫ componentMor Λ a g m =
      (VectorGroup.weightAction (n := 1)
        (DiagonalizableCharacter.evalCharacter (CommRingCat.of k) Λ m)).act
        (fst (𝔻).X U.X) (snd (𝔻).X U.X ≫ componentMor Λ a g m) := by
  apply affine_hom_ext
  intro A _ _ v
  rw [← Category.assoc, a.naturality, comp_componentMor, AutomorphicAction.naturality,
    ← Category.assoc v, comp_componentMor]
  apply coord_injective
  rw [coord_component, coaction_act, Diagonalizable.Averaging.coeff_translation,
    coord_weightAction_act, coord_component, charValue_evalCharacter, mul_comm]

/-- The weight-`m` component is equivariant for the action through the character `m`. -/
theorem componentMor_equivariant (m : Λ) {T : Over (Spec (CommRingCat.of k))}
    (d : T ⟶ (𝔻).X) (x : T ⟶ U.X) :
    a.act d x ≫ componentMor Λ a g m =
      (VectorGroup.weightAction (n := 1)
        (DiagonalizableCharacter.evalCharacter (CommRingCat.of k) Λ m)).act d
        (x ≫ componentMor Λ a g m) := by
  have h := congrArg (lift d x ≫ ·) (componentMor_equivariant_universal Λ a g m)
  rw [← Category.assoc, a.naturality, AutomorphicAction.naturality, lift_fst, lift_snd,
    lift_snd_assoc] at h
  exact h

end Morphism

section Differential

/-- Points of the Lie kernel of `𝔾ₐ` are determined by the epsilon part of their
coordinate. -/
theorem lieKernel_ext {x y : lieKernel (VectorGroup.groupScheme (CommRingCat.of k) 1) k}
    (h : (coord (k := k) x.val).snd = (coord (k := k) y.val).snd) : x = y := by
  apply Subtype.ext
  apply coord_injective
  apply TrivSqZeroExt.ext
  · exact (vectorAffineCoordinates_kernel_fst _ VectorGroup.isNaturalVectorCoordinates x 0).trans
      (vectorAffineCoordinates_kernel_fst _ VectorGroup.isNaturalVectorCoordinates y 0).symm
  · exact h

/-- Scaling a Lie kernel point of `𝔾ₐ` scales the epsilon part of its coordinate. -/
theorem coord_smul_snd (c : k)
    (x : Additive (lieKernel (VectorGroup.groupScheme (CommRingCat.of k) 1) k)) :
    (coord (k := k) (c • x).toMul.val).snd = c * (coord (k := k) x.toMul.val).snd := by
  change (coord (k := k) (Lie.affineMap _
    (GeneralLinear.DualNumber.epsilonScaleAlg (R := CommRingCat.of k) c) x.toMul.val)).snd = _
  rw [coord_naturality]
  exact GeneralLinear.DualNumber.epsilonScale_snd c _

variable [IsAffineHom U.X.hom]

/-- Some weight component of a smooth homomorphism to `𝔾ₐ` has surjective differential. -/
theorem exists_component_surjective (hg : Smooth g.hom.hom.left) :
    ∃ m : Λ, Function.Surjective (Lie.targetMapLinear (componentHom Λ a g m) k) := by
  obtain ⟨X, hX⟩ := Lie.targetMapLinear_surjective_of_smooth g k hg
    (Additive.ofMul (vectorLiePoint (VectorGroup.coordinates (CommRingCat.of k) 1)
      VectorGroup.isNaturalVectorCoordinates (A := k) fun _ => 1))
  have h1 : (coord (k := k) (X.toMul.val ≫ g.hom.hom)).snd = 1 := by
    have h := congrArg (fun y => (coord (k := k) y.toMul.val).snd) hX
    change (coord (k := k) (X.toMul.val ≫ g.hom.hom)).snd = _ at h
    rw [h]
    change ((vectorAffineCoordinates _ (DualNumber k) (vectorLiePoint _
      VectorGroup.isNaturalVectorCoordinates (A := k) fun _ => (1 : k)).val).toAdd 0).snd = 1
    rw [vectorAffineCoordinates_vectorLiePoint]
    rfl
  rw [coord_comp_eq_augmentation Λ a g, augmentation_apply] at h1
  have h2 : ∃ m, ((coaction Λ a g X.toMul.val).coeff m).snd ≠ 0 := by
    by_contra hne
    simp only [not_exists, ne_eq, not_not] at hne
    rw [Finsupp.sum, TrivSqZeroExt.snd_sum, Finset.sum_eq_zero (fun m _ => hne m)] at h1
    exact zero_ne_one h1
  obtain ⟨m, hm⟩ := h2
  refine ⟨m, fun W => ?_⟩
  have hc : (coord (k := k) (Lie.targetMapLinear (componentHom Λ a g m) k X).toMul.val).snd =
      ((coaction Λ a g X.toMul.val).coeff m).snd := by
    change (coord (k := k) (X.toMul.val ≫ (componentHom Λ a g m).hom.hom)).snd = _
    rw [componentHom_hom, comp_componentMor, coord_component]
  refine ⟨((coord (k := k) W.toMul.val).snd * ((coaction Λ a g X.toMul.val).coeff m).snd⁻¹) • X,
    ?_⟩
  apply Additive.toMul.injective
  apply lieKernel_ext
  rw [map_smul, coord_smul_snd, hc, inv_mul_cancel_right₀ hm]

end Differential

end Components

/-- The additive group is smooth over the field. -/
theorem smooth_additive : Smooth (VectorGroup.groupScheme (CommRingCat.of k) 1).X.hom :=
  Corepresented.smooth_groupScheme_iff.mpr inferInstance

/-- The additive group is connected. -/
theorem connectedSpace_additive :
    ConnectedSpace (VectorGroup.groupScheme (CommRingCat.of k) 1).X.left := by
  change ConnectedSpace (Spec (CommRingCat.of (MvPolynomial (Fin 1) k)))
  infer_instance

/-- **Equivariant smooth additive quotients.** A nontrivial smooth connected unipotent group
over an algebraically closed field, acted on by a diagonalizable group `D(Λ)`, has a smooth
surjective homomorphism onto `𝔾ₐ` which is equivariant for the action of `D(Λ)` on `𝔾ₐ`
through some character. -/
theorem diagonalizableUnipotentAdditiveQuotient :
    DiagonalizableUnipotentAdditiveQuotientStatement.{u} := by
  intro k _ _ Λ _ U _ _ hsm hc hU hne a
  have := hsm
  obtain ⟨g, hg⟩ := exists_smooth_hom U hc hU hne
  obtain ⟨m, hm⟩ := exists_component_surjective Λ a g hg
  obtain ⟨hfs, hfsurj⟩ := Lie.smoothSurjectiveOfSurjectiveDifferential k U
    (VectorGroup.groupScheme (CommRingCat.of k) 1) hsm smooth_additive inferInstance
    inferInstance connectedSpace_additive (componentHom Λ a g m) hm
  refine ⟨DiagonalizableCharacter.evalCharacter (CommRingCat.of k) Λ m, componentHom Λ a g m,
    hfs, hfsurj, fun T d x => ?_⟩
  rw [componentHom_hom]
  exact componentMor_equivariant Λ a g m d x

end Langlands.GroupScheme.diagonalizableAdditiveQuotient
