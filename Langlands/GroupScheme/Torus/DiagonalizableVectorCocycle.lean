import Langlands.GroupScheme.Torus.DiagonalizableAveraging
import Langlands.GroupScheme.Rational.SplitTorusVectorExtension

/-! # Contraction of regular vector two-cocycles on diagonalizable groups -/

noncomputable section
universe u
open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory

namespace Langlands.GroupScheme.diagonalizableVectorCocycle
open RelativeRoot PointedCoordinateWeights

variable {k : Type u} [Field k] (Λ : Type u) [AddCommGroup Λ]
    {V : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom V.X.hom]
    (a : AutomorphicAction (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp V)
    {d : ℕ}
    (e : ∀ T : Over (Spec (CommRingCat.of k)),
      (T ⟶ V.X) ≃* Multiplicative (Fin d → Γ(T.left, ⊤)))
    (he : IsLinearVectorCoordinates a e)

local notation "𝔻" => CommGroupScheme.toGrp (Diagonalizable.groupScheme (CommRingCat.of k) Λ)

/-- Evaluate a regular two-cochain on any pair of points. -/
def value (cochain : (𝔻).X ⊗ (𝔻).X ⟶ V.X) {T : Over (Spec (CommRingCat.of k))} (t r : T ⟶ (𝔻).X) : T ⟶ V.X :=
  lift t r ≫ cochain

variable (cochain : (Diagonalizable.groupScheme (CommRingCat.of k) Λ).X ⊗
  (Diagonalizable.groupScheme (CommRingCat.of k) Λ).X ⟶ V.X)

omit [IsAffineHom V.X.hom] in
/-- Naturality of evaluation of the regular two-cochain. -/
theorem comp_value {T T' : Over (Spec (CommRingCat.of k))} (b : T' ⟶ T)
    (t r : T ⟶ (𝔻).X) :
    b ≫ value (k := k) (V := V) Λ cochain t r = value (k := k) (V := V) Λ cochain (b ≫ t) (b ≫ r) := by
  rw [value, value, ← Category.assoc, comp_lift]

variable {A : Type u} [CommRing A] [Algebra k A]

/-- Coefficient inclusion for the averaging algebra. -/
abbrev coefficientInclusion (A : Type u) [CommRing A] [Algebra k A] :
    A →ₐ[k] AddMonoidAlgebra A Λ :=
  IsScalarTower.toAlgHom k A (AddMonoidAlgebra A Λ)

/-- Scalar extension of the representing algebra. -/
abbrev scalarExtension (A : Type u) [CommRing A] [Algebra k A] :
    AddMonoidAlgebra k Λ →ₐ[k] AddMonoidAlgebra A Λ :=
  AddMonoidAlgebra.mapAlgHom Λ (Algebra.ofId k A)

/-- The universal diagonalizable point over the averaging algebra. -/
abbrev averagingPoint (A : Type u) [CommRing A] [Algebra k A] :
    Lie.AffinePoints (𝔻) (AddMonoidAlgebra A Λ) :=
  Lie.affineMap _ (scalarExtension Λ A)
    (Diagonalizable.Averaging.universalPoint (CommRingCat.of k) Λ)

local notation "δ" => value (k := k) (V := V) Λ cochain

omit [IsAffineHom V.X.hom] in
/-- Cochain evaluation commutes with extension of coefficients. -/
theorem affineMap_value {B : Type u} [CommRing B] [Algebra k B] (φ : A →ₐ[k] B)
    (t r : Lie.AffinePoints (𝔻) A) :
    Lie.affineMap V φ (δ t r) = δ (Lie.affineMap _ φ t) (Lie.affineMap _ φ r) :=
  comp_value (k := k) (V := V) Λ cochain _ t r

/-- Degree-zero coefficients in the averaging variable. -/
def averageVector (t : Lie.AffinePoints (𝔻) A) : Fin d → A :=
  fun j => ((vectorAffineCoordinates e (AddMonoidAlgebra A Λ)
    (δ (Lie.affineMap _ (coefficientInclusion Λ A) t) (averagingPoint Λ A))).toAdd j).coeff 0

/-- The vector-valued averaged cochain as an actual affine point. -/
def averagePoint (t : Lie.AffinePoints (𝔻) A) : Lie.AffinePoints V A :=
  (vectorAffineCoordinates e A).symm (Multiplicative.ofAdd (averageVector Λ e cochain t))

local notation "β" => averageVector Λ e cochain
local notation "ρ" => averagePoint Λ e cochain

omit [IsAffineHom V.X.hom] in
theorem averagePoint_coordinates (t : Lie.AffinePoints (𝔻) A) :
    (vectorAffineCoordinates e A (ρ t)).toAdd = β t := by
  rw [averagePoint, MulEquiv.apply_symm_apply, toAdd_ofAdd]

/-- The regular morphism whose affine points are the averaged cochain. -/
def averageHom : (𝔻).X ⟶ V.X :=
  homOfAffinePoints fun _ _ _ t => ρ t

include he

omit [IsAffineHom V.X.hom] in
/-- The average is invariant under translation of the averaging variable. -/
theorem averageVector_translate (t r : Lie.AffinePoints (𝔻) A) :
    (fun j => ((vectorAffineCoordinates e (AddMonoidAlgebra A Λ)
      (δ (Lie.affineMap _ (coefficientInclusion Λ A) t)
        (Lie.affineMap _ (coefficientInclusion Λ A) r * averagingPoint Λ A))).toAdd j).coeff 0) =
      β t := by
  let τ := (Diagonalizable.Averaging.translation Λ (Diagonalizable.Averaging.pointsEquiv (CommRingCat.of k) Λ A r)).restrictScalars k
  rw [← Diagonalizable.Averaging.translation_point (CommRingCat.of k), ← Diagonalizable.Averaging.translation_const (CommRingCat.of k) Λ
    (Diagonalizable.Averaging.pointsEquiv (CommRingCat.of k) Λ A r) t, ← affineMap_value, he.1.vectorAffineCoordinates_naturality]
  funext j
  exact Diagonalizable.Averaging.coeff_zero_translation Λ _ _

omit [IsAffineHom V.X.hom] in
/-- Constant group-algebra coefficients of a constant point. -/
theorem coeff_zero_coefficientInclusion (x : Lie.AffinePoints V A) :
    (fun j => ((vectorAffineCoordinates e (AddMonoidAlgebra A Λ)
      (Lie.affineMap V (coefficientInclusion Λ A) x)).toAdd j).coeff 0) =
      (vectorAffineCoordinates e A x).toAdd := by
  rw [he.1.vectorAffineCoordinates_naturality]
  funext j
  change (AddMonoidAlgebra.single 0 _).coeff 0 = _
  simp

/-- Constant group-algebra coefficients of the action of a constant point. -/
theorem coeff_zero_act (h : Lie.AffinePoints 𝔻 A)
    (x : Lie.AffinePoints V (AddMonoidAlgebra A Λ)) :
    (fun j => ((vectorAffineCoordinates e (AddMonoidAlgebra A Λ)
      (a.act (Lie.affineMap 𝔻 (coefficientInclusion Λ A) h) x)).toAdd j).coeff 0) =
      (vectorAffineCoordinates e A (a.act h ((vectorAffineCoordinates e A).symm
        (Multiplicative.ofAdd (fun j =>
          ((vectorAffineCoordinates e (AddMonoidAlgebra A Λ) x).toAdd j).coeff 0))))).toAdd := by
  have hx := he.coordinateAction_eq (CommAlgCat.of k (AddMonoidAlgebra A Λ))
    (Lie.affineMap 𝔻 (coefficientInclusion Λ A) h)
    (vectorAffineCoordinates e (AddMonoidAlgebra A Λ) x).toAdd
  simp only [ofAdd_toAdd, MulEquiv.symm_apply_apply] at hx
  rw [← hx, a.coordinateAction_coeff, he.coordinateAction_eq]

variable (hc : ∀ (T : Over (Spec (CommRingCat.of k)))
  (t r w : T ⟶ (Diagonalizable.groupScheme (CommRingCat.of k) Λ).X),
  value (k := k) (V := V) Λ cochain t r * value (k := k) (V := V) Λ cochain (t * r) w =
    a.act t (value (k := k) (V := V) Λ cochain r w) *
      value (k := k) (V := V) Λ cochain t (r * w))

include hc

/-- The averaged defect bounds the defect: the Hochschild two-cocycle is the
coboundary of the average. -/
theorem cocycle_add_averageVector (t r : Lie.AffinePoints (𝔻) A) :
    (vectorAffineCoordinates e A (δ t r)).toAdd + β (t * r) =
      (vectorAffineCoordinates e A (a.act t (ρ r))).toAdd + β t := by
  have hc := congrArg (fun x : Lie.AffinePoints V (AddMonoidAlgebra A Λ) =>
      fun j : Fin d => ((vectorAffineCoordinates e (AddMonoidAlgebra A Λ) x).toAdd j).coeff 0)
    (hc _ (Lie.affineMap _ (coefficientInclusion Λ A) t)
      (Lie.affineMap _ (coefficientInclusion Λ A) r) (averagingPoint Λ A))
  simp only [map_mul, toAdd_mul] at hc
  have h1 : (fun j : Fin d => ((vectorAffineCoordinates e (AddMonoidAlgebra A Λ)
      (δ (Lie.affineMap _ (coefficientInclusion Λ A) t) (Lie.affineMap _ (coefficientInclusion Λ A) r))).toAdd j +
      (vectorAffineCoordinates e (AddMonoidAlgebra A Λ)
      (δ (Lie.affineMap _ (coefficientInclusion Λ A) t * Lie.affineMap _ (coefficientInclusion Λ A) r)
        (averagingPoint Λ A))).toAdd j).coeff 0) =
      (vectorAffineCoordinates e A (δ t r)).toAdd + β (t * r) := by
    rw [← affineMap_value, ← map_mul]
    funext j
    rw [AddMonoidAlgebra.coeff_add, Pi.add_apply]
    exact congrArg₂ (fun a b : A => a + b) (congrFun (coeff_zero_coefficientInclusion Λ a e he _) j) rfl
  have h2 : (fun j : Fin d => ((vectorAffineCoordinates e (AddMonoidAlgebra A Λ)
      (a.act (Lie.affineMap _ (coefficientInclusion Λ A) t)
        (δ (Lie.affineMap _ (coefficientInclusion Λ A) r) (averagingPoint Λ A)))).toAdd j +
      (vectorAffineCoordinates e (AddMonoidAlgebra A Λ)
      (δ (Lie.affineMap _ (coefficientInclusion Λ A) t)
        (Lie.affineMap _ (coefficientInclusion Λ A) r * averagingPoint Λ A))).toAdd j).coeff 0) =
      (vectorAffineCoordinates e A (a.act t (ρ r))).toAdd + β t := by
    funext j
    rw [AddMonoidAlgebra.coeff_add, Pi.add_apply]
    exact congrArg₂ (· + ·)
      (congrFun (coeff_zero_act Λ a e he _ _) j)
      (congrFun (averageVector_translate Λ a e he cochain t r) j)
  rw [← h1, ← h2]
  exact hc

/-- The cocycle is the coboundary of its average on affine points. -/
theorem averagePoint_coboundary (t r : Lie.AffinePoints (𝔻) A) :
    δ t r * ρ (t * r) = a.act t (ρ r) * ρ t := by
  apply (vectorAffineCoordinates e A).injective
  apply Multiplicative.toAdd.injective
  simp only [map_mul, toAdd_mul, averagePoint_coordinates]
  exact cocycle_add_averageVector Λ a e he cochain hc t r

omit hc

omit [IsAffineHom V.X.hom] in
/-- The average commutes with extension of coefficients. -/
theorem averageVector_naturality {B : Type u} [CommRing B] [Algebra k B] (φ : A →ₐ[k] B)
    (t : Lie.AffinePoints (𝔻) A) :
    β (Lie.affineMap _ φ t) = fun j => φ (β t j) := by
  have hc : (AddMonoidAlgebra.mapAlgHom Λ φ).comp (coefficientInclusion Λ A) =
      (coefficientInclusion Λ B).comp φ := by
    ext a
    simp [coefficientInclusion, AddMonoidAlgebra.coe_algebraMap]
  have hl : (AddMonoidAlgebra.mapAlgHom Λ φ).comp (scalarExtension Λ A) =
      scalarExtension Λ B := by
    rw [scalarExtension, scalarExtension, ← AddMonoidAlgebra.mapRangeAlgHom_comp]
    exact congrArg _ (Subsingleton.elim _ _)
  have hd : δ (Lie.affineMap _ (coefficientInclusion Λ B) (Lie.affineMap _ φ t)) (averagingPoint Λ B) =
      Lie.affineMap V (AddMonoidAlgebra.mapAlgHom Λ φ)
        (δ (Lie.affineMap _ (coefficientInclusion Λ A) t) (averagingPoint Λ A)) := by
    rw [affineMap_value, averagingPoint, averagingPoint, ← Lie.affineMap_comp,
      ← Lie.affineMap_comp, ← Lie.affineMap_comp, hc, hl]
  funext j
  simp only [averageVector]
  rw [hd, he.1.vectorAffineCoordinates_naturality]
  exact AddMonoidAlgebra.coeff_mapAlgHom _ _ _

omit [IsAffineHom V.X.hom] in
/-- The averaged point commutes with extension of coefficients. -/
theorem averagePoint_naturality {B : Type u} [CommRing B] [Algebra k B] (φ : A →ₐ[k] B)
    (t : Lie.AffinePoints (𝔻) A) :
    Lie.affineMap V φ (ρ t) = ρ (Lie.affineMap _ φ t) := by
  apply (vectorAffineCoordinates e B).injective
  apply Multiplicative.toAdd.injective
  rw [he.1.vectorAffineCoordinates_naturality, averagePoint_coordinates,
    averagePoint_coordinates, averageVector_naturality Λ a e he cochain]

omit [IsAffineHom V.X.hom] in
/-- Evaluation of the averaged morphism on affine points. -/
theorem comp_averageHom (t : Lie.AffinePoints (𝔻) A) :
    t ≫ averageHom Λ e cochain = ρ t :=
  comp_homOfAffinePoints _
    (fun _ _ _ _ _ _ f v => averagePoint_naturality Λ a e he cochain f v) t

include hc

/-- The coboundary equation on the universal pair of points. -/
theorem averageHom_coboundary_universal :
    cochain * ((fst (𝔻).X (𝔻).X * snd (𝔻).X (𝔻).X) ≫ averageHom Λ e cochain) =
      a.act (fst (𝔻).X (𝔻).X) (snd (𝔻).X (𝔻).X ≫ averageHom Λ e cochain) *
        (fst (𝔻).X (𝔻).X ≫ averageHom Λ e cochain) := by
  apply affine_hom_ext
  intro A _ _ v
  have hv := averagePoint_coboundary Λ a e he cochain hc
    (v ≫ fst (𝔻).X (𝔻).X) (v ≫ snd (𝔻).X (𝔻).X)
  simp only [value, ← comp_lift, lift_fst_snd, Category.comp_id] at hv
  simpa only [MonObj.comp_mul, ← Category.assoc, AutomorphicAction.naturality,
    comp_averageHom Λ a e he cochain] using hv

/-- Every regular vector two-cocycle on a diagonalizable group is the
coboundary of an actual regular morphism, on all test schemes. -/
theorem averageHom_coboundary {T : Over (Spec (CommRingCat.of k))}
    (t r : T ⟶ (𝔻).X) :
    δ t r * ((t * r) ≫ averageHom Λ e cochain) =
      a.act t (r ≫ averageHom Λ e cochain) * (t ≫ averageHom Λ e cochain) := by
  have h := congrArg (fun f => lift t r ≫ f)
    (averageHom_coboundary_universal Λ a e he cochain hc)
  simpa only [MonObj.comp_mul, AutomorphicAction.naturality,
    ← Category.assoc, lift_fst, lift_snd, value] using h

/-- Existence form of regular two-cocycle contraction. -/
theorem exists_coboundary : ∃ b : (𝔻).X ⟶ V.X,
    ∀ (T : Over (Spec (CommRingCat.of k))) (t r : T ⟶ (𝔻).X),
      δ t r * ((t * r) ≫ b) = a.act t (r ≫ b) * (t ≫ b) :=
  ⟨averageHom Λ e cochain, fun _ t r => averageHom_coboundary Λ a e he cochain hc t r⟩

end Langlands.GroupScheme.diagonalizableVectorCocycle
