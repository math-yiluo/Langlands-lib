import Langlands.GroupScheme.Examples.SU3Cocharacter
import Langlands.GroupScheme.SpecialLinearWeilDynamicRoots

/-! # Actual upper points and their contraction in the special unitary scheme -/

noncomputable section

universe u v

open CategoryTheory Opposite AlgebraicGeometry
  CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.SU3Root

section Coefficients

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B]
  {c : RingInvolution A} {d : RingInvolution B}

/-- The original upper matrix with codomain restricted to actual special unitary matrices. -/
def upperSpecialUnitaryHom (c : RingInvolution A) :
    Parameters c →* specialUnitarySubgroup c :=
  (Parameters.embedding c).codRestrict (specialUnitarySubgroup c)
    (embedding_mem_specialUnitarySubgroup c)

/-- The actual upper matrix respects every involution-compatible coefficient map. -/
theorem specialUnitaryMap_upper (f : A →+* B)
    (hf : ∀ a, f (c.bar a) = d.bar (f a)) (x : Parameters c) :
    specialUnitaryMap f hf (upperSpecialUnitaryHom c x) =
      upperSpecialUnitaryHom d (Parameters.map f hf x) := by
  apply Subtype.ext
  apply Units.ext
  rw [specialUnitaryMap_val]
  exact congrArg (fun g : Matrix.GeneralLinearGroup (Fin 3) B =>
    (g : Matrix (Fin 3) (Fin 3) B)) (Parameters.embedding_map f hf x).symm

/-- Diagonal conjugation on actual special unitary matrices is the proved root scaling. -/
theorem diagonalSpecialUnitaryHom_conjugate_upper (t : Aˣ) (x : Parameters c) :
    diagonalSpecialUnitaryHom c t * upperSpecialUnitaryHom c x *
        (diagonalSpecialUnitaryHom c t)⁻¹ =
      upperSpecialUnitaryHom c (Parameters.scale (diagonalRootScalar c t : A) x) := by
  apply Subtype.ext
  exact diagonal_conjugate_embedding c t x

/-- Scaling both root coordinates by zero gives the actual identity parameter. -/
theorem scale_zero_apply (x : Parameters c) : Parameters.scale (0 : A) x = 1 := by
  apply Parameters.ext <;> simp

end Coefficients

namespace SchemeModel

variable (k L : Type u) [Field k] [Field L] [Algebra k L]
  [Algebra.IsQuadraticExtension k L] [Algebra.IsSeparable k L]

/-- Original upper parameters over the actual tensor coefficient ring give actual test points. -/
def upperPoints (T : Over (Spec (CommRingCat.of k))) :
    Parameters (coefficientInvolution k L T) →* (T ⟶ (groupScheme k L).X) :=
  (pointsEquiv k L T).symm.toMonoidHom.comp
    (upperSpecialUnitaryHom (coefficientInvolution k L T))

@[simp] theorem pointsEquiv_upperPoints (T : Over (Spec (CommRingCat.of k)))
    (x : Parameters (coefficientInvolution k L T)) :
    pointsEquiv k L T (upperPoints k L T x) =
      upperSpecialUnitaryHom (coefficientInvolution k L T) x :=
  (pointsEquiv k L T).apply_symm_apply _

/-- Pulling back an actual upper point pulls back exactly its two tensor coordinates. -/
theorem upperPoints_naturality {T T' : Over (Spec (CommRingCat.of k))}
    (a : T' ⟶ T) (x : Parameters (coefficientInvolution k L T)) :
    upperPoints k L T' (Parameters.map
      (SpecialLinear.WeilRoot.tensorMap k L a) (tensorMap_bar k L a) x) =
      a ≫ upperPoints k L T x := by
  apply (pointsEquiv k L T').injective
  rw [pointsEquiv_upperPoints, pointsEquiv_map, pointsEquiv_upperPoints,
    specialUnitaryMap_upper]

/-- The original upper matrices define a subgroup functor on all actual test schemes. -/
def upperFunctor : SubgroupFunctor (groupScheme k L) where
  carrier T := (upperPoints k L T).range
  comp_mem a g := by
    rintro ⟨x, rfl⟩
    exact ⟨Parameters.map (SpecialLinear.WeilRoot.tensorMap k L a)
      (tensorMap_bar k L a) x, upperPoints_naturality k L a x⟩

/-- The scalar unit fixed by conjugation is also the exact scalar of the upper-root action. -/
theorem diagonalRootScalar_scalarUnit {T : Over (Spec (CommRingCat.of k))}
    (x : T ⟶ (Gm (Spec (CommRingCat.of k))).X) :
    diagonalRootScalar (coefficientInvolution k L T) (scalarUnit k L T x) =
      scalarUnit k L T x := by
  rw [diagonalRootScalar, scalarUnit_bar, mul_inv_cancel_right]

/-- The actual polynomial curve scales the two upper-root coordinates with weights one and two. -/
def upperContraction {T : Over (Spec (CommRingCat.of k))}
    (x : Parameters (coefficientInvolution k L T)) :
    T ⊗ AffineLine.scheme (Spec (CommRingCat.of k)) ⟶ (groupScheme k L).X :=
  upperPoints k L _
    (Parameters.scale
      (SpecialLinear.WeilRoot.includeSections k L _
        ((snd T (AffineLine.scheme (Spec (CommRingCat.of k)))).left.appTop
          (AffineLine.coord (Spec (CommRingCat.of k)))))
      (Parameters.map
        (SpecialLinear.WeilRoot.tensorMap k L
          (fst T (AffineLine.scheme (Spec (CommRingCat.of k)))))
        (tensorMap_bar k L (fst T (AffineLine.scheme (Spec (CommRingCat.of k))))) x))

/-- Restricting the curve restricts its scalar and original tensor parameters. -/
theorem pointsEquiv_comp_upperContraction
    {T T' : Over (Spec (CommRingCat.of k))}
    (a : T' ⟶ T ⊗ AffineLine.scheme (Spec (CommRingCat.of k)))
    (x : Parameters (coefficientInvolution k L T)) :
    pointsEquiv k L T' (a ≫ upperContraction k L x) =
      upperSpecialUnitaryHom (coefficientInvolution k L T')
        (Parameters.scale
          (SpecialLinear.WeilRoot.includeSections k L T'
            ((a ≫ snd T (AffineLine.scheme (Spec (CommRingCat.of k)))).left.appTop
              (AffineLine.coord (Spec (CommRingCat.of k)))))
          (Parameters.map
            (SpecialLinear.WeilRoot.tensorMap k L
              (a ≫ fst T (AffineLine.scheme (Spec (CommRingCat.of k)))))
            (tensorMap_bar k L
              (a ≫ fst T (AffineLine.scheme (Spec (CommRingCat.of k))))) x)) := by
  rw [upperContraction, ← upperPoints_naturality, pointsEquiv_upperPoints,
    Parameters.scale_map, SpecialLinear.WeilRoot.tensorMap_includeSections]
  simp only [Over.comp_left, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
  apply congrArg (upperSpecialUnitaryHom _)
  apply congrArg (Parameters.scale _)
  apply Parameters.ext <;> exact SpecialLinear.WeilRoot.tensorMap_comp k L _ _ _

/-- The polynomial curve extends the actual conjugation orbit of the original upper point. -/
theorem upperContraction_isOrbitExtension {T : Over (Spec (CommRingCat.of k))}
    (x : Parameters (coefficientInvolution k L T)) :
    Dynamic.IsOrbitExtension (cocharacter k L) (upperPoints k L T x)
      (upperContraction k L x) := by
  apply (pointsEquiv k L _).injective
  rw [pointsEquiv_comp_upperContraction]
  simp only [Dynamic.orbit, map_mul, map_inv, pointsEquiv_cocharacter]
  rw [← upperPoints_naturality, pointsEquiv_upperPoints,
    diagonalSpecialUnitaryHom_conjugate_upper, diagonalRootScalar_scalarUnit]
  rw [whiskerLeft_snd, whiskerLeft_fst]
  rw [← AffineLine.homEquiv_apply, AffineLine.homEquiv_comp_unitInclusion]
  rfl

/-- The actual polynomial upper-root curve has identity value at zero. -/
theorem upperContraction_evalZero {T : Over (Spec (CommRingCat.of k))}
    (x : Parameters (coefficientInvolution k L T)) :
    Dynamic.evalZero (upperContraction k L x) = 1 := by
  apply (pointsEquiv k L _).injective
  rw [Dynamic.evalZero, pointsEquiv_comp_upperContraction, map_one]
  rw [lift_snd, ← AffineLine.homEquiv_apply, AffineLine.homEquiv_comp_zeroSection,
    map_zero, scale_zero_apply, map_one]

/-- Every actual upper point contracts to the identity under the actual split cocharacter. -/
theorem upperFunctor_le_dynamicUnipotent :
    upperFunctor k L ≤ Dynamic.unipotent (cocharacter k L) := by
  intro T g hg
  obtain ⟨x, rfl⟩ := hg
  exact ⟨upperContraction k L x, upperContraction_isOrbitExtension k L x,
    upperContraction_evalZero k L x⟩

end SchemeModel
end Langlands.GroupScheme.SU3Root
