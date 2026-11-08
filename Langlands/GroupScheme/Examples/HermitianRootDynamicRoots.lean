import Langlands.GroupScheme.Examples.HermitianRootCocharacter

/-! # Actual upper points and contraction for the weighted Hermitian scheme -/

noncomputable section

universe u v z

open CategoryTheory Opposite AlgebraicGeometry
  CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.HermitianRoot

open SU3Root

section Coefficients

variable {A : Type u} {B : Type v} {Middle : Type z}
  [CommRing A] [CommRing B] [Fintype Middle]
  {c : RingInvolution A} {d : RingInvolution B}
  {H : DiagonalForm c Middle} {K : DiagonalForm d Middle}

/-- The actual weight-one/weight-two scaling commutes with compatible coefficients. -/
theorem Parameters.scale_map (f : A →+* B)
    (hf : ∀ a, f (c.bar a) = d.bar (f a))
    (hH : ∀ i, f (H.weight i) = K.weight i)
    (r : A) (hr : c.bar r = r) (x : Parameters H) :
    Parameters.map f hf hH (Parameters.scale r hr x) =
      Parameters.scale (f r) (by rw [← hf, hr]) (Parameters.map f hf hH x) := by
  apply Parameters.ext
  · funext i
    exact map_mul f _ _
  · exact (map_mul f _ _).trans (congrArg (fun a => a * f x.scalar) (map_pow f r 2))

variable [DecidableEq Middle]

/-- The original upper matrices as elements of the full weighted special-unitary subgroup. -/
def upperSpecialUnitaryHom (H : DiagonalForm c Middle) :
    Parameters H →* specialUnitarySubgroup H :=
  (Parameters.embedding H).codRestrict (specialUnitarySubgroup H)
    (embedding_mem_specialUnitarySubgroup H)

/-- Compatible coefficient maps preserve the original upper matrices. -/
theorem specialUnitaryMap_upper (f : A →+* B)
    (hf : ∀ a, f (c.bar a) = d.bar (f a))
    (hH : ∀ i, f (H.weight i) = K.weight i) (x : Parameters H) :
    specialUnitaryMap f hf hH (upperSpecialUnitaryHom H x) =
      upperSpecialUnitaryHom K (Parameters.map f hf hH x) := by
  apply Subtype.ext
  exact (Parameters.embedding_map f hf hH x).symm

end Coefficients

namespace SchemeModel

open SU3Root.SchemeModel (scalarUnit sectionToTensor_bar tensorMap_bar)

variable (k L : Type u) [Field k] [Field L] [Algebra k L]
  [Algebra.IsQuadraticExtension k L] [Algebra.IsSeparable k L]
  {Middle : Type} [Fintype Middle] [DecidableEq Middle]
  (H : DiagonalForm (fieldInvolution k L) Middle)
  (w : Middle → Lˣ) (hw : ∀ i, (w i : L) = H.weight i)

/-- Original upper parameters in the tensor coefficient algebra give actual scheme points. -/
def upperPoints (T : Over (Spec (CommRingCat.of k))) :
    Parameters (tensorForm k L H T) →* (T ⟶ (groupScheme k L H w hw).X) :=
  (pointsEquiv k L H w hw T).symm.toMonoidHom.comp
    (upperSpecialUnitaryHom (tensorForm k L H T))

@[simp] theorem pointsEquiv_upperPoints (T : Over (Spec (CommRingCat.of k)))
    (x : Parameters (tensorForm k L H T)) :
    pointsEquiv k L H w hw T (upperPoints k L H w hw T x) =
      upperSpecialUnitaryHom (tensorForm k L H T) x :=
  (pointsEquiv k L H w hw T).apply_symm_apply _

/-- Restriction of actual upper points pulls back their original tensor coordinates. -/
theorem upperPoints_naturality {T T' : Over (Spec (CommRingCat.of k))}
    (a : T' ⟶ T) (x : Parameters (tensorForm k L H T)) :
    upperPoints k L H w hw T' (Parameters.map
      (SpecialLinear.WeilRoot.tensorMap k L a) (tensorMap_bar k L a)
        (tensorMap_weight k L H a) x) =
      a ≫ upperPoints k L H w hw T x := by
  apply (pointsEquiv k L H w hw T').injective
  rw [pointsEquiv_upperPoints, pointsEquiv_map, pointsEquiv_upperPoints,
    specialUnitaryMap_upper]

/-- The original upper images form a subgroup functor on all relative test schemes. -/
def upperFunctor : SubgroupFunctor (groupScheme k L H w hw) where
  carrier T := (upperPoints k L H w hw T).range
  comp_mem a g := by
    rintro ⟨x, rfl⟩
    exact ⟨Parameters.map (SpecialLinear.WeilRoot.tensorMap k L a)
      (tensorMap_bar k L a) (tensorMap_weight k L H a) x,
        upperPoints_naturality k L H w hw a x⟩

/-- The polynomial curve scales the middle vector by t and the top-right scalar by t². -/
def upperContraction {T : Over (Spec (CommRingCat.of k))}
    (x : Parameters (tensorForm k L H T)) :
    T ⊗ AffineLine.scheme (Spec (CommRingCat.of k)) ⟶ (groupScheme k L H w hw).X :=
  upperPoints k L H w hw _
    (Parameters.scale
      (SpecialLinear.WeilRoot.includeSections k L _
        ((snd T (AffineLine.scheme (Spec (CommRingCat.of k)))).left.appTop
          (AffineLine.coord (Spec (CommRingCat.of k)))))
      (sectionToTensor_bar k L _ _)
      (Parameters.map
        (SpecialLinear.WeilRoot.tensorMap k L
          (fst T (AffineLine.scheme (Spec (CommRingCat.of k)))))
        (tensorMap_bar k L (fst T (AffineLine.scheme (Spec (CommRingCat.of k)))))
        (tensorMap_weight k L H (fst T (AffineLine.scheme (Spec (CommRingCat.of k))))) x))

/-- Pulling back the curve pulls back its scalar and its original tensor parameters. -/
theorem pointsEquiv_comp_upperContraction
    {T T' : Over (Spec (CommRingCat.of k))}
    (a : T' ⟶ T ⊗ AffineLine.scheme (Spec (CommRingCat.of k)))
    (x : Parameters (tensorForm k L H T)) :
    pointsEquiv k L H w hw T' (a ≫ upperContraction k L H w hw x) =
      upperSpecialUnitaryHom (tensorForm k L H T')
        (Parameters.scale
          (SpecialLinear.WeilRoot.includeSections k L T'
            ((a ≫ snd T (AffineLine.scheme (Spec (CommRingCat.of k)))).left.appTop
              (AffineLine.coord (Spec (CommRingCat.of k)))))
          (sectionToTensor_bar k L T' _)
          (Parameters.map
            (SpecialLinear.WeilRoot.tensorMap k L
              (a ≫ fst T (AffineLine.scheme (Spec (CommRingCat.of k)))))
            (tensorMap_bar k L
              (a ≫ fst T (AffineLine.scheme (Spec (CommRingCat.of k)))))
            (tensorMap_weight k L H
              (a ≫ fst T (AffineLine.scheme (Spec (CommRingCat.of k))))) x)) := by
  rw [upperContraction, ← upperPoints_naturality, pointsEquiv_upperPoints,
    Parameters.scale_map]
  apply congrArg (upperSpecialUnitaryHom _)
  apply Parameters.ext
  · funext i
    simp only [Parameters.vector_scale, Parameters.vector_map,
      SpecialLinear.WeilRoot.tensorMap_includeSections, Over.comp_left,
      Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
    congr 1
    exact SpecialLinear.WeilRoot.tensorMap_comp k L _ _ _
  · simp only [Parameters.scalar_scale, Parameters.scalar_map,
      SpecialLinear.WeilRoot.tensorMap_includeSections, Over.comp_left,
      Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
    congr 1
    exact SpecialLinear.WeilRoot.tensorMap_comp k L _ _ _

/-- The polynomial curve extends conjugation by the actual split diagonal cocharacter. -/
theorem upperContraction_isOrbitExtension {T : Over (Spec (CommRingCat.of k))}
    (x : Parameters (tensorForm k L H T)) :
    Dynamic.IsOrbitExtension (cocharacter k L H w hw) (upperPoints k L H w hw T x)
      (upperContraction k L H w hw x) := by
  apply (pointsEquiv k L H w hw _).injective
  rw [pointsEquiv_comp_upperContraction]
  simp only [Dynamic.orbit, map_mul, map_inv]
  rw [← upperPoints_naturality, pointsEquiv_upperPoints]
  apply Subtype.ext
  change Parameters.embedding _ _ =
    (pointsEquiv k L H w hw _ _).1 * Parameters.embedding _ _ *
      ((pointsEquiv k L H w hw _ _).1)⁻¹
  rw [pointsEquiv_cocharacter, ← Parameters.embedding_scale _
    (sectionToTensor_bar k L _ _)]
  rw [whiskerLeft_snd, whiskerLeft_fst]
  rw [← AffineLine.homEquiv_apply, AffineLine.homEquiv_comp_unitInclusion]
  rfl

/-- The actual polynomial curve has identity value at zero. -/
theorem upperContraction_evalZero {T : Over (Spec (CommRingCat.of k))}
    (x : Parameters (tensorForm k L H T)) :
    Dynamic.evalZero (upperContraction k L H w hw x) = 1 := by
  apply (pointsEquiv k L H w hw _).injective
  rw [Dynamic.evalZero, pointsEquiv_comp_upperContraction, map_one]
  rw [lift_snd, ← AffineLine.homEquiv_apply, AffineLine.homEquiv_comp_zeroSection]
  simp only [map_zero, Parameters.scale_zero, map_one]

/-- Every actual upper point contracts to the identity under the constructed cocharacter. -/
theorem upperFunctor_le_dynamicUnipotent :
    upperFunctor k L H w hw ≤ Dynamic.unipotent (cocharacter k L H w hw) := by
  intro T g hg
  obtain ⟨x, rfl⟩ := hg
  exact ⟨upperContraction k L H w hw x, upperContraction_isOrbitExtension k L H w hw x,
    upperContraction_evalZero k L H w hw x⟩

end SchemeModel
end Langlands.GroupScheme.HermitianRoot
