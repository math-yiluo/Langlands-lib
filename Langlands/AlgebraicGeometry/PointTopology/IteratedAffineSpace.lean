import Langlands.AlgebraicGeometry.GeometricIrreducibilityTransport
import Mathlib.AlgebraicGeometry.AffineSpace
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Morphisms.Preimmersion
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! # Iterated affine spaces and their function fields -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology

namespace Langlands.AlgebraicGeometry.PointTopology

section GenericPoints

variable {α β : Type*} [TopologicalSpace β]

/-- A continuous map with dense range sends a generic point of its source
to a generic point of its target. -/
theorem isGenericPoint_univ_of_denseRange [TopologicalSpace α] {f : α → β} (hf : Continuous f)
    (hd : DenseRange f) {x : α} (hx : IsGenericPoint x Set.univ) :
    IsGenericPoint (f x) Set.univ := by
  have h := hx.image hf
  rwa [Set.image_univ, hd.closure_range] at h

/-- A map whose range contains a generic point has dense range. -/
theorem denseRange_of_isGenericPoint {f : α → β} {a : α}
    (ha : IsGenericPoint (f a) Set.univ) : DenseRange f :=
  (dense_iff_closure_eq.mpr ha.def).mono (Set.singleton_subset_iff.mpr ⟨a, rfl⟩)

end GenericPoints

section AffineSpaceSum

variable (m n : Type u) (S : Scheme.{u})

set_option backward.isDefEq.respectTransparency.types false in
/-- Affine space on a disjoint sum of coordinates is iterated affine space:
`𝔸(m ⊕ n; S) ≅ 𝔸(n; 𝔸(m; S))`. The coordinates indexed by `m` become the
coordinates of the inner affine space `𝔸(m; S)`, and those indexed by `n` the
coordinates of the outer one. -/
def affineSpaceSumIso : 𝔸(m ⊕ n; S) ≅ 𝔸(n; 𝔸(m; S)) where
  hom := AffineSpace.homOfVector
    (AffineSpace.homOfVector (𝔸(m ⊕ n; S) ↘ S) (fun i => AffineSpace.coord S (Sum.inl i)))
    (fun j => AffineSpace.coord S (Sum.inr j))
  inv := AffineSpace.homOfVector (𝔸(n; 𝔸(m; S)) ↘ 𝔸(m; S) ≫ 𝔸(m; S) ↘ S)
    (Sum.elim (fun i => (𝔸(n; 𝔸(m; S)) ↘ 𝔸(m; S)).appTop (AffineSpace.coord S i))
      (AffineSpace.coord (𝔸(m; S))))
  hom_inv_id := by
    apply AffineSpace.hom_ext
    · rw [Category.assoc, AffineSpace.homOfVector_over, AffineSpace.homOfVector_over_assoc,
        AffineSpace.homOfVector_over, Category.id_comp]
    · rintro (i | j)
      · simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
          AffineSpace.homOfVector_appTop_coord, Sum.elim_inl]
        change (AffineSpace.homOfVector _ _ ≫ 𝔸(n; 𝔸(m; S)) ↘ 𝔸(m; S)).appTop
          (AffineSpace.coord S i) = _
        rw [AffineSpace.homOfVector_over, AffineSpace.homOfVector_appTop_coord]
        simp
      · simp
  inv_hom_id := by
    apply AffineSpace.hom_ext
    · apply AffineSpace.hom_ext
      · simp
      · intro i
        simp
    · intro j
      simp

@[reassoc]
theorem affineSpaceSumIso_hom_over :
    (affineSpaceSumIso m n S).hom ≫ 𝔸(n; 𝔸(m; S)) ↘ 𝔸(m; S) ≫ 𝔸(m; S) ↘ S =
      𝔸(m ⊕ n; S) ↘ S := by
  change AffineSpace.homOfVector _ _ ≫ _ = _
  rw [AffineSpace.homOfVector_over_assoc, AffineSpace.homOfVector_over]

@[reassoc]
theorem affineSpaceSumIso_inv_over :
    (affineSpaceSumIso m n S).inv ≫ 𝔸(m ⊕ n; S) ↘ S =
      𝔸(n; 𝔸(m; S)) ↘ 𝔸(m; S) ≫ 𝔸(m; S) ↘ S :=
  AffineSpace.homOfVector_over _ _

end AffineSpaceSum

section FunctionField

variable {X Y : Scheme.{u}} [IrreducibleSpace X] [IrreducibleSpace Y]

/-- The map of function fields `k(Y) → k(X)` induced by a morphism `f : X ⟶ Y`
sending the generic point of `X` to the generic point of `Y`. -/
def functionFieldMap (f : X ⟶ Y) (hf : f (genericPoint X) = genericPoint Y) :
    Y.functionField ⟶ X.functionField :=
  Y.presheaf.stalkSpecializes (specializes_of_eq hf) ≫ f.stalkMap (genericPoint X)

@[reassoc]
theorem SpecMap_functionFieldMap_fromSpecStalk (f : X ⟶ Y)
    (hf : f (genericPoint X) = genericPoint Y) :
    Spec.map (functionFieldMap f hf) ≫ Y.fromSpecStalk (genericPoint Y) =
      X.fromSpecStalk (genericPoint X) ≫ f := by
  rw [functionFieldMap, Spec.map_comp, Category.assoc,
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk, Scheme.SpecMap_stalkMap_fromSpecStalk]

/-- A preimmersion of integral schemes sending the generic point to the generic
point induces an isomorphism of function fields. -/
theorem isIso_functionFieldMap [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y) [IsPreimmersion f]
    (hf : f (genericPoint X) = genericPoint Y) : IsIso (functionFieldMap f hf) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨RingHom.injective (functionFieldMap f hf).hom, fun z => ?_⟩
  have : IsIso (Y.presheaf.stalkSpecializes (specializes_of_eq hf)) :=
    inferInstanceAs (IsIso (Y.presheaf.stalkCongr (.of_eq hf)).inv)
  obtain ⟨w, rfl⟩ := f.stalkMap_surjective (genericPoint X) z
  obtain ⟨v, rfl⟩ := (ConcreteCategory.bijective_of_isIso
    (Y.presheaf.stalkSpecializes (specializes_of_eq hf))).2 w
  exact ⟨v, by rw [functionFieldMap, ConcreteCategory.comp_apply]⟩

end FunctionField

section IteratedFunctionField

variable (m n : Type u) (S : Scheme.{u}) [IsIntegral S]

/-- The comparison morphism `𝔸(n; Spec k(𝔸(m; S))) ⟶ 𝔸(m ⊕ n; S)`: base change
of `𝔸(n; -)` along the generic point `Spec k(𝔸(m; S)) ⟶ 𝔸(m; S)`, followed by
the inverse of `affineSpaceSumIso`. -/
def affineSpaceFunctionFieldToSum :
    𝔸(n; Spec (𝔸(m; S)).functionField) ⟶ 𝔸(m ⊕ n; S) :=
  AffineSpace.map n ((𝔸(m; S)).fromSpecStalk (genericPoint _)) ≫ (affineSpaceSumIso m n S).inv

@[reassoc (attr := simp)]
theorem affineSpaceFunctionFieldToSum_over :
    affineSpaceFunctionFieldToSum m n S ≫ 𝔸(m ⊕ n; S) ↘ S =
      𝔸(n; Spec (𝔸(m; S)).functionField) ↘ Spec (𝔸(m; S)).functionField ≫
        (𝔸(m; S)).fromSpecStalk (genericPoint _) ≫ 𝔸(m; S) ↘ S := by
  rw [affineSpaceFunctionFieldToSum, Category.assoc, affineSpaceSumIso_inv_over,
    AffineSpace.map_over_assoc]

instance : IsPreimmersion (AffineSpace.map n ((𝔸(m; S)).fromSpecStalk (genericPoint _))) :=
  MorphismProperty.of_isPullback (P := @IsPreimmersion)
    (AffineSpace.isPullback_map (n := n) ((𝔸(m; S)).fromSpecStalk (genericPoint _))).flip
    inferInstance

instance : IsPreimmersion (affineSpaceFunctionFieldToSum m n S) := by
  rw [affineSpaceFunctionFieldToSum]
  infer_instance

theorem affineSpaceFunctionFieldToSum_genericPoint :
    affineSpaceFunctionFieldToSum m n S (genericPoint _) = genericPoint _ := by
  let φ := AffineSpace.map n ((𝔸(m; S)).fromSpecStalk (genericPoint _))
  -- The generic point of `𝔸(n; 𝔸(m; S))` lies over the generic point of `𝔸(m; S)`.
  have hη : (𝔸(n; 𝔸(m; S)) ↘ 𝔸(m; S)) (genericPoint 𝔸(n; 𝔸(m; S))) =
      genericPoint 𝔸(m; S) :=
    (isGenericPoint_univ_of_denseRange (Scheme.Hom.continuous _)
      (Scheme.Hom.surjective (𝔸(n; 𝔸(m; S)) ↘ 𝔸(m; S))).denseRange
      (genericPoint_spec _)).eq (genericPoint_spec _)
  obtain ⟨c⟩ : Nonempty (Spec (𝔸(m; S)).functionField) := inferInstance
  have hc : (𝔸(m; S)).fromSpecStalk (genericPoint _) c = genericPoint 𝔸(m; S) := by
    convert Scheme.fromSpecStalk_closedPoint (X := 𝔸(m; S)) (x := genericPoint _) using 3
    exact congrArg _ (Subsingleton.elim (α := PrimeSpectrum (𝔸(m; S)).functionField) _ _)
  -- It is therefore in the range of `φ`; its preimage is the generic point.
  obtain ⟨p, hp, -⟩ := Scheme.exists_preimage_of_isPullback
    (AffineSpace.isPullback_map (n := n) ((𝔸(m; S)).fromSpecStalk (genericPoint _)))
    (genericPoint 𝔸(n; 𝔸(m; S))) c (by rw [hη, hc])
  have hgen : IsGenericPoint p Set.univ := by
    refine Langlands.AlgebraicGeometry.SchemeFiberGeometry.isGenericPoint_of_isInducing (Scheme.Hom.isEmbedding φ).isInducing ?_
    rw [show φ p = genericPoint 𝔸(n; 𝔸(m; S)) from hp]
    exact genericPoint_spec _
  have hφ : φ (genericPoint _) = genericPoint 𝔸(n; 𝔸(m; S)) := by
    rw [(genericPoint_spec 𝔸(n; Spec (𝔸(m; S)).functionField)).eq hgen]
    exact hp
  rw [affineSpaceFunctionFieldToSum, Scheme.Hom.comp_apply, show
    AffineSpace.map n ((𝔸(m; S)).fromSpecStalk (genericPoint _)) (genericPoint _) =
      genericPoint 𝔸(n; 𝔸(m; S)) from hφ]
  exact (isGenericPoint_univ_of_denseRange (Scheme.Hom.continuous _)
    (Scheme.Hom.surjective (affineSpaceSumIso m n S).inv).denseRange
    (genericPoint_spec _)).eq (genericPoint_spec _)

/-- **Iterated rational function fields.** The function field of `𝔸(m ⊕ n; S)`
is isomorphic to the function field of `𝔸(n; Spec K)`, where `K` is the function
field of `𝔸(m; S)`. -/
def functionFieldAffineSpaceSumIso :
    (𝔸(m ⊕ n; S)).functionField ≅ (𝔸(n; Spec (𝔸(m; S)).functionField)).functionField :=
  have := isIso_functionFieldMap (affineSpaceFunctionFieldToSum m n S)
    (affineSpaceFunctionFieldToSum_genericPoint m n S)
  asIso (functionFieldMap _ (affineSpaceFunctionFieldToSum_genericPoint m n S))

@[reassoc]
theorem SpecMap_functionFieldAffineSpaceSumIso_hom_fromSpecStalk :
    Spec.map (functionFieldAffineSpaceSumIso m n S).hom ≫
        (𝔸(m ⊕ n; S)).fromSpecStalk (genericPoint _) =
      (𝔸(n; Spec (𝔸(m; S)).functionField)).fromSpecStalk (genericPoint _) ≫
        affineSpaceFunctionFieldToSum m n S :=
  SpecMap_functionFieldMap_fromSpecStalk _ (affineSpaceFunctionFieldToSum_genericPoint m n S)

/-- **Iterated rational function fields over a base.** Over an integral scheme
`S`, let `K` be the function field of `𝔸(m; S)`. The spectrum of the function
field of `𝔸(n; Spec K)`, over `S` through `Spec K ⟶ 𝔸(m; S) ⟶ S`, is isomorphic
over `S` to the spectrum of the function field of `𝔸(m ⊕ n; S)`. -/
def iteratedFunctionFieldOverIso :
    Over.mk ((𝔸(n; Spec (𝔸(m; S)).functionField)).fromSpecStalk (genericPoint _) ≫
        𝔸(n; Spec (𝔸(m; S)).functionField) ↘ Spec (𝔸(m; S)).functionField ≫
        (𝔸(m; S)).fromSpecStalk (genericPoint _) ≫ 𝔸(m; S) ↘ S) ≅
      Over.mk ((𝔸(m ⊕ n; S)).fromSpecStalk (genericPoint _) ≫ 𝔸(m ⊕ n; S) ↘ S) :=
  Over.isoMk (asIso (Spec.map (functionFieldAffineSpaceSumIso m n S).hom)) (by
    simp only [Over.mk_hom, asIso_hom]
    rw [SpecMap_functionFieldAffineSpaceSumIso_hom_fromSpecStalk_assoc,
      affineSpaceFunctionFieldToSum_over])

end IteratedFunctionField

end Langlands.AlgebraicGeometry.PointTopology
