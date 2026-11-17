import Langlands.GroupScheme.Torus.UnitsProductDecompositionStatement
import Langlands.AbelianScheme.SeparatingLineBundle.RationalPoints
import Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_geometricallyIntegral_of_isAlgClosed

/-! # Geometric reduction of the product-units theorem to affine schemes -/

noncomputable section
universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.UnitsProduct

section Cartesian
variable {C : Type*} [Category* C] [CartesianMonoidalCategory C]
  [BraidedCategory C] {X Y G : C} [CommGrpObj G]

/-- A split function is determined by its restrictions to two axes. -/
theorem normalized_of_split (p : 𝟙_ C ⟶ X) (q : 𝟙_ C ⟶ Y)
    (f : X ⊗ Y ⟶ G) (a : X ⟶ G) (b : Y ⟶ G)
    (hf : f = (fst X Y ≫ a) * (snd X Y ≫ b)) :
    f = (fst X Y ≫ lift (𝟙 X) (toUnit X ≫ q) ≫ f) *
      (snd X Y ≫ lift (toUnit Y ≫ p) (𝟙 Y) ≫ f) *
      (toUnit (X ⊗ Y) ≫ lift p q ≫ f)⁻¹ := by
  subst f
  simp only [MonObj.comp_mul, Category.assoc, lift_fst_assoc, lift_snd_assoc,
    Category.id_comp]
  simp only [← Category.assoc, comp_toUnit]
  simp [mul_inv_rev, mul_assoc, mul_comm, mul_left_comm]

/-- Splitting on a product of pointed subobjects extends when restriction is injective. -/
theorem split_of_restriction {U V : C} (i : U ⟶ X) (j : V ⟶ Y)
    (p : 𝟙_ C ⟶ U) (q : 𝟙_ C ⟶ V) (f : X ⊗ Y ⟶ G)
    (a : U ⟶ G) (b : V ⟶ G)
    (hf : (i ⊗ₘ j) ≫ f = (fst U V ≫ a) * (snd U V ≫ b))
    (hinj : Function.Injective (fun g : X ⊗ Y ⟶ G ↦ (i ⊗ₘ j) ≫ g)) :
    ∃ (a' : X ⟶ G) (b' : Y ⟶ G), f = (fst X Y ≫ a') * (snd X Y ≫ b') := by
  refine ⟨lift (𝟙 X) (toUnit X ≫ q ≫ j) ≫ f,
    (lift (toUnit Y ≫ p ≫ i) (𝟙 Y) ≫ f) *
      (toUnit Y ≫ lift (p ≫ i) (q ≫ j) ≫ f)⁻¹, hinj ?_⟩
  simpa [MonObj.comp_mul, GrpObj.comp_inv, Category.assoc, comp_lift_assoc,
    lift_map_assoc, mul_assoc] using normalized_of_split p q ((i ⊗ₘ j) ≫ f) a b hf

end Cartesian

/-- The affine case needed for the geometric reduction. -/
def AffineSplitting : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k]
    (X Y : Over (Spec (CommRingCat.of k))) [IsAffine X.left] [IsAffine Y.left]
    [IsIntegral X.left] [IsIntegral Y.left]
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⊗ Y ⟶ (Gm (Spec (CommRingCat.of k))).X),
    ∃ (a : X ⟶ (Gm (Spec (CommRingCat.of k))).X)
      (b : Y ⟶ (Gm (Spec (CommRingCat.of k))).X),
      f = (fst X Y ≫ a) * (snd X Y ≫ b)

/-- An integral scheme locally of finite type has a nonempty pointed affine chart. -/
theorem exists_pointed_affine_chart (k : Type u) [Field k] [IsAlgClosed k]
    (X : Over (Spec (CommRingCat.of k))) [IsIntegral X.left] [LocallyOfFiniteType X.hom] :
    ∃ (U : Over (Spec (CommRingCat.of k))) (i : U ⟶ X),
      IsAffine U.left ∧ IsIntegral U.left ∧ LocallyOfFiniteType U.hom ∧
        IsOpenImmersion i.left ∧ Nonempty (𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ U) := by
  classical
  obtain ⟨x⟩ := (inferInstance : Nonempty X.left)
  let t := X.left.affineCover.idx x
  obtain ⟨z, _⟩ := X.left.affineCover.covers x
  let U : Over (Spec (CommRingCat.of k)) :=
    Over.mk (X.left.affineCover.f t ≫ X.hom)
  let i : U ⟶ X := Over.homMk (X.left.affineCover.f t)
  have : Nonempty U.left := ⟨z⟩
  have : IsAffine U.left := by
    change IsAffine (X.left.affineCover.X t)
    infer_instance
  have : IsOpenImmersion i.left := by
    change IsOpenImmersion (X.left.affineCover.f t)
    infer_instance
  have : IsIntegral U.left := isIntegral_of_isOpenImmersion i.left
  have : LocallyOfFiniteType U.hom := by
    change LocallyOfFiniteType (X.left.affineCover.f t ≫ X.hom)
    infer_instance
  obtain ⟨p, hp, _⟩ :=
    SeparatingLineBundle.exists_rationalPoint_mem_of_isOpen U.hom
      (fun _ : Fin 0 ↦ Set.univ) (by simp) (by simp)
  exact ⟨U, i, inferInstance, inferInstance, inferInstance, inferInstance,
    ⟨Over.homMk p hp⟩⟩

/-- The affine case implies the full product-units statement. -/
theorem geometric_reduction (hAffine : AffineSplitting.{u}) :
    UnitsProductDecompositionStatement.{u} := by
  intro k _ _ X Y hftX _ _ hredX hirrX hftY _ _ hredY hirrY f
  have := hftX
  have := hftY
  have : IsIntegral X.left :=
    (isIntegral_iff_irreducibleSpace_and_isReduced X.left).mpr ⟨hirrX, hredX⟩
  have : IsIntegral Y.left :=
    (isIntegral_iff_irreducibleSpace_and_isReduced Y.left).mpr ⟨hirrY, hredY⟩
  obtain ⟨U, i, hUa, hUi, hUf, hi, ⟨p⟩⟩ := exists_pointed_affine_chart k X
  obtain ⟨V, j, hVa, hVi, hVf, hj, ⟨q⟩⟩ := exists_pointed_affine_chart k Y
  have := hUa
  have := hUi
  have := hUf
  have := hi
  have := hVa
  have := hVi
  have := hVf
  have := hj
  obtain ⟨a, b, hab⟩ := hAffine k U V ((i ⊗ₘ j) ≫ f)
  apply split_of_restriction i j p q f a b hab
  have : GeometricallyIntegral X.hom :=
    P2MW.S_AlgebraicGeometry_geometricallyIntegral_of_isAlgClosed.solution X.hom
  have : IsLocallyNoetherian Y.left := LocallyOfFiniteType.isLocallyNoetherian Y.hom
  have : IsIntegral (X ⊗ Y).left := by
    change IsIntegral (pullback X.hom Y.hom)
    infer_instance
  have : IsOpenImmersion (i ⊗ₘ j).left := by
    rw [Over.tensorHom_left]
    infer_instance
  have : Nonempty (U ⊗ V).left :=
    ⟨(lift p q).left (IsLocalRing.closedPoint k)⟩
  have : IsDominant (i ⊗ₘ j).left :=
    ⟨((i ⊗ₘ j).left.isOpenEmbedding.isOpen_range).dense (Set.range_nonempty _)⟩
  have : IsSeparated (Gm (Spec (CommRingCat.of k))).X.hom := by
    change IsSeparated (pullback.snd
      (Spec.map (CommRingCat.ofHom (LaurentPolynomial.C (R := ULift.{u} ℤ))))
      (Gm.toSpecZ (Spec (CommRingCat.of k))))
    infer_instance
  intro g h hgh
  apply Over.OverMorphism.ext
  exact ext_of_isDominant_of_isSeparated (Gm (Spec (CommRingCat.of k))).X.hom
    (g.w.trans h.w.symm) (i ⊗ₘ j).left (congrArg (fun t ↦ t.left) hgh)

end Langlands.GroupScheme.UnitsProduct
