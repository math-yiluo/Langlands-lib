import Langlands.GroupScheme.Torus.WeilRestrictionNormSplit
import Langlands.GroupScheme.Torus.WeilRestrictionSeparable

/-! # The actual norm-one Weil restriction -/

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4000

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.WeilGm

private def kernelModelEquiv {M N M' N' : Type*}
    [Group M] [Group N] [Group M'] [Group N']
    (f : M →* N) (f' : M' →* N') (eM : M ≃* M') (eN : N ≃* N')
    (h : ∀ x, eN (f x) = f' (eM x)) : f.ker ≃* f'.ker where
  toFun x := ⟨eM x, by
    change f' (eM x.val) = 1
    rw [← h, x.property, map_one]⟩
  invFun x := ⟨eM.symm x, by
    apply eN.injective
    rw [h, eM.apply_symm_apply, x.property, map_one]⟩
  left_inv x := Subtype.ext (eM.symm_apply_apply x)
  right_inv x := Subtype.ext (eM.apply_symm_apply x)
  map_mul' x y := Subtype.ext (eM.map_mul x y)

section ProductOne

variable (I : Type u) [Fintype I] (M : Type v) [CommGroup M]

/-- Multiplication of the coordinates of a finite family. -/
def coordinateProduct : (I → M) →* M where
  toFun x := ∏ i, x i
  map_one' := by simp
  map_mul' x y := Finset.prod_mul_distrib

/-- Families of units, or of elements of any commutative group, with product one. -/
abbrev productOne := (coordinateProduct I M).ker

/-- Deleting one coordinate identifies product-one families with unrestricted
families on the remaining indices. The missing coordinate is the inverse product. -/
def productOneDropEquiv [DecidableEq I] (i₀ : I) :
    productOne I M ≃* ({i : I // i ≠ i₀} → M) where
  toFun x i := x.val i
  invFun x := ⟨fun i => if h : i = i₀ then (∏ j, x j)⁻¹ else x ⟨i, h⟩, by
    change (∏ i, if h : i = i₀ then (∏ j, x j)⁻¹ else x ⟨i, h⟩) = 1
    rw [Fintype.prod_eq_mul_prod_subtype_ne _ i₀]
    have hrest : (fun j : {i : I // i ≠ i₀} =>
        if h : j.val = i₀ then (∏ j, x j)⁻¹ else x ⟨j.val, h⟩) = x := by
      funext j
      exact dite_eq_right j.property
    simp only [dite_eq_left, hrest, inv_mul_cancel]⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    by_cases hi : i = i₀
    · subst i
      simp only [dite_eq_left]
      apply Eq.symm
      apply eq_inv_iff_mul_eq_one.mpr
      rw [← Fintype.prod_eq_mul_prod_subtype_ne]
      exact x.property
    · simp only [dite_eq_right hi]
  right_inv x := by
    funext i
    simp only [dite_eq_right i.property]
  map_mul' x y := rfl

@[simp] theorem productOneDropEquiv_apply [DecidableEq I] (i₀ : I)
    (x : productOne I M) (i : {i : I // i ≠ i₀}) :
    productOneDropEquiv I M i₀ x i = x.val i := rfl

end ProductOne

section Kernel

variable (A : CommRingCat.{u}) (B : Type u) [CommRing B] [Algebra A B]
  [Module.Finite A B] [Module.Free A B]

/-- The norm-one group scheme is the actual group-scheme kernel of the norm. -/
def normOne : GroupScheme (Spec A) := kernel (norm A B)

/-- The same actual kernel with its inherited commutativity. -/
abbrev normOneCommGroupScheme : CommGroupScheme (Spec A) where
  toGrp := normOne A B
  comm := kernel_isCommMonObj (norm A B)

/-- The canonical inclusion of the actual norm-one subgroup scheme. -/
def normOneι : normOne A B ⟶ groupScheme A B := kernelι (norm A B)

/-- The canonical inclusion in the commutative group-scheme category. -/
def normOneιHom : normOneCommGroupScheme A B ⟶ commGroupScheme A B :=
  Additive.ofMul (normOneι A B)

/-- On every test scheme, the actual norm-one points are precisely tensor units
whose determinant norm is one. -/
def normOnePointsEquiv (T : Over (Spec A)) :
    (T ⟶ (normOne A B).X) ≃*
      (Langlands.Algebra.tensorNormUnits A B ((algΓ A).obj T).unop).ker :=
  (kernelPointsEquiv (norm A B) T).trans
    (kernelModelEquiv _ _ (pointsEquiv A B T) (Gm.pointsEquiv (Spec A) T)
      (norm_points A B T))

@[simp] theorem normOnePointsEquiv_val (T : Over (Spec A))
    (x : T ⟶ (normOne A B).X) :
    (normOnePointsEquiv A B T x).val =
      pointsEquiv A B T (x ≫ (normOneι A B).hom.hom) := rfl

/-- Restriction of tensor norm-one units along any test morphism. -/
def normOneUnitsRestrict {T T' : Over (Spec A)} (a : T' ⟶ T) :
    (Langlands.Algebra.tensorNormUnits A B ((algΓ A).obj T).unop).ker →*
      (Langlands.Algebra.tensorNormUnits A B ((algΓ A).obj T').unop).ker where
  toFun x := ⟨Units.map
    (Algebra.TensorProduct.lTensor (S := B) B ((algΓ A).map a).unop.hom).toMonoidHom x, by
      change Langlands.Algebra.tensorNormUnits A B _
        (Units.map _ x.val) = 1
      rw [Langlands.Algebra.tensorNormUnits_naturality, x.property, map_one]⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' x y := Subtype.ext (map_mul _ x.val y.val)

/-- The norm-one point identification is natural on all test schemes. -/
theorem normOnePointsEquiv_naturality {T T' : Over (Spec A)} (a : T' ⟶ T)
    (x : T ⟶ (normOne A B).X) :
    normOnePointsEquiv A B T' (a ≫ x) =
      normOneUnitsRestrict A B a (normOnePointsEquiv A B T x) := by
  apply Subtype.ext
  change pointsEquiv A B T' ((a ≫ x) ≫ (normOneι A B).hom.hom) = _
  rw [Category.assoc, pointsEquiv_naturality]
  rfl

/-- The inclusion followed by the norm is the zero morphism of commutative
group schemes, meaning the constant unit as a group homomorphism. -/
theorem normOneιHom_comp_normHom : normOneιHom A B ≫ normHom A B = 0 := by
  apply Additive.toMul.injective
  apply hom_ext_points
  intro T x
  change (x ≫ (normOneι A B).hom.hom) ≫ (norm A B).hom.hom = x ≫ (1 : normOne A B ⟶ _).hom.hom
  rw [show x ≫ (1 : normOne A B ⟶ (Gm (Spec A)).toGrp).hom.hom = 1 from
    CategoryTheory.MonObj.comp_one x]
  exact (kernelPointsEquiv (norm A B) T x).property

end Kernel

section Decomposition

variable (A A' : CommRingCat.{u}) [Algebra A A'] (B : Type u) [CommRing B]
  [Algebra A B] [Module.Finite A B] [Module.Free A B]
  (I : Type u) [Fintype I] [DecidableEq I] (e : A' ⊗[A] B ≃ₐ[A'] (I → A'))

/-- In splitting coordinates, the actual base-changed norm-one kernel has
product-one coordinates on every test scheme. -/
def normOneDecompositionPointsEquiv (T : Over (Spec A')) :
    (T ⟶ ((GroupScheme.baseChange (baseMap A A')).obj (normOne A B)).X) ≃*
      productOne I (Γ(T.left, ⊤))ˣ :=
  (isoPointsEquiv (kernelBaseChangeIso (baseMap A A') (norm A B)) T).trans
    ((kernelPointsEquiv ((GroupScheme.baseChange (baseMap A A')).map (norm A B)) T).trans
      (kernelModelEquiv _ _ (decompositionPointsEquiv A A' B I e T)
        (Gm.baseChangeUnitsEquiv (baseMap A A') T) (by
          intro x
          change T ⟶ ((CommGroupScheme.baseChange (baseMap A A')).obj
            (commGroupScheme A B)).X at x
          have h := decompositionNormHom_points A A' B I e T x
          rw [decompositionNormHom, characterLattice.baseChange_apply, comp_groupHom_comp] at h
          change Gm.pointsEquiv (Spec A') T
            ((x ≫ ((GroupScheme.baseChange (baseMap A A')).map (norm A B)).hom.hom) ≫
              (Gm.baseChangeIso (baseMap A A')).hom.hom.hom) = _ at h
          rwa [Gm.pointsEquiv_baseChangeIso_hom] at h)))

set_option maxHeartbeats 800000 in
/-- The product-one coordinates are the existing Weil-restriction coordinates
of the image under the actual kernel inclusion. -/
theorem normOneDecompositionPointsEquiv_val (T : Over (Spec A'))
    (x : T ⟶ ((GroupScheme.baseChange (baseMap A A')).obj (normOne A B)).X) :
    (normOneDecompositionPointsEquiv A A' B I e T x).val =
      decompositionPointsEquiv A A' B I e T
        (x ≫ ((GroupScheme.baseChange (baseMap A A')).map (normOneι A B)).hom.hom) := by
  change decompositionPointsEquiv A A' B I e T
    ((x ≫ (kernelBaseChangeIso (baseMap A A') (norm A B)).hom.hom.hom) ≫
      (kernelι ((GroupScheme.baseChange (baseMap A A')).map (norm A B))).hom.hom) = _
  congr 1
  rw [Category.assoc]
  congr 1
  exact congrArg (fun f => f.hom.hom) (kernelBaseChangeIso_hom_ι (baseMap A A') (norm A B))

/-- After deleting a chosen coordinate, norm-one points are unrestricted
families of units on the remaining coordinates. -/
def normOneSplitPointsEquiv (i₀ : I) (T : Over (Spec A')) :
    (T ⟶ ((GroupScheme.baseChange (baseMap A A')).obj (normOne A B)).X) ≃*
      ({i : I // i ≠ i₀} → (Γ(T.left, ⊤))ˣ) :=
  (normOneDecompositionPointsEquiv A A' B I e T).trans
    (productOneDropEquiv I (Γ(T.left, ⊤))ˣ i₀)

/-- The deleted-coordinate point model is natural on all test schemes. -/
theorem normOneSplitPointsEquiv_naturality (i₀ : I)
    {T T' : Over (Spec A')} (a : T' ⟶ T)
    (x : T ⟶ ((GroupScheme.baseChange (baseMap A A')).obj (normOne A B)).X) :
    normOneSplitPointsEquiv A A' B I e i₀ T' (a ≫ x) =
      splitTorus.unitsRestrict {i : I // i ≠ i₀} a
        (normOneSplitPointsEquiv A A' B I e i₀ T x) := by
  funext i
  change (normOneDecompositionPointsEquiv A A' B I e T' (a ≫ x)).val i.val =
    Units.map a.left.appTop.hom.toMonoidHom
      ((normOneDecompositionPointsEquiv A A' B I e T x).val i.val)
  rw [normOneDecompositionPointsEquiv_val, normOneDecompositionPointsEquiv_val,
    Category.assoc, decompositionPointsEquiv_naturality]
  rfl

/-- An algebra decomposition splits the actual norm-one group scheme into the
split torus indexed by all but one chosen coordinate. -/
def normOneDecompositionIso (i₀ : I) :
    (GroupScheme.baseChange (baseMap A A')).obj (normOne A B) ≅
      splitTorus (Spec A') {i : I // i ≠ i₀} :=
  isoOfPointModels (fun T : Over (Spec A') => {i : I // i ≠ i₀} → (Γ(T.left, ⊤))ˣ)
    (fun a => splitTorus.unitsRestrict {i : I // i ≠ i₀} a)
    (normOneSplitPointsEquiv A A' B I e i₀)
    (splitTorus.pointsEquiv {i : I // i ≠ i₀})
    (fun a x => normOneSplitPointsEquiv_naturality A A' B I e i₀ a x)
    (fun a y => splitTorus.pointsEquiv_naturality {i : I // i ≠ i₀} a y)

/-- The actual splitting retains exactly the chosen remaining coordinates
of the included Weil-restriction point. -/
theorem normOneDecompositionIso_hom_points (i₀ : I) (T : Over (Spec A'))
    (x : T ⟶ ((GroupScheme.baseChange (baseMap A A')).obj (normOne A B)).X)
    (i : {i : I // i ≠ i₀}) :
    splitTorus.pointsEquiv {i : I // i ≠ i₀} T
        (x ≫ (normOneDecompositionIso A A' B I e i₀).hom.hom.hom) i =
      decompositionPointsEquiv A A' B I e T
        (x ≫ ((GroupScheme.baseChange (baseMap A A')).map (normOneι A B)).hom.hom) i := by
  rw [normOneDecompositionIso, isoOfPointModels_hom
    (hH := fun a y => splitTorus.pointsEquiv_naturality {i : I // i ≠ i₀} a y)]
  change (normOneDecompositionPointsEquiv A A' B I e T x).val i.val = _
  rw [normOneDecompositionPointsEquiv_val]

/-- The same actual splitting in the commutative group-scheme category. -/
def normOneDecompositionCommIso (i₀ : I) :
    (CommGroupScheme.baseChange (baseMap A A')).obj (normOneCommGroupScheme A B) ≅
      splitTorus.commGroupScheme (Spec A') {i : I // i ≠ i₀} where
  hom := Additive.ofMul (normOneDecompositionIso A A' B I e i₀).hom
  inv := Additive.ofMul (normOneDecompositionIso A A' B I e i₀).inv
  hom_inv_id := congrArg Additive.ofMul (normOneDecompositionIso A A' B I e i₀).hom_inv_id
  inv_hom_id := congrArg Additive.ofMul (normOneDecompositionIso A A' B I e i₀).inv_hom_id

end Decomposition

section Separable

variable (k K Ω : Type u) [Field k] [Field K] [Field Ω]
  [Algebra k K] [Algebra k Ω] [FiniteDimensional k K] [Algebra.IsSeparable k K]
  (hsplit : ∀ x : K, ((minpoly k x).map (algebraMap k Ω)).Splits)

/-- The finite-separable norm-one group splits in canonical embedding
coordinates after deleting any one chosen embedding. -/
def normOneSeparableEmbeddingIso (τ₀ : K →ₐ[k] Ω) :
    (GroupScheme.baseChange (algebraBaseMap k Ω)).obj (normOne (CommRingCat.of k) K) ≅
      splitTorus (Spec (CommRingCat.of Ω)) {τ : K →ₐ[k] Ω // τ ≠ τ₀} := by
  classical
  exact normOneDecompositionIso (CommRingCat.of k) (CommRingCat.of Ω) K (K →ₐ[k] Ω)
    (separableEmbeddingDecomposition k K Ω hsplit) τ₀

/-- The finite-separable norm-one splitting in the commutative category. -/
def normOneSeparableEmbeddingCommIso (τ₀ : K →ₐ[k] Ω) :
    (CommGroupScheme.baseChange (algebraBaseMap k Ω)).obj
        (normOneCommGroupScheme (CommRingCat.of k) K) ≅
      splitTorus.commGroupScheme (Spec (CommRingCat.of Ω)) {τ : K →ₐ[k] Ω // τ ≠ τ₀} := by
  classical
  exact normOneDecompositionCommIso (CommRingCat.of k) (CommRingCat.of Ω) K (K →ₐ[k] Ω)
    (separableEmbeddingDecomposition k K Ω hsplit) τ₀

include hsplit in
/-- The norm-one splitting has one fewer multiplicative factor than the extension degree. -/
theorem normOneSeparableEmbedding_card (τ₀ : K →ₐ[k] Ω) :
    Nat.card {τ : K →ₐ[k] Ω // τ ≠ τ₀} = Module.finrank k K - 1 := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl,
    Fintype.card_subtype_eq, separableEmbedding_card k K Ω hsplit]

include hsplit in
/-- Under the splitting hypothesis a finite-separable extension has an embedding. -/
theorem separableEmbedding_nonempty : Nonempty (K →ₐ[k] Ω) := by
  apply Fintype.card_pos_iff.mp
  rw [separableEmbedding_card k K Ω hsplit]
  exact Module.finrank_pos

/-- The actual norm-one kernel for a finite-separable field extension is a torus. -/
theorem normOne_isTorus_of_finite_separable : IsTorus (normOne (CommRingCat.of k) K) := by
  let hsplit := separable_minpoly_splits k K (SeparableClosure k)
  obtain ⟨τ₀⟩ := separableEmbedding_nonempty k K (SeparableClosure k) hsplit
  refine ⟨SeparableClosure k, inferInstance, inferInstance, ?_⟩
  exact ⟨{τ : K →ₐ[k] SeparableClosure k // τ ≠ τ₀}, inferInstance,
    ⟨normOneSeparableEmbeddingIso k K (SeparableClosure k) hsplit τ₀⟩⟩

end Separable

end Langlands.GroupScheme.WeilGm
