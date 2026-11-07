import Langlands.GroupScheme.MatrixRepresentation.FrobeniusConvolutionAction
import Langlands.GroupScheme.Lie.SubgroupEqualityProof

/-! # Functoriality of actual Frobenius quotients and distributions -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct Matrix

namespace Langlands.GroupScheme.MatrixRepresentation.FrobeniusFunctoriality

open FrobeniusCoordinateModel FrobeniusOrderedDistributions FrobeniusOriginUniversality
open FrobeniusDistributionAlgebra FrobeniusConvolutionAction

variable {k : Type u} [Field k]
    {G H J : GroupScheme (Spec (.of k))}
    [IsAffineHom G.X.hom] [IsAffineHom H.X.hom] [IsAffineHom J.X.hom]
    (p : ℕ) [ExpChar k p] (r : ℕ)

omit [ExpChar k p] in
/-- Every actual group homomorphism preserves intrinsic origin points. -/
theorem isOriginPoint_comp_hom (f : G ⟶ H) (A : CommAlgCat.{u} k)
    {g : G.affinePoints A} (hg : IsOriginPoint p r A g) :
    IsOriginPoint p r A (g ≫ f.hom.hom) := by
  intro a ha
  rw [Lie.pointCoordinates_comp_hom, AlgHom.comp_apply]
  apply hg
  change Lie.coordinateOrigin G (Lie.restrictionMap f a) = 0
  rw [← AlgHom.comp_apply, Lie.coordinateOrigin_comp_restrictionMap]
  exact ha

/-- Pull back along the original homomorphism on the actual Frobenius quotients. -/
def quotientPullback (f : G ⟶ H) :
    quotientAlgebra H p r →ₐ[k] quotientAlgebra G p r :=
  pointLift p r (quotientAlgebra G p r) (quotientPoint G p r ≫ f.hom.hom)
    (isOriginPoint_comp_hom p r f _ (isOriginPoint_quotientPoint p r))

@[simp]
theorem quotientPullback_quotientMap (f : G ⟶ H) (a : CharacterUnits.Coord H) :
    quotientPullback p r f (quotientMap H p r a) =
      quotientMap G p r (Lie.restrictionMap f a) := by
  rw [quotientPullback, pointLift_quotientMap, Lie.pointCoordinates_comp_hom,
    AlgHom.comp_apply]
  exact AlgHom.congr_fun (pointCoordinates_quotientPoint G p r) _

/-- The genuine quotient point maps to the original homomorphism's value. -/
theorem affineMap_quotientPullback (f : G ⟶ H) :
    Lie.affineMap H (quotientPullback p r f) (quotientPoint H p r) =
      quotientPoint G p r ≫ f.hom.hom :=
  affineMap_pointLift p r _ _ _

omit [ExpChar k p] in
@[simp]
theorem restrictionMap_id :
    Lie.restrictionMap (𝟙 G) = AlgHom.id k (CharacterUnits.Coord G) := by
  simp [Lie.restrictionMap, Lie.pointCoordinates]
  rfl

omit [ExpChar k p] in
theorem restrictionMap_comp (f : G ⟶ H) (g : H ⟶ J) :
    Lie.restrictionMap (f ≫ g) =
      (Lie.restrictionMap f).comp (Lie.restrictionMap g) := by
  change Lie.pointCoordinates J ((Lie.coordinateIso G).hom ≫ (f ≫ g).hom.hom) = _
  rw [Grp.comp_hom_hom, ← Category.assoc, Lie.pointCoordinates_comp_hom]
  rfl

@[simp]
theorem quotientPullback_id :
    quotientPullback p r (𝟙 G) = AlgHom.id k (quotientAlgebra G p r) := by
  apply Ideal.Quotient.algHom_ext k
  ext a
  change quotientPullback p r (𝟙 G) (quotientMap G p r a) = quotientMap G p r a
  rw [quotientPullback_quotientMap, restrictionMap_id, AlgHom.id_apply]

theorem quotientPullback_comp (f : G ⟶ H) (g : H ⟶ J) :
    quotientPullback p r (f ≫ g) =
      (quotientPullback p r f).comp (quotientPullback p r g) := by
  apply Ideal.Quotient.algHom_ext k
  ext a
  change quotientPullback p r (f ≫ g) (quotientMap J p r a) =
    quotientPullback p r f (quotientPullback p r g (quotientMap J p r a))
  rw [quotientPullback_quotientMap, quotientPullback_quotientMap,
    quotientPullback_quotientMap, restrictionMap_comp, AlgHom.comp_apply]

private theorem pt_comp_restrictionMap (f : G ⟶ H)
    {A : Type u} [CommRing A] [Algebra k A]
    (h : CharacterUnits.Coord G →ₐ[k] A) :
    TorusUnipotence.pt H (h.comp (Lie.restrictionMap f)) =
      TorusUnipotence.pt G h ≫ f.hom.hom := by
  apply (Lie.pointCoordinates H).injective
  rw [TorusUnipotence.pt, Equiv.apply_symm_apply,
    Lie.pointCoordinates_comp_hom, TorusUnipotence.pt, Equiv.apply_symm_apply]

/-- The actual coordinate pullback intertwines the original coproducts. -/
theorem comul_restrictionMap (f : G ⟶ H) :
    (CharacterUnits.comul G).comp (Lie.restrictionMap f) =
      (Algebra.TensorProduct.map (Lie.restrictionMap f) (Lie.restrictionMap f)).comp
        (CharacterUnits.comul H) := by
  apply TorusUnipotence.pt_injective H
  rw [pt_comp_restrictionMap, TorusUnipotence.pt_comul, Lie.mul_comp_hom,
    TorusUnipotence.pt_comp_comul H _
      (Algebra.TensorProduct.map_comp_includeLeft _ _)
      (Algebra.TensorProduct.map_comp_includeRight _ _),
    pt_comp_restrictionMap, pt_comp_restrictionMap]

/-- Pullback preserves the inherited quotient counit. -/
theorem counit_quotientPullback (f : G ⟶ H) (a : quotientAlgebra H p r) :
  Coalgebra.counit (R := k) (quotientPullback p r f a) =
    Coalgebra.counit (R := k) a := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  change Coalgebra.counit (R := k)
    (quotientPullback p r f (quotientMap H p r a)) =
    Coalgebra.counit (R := k) (quotientMap H p r a)
  rw [quotientPullback_quotientMap, counit_quotientMap, counit_quotientMap]
  exact AlgHom.congr_fun (Lie.coordinateOrigin_comp_restrictionMap f) a

/-- Pullback preserves the inherited quotient coproduct. -/
theorem comul_quotientPullback (f : G ⟶ H) (a : quotientAlgebra H p r) :
  Coalgebra.comul (R := k) (quotientPullback p r f a) =
    Algebra.TensorProduct.map (quotientPullback p r f) (quotientPullback p r f)
      (Coalgebra.comul (R := k) a) := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  change Coalgebra.comul (R := k)
    (quotientPullback p r f (quotientMap H p r a)) =
    Algebra.TensorProduct.map (quotientPullback p r f) (quotientPullback p r f)
      (Coalgebra.comul (R := k) (quotientMap H p r a))
  rw [quotientPullback_quotientMap, comul_quotientMap, comul_quotientMap]
  have h := AlgHom.congr_fun (comul_restrictionMap f) a
  change CharacterUnits.comul G (Lie.restrictionMap f a) = _ at h
  rw [h]
  have hleft : (quotientMap G p r).comp (Lie.restrictionMap f) =
      (quotientPullback p r f).comp (quotientMap H p r) := by
    ext b
    exact (quotientPullback_quotientMap p r f b).symm
  change ((Algebra.TensorProduct.map (quotientMap G p r) (quotientMap G p r)).comp
      (Algebra.TensorProduct.map (Lie.restrictionMap f) (Lie.restrictionMap f)))
      (CharacterUnits.comul H a) =
    ((Algebra.TensorProduct.map (quotientPullback p r f) (quotientPullback p r f)).comp
      (Algebra.TensorProduct.map (quotientMap H p r) (quotientMap H p r)))
      (CharacterUnits.comul H a)
  rw [← Algebra.TensorProduct.map_comp, hleft, Algebra.TensorProduct.map_comp]

/-- The actual Frobenius quotient pullback is a bialgebra homomorphism. -/
def quotientBialgHom (f : G ⟶ H) :
    quotientAlgebra H p r →ₐc[k] quotientAlgebra G p r :=
  BialgHom.ofAlgHom (quotientPullback p r f)
    (by ext a; exact counit_quotientPullback p r f a)
    (by ext a; exact (comul_quotientPullback p r f a).symm)

/-- Pushforward of the full convolution dual by actual group homomorphisms. -/
def distributionPushforward (f : G ⟶ H) :
    DistributionAlgebra (G := G) p r →ₐ[k] DistributionAlgebra (G := H) p r :=
  AlgHom.ofLinearMap
    { toFun := fun ell => WithConv.toConv
        (ell.ofConv.comp (quotientPullback p r f).toLinearMap)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    (by
      apply WithConv.ext
      ext a
      change (1 : DistributionAlgebra (G := G) p r)
        (quotientPullback p r f a) = (1 : DistributionAlgebra (G := H) p r) a
      simp only [LinearMap.convOne_apply, counit_quotientPullback])
    (by
      intro ell ell2
      apply WithConv.ext
      exact LinearMap.convMul_comp_coalgHom_distrib ell ell2
        (quotientBialgHom p r f).toCoalgHom)

@[simp]
theorem distributionPushforward_apply (f : G ⟶ H)
    (ell : DistributionAlgebra (G := G) p r) (a : quotientAlgebra H p r) :
    distributionPushforward p r f ell a = ell (quotientPullback p r f a) := rfl

@[simp]
theorem distributionPushforward_id :
    distributionPushforward p r (𝟙 G) =
      AlgHom.id k (DistributionAlgebra (G := G) p r) := by
  ext ell a
  simp only [distributionPushforward_apply, quotientPullback_id, AlgHom.id_apply]

theorem distributionPushforward_comp (f : G ⟶ H) (g : H ⟶ J) :
    distributionPushforward p r (f ≫ g) =
      (distributionPushforward p r g).comp (distributionPushforward p r f) := by
  ext ell a
  simp only [AlgHom.comp_apply, distributionPushforward_apply, quotientPullback_comp]

variable {n : Type} [Fintype n] [DecidableEq n] (ρ : MatrixRepresentation H n)

/-- Restriction uses the pullback of the original quotient coefficient matrix. -/
theorem coefficientMatrix_restrict (f : G ⟶ H) (i j : n) :
    coefficientMatrix p r (ρ.restrict f) i j =
      quotientPullback p r f (coefficientMatrix p r ρ i j) := by
  have h := ρ.affineMatrix_naturality
    (CommAlgCat.ofHom (quotientPullback p r f)) (quotientPoint H p r)
  change ρ.affineMatrix (quotientAlgebra G p r)
    (Lie.affineMap H (quotientPullback p r f) (quotientPoint H p r)) = _ at h
  rw [affineMap_quotientPullback] at h
  exact congrArg (fun M : Matrix.GeneralLinearGroup n (quotientAlgebra G p r) =>
    (M : Matrix n n (quotientAlgebra G p r)) i j)
    ((affineMatrix_restrict ρ f _ _).trans h)

/-- Pushforward acts on the original representation exactly as restriction. -/
theorem actionAlgHom_distributionPushforward (f : G ⟶ H)
    (ell : DistributionAlgebra (G := G) p r) :
    actionAlgHom p r ρ (distributionPushforward p r f ell) =
      actionAlgHom p r (ρ.restrict f) ell := by
  have hM : (coefficientMatrix p r ρ).map (distributionPushforward p r f ell).ofConv =
      (coefficientMatrix p r (ρ.restrict f)).map ell.ofConv := by
    ext i j
    change ell (quotientPullback p r f (coefficientMatrix p r ρ i j)) =
      ell (coefficientMatrix p r (ρ.restrict f) i j)
    rw [coefficientMatrix_restrict]
  change Matrix.toLin' ((coefficientMatrix p r ρ).map
      (distributionPushforward p r f ell).ofConv) =
    Matrix.toLin' ((coefficientMatrix p r (ρ.restrict f)).map ell.ofConv)
  rw [hM]

end Langlands.GroupScheme.MatrixRepresentation.FrobeniusFunctoriality
