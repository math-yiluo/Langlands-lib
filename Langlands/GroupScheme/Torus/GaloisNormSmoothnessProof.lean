import Langlands.GroupScheme.Torus.GaloisNormSmoothness
import Langlands.GroupScheme.Torus.GaloisNormSmoothnessGeometry
import Langlands.GroupScheme.Torus.WeilRestrictionEmbeddings
import Langlands.Algebra.SeparableTensorProof
import Langlands.GroupScheme.Torus.Products
import Langlands.GroupScheme.Torus.SplittingAssembly
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped TensorProduct CategoryTheory.MonObj BigOperators

namespace Langlands.GroupScheme.GaloisNormSmoothnessProof

set_option backward.isDefEq.respectTransparency false

section AffineYoneda
variable {k : Type u} [Field k]
variable (G H : GroupScheme (Spec (CommRingCat.of k)))
  [IsAffine G.X.left] [IsAffine H.X.left]
variable (F : ∀ A : CommAlgCat.{u} k, G.affinePoints A → H.affinePoints A)
  (hF : ∀ {A B : CommAlgCat.{u} k} (f : A ⟶ B) (x : G.affinePoints A),
    F B (G.affinePointMap f x) = H.affinePointMap f (F A x))

private def mapOfAffinePoints : G.X ⟶ H.X :=
  (CocharacterDatum.coordIso G).inv ≫
    F (CocharacterDatum.coordAlgebra G) (CocharacterDatum.coordIso G).hom

include hF in
omit [IsAffine H.X.left] in
private theorem mapOfAffinePoints_apply (A : CommAlgCat.{u} k) (x : G.affinePoints A) :
    x ≫ mapOfAffinePoints G H F = F A x := by
  let f := CocharacterDatum.coord x
  have hf : G.affinePointMap f (CocharacterDatum.coordIso G).hom = x :=
    CocharacterDatum.map_coord x
  rw [← hf, hF]
  simp only [affinePointMap_apply, mapOfAffinePoints, Category.assoc,
    Iso.hom_inv_id_assoc]

private theorem affine_hom_ext {Y : Over (Spec (CommRingCat.of k))}
    (f g : G.X ⟶ Y)
    (h : ∀ A : CommAlgCat.{u} k, ∀ x : G.affinePoints A, x ≫ f = x ≫ g) : f = g := by
  exact (cancel_epi (CocharacterDatum.coordIso G).hom).mp
    (h (CocharacterDatum.coordAlgebra G) (CocharacterDatum.coordIso G).hom)

private def isoOfAffinePoints
    (e : ∀ A : CommAlgCat.{u} k, G.affinePoints A ≃ H.affinePoints A)
    (he : ∀ {A B : CommAlgCat.{u} k} (f : A ⟶ B) (x : G.affinePoints A),
      e B (G.affinePointMap f x) = H.affinePointMap f (e A x)) : G.X ≅ H.X where
  hom := mapOfAffinePoints G H (fun A => e A)
  inv := mapOfAffinePoints H G (fun A => (e A).symm)
  hom_inv_id := by
    have hi : ∀ {A B : CommAlgCat.{u} k} (f : A ⟶ B) (y : H.affinePoints A),
        (e B).symm (H.affinePointMap f y) = G.affinePointMap f ((e A).symm y) := by
      intro A B f y
      apply (e B).injective
      rw [Equiv.apply_symm_apply, he, Equiv.apply_symm_apply]
    apply affine_hom_ext G
    intro A x
    rw [← Category.assoc, mapOfAffinePoints_apply G H _ he,
      mapOfAffinePoints_apply H G _ hi, Equiv.symm_apply_apply, Category.comp_id]
  inv_hom_id := by
    have hi : ∀ {A B : CommAlgCat.{u} k} (f : A ⟶ B) (y : H.affinePoints A),
        (e B).symm (H.affinePointMap f y) = G.affinePointMap f ((e A).symm y) := by
      intro A B f y
      apply (e B).injective
      rw [Equiv.apply_symm_apply, he, Equiv.apply_symm_apply]
    apply affine_hom_ext H
    intro A x
    rw [← Category.assoc, mapOfAffinePoints_apply H G _ hi,
      mapOfAffinePoints_apply G H _ he, Equiv.apply_symm_apply, Category.comp_id]

end AffineYoneda

section ProductAlgebras
variable {k : Type u} [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
  [IsAffine G.X.left]
variable (I : Type u) (A : Type u) [CommRing A] [Algebra k A]

private def piAlgebraPointsEquiv :
    Lie.AffinePoints G (I → A) ≃ (I → Lie.AffinePoints G A) where
  toFun x i := Lie.affineMap G (Pi.evalAlgHom k (fun _ : I => A) i) x
  invFun x :=
    (algSpec (CommRingCat.of k)).map (CommAlgCat.ofHom
      (AlgHom.pi fun i => (CocharacterDatum.coord (x i)).hom)).op ≫
      (CocharacterDatum.coordIso G).hom
  left_inv x := by
    apply CocharacterDatum.coord_injective
    apply CommAlgCat.hom_ext
    ext c i
    have h := CocharacterDatum.coord_affineMap (G := G)
      (Pi.evalAlgHom k (fun _ : I => A) i) x
    simp only [CocharacterDatum.coord, Category.assoc, Iso.hom_inv_id,
      Category.comp_id, Functor.FullyFaithful.preimage_map, Quiver.Hom.unop_op]
    exact congrArg (fun f => f.hom c) h
  right_inv x := by
    funext i
    apply CocharacterDatum.coord_injective
    rw [CocharacterDatum.coord_affineMap]
    apply CommAlgCat.hom_ext
    ext c
    simp [CocharacterDatum.coord]

end ProductAlgebras

section Tensor
variable (k L : Type u) [Field k] [Field L] [Algebra k L]
  [FiniteDimensional k L] [IsGalois k L]
variable (A : Type u) [CommRing A] [Algebra k A] [Algebra L A] [IsScalarTower k L A]

private def tensorEquiv : L ⊗[k] A ≃ₐ[k] ((L →ₐ[k] L) → A) := by
  let h := Langlands.Algebra.SeparableTensor.embeddingEvaluationStatement k L L
    (fun x => Normal.splits (inferInstance : Normal k L) x)
  let d := WeilGm.decompositionTensorEquiv k L L A (L →ₐ[k] L)
    (WeilGm.embeddingDecomposition k L L h)
  refine AlgEquiv.ofRingEquiv (f := d) ?_
  intro c
  ext τ
  change d ((algebraMap k L c) ⊗ₜ[k] (1 : A)) τ = _
  simp [d, Algebra.smul_def]
  exact (IsScalarTower.algebraMap_apply k L A c).symm

private def evalTensor (τ : L →ₐ[k] L) : L ⊗[k] A →ₐ[k] A :=
  Langlands.Algebra.SeparableTensor.tensorCoordinate (IsScalarTower.toAlgHom k L A) τ

private theorem tensorEquiv_apply (z : L ⊗[k] A) (τ : L →ₐ[k] L) :
    tensorEquiv k L A z τ = evalTensor k L A τ z := by
  exact WeilGm.embeddingDecompositionTensorEquiv_apply k L L _ A z τ

private def tensorPointsEquiv (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffine G.X.left] :
    Lie.AffinePoints G (L ⊗[k] A) ≃ ((L →ₐ[k] L) → Lie.AffinePoints G A) :=
  ({ toFun := Lie.affineMap G (tensorEquiv k L A).toAlgHom
     invFun := Lie.affineMap G (tensorEquiv k L A).symm.toAlgHom
     left_inv := fun x => by rw [← Lie.affineMap_comp]; simp
     right_inv := fun x => by rw [← Lie.affineMap_comp]; simp } :
      Lie.AffinePoints G (L ⊗[k] A) ≃ Lie.AffinePoints G ((L →ₐ[k] L) → A)).trans
    (piAlgebraPointsEquiv G (L →ₐ[k] L) A)

private theorem tensorPointsEquiv_apply (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffine G.X.left] (x : Lie.AffinePoints G (L ⊗[k] A)) (τ : L →ₐ[k] L) :
    tensorPointsEquiv k L A G x τ = Lie.affineMap G (evalTensor k L A τ) x := by
  change Lie.affineMap G (Pi.evalAlgHom k (fun _ : L →ₐ[k] L => A) τ)
    (Lie.affineMap G (tensorEquiv k L A).toAlgHom x) = _
  rw [← Lie.affineMap_comp]
  apply congrArg (fun f : L ⊗[k] A →ₐ[k] A => Lie.affineMap G f x)
  apply AlgHom.ext
  intro z
  exact tensorEquiv_apply k L A z τ

omit [FiniteDimensional k L] [IsGalois k L] in
private theorem evalTensor_includeRight :
    (evalTensor k L A (AlgHom.id k L)).comp Algebra.TensorProduct.includeRight =
      AlgHom.id k A := by
  ext a
  simp [evalTensor, Algebra.TensorProduct.includeRight_apply]

omit [FiniteDimensional k L] [IsGalois k L] in
private theorem evalTensor_conjugate (σ : L ≃ₐ[k] L) :
    (evalTensor k L A (AlgHom.id k L)).comp
        (TensorGaloisPoint.coefficientConjugate k L A σ) =
      evalTensor k L A σ.toAlgHom := by
  apply AlgHom.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul c a => simp [evalTensor]
  | add z w hz hw => simp only [map_add, hz, hw]

private theorem norm_eq_prod (T : CommGroupScheme (Spec (CommRingCat.of k)))
    [IsAffine T.X.left] (x : Lie.AffinePoints T.toGrp (L ⊗[k] A)) :
    TensorGaloisPoint.norm k L A T x =
      ∏ σ : L ≃ₐ[k] L, Lie.affineMap T.toGrp (evalTensor k L A σ.toAlgHom) x := by
  have h := congrArg (Lie.affineMap T.toGrp (evalTensor k L A (AlgHom.id k L)))
    (TensorGaloisPoint.extend_norm k L A T x)
  rw [TensorGaloisPoint.extend, ← Lie.affineMap_comp, evalTensor_includeRight,
    Lie.affineMap_id, map_prod] at h
  rw [h]
  apply Finset.prod_congr rfl
  intro σ _
  rw [TensorGaloisPoint.conjugate, ← Lie.affineMap_comp, evalTensor_conjugate]

end Tensor

section WeilPoints
variable (k L : Type u) [Field k] [Field L] [Algebra k L]
  [FiniteDimensional k L] [IsGalois k L]
variable (T : CommGroupScheme (Spec (CommRingCat.of k))) [IsAffine T.X.left]
  [IsAffine (GaloisPointComparison.baseChanged k L T.toGrp).X.left]
  [LocallyOfFiniteType (GaloisPointComparison.baseChanged k L T.toGrp).X.hom]

local notation "T_L" => GaloisPointComparison.baseChanged k L T.toGrp
local notation "W" => AffineWeil.groupScheme k L T_L
local notation "W_L" => GaloisPointComparison.baseChanged k L W

variable (A : Type u) [CommRing A] [Algebra k A] [Algebra L A] [IsScalarTower k L A]

private def weilTensorPointsEquiv :
    Lie.AffinePoints W_L A ≃* Lie.AffinePoints T.toGrp (L ⊗[k] A) :=
  (Lie.affineBaseChangeEquiv k L W A).trans
    ((AffineWeil.pointsEquiv k L T_L A).trans
      (Lie.affineBaseChangeEquiv k L T.toGrp (L ⊗[k] A)))

private def splitWeilPointsEquiv :
    Lie.AffinePoints W_L A ≃ ((L →ₐ[k] L) → Lie.AffinePoints T_L A) :=
  (weilTensorPointsEquiv k L T A).toEquiv.trans
    ((tensorPointsEquiv k L A T.toGrp).trans
      (Equiv.piCongrRight fun _ => (Lie.affineBaseChangeEquiv k L T.toGrp A).symm.toEquiv))

private theorem splitWeilPointsEquiv_apply (x : Lie.AffinePoints W_L A)
    (τ : L →ₐ[k] L) :
    Lie.affineBaseChangeEquiv k L T.toGrp A (splitWeilPointsEquiv k L T A x τ) =
      Lie.affineMap T.toGrp (evalTensor k L A τ) (weilTensorPointsEquiv k L T A x) := by
  change Lie.affineBaseChangeEquiv k L T.toGrp A
    ((Lie.affineBaseChangeEquiv k L T.toGrp A).symm
      (tensorPointsEquiv k L A T.toGrp (weilTensorPointsEquiv k L T A x) τ)) = _
  rw [MulEquiv.apply_symm_apply]
  exact tensorPointsEquiv_apply k L A T.toGrp _ τ

variable {A} {B : Type u} [CommRing B] [Algebra k B] [Algebra L B]
  [IsScalarTower k L B]

omit [IsAffine T.X.left] in
private theorem weilTensorPointsEquiv_naturality (f : A →ₐ[L] B)
    (x : Lie.AffinePoints W_L A) :
    weilTensorPointsEquiv k L T B (Lie.affineMap W_L f x) =
      Lie.affineMap T.toGrp (TensorGaloisPoint.tensorMap k L (f.restrictScalars k))
        (weilTensorPointsEquiv k L T A x) := by
  unfold weilTensorPointsEquiv
  simp only [MulEquiv.trans_apply]
  rw [Lie.affineBaseChangeEquiv_naturality]
  have h := AffineWeil.pointsEquiv_naturality k L T_L (f.restrictScalars k)
    (Lie.affineBaseChangeEquiv k L W A x)
  simp only [affinePointMap, CommAlgCat.hom_ofHom] at h
  rw [h]
  rw [Lie.affineBaseChangeEquiv_naturality]
  rfl

omit [FiniteDimensional k L] [IsGalois k L] in
private theorem evalTensor_naturality (f : A →ₐ[L] B) (τ : L →ₐ[k] L) :
    (evalTensor k L B τ).comp (TensorGaloisPoint.tensorMap k L (f.restrictScalars k)) =
      (f.restrictScalars k).comp (evalTensor k L A τ) := by
  apply AlgHom.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul c a => simp [evalTensor, TensorGaloisPoint.tensorMap]
  | add z w hz hw => simp only [map_add, hz, hw]

private theorem splitWeilPointsEquiv_naturality (f : A →ₐ[L] B)
    (x : Lie.AffinePoints W_L A) :
    splitWeilPointsEquiv k L T B (Lie.affineMap W_L f x) =
      fun τ => Lie.affineMap T_L f (splitWeilPointsEquiv k L T A x τ) := by
  funext τ
  apply (Lie.affineBaseChangeEquiv k L T.toGrp B).injective
  rw [splitWeilPointsEquiv_apply, Lie.affineBaseChangeEquiv_naturality,
    splitWeilPointsEquiv_apply, weilTensorPointsEquiv_naturality,
    ← Lie.affineMap_comp, ← Lie.affineMap_comp, evalTensor_naturality]

omit [FiniteDimensional k L] [IsGalois k L] in
private theorem affineBaseChangeEquiv_comp
    (G H : GroupScheme (Spec (CommRingCat.of k))) (f : G ⟶ H)
    (x : Lie.AffinePoints (GaloisPointComparison.baseChanged k L G) A) :
    Lie.affineBaseChangeEquiv k L H A
      (x ≫ ((GroupScheme.baseChange (algebraBaseMap k L)).map f).hom.hom) =
      Lie.affineBaseChangeEquiv k L G A x ≫ f.hom.hom := by
  change (Lie.affineBaseTestIso k L A).inv ≫
      baseChangePointsEquiv (algebraBaseMap k L) H _
        (x ≫ ((GroupScheme.baseChange (algebraBaseMap k L)).map f).hom.hom) =
    ((Lie.affineBaseTestIso k L A).inv ≫
      baseChangePointsEquiv (algebraBaseMap k L) G _ x) ≫ f.hom.hom
  rw [baseChangePointsEquiv_comp, Category.assoc]

local instance : Fintype (L →ₐ[k] L) := Fintype.ofFinite _

private theorem baseChangedNorm_eq_prod (x : Lie.AffinePoints W_L A) :
    x ≫ ((GroupScheme.baseChange (algebraBaseMap k L)).map
      (GaloisNorm.norm k L T)).hom.hom =
        ∏ τ : L →ₐ[k] L, splitWeilPointsEquiv k L T A x τ := by
  apply (Lie.affineBaseChangeEquiv k L T.toGrp A).injective
  rw [affineBaseChangeEquiv_comp, GaloisNorm.norm_affinePoints, map_prod]
  change TensorGaloisPoint.norm k L A T (weilTensorPointsEquiv k L T A x) = _
  rw [norm_eq_prod]
  refine Fintype.prod_equiv (Algebra.IsAlgebraic.algEquivEquivAlgHom k L).toEquiv
    (fun σ => Lie.affineMap T.toGrp (evalTensor k L A σ.toAlgHom)
      (weilTensorPointsEquiv k L T A x))
    (fun τ => Lie.affineBaseChangeEquiv k L T.toGrp A
      (splitWeilPointsEquiv k L T A x τ)) ?_
  intro σ
  exact (splitWeilPointsEquiv_apply k L T A x σ.toAlgHom).symm

end WeilPoints

section ProductCoordinates
variable (k L : Type u) [Field k] [Field L] [Algebra k L]
  [FiniteDimensional k L] [IsGalois k L]
variable (T : CommGroupScheme (Spec (CommRingCat.of k))) [IsAffine T.X.left]

private abbrev RestIndex := {τ : L →ₐ[k] L // τ ≠ AlgHom.id k L}

local notation "T_L" => GaloisPointComparison.baseChanged k L T.toGrp
local notation "R" => pi (fun _ : RestIndex k L => T_L)
local notation "P" => T_L ⊗ R

private def productCoordinatesEquiv (A : CommAlgCat.{u} L) :
    ((T_L).affinePoints A × (RestIndex k L → (T_L).affinePoints A)) ≃* (P).affinePoints A :=
  ((MulEquiv.refl _).prodCongr
      (piPointsEquiv (fun _ : RestIndex k L => T_L) ((algSpec (CommRingCat.of L)).obj
        (op A))).symm).trans
    (productPointsEquiv T_L R ((algSpec (CommRingCat.of L)).obj (op A))).symm

omit [IsGalois k L] [IsAffine T.X.left] in
private theorem productCoordinatesEquiv_coordinates (A : CommAlgCat.{u} L)
    (x : (T_L).affinePoints A × (RestIndex k L → (T_L).affinePoints A)) :
    productPointsEquiv T_L R _ (productCoordinatesEquiv k L T A x) =
      (x.1, (piPointsEquiv (fun _ : RestIndex k L => T_L) _).symm x.2) := by
  simp only [productCoordinatesEquiv, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
  rfl

omit [IsGalois k L] [IsAffine T.X.left] in
private theorem productCoordinatesEquiv_naturality {A B : CommAlgCat.{u} L}
    (f : A ⟶ B) (x : (T_L).affinePoints A × (RestIndex k L → (T_L).affinePoints A)) :
    productCoordinatesEquiv k L T B
      ((T_L).affinePointMap f x.1, fun i => (T_L).affinePointMap f (x.2 i)) =
      (P).affinePointMap f (productCoordinatesEquiv k L T A x) := by
  apply (productPointsEquiv T_L R _).injective
  simp only [affinePointMap_apply]
  rw [productPointsEquiv_naturality,
    productCoordinatesEquiv_coordinates, productCoordinatesEquiv_coordinates]
  refine Prod.ext rfl ?_
  apply (piPointsEquiv (fun _ : RestIndex k L => T_L) _).injective
  funext i
  simp only [piPointsEquiv_apply, Category.assoc, piPointsEquiv_symm_π]

end ProductCoordinates

section Assembly
variable (k L : Type u) [Field k] [Field L] [Algebra k L]
  [FiniteDimensional k L] [IsGalois k L]
variable (T : CommGroupScheme (Spec (CommRingCat.of k))) [IsAffine T.X.left]
  [IsAffine (GaloisPointComparison.baseChanged k L T.toGrp).X.left]
  [LocallyOfFiniteType (GaloisPointComparison.baseChanged k L T.toGrp).X.hom]

local notation "T_L" => GaloisPointComparison.baseChanged k L T.toGrp
local notation "W" => AffineWeil.groupScheme k L T_L
local notation "W_L" => GaloisPointComparison.baseChanged k L W
local notation "R" => pi (fun _ : RestIndex k L => T_L)
local notation "P" => T_L ⊗ R

local instance : Fintype (L →ₐ[k] L) := Fintype.ofFinite _
local instance (A : CommAlgCat.{u} L) : Algebra k A :=
  Algebra.compHom A (algebraMap k L)
local instance (A : CommAlgCat.{u} L) : IsScalarTower k L A :=
  IsScalarTower.of_algebraMap_eq' rfl

private def shearedPointsEquiv (A : CommAlgCat.{u} L) :
    (W_L).affinePoints A ≃ (P).affinePoints A := by
  classical
  exact (splitWeilPointsEquiv k L T A).trans
    ((GaloisNormSmoothnessGeometry.shearEquiv (AlgHom.id k L)).toEquiv.trans
      (productCoordinatesEquiv k L T A).toEquiv)

private theorem shearedPointsEquiv_naturality {A B : CommAlgCat.{u} L}
    (f : A ⟶ B) (x : (W_L).affinePoints A) :
    shearedPointsEquiv k L T B ((W_L).affinePointMap f x) =
      (P).affinePointMap f (shearedPointsEquiv k L T A x) := by
  classical
  change productCoordinatesEquiv k L T B
      (GaloisNormSmoothnessGeometry.shearEquiv (AlgHom.id k L)
        (splitWeilPointsEquiv k L T B (Lie.affineMap W_L f.hom x))) = _
  rw [splitWeilPointsEquiv_naturality]
  rw [GaloisNormSmoothnessGeometry.shearEquiv_naturality (AlgHom.id k L)
    (Lie.affineMap T_L f.hom)]
  exact productCoordinatesEquiv_naturality k L T f
    (GaloisNormSmoothnessGeometry.shearEquiv (AlgHom.id k L)
      (splitWeilPointsEquiv k L T A x))

private theorem shearedPointsEquiv_fst (A : CommAlgCat.{u} L)
    (x : (W_L).affinePoints A) :
    shearedPointsEquiv k L T A x ≫ fst (T_L).X (R).X =
      x ≫ ((GroupScheme.baseChange (algebraBaseMap k L)).map
        (GaloisNorm.norm k L T)).hom.hom := by
  classical
  change (productPointsEquiv T_L R _
    (productCoordinatesEquiv k L T A
      (GaloisNormSmoothnessGeometry.shearEquiv (AlgHom.id k L)
        (splitWeilPointsEquiv k L T A x)))).1 = _
  rw [productCoordinatesEquiv_coordinates, GaloisNormSmoothnessGeometry.shearEquiv_fst,
    baseChangedNorm_eq_prod]

private theorem smooth_baseChangedNorm (hSplit : IsSplitTorus T_L) :
    Smooth ((GroupScheme.baseChange (algebraBaseMap k L)).map
      (GaloisNorm.norm k L T)).hom.hom.left := by
  have : IsAffine (R).X.left := SplittingAssembly.isAffine_of_isTorus R
    (IsTorus.pi _ (fun _ => hSplit.isTorus))
  have : IsAffine (P).X.left := by
    change IsAffine (pullback (T_L).X.hom (R).X.hom)
    infer_instance
  have : IsAffine (W_L).X.left := by
    change IsAffine (pullback (W).X.hom (algebraBaseMap k L))
    infer_instance
  let e := isoOfAffinePoints W_L P (shearedPointsEquiv k L T)
    (shearedPointsEquiv_naturality k L T)
  apply GaloisNormSmoothnessGeometry.smooth_of_iso_fst e
    (((GroupScheme.baseChange (algebraBaseMap k L)).map
      (GaloisNorm.norm k L T)).hom.hom)
  · have he : e.hom ≫ fst (T_L).X (R).X =
        ((GroupScheme.baseChange (algebraBaseMap k L)).map
          (GaloisNorm.norm k L T)).hom.hom := by
      apply affine_hom_ext W_L
      intro A x
      rw [← Category.assoc]
      change (x ≫ mapOfAffinePoints W_L P (fun A => shearedPointsEquiv k L T A)) ≫ _ = _
      rw [mapOfAffinePoints_apply W_L P _ (shearedPointsEquiv_naturality k L T)]
      exact shearedPointsEquiv_fst k L T A x
    exact congrArg (fun f => f.left) he
  · exact GaloisNormSmoothnessGeometry.smooth_complement (AlgHom.id k L) T_L hSplit.smooth

end Assembly

/-- The actual finite-Galois torus norm is smooth in arbitrary characteristic. -/
theorem galoisNormSmoothness : GaloisNormSmoothnessStatement.{u} := by
  intro k L _ _ _ _ _ T _ _ _ hSplit
  exact GaloisNormSmoothnessGeometry.smooth_of_field_baseChange k L
    (GaloisNorm.norm k L T) (smooth_baseChangedNorm k L T hSplit)

end Langlands.GroupScheme.GaloisNormSmoothnessProof
