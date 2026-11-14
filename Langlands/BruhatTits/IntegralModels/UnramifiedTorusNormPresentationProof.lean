import Langlands.BruhatTits.IntegralModels.UnramifiedTorusNormPresentationStatement
import Langlands.GroupScheme.Torus.GaloisNormRational
import Langlands.GroupScheme.Torus.GaloisNormSmoothnessProof
import Langlands.GroupScheme.AffineWeilRestrictionMaps
import Langlands.GroupScheme.AffineWeilEvaluation
import Langlands.GroupScheme.ProductProperties
import Langlands.GroupScheme.AffinePointComparison
import Langlands.GroupScheme.Torus.RetractionKernel
import Langlands.GroupScheme.Torus.MultiplicativeTypeGeometry
import Langlands.AbelianScheme.KernelBaseChange
import Langlands.Geometry.Building.KPCharacterValuationExtension

noncomputable section
universe u
open CategoryTheory Opposite AlgebraicGeometry CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped TensorProduct CategoryTheory.MonObj BigOperators
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.Geometry.Building

namespace Langlands.BruhatTits.IntegralModels.TorusNormPresentation
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
set_option maxRecDepth 4000

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


section SplitStructure
variable (k L : Type u) [Field k] [Field L] [Algebra k L]
  [FiniteDimensional k L] [IsGalois k L]
  (T : CommGroupScheme (Spec (CommRingCat.of k))) [IsAffine T.X.left]
  [IsAffine (baseChanged k L T.toGrp).X.left]
  [LocallyOfFiniteType (baseChanged k L T.toGrp).X.hom]

local notation "T_L" => baseChanged k L T.toGrp
local notation "W" => AffineWeil.groupScheme k L T_L
local notation "W_L" => baseChanged k L W
local notation "P" => GroupScheme.pi (fun _ : L →ₐ[k] L => T_L)

local instance : Fintype (L →ₐ[k] L) := Fintype.ofFinite _
local instance (A : CommAlgCat.{u} L) : Algebra k A :=
  Algebra.compHom A (algebraMap k L)
local instance (A : CommAlgCat.{u} L) : IsScalarTower k L A :=
  IsScalarTower.of_algebraMap_eq' rfl
local instance : IsAffine (W_L).X.left := by
  change IsAffine (pullback (W).X.hom (algebraBaseMap k L))
  infer_instance
local instance : IsAffine (P).X.left := by
  have : IsAffineHom (P).X.hom :=
    prop_pi_hom @IsAffineHom (fun _ : L →ₐ[k] L => T_L) (fun _ => inferInstance)
  exact isAffine_of_isAffineHom (P).X.hom

private def splitPointsMulEquiv (A : CommAlgCat.{u} L) :
    (W_L).affinePoints A ≃* ((L →ₐ[k] L) → (T_L).affinePoints A) :=
  { splitWeilPointsEquiv k L T A with
    map_mul' := by
      intro x y
      funext τ
      apply (Lie.affineBaseChangeEquiv k L T.toGrp A).injective
      change Lie.affineBaseChangeEquiv k L T.toGrp A
        (splitWeilPointsEquiv k L T A (x * y) τ) =
          Lie.affineBaseChangeEquiv k L T.toGrp A
            (splitWeilPointsEquiv k L T A x τ * splitWeilPointsEquiv k L T A y τ)
      simp only [splitWeilPointsEquiv_apply, map_mul] }

private def splitProductPointsEquiv (A : CommAlgCat.{u} L) :
    (W_L).affinePoints A ≃* (P).affinePoints A :=
  (splitPointsMulEquiv k L T A).trans
    (piPointsEquiv (fun _ : L →ₐ[k] L => T_L)
      ((algSpec (CommRingCat.of L)).obj (op A))).symm

private theorem splitProductPointsEquiv_naturality
    {A B : CommAlgCat.{u} L} (f : A ⟶ B) (x : (W_L).affinePoints A) :
    splitProductPointsEquiv k L T B ((W_L).affinePointMap f x) =
      (P).affinePointMap f (splitProductPointsEquiv k L T A x) := by
  apply (piPointsEquiv (fun _ : L →ₐ[k] L => T_L)
    ((algSpec (CommRingCat.of L)).obj (op B))).injective
  simp only [splitProductPointsEquiv, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
  simp only [affinePointMap_apply, piPointsEquiv_naturality, MulEquiv.apply_symm_apply]
  exact splitWeilPointsEquiv_naturality k L T f.hom x

private def splitProductAffinePointIso : (W_L).affinePointFunctor ≅ (P).affinePointFunctor :=
  NatIso.ofComponents (fun A => (splitProductPointsEquiv k L T A).toGrpIso) (by
    intro A B f
    ext x
    exact splitProductPointsEquiv_naturality k L T f x)

/-- The actual norm source becomes the product of the original torus over the Galois embeddings. -/
def splitProductIso : W_L ≅ P :=
  AffinePointComparison.iso (splitProductAffinePointIso k L T)

/-- The Weil source is a torus whenever the target splits over the extension. -/
theorem source_isTorus (hSplit : IsSplitTorus T_L) : IsTorus W := by
  apply IsTorus.of_baseChange (K := L)
  exact IsTorus.of_iso (splitProductIso k L T)
    (IsTorus.pi _ (fun _ => hSplit.isTorus))

private def identityCoordinate (A : CommAlgCat.{u} L) :
    (T_L).affinePoints A →* ((L →ₐ[k] L) → (T_L).affinePoints A) := by
  classical
  exact
    { toFun := fun x τ => if τ = AlgHom.id k L then x else 1
      map_one' := by ext τ; simp
      map_mul' := by intro x y; funext τ; by_cases h : τ = AlgHom.id k L <;> simp [h] }

private def sectionPoints (A : CommAlgCat.{u} L) :
    (T_L).affinePoints A →* (W_L).affinePoints A :=
  (splitPointsMulEquiv k L T A).symm.toMonoidHom.comp (identityCoordinate k L T A)

private theorem sectionPoints_naturality {A B : CommAlgCat.{u} L}
    (f : A ⟶ B) (x : (T_L).affinePoints A) :
    sectionPoints k L T B ((T_L).affinePointMap f x) =
      (W_L).affinePointMap f (sectionPoints k L T A x) := by
  classical
  apply (splitPointsMulEquiv k L T B).injective
  change splitWeilPointsEquiv k L T B
      ((splitPointsMulEquiv k L T B).symm _) =
    splitWeilPointsEquiv k L T B
      (Lie.affineMap (W_L) f.hom (sectionPoints k L T A x))
  rw [splitWeilPointsEquiv_naturality]
  change (splitPointsMulEquiv k L T B) ((splitPointsMulEquiv k L T B).symm _) =
    fun τ => Lie.affineMap (T_L) f.hom
      ((splitPointsMulEquiv k L T A) ((splitPointsMulEquiv k L T A).symm _) τ)
  simp only [MulEquiv.apply_symm_apply]
  funext τ
  change (if τ = AlgHom.id k L then _ else 1) =
    Lie.affineMap (T_L) f.hom (if τ = AlgHom.id k L then x else 1)
  split_ifs <;> simp [affinePointMap_apply]

private def sectionNat : (T_L).affinePointFunctor ⟶ (W_L).affinePointFunctor where
  app A := GrpCat.ofHom (sectionPoints k L T A)
  naturality A B f := by
    ext x
    exact sectionPoints_naturality k L T f x

/-- Over the splitting extension, insert a point at the identity embedding. -/
def normSection : T_L ⟶ W_L :=
  AffinePointComparison.map (sectionNat k L T)

theorem normSection_comp_norm :
    normSection k L T ≫
      (GroupScheme.baseChange (algebraBaseMap k L)).map (GaloisNorm.norm k L T) =
        𝟙 T_L := by
  classical
  apply AffinePointComparison.hom_ext (T_L)
  intro A x
  change (x ≫ (normSection k L T).hom.hom) ≫
    ((GroupScheme.baseChange (algebraBaseMap k L)).map
      (GaloisNorm.norm k L T)).hom.hom = x ≫ 𝟙 (T_L).X
  rw [normSection, AffinePointComparison.map_points, Category.comp_id]
  rw [baseChangedNorm_eq_prod]
  change (∏ τ, (splitPointsMulEquiv k L T A)
    ((splitPointsMulEquiv k L T A).symm (identityCoordinate k L T A x)) τ) = x
  rw [MulEquiv.apply_symm_apply]
  change (∏ τ : L →ₐ[k] L, if τ = AlgHom.id k L then x else 1) = x
  simp

/-- The algebraic norm is scheme-surjective, by its section after field extension. -/
theorem norm_surjective : Surjective (GaloisNorm.norm k L T).hom.hom.left := by
  let q := GaloisNorm.norm k L T
  let b := algebraBaseMap k L
  let qL := (GroupScheme.baseChange b).map q
  have hs : (normSection k L T).hom.hom.left ≫ qL.hom.hom.left = 𝟙 (T_L).X.left :=
    congrArg (fun f => f.hom.hom.left) (normSection_comp_norm k L T)
  have hsection : Surjective ((normSection k L T).hom.hom.left ≫ qL.hom.hom.left) := by
    rw [hs]
    infer_instance
  have hqL : Surjective qL.hom.hom.left :=
    ⟨Function.Surjective.of_comp hsection.surj⟩
  let : Surjective b := (fieldExtension_fpqc k L).1
  have hprojection : Surjective (pullback.fst T.X.hom b) := inferInstance
  have hc : qL.hom.hom.left ≫ pullback.fst T.X.hom b =
      pullback.fst (W).X.hom b ≫ q.hom.hom.left := by
    change ((Over.pullback b).map q.hom.hom).left ≫ _ = _
    simp only [Over.pullback_map_left, pullback.lift_fst]
  have hcomp : Surjective (pullback.fst (W).X.hom b ≫ q.hom.hom.left) := by
    rw [← hc]
    exact ⟨hprojection.surj.comp hqL.surj⟩
  exact ⟨Function.Surjective.of_comp hcomp.surj⟩

local instance : IsCommMonObj (T_L).X :=
  ((CommGroupScheme.baseChange (algebraBaseMap k L)).obj T).comm
/-- The commutative Weil restriction used as the norm source. -/
def normSource : CommGroupScheme (Spec (CommRingCat.of k)) :=
  AffineWeil.commGroupScheme k L T_L

instance normSource_isAffine : IsAffine (normSource k L T).X.left := by
  change IsAffine (W).X.left
  infer_instance

local instance : IsCommMonObj (W_L).X :=
  ((CommGroupScheme.baseChange (algebraBaseMap k L)).obj
    (AffineWeil.commGroupScheme k L T_L)).comm

/-- The entire scheme-theoretic kernel is a torus. -/
theorem norm_kernel_isTorus (hSplit : IsSplitTorus T_L) :
    IsTorus (GroupScheme.kernel (GaloisNorm.norm k L T)) := by
  let qL := (GroupScheme.baseChange (algebraBaseMap k L)).map (GaloisNorm.norm k L T)
  let S : CommGroupScheme (Spec (CommRingCat.of L)) :=
    { W_L with comm := inferInstance }
  have hAffine : IsAffineHom (GroupScheme.kernel qL).X.hom := by
    rw [← (kernelι qL).hom.hom.w]
    exact MorphismProperty.comp_mem (@IsAffineHom) _ _
      (inferInstance : IsAffineHom (kernelι qL).hom.hom.left)
      (inferInstance : IsAffineHom (W_L).X.hom)
  have hker : IsTorus (GroupScheme.kernel qL) :=
    @Torus.isTorus_kernel_of_section L _ S T_L qL (normSection k L T)
      (normSection_comp_norm k L T) hAffine
      (IsTorus.of_iso (splitProductIso k L T)
        (IsTorus.pi _ (fun _ => hSplit.isTorus)))
  apply IsTorus.of_baseChange (K := L)
  exact IsTorus.of_iso (kernelBaseChangeIso (algebraBaseMap k L) (GaloisNorm.norm k L T))
    hker

end SplitStructure

section EvaluationCoefficients
variable (k L : Type u) [Field k] [Field L] [Algebra k L]
  [FiniteDimensional k L]
  (H : GroupScheme (Spec (CommRingCat.of L)))
  [IsAffine H.X.left] [LocallyOfFiniteType H.X.hom]

attribute [local instance] AffineWeil.coefficientBaseAlgebra AffineWeil.coefficientScalarTower

private theorem evaluation_extendedCoeff (R : CommAlgCat.{u} L)
    (p : (AffineWeil.groupScheme k L H).affinePoints (CommAlgCat.of k k)) :
    H.affinePointMap (AffineWeil.evaluationCoefficientMap k L R)
        (AffineWeil.pointsEquiv k L H R
          ((AffineWeil.groupScheme k L H).affinePointMap
            (CommAlgCat.ofHom (Algebra.ofId k R)) p)) =
      H.affinePointMap (CommAlgCat.ofHom (Algebra.ofId L R))
        (AffineWeil.basePointsEquiv k L H p) := by
  rw [AffineWeil.pointsEquiv_naturality]
  change Lie.affineMap H _ (Lie.affineMap H _ _) =
    Lie.affineMap H _ (Lie.affineMap H (Algebra.TensorProduct.rid k L L).toAlgHom _)
  rw [← Lie.affineMap_comp, ← Lie.affineMap_comp]
  apply congrArg (fun f : L ⊗[k] k →ₐ[L] R =>
    Lie.affineMap H f (AffineWeil.pointsEquiv k L H k p))
  ext

private theorem evaluation_of_projected_eq (R : CommAlgCat.{u} L)
    (p : ((GroupScheme.baseChange (algebraBaseMap k L)).obj
      (AffineWeil.groupScheme k L H)).affinePoints R)
    (x : (AffineWeil.groupScheme k L H).affinePoints (CommAlgCat.of k k))
    (hp : p.left ≫ pullback.fst (AffineWeil.groupScheme k L H).X.hom
        (algebraBaseMap k L) =
      Spec.map (CommRingCat.ofHom (algebraMap k R)) ≫ x.left) :
    p ≫ (AffineWeil.evaluation k L H).hom.hom =
      H.affinePointMap (CommAlgCat.ofHom (Algebra.ofId L R))
        (AffineWeil.basePointsEquiv k L H x) := by
  rw [AffineWeil.evaluation_affinePoints, ← evaluation_extendedCoeff k L H R x]
  apply congrArg (H.affinePointMap (AffineWeil.evaluationCoefficientMap k L R))
  apply congrArg (AffineWeil.pointsEquiv k L H R)
  apply Over.OverMorphism.ext
  exact (affinePointsBaseChangeMulEquiv_symm_left k L R
    (AffineWeil.groupScheme k L H) p).trans hp

end EvaluationCoefficients

section BoundedImage
variable (k L : Type u) [Field k] [Field L] [Algebra k L]
  [FiniteDimensional k L] [IsGalois k L]
  (T : CommGroupScheme (Spec (CommRingCat.of k))) [IsAffine T.X.left]
  [IsAffine (baseChanged k L T.toGrp).X.left]
  [LocallyOfFiniteType (baseChanged k L T.toGrp).X.hom]

local notation "T_L" => baseChanged k L T.toGrp
local notation "W" => AffineWeil.groupScheme k L T_L

omit [IsAffine T.X.left] in
private theorem evaluation_rationalExtend (x : rationalPoints W) :
    rationalPoints.map (AffineWeil.evaluation k L T_L) (rationalExtend k L W x) =
      (GaloisNorm.rationalPointsEquiv k L T).symm x := by
  apply (rationalCoeffEquiv L T_L).injective
  rw [rationalCoeffEquiv_map, affinePointsTarget_apply]
  have hp :
      (rationalCoeffEquiv L (baseChanged k L W) (rationalExtend k L W x)).left ≫
          pullback.fst (W).X.hom (algebraBaseMap k L) =
        baseMap k L ≫ (rationalCoeffEquiv k W x).left := by
    rw [rationalCoeffEquiv_left, rationalExtend_fst]
    change baseMap k L ≫ x.left =
      baseMap k L ≫ (rationalCoeffEquiv k W x).left
    rw [rationalCoeffEquiv_left]
  rw [evaluation_of_projected_eq k L T_L (CommAlgCat.of L L) _ _ hp]
  change (T_L).affinePointMap (CommAlgCat.ofHom (Algebra.ofId L L))
      (AffineWeil.basePointsEquiv k L T_L (rationalCoeffEquiv k W x)) =
    rationalCoeffEquiv L T_L
      ((rationalCoeffEquiv L T_L).symm
        (AffineWeil.basePointsEquiv k L T_L (rationalCoeffEquiv k W x)))
  rw [MulEquiv.apply_symm_apply]
  apply Over.OverMorphism.ext
  change Spec.map (𝟙 (CommRingCat.of L)) ≫ _ = _
  rw [Spec.map_id, Category.id_comp]

variable {Γk ΓL : Type*} [LinearOrderedCommGroupWithZero Γk]
  [LinearOrderedCommGroupWithZero ΓL]
  (vk : Valuation k Γk) (vL : Valuation L ΓL) [vk.HasExtension vL]
  (hinv : ∀ (σ : L ≃ₐ[k] L) (z : L), vL (σ z) = vL z)

include hinv in
/-- The norm image of the Weil source's character-valuation kernel is in the
norm-defined Iwahori subgroup. -/
theorem norm_bounded_image :
    (characterValuationKernel vk W).map (rationalPoints.map (GaloisNorm.norm k L T)) ≤
      torusNormIwahori k L vL T := by
  rintro _ ⟨x, hx, rfl⟩
  let y := (GaloisNorm.rationalPointsEquiv k L T).symm x
  refine ⟨y, ?_, ?_⟩
  · have hext := characterValuationKernel_le_comap vk vL hinv W hx
    have hev := map_characterValuationKernel_le vL (AffineWeil.evaluation k L T_L)
    change y ∈ characterValuationKernel vL T_L
    rw [show y = rationalPoints.map (AffineWeil.evaluation k L T_L)
      (rationalExtend k L W x) from (evaluation_rationalExtend k L T x).symm]
    exact hev ⟨rationalExtend k L W x, hext, rfl⟩
  · simpa only [y, MulEquiv.apply_symm_apply] using
      (GaloisNorm.norm_rationalPoints k L T y).symm

end BoundedImage
end Langlands.BruhatTits.IntegralModels.TorusNormPresentation

namespace Langlands.BruhatTits.IntegralModels

open Langlands.LocalGalois.Separable TorusNormPresentation

set_option maxHeartbeats 800000 in
/-- The actual finite Galois Weil restriction and its norm give the presentation
used in the connected integral-point bound. -/
theorem unramifiedTorusNormPresentation :
    UnramifiedTorusNormPresentationStatement.{u} := by
  intro F _ _ _ _ T _ L _ _ hSplit
  let K := inertiaFixedField F
  let T_L := baseChanged K L T.toGrp
  let : IsAffine T_L.X.left := hSplit.isTorus.isMultiplicativeType.isAffine
  let : LocallyOfFiniteType T_L.X.hom :=
    hSplit.isTorus.isMultiplicativeType.locallyOfFiniteType
  let S := normSource K L T
  refine ⟨S, normSource_isAffine K L T, source_isTorus K L T hSplit, GaloisNorm.norm K L T,
    norm_surjective K L T, norm_kernel_isTorus K L T hSplit, ?_⟩
  exact norm_bounded_image K L T (fixedFieldValuation F)
    (intermediateValuation F L) (intermediateValuation_conjugate F L)

end Langlands.BruhatTits.IntegralModels
