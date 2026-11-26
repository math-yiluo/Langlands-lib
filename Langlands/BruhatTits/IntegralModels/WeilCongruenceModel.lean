import Langlands.BruhatTits.IntegralModels.WeilCongruencePairs
import Langlands.GroupScheme.SplitKernelRetractGeometry
import Langlands.GroupScheme.KernelSquareTransport
import Langlands.GroupScheme.Torus.WeilRestrictionGeometricallyConnected
import Langlands.AbelianScheme.KernelBaseChange

/-! # An integral model for congruent units of a Weil restriction -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open Langlands.GroupScheme
open scoped TensorProduct CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000
set_option quotPrecheck false

namespace Langlands.BruhatTits.IntegralModels.WeilCongruence

section CoefficientMap

variable {A : Type u} [CommRing A] {C D : Type u} [CommRing C] [CommRing D]
  [Algebra A C] [Algebra A D]

private def tensorMap (f : C →ₐ[A] D) (T : Type u) [CommRing T] [Algebra A T] :
    C ⊗[A] T →ₐ[A] D ⊗[A] T := Algebra.TensorProduct.map f (AlgHom.id A T)

private theorem tensorMap_tmul (f : C →ₐ[A] D) {T : Type u} [CommRing T] [Algebra A T]
    (x : C) (y : T) : tensorMap f T (x ⊗ₜ y) = f x ⊗ₜ y := rfl

variable [Module.Finite A C] [Module.Projective A C] [Module.Finite A D] [Module.Projective A D]

local notation "SpecA" => Spec (CommRingCat.of A)
local notation "W" => WeilGm.groupScheme (CommRingCat.of A)
local notation "P" => WeilGm.pointsEquiv (CommRingCat.of A)
local notation "ΓS" => (fun T => ((algΓ (CommRingCat.of A)).obj T).unop)

private def coefficientPoints (f : C →ₐ[A] D) (T : Over SpecA) :
    (T ⟶ (W C).X) →* (T ⟶ (W D).X) :=
  (P D T).symm.toMonoidHom.comp
    ((Units.map (tensorMap f (ΓS T)).toMonoidHom).comp (P C T).toMonoidHom)

private theorem coefficientPoints_naturality (f : C →ₐ[A] D)
    {T T' : Over SpecA} (g : T' ⟶ T) (x : T ⟶ (W C).X) :
    coefficientPoints f T' (g ≫ x) = g ≫ coefficientPoints f T x := by
  apply (P D T').injective
  change P D T' ((P D T').symm
      (Units.map (tensorMap f (ΓS T')).toMonoidHom (P C T' (g ≫ x)))) =
    P D T' (g ≫ (P D T).symm
      (Units.map (tensorMap f (ΓS T)).toMonoidHom (P C T x)))
  rw [MulEquiv.apply_symm_apply, WeilGm.pointsEquiv_naturality,
    WeilGm.pointsEquiv_naturality, MulEquiv.apply_symm_apply]
  apply Units.ext
  change tensorMap f (ΓS T')
    (Algebra.TensorProduct.lTensor (S := C) C ((algΓ _).map g).unop.hom _) =
    Algebra.TensorProduct.lTensor (S := D) D ((algΓ _).map g).unop.hom
      (tensorMap f (ΓS T) _)
  generalize (P C T x).val = z
  induction z using TensorProduct.inductionOn with
  | tmul a b => simp [Algebra.TensorProduct.lTensor, tensorMap_tmul]
  | add a b ha hb => simp only [map_add, ha, hb]

/-- A coefficient algebra map acts functorially on the tensor-valued units
represented by the multiplicative Weil restriction. -/
def coefficientMap (f : C →ₐ[A] D) : W C ⟶ W D :=
  homOfPoints (coefficientPoints f) (coefficientPoints_naturality f)

@[simp] theorem coefficientMap_points (f : C →ₐ[A] D) (T : Over SpecA)
    (x : T ⟶ (W C).X) :
    P D T (x ≫ (coefficientMap f).hom.hom) =
      Units.map (tensorMap f (ΓS T)).toMonoidHom (P C T x) := by
  rw [coefficientMap, comp_homOfPoints (coefficientPoints f) (coefficientPoints_naturality f)]
  exact (P D T).apply_symm_apply _

theorem coefficientMap_sectionUnits (f : C →ₐ[A] D) (x : rationalPoints (W C)) :
    WeilGm.sectionUnitsEquiv (CommRingCat.of A) D
      (rationalPoints.map (coefficientMap f) x) =
    Units.map f.toMonoidHom (WeilGm.sectionUnitsEquiv (CommRingCat.of A) C x) := by
  apply Units.ext
  let T := Over.mk (𝟙 SpecA)
  change WeilGm.sectionTensorEquiv (CommRingCat.of A) D
      (P D T (x ≫ (coefficientMap f).hom.hom)).val =
    f (WeilGm.sectionTensorEquiv (CommRingCat.of A) C (P C T x).val)
  rw [coefficientMap_points]
  change WeilGm.sectionTensorEquiv (CommRingCat.of A) D (tensorMap f (ΓS T) (P C T x).val) = _
  generalize (P C T x).val = z
  induction z using TensorProduct.inductionOn with
  | tmul a b =>
    rw [tensorMap_tmul, WeilGm.sectionTensorEquiv_tmul (CommRingCat.of A) D (f a) b,
      WeilGm.sectionTensorEquiv_tmul (CommRingCat.of A) C a b]
    exact (map_smul f _ a).symm
  | add a b ha hb => simp only [map_add, ha, hb]

end CoefficientMap

section Compatibility

variable {A K C D B E : Type u} [CommRing A] [IsDomain A] [Field K]
  [Algebra A K] [IsFractionRing A K]
  [CommRing C] [CommRing D] [Algebra A C] [Algebra A D]
  [Module.Finite A C] [Module.Projective A C] [Module.Finite A D] [Module.Projective A D]
  [CommRing B] [CommRing E] [Algebra K B] [Algebra K E]
  [Module.Finite K B] [Module.Finite K E]

private theorem coefficientMap_generic_comm (f : C →ₐ[A] D) (g : B →ₐ[K] E)
    (e : K ⊗[A] C ≃ₐ[K] B) (d : K ⊗[A] D ≃ₐ[K] E)
    (h : ∀ c : C, d ((1 : K) ⊗ₜ f c) = g (e ((1 : K) ⊗ₜ c))) :
    (GroupScheme.baseChange (Spec.algebraMap A K)).map (coefficientMap f) ≫
      (WeilGm.integralModel A K D E d).genericIso.hom =
      (WeilGm.integralModel A K C B e).genericIso.hom ≫ coefficientMap g := by
  apply hom_ext_points
  intro T x
  let := WeilGm.restrictedSectionsAlgebra (CommRingCat.of A) (CommRingCat.of K) T
  let := WeilGm.restrictedSectionsScalarTower (CommRingCat.of A) (CommRingCat.of K) T
  apply (WeilGm.pointsEquiv (CommRingCat.of K) E T).injective
  simp only [WeilGm.integralModel, Iso.trans_hom, Grp.comp_hom_hom, ← Category.assoc]
  rw [coefficientMap_points, WeilGm.congrIso_hom_points, WeilGm.congrIso_hom_points]
  rw [WeilGm.algebraBaseChangeIso_hom_points (CommRingCat.of A) (CommRingCat.of K) D,
    WeilGm.algebraBaseChangeIso_hom_points (CommRingCat.of A) (CommRingCat.of K) C,
    GroupScheme.baseChangePointsEquiv_comp, coefficientMap_points]
  apply Units.ext
  let z := WeilGm.pointsEquiv (CommRingCat.of A) C _
    (GroupScheme.baseChangePointsEquiv (Spec.algebraMap A K)
      (WeilGm.groupScheme (CommRingCat.of A) C) T x)
  change Algebra.TensorProduct.congr d AlgEquiv.refl
      (WeilGm.baseChangeTensorEquiv A K D (WeilGm.restrictedSections _ _ T)
        (tensorMap f _ z.val)) =
    tensorMap g _ (Algebra.TensorProduct.congr e AlgEquiv.refl
      (WeilGm.baseChangeTensorEquiv A K C (WeilGm.restrictedSections _ _ T) z.val))
  generalize z.val = w
  induction w using TensorProduct.inductionOn with
  | tmul c t => simp [tensorMap_tmul, h]
  | add x y hx hy => simp only [map_add, hx, hy]

end Compatibility

section Model

variable (A : Type u) [CommRing A] [IsDomain A] [IsPrincipalIdealRing A]
  {C : Type u} [CommRing C] [Algebra A C] [Module.Finite A C] [Module.Free A C]
  (J : Ideal C)

local notation "W" => WeilGm.groupScheme (CommRingCat.of A)
local notation "D" => pairs A J

/-- The split projection on multiplicative Weil restrictions. -/
abbrev quotient : W D ⟶ W A := coefficientMap (first A J)

private abbrev sectionMap : W A ⟶ W D := coefficientMap (IsScalarTower.toAlgHom A A D)

private theorem sectionMap_quotient : sectionMap A J ≫ quotient A J = 𝟙 _ := by
  apply hom_ext_points
  intro T x
  apply (WeilGm.pointsEquiv (CommRingCat.of A) A T).injective
  simp only [Grp.comp_hom_hom, ← Category.assoc, Grp.id_hom_hom, Category.comp_id]
  rw [coefficientMap_points, coefficientMap_points]
  apply Units.ext
  change tensorMap (first A J) _
    (tensorMap (IsScalarTower.toAlgHom A A D) _
      (WeilGm.pointsEquiv (CommRingCat.of A) A T x).val) = _
  generalize (WeilGm.pointsEquiv (CommRingCat.of A) A T x).val = w
  induction w using TensorProduct.inductionOn with
  | tmul a b =>
    simp only [tensorMap_tmul]
    rfl
  | add a b ha hb => simp only [map_add, ha, hb]

/-- The actual kernel of the split augmentation of the unit group. -/
abbrev group : GroupScheme (Spec (CommRingCat.of A)) := GroupScheme.kernel (quotient A J)

local instance (U : Type u) [CommRing U] [Algebra A U]
    [Module.Finite A U] [Module.Projective A U] : IsAffineHom (W U).X.hom := by
  have : IsAffine (W U).X.left := by
    change IsAffine (Spec _)
    infer_instance
  exact isAffineHom_of_isAffine _

instance group_affine : IsAffineHom (group A J).X.hom := by
  rw [← (GroupScheme.kernelι (quotient A J)).hom.hom.w]
  infer_instance

/-- The kernel is smooth because its split projection makes it a retract of
smooth affine Weil restriction over the principal ideal domain. -/
theorem group_smooth : Smooth (group A J).X.hom := by
  let q := quotient A J
  let s := sectionMap A J
  have h := sectionMap_quotient A J
  let : Smooth (W D).X.hom := WeilGm.smooth _ _
  let : IsAffine (W D).X.left := isAffine_of_isAffineHom (W D).X.hom
  let : IsAffine (group A J).X.left := isAffine_of_isAffineHom (group A J).X.hom
  exact AffineRetractGeometry.smooth_of_retract (GroupScheme.kernelι q).hom.hom
    (SplitKernelRetract.retraction q (𝟙 _) q s (Category.comp_id _) h)
    (SplitKernelRetract.ι_retraction q (𝟙 _) q s (Category.comp_id _) h)

/-- The retract remains a retract over every field, where the ambient Weil
restriction of the multiplicative group is connected. -/
theorem group_geometricallyConnected : GeometricallyConnected (group A J).X.hom := by
  let q := quotient A J
  let s := sectionMap A J
  have h := sectionMap_quotient A J
  let i := (GroupScheme.kernelι q).hom.hom
  let p := SplitKernelRetract.retraction q (𝟙 _) q s (Category.comp_id _) h
  have hip : i ≫ p = 𝟙 _ :=
    SplitKernelRetract.ι_retraction q (𝟙 _) q s (Category.comp_id _) h
  have hW : GeometricallyConnected (W D).X.hom := WeilGm.geometricallyConnected A D
  rw [geometricallyConnected_iff, geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms]
  rw [geometricallyConnected_iff, geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms] at hW
  intro L _ _
  let P := Over.pullback (Spec.algebraMap A L)
  let : ConnectedSpace (P.obj (W D).X).left := hW L
  exact AffineRetractGeometry.connectedSpace_of_retract (P.map i) (P.map p) (by
    rw [← P.map_comp, hip, P.map_id])

/-- The unit pair over one gives an actual section of the congruence kernel. -/
private def sectionOfUnit (w : Cˣ) (h : (w : C) - 1 ∈ J) : rationalPoints (group A J) := by
  let T := Over.mk (𝟙 (Spec (CommRingCat.of A)))
  let k := GroupScheme.kernelPointsEquiv (quotient A J) T
  let U := WeilGm.sectionUnitsEquiv (CommRingCat.of A) D
  let z := U.symm (unitPair A J w h)
  refine k.symm ⟨z, ?_⟩
  change rationalPoints.map (coefficientMap (first A J)) z = 1
  apply (WeilGm.sectionUnitsEquiv (CommRingCat.of A) A).injective
  rw [coefficientMap_sectionUnits, map_one]
  change Units.map (first A J).toMonoidHom (U (U.symm _)) = 1
  rw [MulEquiv.apply_symm_apply U]
  apply Units.ext
  exact first_unitPair A J w h

private theorem sectionOfUnit_units (w : Cˣ) (h : (w : C) - 1 ∈ J) :
    WeilGm.sectionUnitsEquiv (CommRingCat.of A) D
      (rationalPoints.map (GroupScheme.kernelι (quotient A J)) (sectionOfUnit A J w h)) =
    unitPair A J w h := by
  let T := Over.mk (𝟙 (Spec (CommRingCat.of A)))
  let k := GroupScheme.kernelPointsEquiv (quotient A J) T
  let U := WeilGm.sectionUnitsEquiv (CommRingCat.of A) D
  change U (k (sectionOfUnit A J w h)).val = _
  unfold sectionOfUnit
  rw [MulEquiv.apply_symm_apply k, MulEquiv.apply_symm_apply U]

end Model
end Langlands.BruhatTits.IntegralModels.WeilCongruence

namespace Langlands.BruhatTits.IntegralModels.WeilCongruence

section ProductKernel

variable (K : Type u) [Field K] (B : Type u) [CommRing B] [Algebra K B]
  [Module.Finite K B]

local notation "WK" => WeilGm.groupScheme (CommRingCat.of K)
local notation "SpecK" => Spec (CommRingCat.of K)
local notation "π₁" => coefficientMap (AlgHom.fst K K B)
local notation "π₂" => coefficientMap (AlgHom.snd K K B)
local notation "P" => WeilGm.pointsEquiv (CommRingCat.of K)

private def productTensorEquiv (T : Type u) [CommRing T] [Algebra K T] :
    (K × B) ⊗[K] T ≃ₐ[K] (K ⊗[K] T) × (B ⊗[K] T) :=
  (Algebra.TensorProduct.comm K (K × B) T).trans
    ((Algebra.TensorProduct.prodRight K K T K B).trans
      ((Algebra.TensorProduct.comm K T K).prodCongr (Algebra.TensorProduct.comm K T B)))

omit [Module.Finite K B] in
private theorem productTensorEquiv_projections {T : Type u} [CommRing T] [Algebra K T]
    (z : (K × B) ⊗[K] T) : productTensorEquiv K B T z =
      (tensorMap (AlgHom.fst K K B) T z, tensorMap (AlgHom.snd K K B) T z) := by
  induction z using TensorProduct.inductionOn with
  | tmul x y =>
    simp only [productTensorEquiv, AlgEquiv.trans_apply, Algebra.TensorProduct.comm_tmul,
      Algebra.TensorProduct.prodRight_tmul, AlgEquiv.prodCongr_apply, tensorMap_tmul]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy, Prod.mk_add_mk]

private def productPoints (T : Over SpecK) :
    (T ⟶ (WK (K × B)).X) ≃* (T ⟶ (WK K).X) × (T ⟶ (WK B).X) :=
  (P (K × B) T).trans
    ((Units.mapEquiv (productTensorEquiv K B (((algΓ (CommRingCat.of K)).obj T).unop)).toMulEquiv).trans
      (MulEquiv.prodUnits.trans ((P K T).symm.prodCongr (P B T).symm)))

private theorem productPoints_apply (T : Over SpecK) (z : T ⟶ (WK (K × B)).X) :
    productPoints K B T z = (z ≫ (π₁).hom.hom, z ≫ (π₂).hom.hom) := by
  apply Prod.ext
  · apply (P K T).injective
    rw [coefficientMap_points]
    change P K T ((P K T).symm _) = _
    rw [MulEquiv.apply_symm_apply]
    apply Units.ext
    change (productTensorEquiv K B _ (P (K × B) T z).val).1 = _
    rw [productTensorEquiv_projections]
    rfl
  · apply (P B T).injective
    rw [coefficientMap_points]
    change P B T ((P B T).symm _) = _
    rw [MulEquiv.apply_symm_apply]
    apply Units.ext
    change (productTensorEquiv K B _ (P (K × B) T z).val).2 = _
    rw [productTensorEquiv_projections]
    rfl

private abbrev productKernelMap : GroupScheme.kernel (π₁) ⟶ WK B :=
  GroupScheme.kernelι (π₁) ≫ (π₂)

private theorem productKernelMap_bijective (T : Over SpecK) :
    Function.Bijective (fun x : T ⟶ (GroupScheme.kernel (π₁)).X =>
      x ≫ (productKernelMap K B).hom.hom) := by
  let p := productPoints K B T
  let k := GroupScheme.kernelPointsEquiv (π₁) T
  have hp (x : T ⟶ (GroupScheme.kernel (π₁)).X) :
      p (k x).val = (1, x ≫ (productKernelMap K B).hom.hom) := by
    rw [productPoints_apply]
    apply Prod.ext
    · exact (k x).property
    · exact Category.assoc x _ _
  refine ⟨fun x y h => k.injective (Subtype.ext (p.injective ?_)), ?_⟩
  · rw [hp, hp]
    exact congrArg (fun t => (1, t)) h
  · intro y
    let z := p.symm (1, y)
    have hz : (z ≫ (π₁).hom.hom, z ≫ (π₂).hom.hom) = (1, y) := by
      rw [← productPoints_apply]
      exact p.apply_symm_apply _
    let x := k.symm ⟨z, congrArg Prod.fst hz⟩
    refine ⟨x, ?_⟩
    have hpx := hp x
    rw [MulEquiv.apply_symm_apply k] at hpx
    exact (congrArg Prod.snd hpx).symm.trans (congrArg Prod.snd (p.apply_symm_apply (1, y)))

private def productKernelIso : GroupScheme.kernel (π₁) ≅ WK B :=
  isoOfPoints (fun T => MulEquiv.ofBijective
    (((yonedaGrp.map (productKernelMap K B)).app (op T)).hom)
    (productKernelMap_bijective K B T)) (by
    intro T T' f x
    exact Category.assoc f x _)

private theorem productKernelIso_hom : (productKernelIso K B).hom = productKernelMap K B := by
  apply hom_ext_points
  intro T x
  unfold productKernelIso isoOfPoints
  dsimp only
  rw [comp_homOfPoints]
  rfl

end ProductKernel
end Langlands.BruhatTits.IntegralModels.WeilCongruence

namespace Langlands.BruhatTits.IntegralModels.WeilCongruence

section IntegralModel

variable (A K : Type u) [CommRing A] [IsDomain A] [IsPrincipalIdealRing A]
  [Field K] [Algebra A K] [IsFractionRing A K]
  {C : Type u} [CommRing C] [Algebra A C] [Module.Finite A C] [Module.Free A C]
  (J : Ideal C) (B : Type u) [CommRing B] [Algebra K B] [Module.Finite K B]
  (e : K ⊗[A] C ≃ₐ[K] B) (a : A) (ha : a ≠ 0) (hJ : algebraMap A C a ∈ J)

local notation "WK" => WeilGm.groupScheme (CommRingCat.of K)
local notation "WA" => WeilGm.groupScheme (CommRingCat.of A)
local notation "D" => pairs A J
local notation "E" => genericPairsEquiv A J K B e a ha hJ
local notation "p" => Spec.algebraMap A K
local notation "π₁" => coefficientMap (AlgHom.fst K K B)
local notation "π₂" => coefficientMap (AlgHom.snd K K B)

private abbrev pairModel : IntegralModel A K (WK (K × B)) :=
  WeilGm.integralModel A K D (K × B) (E)

private abbrev baseUnitModel : IntegralModel A K (WK K) :=
  WeilGm.integralModel A K A K (Algebra.TensorProduct.rid A K K)

private theorem quotient_generic_comm :
    (GroupScheme.baseChange (p)).map (quotient A J) ≫ (baseUnitModel A K).genericIso.hom =
      (pairModel A K J B e a ha hJ).genericIso.hom ≫ (π₁) := by
  apply coefficientMap_generic_comm
  intro x
  rw [genericPairsEquiv_tmul]
  change Algebra.TensorProduct.rid A K K ((1 : K) ⊗ₜ first A J x) = _
  simp [Algebra.smul_def]

private theorem second_generic_comm :
    (GroupScheme.baseChange (p)).map (coefficientMap (second A J)) ≫
      (WeilGm.integralModel A K C B e).genericIso.hom =
    (pairModel A K J B e a ha hJ).genericIso.hom ≫ (π₂) := by
  apply coefficientMap_generic_comm
  intro x
  rw [genericPairsEquiv_tmul]
  rfl

private def genericIso : (GroupScheme.baseChange (p)).obj (group A J) ≅ WK B :=
  GroupScheme.kernelBaseChangeIso (p) (quotient A J) ≪≫
    (kernelSquareIso ((GroupScheme.baseChange (p)).map (quotient A J)) (π₁)
      (pairModel A K J B e a ha hJ).genericIso (baseUnitModel A K).genericIso
      (quotient_generic_comm A K J B e a ha hJ).symm) ≪≫
    productKernelIso K B

/-- The model of the generic Weil restriction obtained from the congruence
kernel of the finite projective coefficient algebra of pairs. -/
def integralModel : IntegralModel A K (WK B) := by
  letI := group_smooth A J
  exact { group := group A J
          genericIso := genericIso A K J B e a ha hJ }

/-- The presentation of the generic fibre uses the second projection. -/
def toAmbient : (integralModel A K J B e a ha hJ).Hom (WeilGm.integralModel A K C B e) (𝟙 _) where
  hom := GroupScheme.kernelι (quotient A J) ≫ coefficientMap (second A J)
  generic_comm := by
    change (GroupScheme.baseChange (p)).map
        (GroupScheme.kernelι (quotient A J) ≫ coefficientMap (second A J)) ≫ _ =
      (genericIso A K J B e a ha hJ).hom ≫ 𝟙 _
    rw [Category.comp_id, Functor.map_comp, Category.assoc, second_generic_comm]
    simp only [genericIso, Iso.trans_hom, productKernelIso_hom, productKernelMap]
    rw [kernelSquareIso_hom_ι_assoc]
    change (GroupScheme.baseChange (p)).map (GroupScheme.kernelι (quotient A J)) ≫ _ =
      (GroupScheme.kernelBaseChangeIso (p) (quotient A J)).hom ≫
        GroupScheme.kernelι ((GroupScheme.baseChange (p)).map (quotient A J)) ≫ _
    rw [← Category.assoc (GroupScheme.kernelBaseChangeIso (p) (quotient A J)).hom,
      GroupScheme.kernelBaseChangeIso_hom_ι]

private theorem integralPoint_val (x : (integralModel A K J B e a ha hJ).integralSections) :
    (WeilGm.rationalUnitsEquiv K B ((integralModel A K J B e a ha hJ).integralPointMap x) : B) =
      e (1 ⊗ₜ second A J ((WeilGm.sectionUnitsEquiv (CommRingCat.of A) D
        (rationalPoints.map (GroupScheme.kernelι (quotient A J)) x) : D))) := by
  have h := (toAmbient A K J B e a ha hJ).integralPointMap_naturality x
  rw [rationalPoints.map_apply (𝟙 (WK B)), Grp.id_hom_hom, Category.comp_id] at h
  rw [← h, WeilGm.rationalUnitsEquiv_integralPointMap]
  have hc : rationalPoints.map (toAmbient A K J B e a ha hJ).hom x =
      rationalPoints.map (coefficientMap (second A J))
        (rationalPoints.map (GroupScheme.kernelι (quotient A J)) x) := by
    simp only [toAmbient, rationalPoints.map_apply, Grp.comp_hom_hom, Category.assoc]
  rw [hc, coefficientMap_sectionUnits]
  rfl

set_option maxHeartbeats 2500000 in
/-- The literal integral-point image consists of units from the integral
coefficient algebra congruent to one modulo the specified ideal. -/
theorem mem_integralPoints_iff (y : rationalPoints (WK B)) :
    y ∈ (integralModel A K J B e a ha hJ).integralPoints ↔
      ∃ w : Cˣ, (w : C) - 1 ∈ J ∧ (WeilGm.rationalUnitsEquiv K B y : B) = e (1 ⊗ₜ (w : C)) := by
  let T := Over.mk (𝟙 (Spec (CommRingCat.of A)))
  let k := GroupScheme.kernelPointsEquiv (quotient A J) T
  let U := WeilGm.sectionUnitsEquiv (CommRingCat.of A) D
  let V := WeilGm.sectionUnitsEquiv (CommRingCat.of A) A
  have hfst (z : rationalPoints (WA D)) :
      V (z ≫ (quotient A J).hom.hom) = Units.map (first A J).toMonoidHom (U z) :=
    coefficientMap_sectionUnits (first A J) z
  constructor
  · rintro ⟨x, rfl⟩
    let z := U (k x).val
    have hz : first A J z = 1 := by
      have hk : (k x).val ≫ (quotient A J).hom.hom = 1 := (k x).property
      have hz' := (hfst (k x).val).symm
      rw [hk, map_one] at hz'
      exact congrArg Units.val hz'
    exact ⟨Units.map (second A J).toMonoidHom z, unit_difference_mem A J z hz,
      integralPoint_val A K J B e a ha hJ x⟩
  · rintro ⟨w, hw, hy⟩
    let x := sectionOfUnit A J w hw
    refine ⟨x, ?_⟩
    apply (WeilGm.rationalUnitsEquiv K B).injective
    apply Units.ext
    rw [integralPoint_val A K J B e a ha hJ x, hy]
    change e (1 ⊗ₜ second A J
      (U (rationalPoints.map (GroupScheme.kernelι (quotient A J)) (sectionOfUnit A J w hw)))) = _
    rw [sectionOfUnit_units, second_unitPair]

end IntegralModel
end Langlands.BruhatTits.IntegralModels.WeilCongruence
