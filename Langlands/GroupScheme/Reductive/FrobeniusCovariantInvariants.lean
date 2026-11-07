import Langlands.GroupScheme.Reductive.FrobeniusCovariantKernel
import Langlands.GroupScheme.Rational.TorusUnipotence.Rigidity
import Langlands.GroupScheme.MatrixRepresentation.FrobeniusOriginUniversality

/-! # Actual Frobenius-origin invariance from augmentation annihilation -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct Coalgebra Module
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option maxRecDepth 2048

namespace Langlands.GroupScheme.FrobeniusCovariantInvariants

open AffineLinearEmbedding FrobeniusCovariantKernel

section Coalgebra

variable {k B C : Type*} [Field k]
    [AddCommGroup B] [Module k B] [Coalgebra k B]
    [CommRing C] [Bialgebra k C]

/-- The actual coordinate coaction along a quotient coalgebra map. -/
def coaction (q : B →ₗc[k] C) : B →ₗ[k] B ⊗[k] C :=
  q.toLinearMap.lTensor B ∘ₗ comul

theorem contract_coaction (q : B →ₗc[k] C)
    (ell : Module.Dual k C) (b : B) :
    TensorProduct.rid k B (ell.lTensor B (coaction q b)) =
      regularAction q (WithConv.toConv ell) b := by
  change TensorProduct.rid k B (ell.lTensor B
    (q.toLinearMap.lTensor B (comul b))) =
      TensorProduct.rid k B ((ell.comp q.toLinearMap).lTensor B (comul b))
  rw [LinearMap.lTensor_comp_apply]

/-- Augmentation annihilation is scalar action for every distribution. -/
theorem regularAction_eq_smul_of_annihilated (q : B →ₗc[k] C) {b : B}
    (hb : ∀ ell : WithConv (Module.Dual k C), ell.ofConv 1 = 0 →
      regularAction q ell b = 0) (ell : WithConv (Module.Dual k C)) :
    regularAction q ell b = ell.ofConv 1 • b := by
  have hzero : (ell - ell.ofConv 1 • (1 : WithConv (Module.Dual k C))).ofConv 1 = 0 := by
    simp [LinearMap.convOne_apply]
  have h := hb _ hzero
  simpa only [map_sub, map_smul, map_one, LinearMap.sub_apply,
    LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero] using h

/-- All augmentation distributions annihilate a vector exactly when its
actual quotient coaction is constant in the quotient factor. -/
theorem coaction_eq_tmul_one_iff (q : B →ₗc[k] C) (b : B) :
    coaction q b = b ⊗ₜ[k] (1 : C) ↔
      ∀ ell : WithConv (Module.Dual k C), ell.ofConv 1 = 0 →
        regularAction q ell b = 0 := by
  constructor
  · intro h ell hell
    rw [← contract_coaction, h]
    simp [hell]
  · intro h
    apply sub_eq_zero.mp
    apply TorusUnipotence.eq_zero_of_forall_lTensor
    intro ell
    rw [map_sub, map_sub, contract_coaction,
      regularAction_eq_smul_of_annihilated q h]
    simp

end Coalgebra

section Affine

open AffineCoordinates MatrixRepresentation MatrixRepresentation.FrobeniusCoordinateModel
open MatrixRepresentation.FrobeniusConvolutionAction
open MatrixRepresentation.FrobeniusAugmentationNilpotence

variable {k : Type u} [Field k]
    {G H : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]

local instance {K : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom K.X.hom] :
    IsAffine K.X.left := isAffine_of_isAffineHom K.X.hom

local instance regularCoalgebra : Coalgebra k (algebra G) :=
  (bialgebra (corepresentation G)).toCoalgebra

variable (j : H ⟶ G) (p : ℕ) [ExpChar k p] (r : ℕ)

/-- The actual right Frobenius coaction on the original coordinate algebra. -/
def restrictionCoaction : algebra G →ₐ[k] algebra G ⊗[k] quotientAlgebra H p r :=
  (Algebra.TensorProduct.map (AlgHom.id k (algebra G))
    (restrictionAlgebra j p r)).comp (AffineLinearEmbedding.comul (corepresentation G))

theorem restrictionCoaction_eq (b : algebra G) :
    restrictionCoaction j p r b = coaction (restrictionCoalgebra j p r) b := rfl

/-- The augmentation-annihilation criterion for the actual subgroup quotient. -/
theorem restrictionCoaction_eq_tmul_one_iff (b : algebra G) :
    restrictionCoaction j p r b = b ⊗ₜ[k] (1 : quotientAlgebra H p r) ↔
      ∀ ell ∈ augmentationIdeal (G := H) p r,
        restrictionAction j p r ell b = 0 :=
  coaction_eq_tmul_one_iff (restrictionCoalgebra j p r) b

variable (H)

/-- Actual Lie coordinates evaluated on any relative test scheme. -/
def testCoordinates (V : Over (Spec (CommRingCat.of k))) (h : V ⟶ H.X) :
    CharacterUnits.Coord H →ₐ[k] ((algΓ (CommRingCat.of k)).obj V).unop :=
  (pointAlgebraHom H V h).comp (lieCoordinateAlgEquiv H).symm.toAlgHom

/-- Every coordinate vanishing at the identity has zero characteristic power
at this point of the original test scheme. -/
def IsOriginTestPoint (V : Over (Spec (CommRingCat.of k))) (h : V ⟶ H.X) : Prop :=
  ∀ a : CharacterUnits.Coord H, Lie.coordinateOrigin H a = 0 →
    testCoordinates H V h a ^ p ^ r = 0

theorem isOriginTestPoint_iff_quotientIdeal_le_ker
    (V : Over (Spec (CommRingCat.of k))) (h : V ⟶ H.X) :
    IsOriginTestPoint H p r V h ↔
      quotientIdeal H p r ≤ RingHom.ker (testCoordinates H V h).toRingHom := by
  rw [quotientIdeal, Ideal.map_le_iff_le_comap]
  constructor
  · intro hh a ha
    change testCoordinates H V h
      (characteristicPowerMap k p (CharacterUnits.Coord H) r a) = 0
    rw [characteristicPowerMap_apply, map_pow]
    exact hh a ha
  · intro hh a ha
    have hz := hh ha
    change testCoordinates H V h
      (characteristicPowerMap k p (CharacterUnits.Coord H) r a) = 0 at hz
    simpa only [characteristicPowerMap_apply, map_pow] using hz

/-- Evaluation at any intrinsic origin point factors through the actual quotient. -/
def testPointLift (V : Over (Spec (CommRingCat.of k))) (h : V ⟶ H.X)
    (hh : IsOriginTestPoint H p r V h) :
    quotientAlgebra H p r →ₐ[k] ((algΓ (CommRingCat.of k)).obj V).unop :=
  Ideal.Quotient.liftₐ (quotientIdeal H p r) (testCoordinates H V h)
    ((isOriginTestPoint_iff_quotientIdeal_le_ker H p r V h).mp hh)

@[simp]
theorem testPointLift_quotientMap (V : Over (Spec (CommRingCat.of k))) (h : V ⟶ H.X)
    (hh : IsOriginTestPoint H p r V h) (a : CharacterUnits.Coord H) :
    testPointLift H p r V h hh (quotientMap H p r a) = testCoordinates H V h a := rfl

variable {H}

theorem testPointLift_restrictionAlgebra
    (V : Over (Spec (CommRingCat.of k))) (h : V ⟶ H.X)
    (hh : IsOriginTestPoint H p r V h) (a : algebra G) :
    testPointLift H p r V h hh (restrictionAlgebra j p r a) =
      pointAlgebraHom G V (h ≫ j.hom.hom) a := by
  rw [AffineHomImageHopfAdapter.pointAlgebraHom_pullback]
  change testCoordinates H V h
    (lieCoordinateAlgEquiv H ((AffineHomImageHopfAdapter.pullback j).hom a)) = _
  change pointAlgebraHom H V h
    ((lieCoordinateAlgEquiv H).symm
      (lieCoordinateAlgEquiv H ((AffineHomImageHopfAdapter.pullback j).hom a))) = _
  rw [AlgEquiv.symm_apply_apply]
  rfl

/-- Evaluate the actual coaction on the original arbitrary test scheme. -/
theorem evaluate_restrictionCoaction
    (V : Over (Spec (CommRingCat.of k))) (g : V ⟶ G.X) (h : V ⟶ H.X)
    (hh : IsOriginTestPoint H p r V h) (b : algebra G) :
    Algebra.TensorProduct.productMap (pointAlgebraHom G V g)
      (testPointLift H p r V h hh) (restrictionCoaction j p r b) =
        pointAlgebraHom G V (g * (h ≫ j.hom.hom)) b := by
  rw [pointAlgebraHom_mul]
  change Algebra.TensorProduct.productMap _ _
    (Algebra.TensorProduct.map (AlgHom.id k (algebra G)) (restrictionAlgebra j p r)
      (AffineLinearEmbedding.comul (corepresentation G) b)) = _
  simp only [AlgHom.comp_apply]
  generalize (AffineLinearEmbedding.comul (corepresentation G) b) = z
  induction z using TensorProduct.inductionOn with
  | tmul a b =>
      simp only [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.productMap_apply_tmul,
        AlgHom.id_apply, testPointLift_restrictionAlgebra]
  | add z w hz hw => simp only [map_add, hz, hw]

/-- Augmentation annihilation gives invariance at every intrinsic origin
point on every relative test scheme, without reducedness or affineness. -/
theorem pointAlgebraHom_mul_eq_of_annihilated
    {b : algebra G}
    (hb : ∀ ell ∈ augmentationIdeal (G := H) p r,
      restrictionAction j p r ell b = 0)
    (V : Over (Spec (CommRingCat.of k))) (g : V ⟶ G.X) (h : V ⟶ H.X)
    (hh : IsOriginTestPoint H p r V h) :
    pointAlgebraHom G V (g * (h ≫ j.hom.hom)) b = pointAlgebraHom G V g b := by
  rw [← evaluate_restrictionCoaction j p r V g h hh b,
    (restrictionCoaction_eq_tmul_one_iff j p r b).mpr hb]
  simp

end Affine

section Dynamic

open AffineCoordinates MatrixRepresentation.FrobeniusCoordinateModel

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

local instance {K : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom K.X.hom] :
    IsAffine K.X.left := isAffine_of_isAffineHom K.X.hom

local notation "U" => Standard.unipotentScheme i (-ν) ∅
local notation "iU" => Standard.unipotentHom i (-ν) ∅

local instance : IsAffineHom
    (Dynamic.Affine.parabolicScheme (CommGroupScheme.groupHom ν ≫ i)).X.hom :=
  (Dynamic.Affine.isClosedSubgroup_parabolicHom (CommGroupScheme.groupHom ν ≫ i)).isAffineHom

variable (χ : algebra (Dynamic.Affine.parabolicScheme (CommGroupScheme.groupHom ν ≫ i)))
    (p : ℕ) [ExpChar k p] (r : ℕ) [Smooth G.X.hom] (hT : IsSplitTorus T.toGrp)

include hT in
/-- Failure of the actual fixed-height restriction injectivity gives a nonzero
entire-covariant kernel vector invariant under all intrinsic origin tests. -/
theorem exists_originInvariant_of_not_injective
    (hnot : ¬ Function.Injective
      (Dynamic.oppositeUnipotentFrobeniusRestriction (k := k) (G := G) (T := T) i ν χ p r)) :
    ∃ f : leftCovariantSubspace (k := k) (G := G)
      (H := Dynamic.Affine.parabolicScheme (CommGroupScheme.groupHom ν ≫ i))
      (Dynamic.Affine.parabolicHom (CommGroupScheme.groupHom ν ≫ i)) χ,
      f ≠ 0 ∧ Dynamic.oppositeUnipotentFrobeniusRestriction (k := k) (G := G) (T := T)
        i ν χ p r f = 0 ∧
      ∀ (V : Over (Spec (CommRingCat.of k))) (g : V ⟶ G.X) (h : V ⟶ (U).X),
        IsOriginTestPoint U p r V h →
        pointAlgebraHom G V (g * (h ≫ (iU).hom.hom)) (f : algebra G) =
          pointAlgebraHom G V g (f : algebra G) := by
  obtain ⟨f, hne, hzero, hann⟩ :=
    exists_annihilated_of_not_injective i ν χ p r hT hnot
  exact ⟨f, hne, hzero, pointAlgebraHom_mul_eq_of_annihilated iU p r hann⟩

end Dynamic

end Langlands.GroupScheme.FrobeniusCovariantInvariants
