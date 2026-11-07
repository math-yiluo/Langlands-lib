import Langlands.GroupScheme.Reductive.DynamicCovariantRestriction
import Langlands.GroupScheme.MatrixRepresentation.DynamicFrobeniusCoordinates
import Langlands.GroupScheme.MatrixRepresentation.FrobeniusAugmentationNilpotence
import Langlands.GroupScheme.Chevalley.RegularQuotient

/-! # Invariant vectors in actual covariant Frobenius restriction kernels -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct Coalgebra Module
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option maxRecDepth 2048

namespace Langlands.GroupScheme.FrobeniusCovariantKernel

open AffineLinearEmbedding

section Coalgebra

variable {k B C : Type*} [Field k]
    [AddCommGroup B] [Module k B] [Coalgebra k B]
    [AddCommGroup C] [Module k C] [Coalgebra k C]

/-- Convolution is the composition law for the original right translation. -/
theorem rightAct_convMul (f g : WithConv (Module.Dual k B)) :
    rightAct (f * g).ofConv = (rightAct f.ofConv).comp (rightAct g.ofConv) := by
  have h : (f * g).ofConv = f.ofConv.comp (rightAct g.ofConv) := by
    ext b
    rw [LinearMap.convMul_apply, LinearMap.comp_apply, rightAct_apply]
    generalize (comul (R := k) b : B ⊗[k] B) = z
    induction z using TensorProduct.inductionOn with
    | tmul a b => simp [LinearMap.mul'_apply, mul_comm]
    | add z w hz hw => simp only [map_add, hz, hw]
  ext b
  rw [h, LinearMap.comp_apply, rightAct_rightAct]

/-- Pulling quotient distributions back along an actual coalgebra map acts on
the original coordinate space, including when it is infinite dimensional. -/
def regularActionLinear (q : B →ₗc[k] C) :
    WithConv (Module.Dual k C) →ₗ[k] Module.End k B where
  toFun f := rightAct (f.ofConv.comp q.toLinearMap)
  map_add' f g := by
    ext b
    simp [rightAct, LinearMap.add_comp, LinearMap.lTensor_add]
  map_smul' c f := by
    ext b
    simp [rightAct, LinearMap.smul_comp, LinearMap.lTensor_smul]

theorem regularActionLinear_one (q : B →ₗc[k] C) :
    regularActionLinear q 1 = 1 := by
  have h : (1 : WithConv (Module.Dual k C)).ofConv.comp q.toLinearMap =
      counit (R := k) := by
    ext b
    simpa only [LinearMap.comp_apply, LinearMap.convOne_apply, Algebra.algebraMap_self,
      RingHom.id_apply] using LinearMap.congr_fun q.counit_comp b
  ext b
  change rightAct _ b = b
  rw [h, rightAct_counit]

theorem regularActionLinear_mul (q : B →ₗc[k] C)
    (f g : WithConv (Module.Dual k C)) :
    regularActionLinear q (f * g) =
      regularActionLinear q f * regularActionLinear q g := by
  change rightAct ((f * g).ofConv.comp q.toLinearMap) = _
  rw [LinearMap.convMul_comp_coalgHom_distrib, rightAct_convMul]
  rfl

/-- The unital action of quotient convolution distributions on original
coordinates, obtained by actual pullback. -/
def regularAction (q : B →ₗc[k] C) :
    WithConv (Module.Dual k C) →ₐ[k] Module.End k B :=
  AlgHom.ofLinearMap (regularActionLinear q) (regularActionLinear_one q)
    (regularActionLinear_mul q)

@[simp]
theorem regularAction_apply (q : B →ₗc[k] C)
    (f : WithConv (Module.Dual k C)) (b : B) :
    regularAction q f b = rightAct (f.ofConv.comp q.toLinearMap) b := rfl

end Coalgebra

section Nilpotent

variable {k A M : Type*} [Field k] [Ring A] [Algebra k A]
    [AddCommGroup M] [Module k M]

/-- A nilpotent ideal acting on any nonzero stable subspace has a nonzero
annihilated vector. No dimension assumption on the space is used. -/
theorem exists_annihilated_mem (ρ : A →ₐ[k] Module.End k M)
    (I : Ideal A) (hI : IsNilpotent I)
    (W : Submodule k M) (hW : W ≠ ⊥)
    (hstable : ∀ a : A, ∀ v ∈ W, ρ a v ∈ W) :
    ∃ v ∈ W, v ≠ 0 ∧ ∀ a ∈ I, ρ a v = 0 := by
  obtain ⟨n, hn⟩ := hI
  have hstep : ∀ m : ℕ, ∀ v ∈ W, v ≠ 0 →
      (∀ a ∈ I ^ m, ρ a v = 0) →
      ∃ w ∈ W, w ≠ 0 ∧ ∀ a ∈ I, ρ a w = 0 := by
    intro m
    induction m with
    | zero =>
        intro v hv hne hann
        exact (hne (by
          simpa using hann 1 (by rw [Submodule.pow_zero, Ideal.one_eq_top]; trivial))).elim
    | succ m ih =>
        intro v hv hne hann
        by_cases h : ∀ a ∈ I, ρ a v = 0
        · exact ⟨v, hv, hne, h⟩
        · push Not at h
          obtain ⟨a, ha, hne'⟩ := h
          apply ih (ρ a v) (hstable a v hv) hne'
          intro c hc
          have hca : c * a ∈ I ^ (m + 1) := by
            rw [Submodule.pow_succ]
            exact Ideal.mul_mem_mul hc ha
          simpa only [map_mul, Module.End.mul_apply] using hann (c * a) hca
  obtain ⟨v, hv, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
  apply hstep n v hv hne
  intro a ha
  have ha0 : a = 0 := by simpa [hn] using ha
  rw [ha0, map_zero, LinearMap.zero_apply]

end Nilpotent

section AffineRestriction

open AffineCoordinates MatrixRepresentation.FrobeniusCoordinateModel
open MatrixRepresentation.FrobeniusDistributionAlgebra

variable {k : Type u} [Field k]
    {G H : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]

local instance {K : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom K.X.hom] :
    IsAffine K.X.left := isAffine_of_isAffineHom K.X.hom

local instance regularCoalgebra : Coalgebra k (algebra G) :=
  (bialgebra (corepresentation G)).toCoalgebra

variable (j : H ⟶ G) (p : ℕ) [ExpChar k p] (r : ℕ)

/-- Actual coordinate restriction followed by the actual Frobenius quotient. -/
def restrictionAlgebra : algebra G →ₐ[k] quotientAlgebra H p r :=
  (quotientMap H p r).comp
    ((lieCoordinateAlgEquiv H).toAlgHom.comp
      (AffineHomImageHopfAdapter.pullback j).hom.toAlgHom)

/-- The actual Frobenius restriction respects the regular coordinate coalgebra. -/
def restrictionCoalgebra : algebra G →ₗc[k] quotientAlgebra H p r where
  toLinearMap := (restrictionAlgebra j p r).toLinearMap
  counit_comp := by
    ext a
    change counit (R := k) (restrictionAlgebra j p r a) = counit (R := k) a
    change counit (R := k) (quotientMap H p r
      (lieCoordinateAlgEquiv H ((AffineHomImageHopfAdapter.pullback j).hom a))) = _
    rw [counit_quotientMap, lieCoordinateAlgEquiv_counit, corepresentation_counit G]
    exact LinearMap.congr_fun (AffineHomImageHopfAdapter.pullback j).hom.counit_comp a
  map_comp_comul := by
    ext a
    change TensorProduct.map (restrictionAlgebra j p r).toLinearMap
      (restrictionAlgebra j p r).toLinearMap (comul (R := k) a) =
        comul (R := k) (restrictionAlgebra j p r a)
    change _ = comul (R := k) (quotientMap H p r
      (lieCoordinateAlgEquiv H ((AffineHomImageHopfAdapter.pullback j).hom a)))
    have hf := LinearMap.congr_fun
      (AffineHomImageHopfAdapter.pullback j).hom.map_comp_comul a
    simp only [LinearMap.comp_apply] at hf
    rw [comul_quotientMap, ← lieCoordinateAlgEquiv_comul]
    change _ = Algebra.TensorProduct.map (quotientMap H p r) (quotientMap H p r)
      (Algebra.TensorProduct.map (lieCoordinateAlgEquiv H).toAlgHom
        (lieCoordinateAlgEquiv H).toAlgHom
          (@comul k (hopfAlgebra H) _ _ _ _ ((AffineHomImageHopfAdapter.pullback j).hom a)))
    erw [← hf]
    rw [corepresentation_comul G]
    generalize (@comul k (hopfAlgebra G) _ _ _ _ a) = z
    induction z using TensorProduct.inductionOn with
    | tmul a b =>
        simp only [TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul,
          restrictionAlgebra, AlgHom.comp_apply, AlgHom.toLinearMap_apply]
        rfl
    | add z w hz hw => simp only [map_add, hz, hw]

@[simp]
theorem restrictionCoalgebra_apply (a : algebra G) :
    restrictionCoalgebra j p r a = restrictionAlgebra j p r a := rfl

/-- The original right-regular action of actual subgroup Frobenius distributions. -/
def restrictionAction :
    MatrixRepresentation.FrobeniusConvolutionAction.DistributionAlgebra (G := H) p r →ₐ[k]
      Module.End k (algebra G) :=
  regularAction (restrictionCoalgebra j p r)

@[simp]
theorem restrictionAction_apply
    (ell : MatrixRepresentation.FrobeniusConvolutionAction.DistributionAlgebra (G := H) p r)
    (b : algebra G) :
    restrictionAction j p r ell b =
      rightAct (ell.ofConv.comp (restrictionCoalgebra j p r).toLinearMap) b := rfl

variable {P : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom P.X.hom]
    (l : P ⟶ G) (χ : algebra P)

/-- The entire covariant space intersected with the actual restriction kernel. -/
def covariantKernel : Submodule k (algebra G) :=
  leftCovariantSubspace l χ ⊓ LinearMap.ker (restrictionCoalgebra j p r).toLinearMap

/-- Both the full covariant space and the actual quotient kernel are stable;
these are proved properties of the original translation action. -/
theorem restrictionAction_mem_covariantKernel
    (ell : MatrixRepresentation.FrobeniusConvolutionAction.DistributionAlgebra (G := H) p r)
    {b : algebra G} (hb : b ∈ covariantKernel j p r l χ) :
    restrictionAction j p r ell b ∈ covariantKernel j p r l χ := by
  rw [restrictionAction_apply]
  refine ⟨?_, ?_⟩
  · exact AffineCoordinates.rightAct_mem_leftCovariantSubspace l χ
      (ell.ofConv.comp (restrictionCoalgebra j p r).toLinearMap) hb.1
  · change restrictionCoalgebra j p r
      (rightAct (ell.ofConv.comp (restrictionCoalgebra j p r).toLinearMap) b) = 0
    rw [← Chevalley.rightAct_coalgHom]
    have hb0 : restrictionCoalgebra j p r b = 0 := hb.2
    rw [hb0, map_zero]

end AffineRestriction

section DynamicKernel

open AffineCoordinates MatrixRepresentation.FrobeniusCoordinateModel
open MatrixRepresentation.FrobeniusConvolutionAction
open MatrixRepresentation.FrobeniusAugmentationNilpotence

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

local instance {K : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom K.X.hom] :
    IsAffine K.X.left := isAffine_of_isAffineHom K.X.hom

local notation "U" => Standard.unipotentScheme i (-ν) ∅
local notation "iU" => Standard.unipotentHom i (-ν) ∅
local notation "P" => Dynamic.Affine.parabolicScheme (CommGroupScheme.groupHom ν ≫ i)
local notation "iP" => Dynamic.Affine.parabolicHom (CommGroupScheme.groupHom ν ≫ i)

local instance : IsAffineHom
    (Dynamic.Affine.parabolicScheme (CommGroupScheme.groupHom ν ≫ i)).X.hom :=
  (Dynamic.Affine.isClosedSubgroup_parabolicHom (CommGroupScheme.groupHom ν ≫ i)).isAffineHom

variable (χ : AffineCoordinates.algebra (Dynamic.Affine.parabolicScheme
  (CommGroupScheme.groupHom ν ≫ i))) (p : ℕ) [ExpChar k p] (r : ℕ)

/-- The actual restriction coalgebra map agrees with the previously constructed
restriction on the entire covariant subtype. -/
theorem restrictionCoalgebra_eq_oppositeUnipotentFrobeniusRestriction
    (f : AffineCoordinates.leftCovariantSubspace (k := k) (G := G)
      (H := Dynamic.Affine.parabolicScheme (CommGroupScheme.groupHom ν ≫ i))
      (Dynamic.Affine.parabolicHom (CommGroupScheme.groupHom ν ≫ i)) χ) :
    restrictionCoalgebra iU p r (f : algebra G) =
      Dynamic.oppositeUnipotentFrobeniusRestriction (k := k) (G := G) (T := T) i ν χ p r f := rfl

local instance regularCoalgebra' : Coalgebra k (algebra G) :=
  (bialgebra (corepresentation G)).toCoalgebra

variable [Smooth G.X.hom] (hT : IsSplitTorus T.toGrp)

include hT in
/-- Failure of fixed-height injectivity produces a nonzero element of the
entire covariant kernel annihilated by every augmentation distribution.
The stability and nilpotence premises are discharged for the actual subgroup. -/
theorem exists_annihilated_of_not_injective
    (hnot : ¬ Function.Injective
      (Dynamic.oppositeUnipotentFrobeniusRestriction (k := k) (G := G) (T := T) i ν χ p r)) :
    ∃ f : AffineCoordinates.leftCovariantSubspace (k := k) (G := G)
      (H := Dynamic.Affine.parabolicScheme (CommGroupScheme.groupHom ν ≫ i))
      (Dynamic.Affine.parabolicHom (CommGroupScheme.groupHom ν ≫ i)) χ,
      f ≠ 0 ∧ Dynamic.oppositeUnipotentFrobeniusRestriction (k := k) (G := G) (T := T) i ν χ p r f = 0 ∧
      ∀ ell ∈ augmentationIdeal (G := U) p r,
        restrictionAction iU p r ell (f : algebra G) = 0 := by
  classical
  let W := covariantKernel iU p r iP χ
  have hW : W ≠ ⊥ := by
    intro hzero
    apply hnot
    apply LinearMap.ker_eq_bot.mp
    apply le_antisymm _ bot_le
    intro f hf
    have hmem : (f : algebra G) ∈ W := by
      refine ⟨f.2, ?_⟩
      change restrictionCoalgebra iU p r (f : algebra G) = 0
      rwa [restrictionCoalgebra_eq_oppositeUnipotentFrobeniusRestriction]
    have hf0 : (f : algebra G) = 0 := by simpa [hzero] using hmem
    exact Subtype.ext hf0
  have hnil : IsNilpotent (augmentationIdeal (G := U) p r) := by
    let coords := Standard.unipotentPolynomialCoordinates i (-ν) hT
    exact isNilpotent_augmentationIdeal p r hT
      (Standard.unipotentAction i (-ν) hT) (-ν) coords.weight coords.generator
      coords.bijective coords.homogeneous coords.origin_zero coords.positive
  obtain ⟨b, hb, hne, hann⟩ :=
    exists_annihilated_mem (restrictionAction iU p r) _ hnil W hW
      (fun ell _ hb => restrictionAction_mem_covariantKernel iU p r iP χ ell hb)
  refine ⟨⟨b, hb.1⟩, ?_, ?_, hann⟩
  · intro he
    exact hne (congrArg Subtype.val he)
  · rw [← restrictionCoalgebra_eq_oppositeUnipotentFrobeniusRestriction]
    exact hb.2

end DynamicKernel

end Langlands.GroupScheme.FrobeniusCovariantKernel
