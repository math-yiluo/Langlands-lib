import Langlands.GroupScheme.Reductive.SplitBorelCellPower
import Langlands.GroupScheme.SmoothConnectedGeometryProof
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Saturation of realized weights over an arbitrary field -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite TensorProduct
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace AffineCoordinates

/-- Over an arbitrary field `k`, two elements with the same positive power differ by a
scalar factor from `k`, provided the base change to an algebraically closed extension
is a domain and the second element has nonzero value at a `k`-rational point. -/
theorem exists_eq_algebraMap_mul_of_pow_eq_of_isDomain_baseChange {k R : Type*} [Field k]
    [CommRing R] [Algebra k R] (K : Type*) [Field K] [IsAlgClosed K] [Algebra k K]
    [IsDomain (K ⊗[k] R)] (ε : R →ₐ[k] k) {n : ℕ} (hn : 0 < n) {y z : R}
    (h : y ^ n = z ^ n) (hz : ε z ≠ 0) : ∃ ζ : k, y = algebraMap k R ζ * z := by
  let inc : R →ₐ[k] K ⊗[k] R := Algebra.TensorProduct.includeRight
  obtain ⟨ξ, hξ⟩ := exists_eq_algebraMap_mul_of_pow_eq (k := K) (R := K ⊗[k] R) hn
    (y := inc y) (z := inc z) (by rw [← map_pow, ← map_pow, h])
  let ε' : K ⊗[k] R →ₐ[K] K :=
    Algebra.TensorProduct.lift (AlgHom.id K K) ((Algebra.ofId k K).comp ε)
      (fun _ _ => Commute.all _ _)
  have hε : ∀ r : R, ε' (inc r) = algebraMap k K (ε r) := fun r => by
    simp [ε', inc, Algebra.TensorProduct.lift_tmul]
  have hy := congrArg ε' hξ
  rw [map_mul, AlgHom.commutes, hε, hε, Algebra.algebraMap_self, RingHom.id_apply] at hy
  have hξ' : ξ = algebraMap k K (ε y / ε z) := by
    rw [map_div₀, hy, mul_div_assoc, div_self ((map_ne_zero _).2 hz), mul_one]
  refine ⟨ε y / ε z, ?_⟩
  apply Algebra.TensorProduct.includeRight_injective (A := K) (algebraMap k K).injective
  change inc y = inc (algebraMap k R (ε y / ε z) * z)
  rw [map_mul, AlgHom.commutes, hξ, hξ', ← IsScalarTower.algebraMap_apply]

variable {k : Type u} [Field k]
  (H G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom H.X.hom] [IsAffineHom G.X.hom]

local instance splitBorelCellSaturationInst1 : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom
local instance splitBorelCellSaturationInst2 : IsAffine H.X.left :=
  isAffine_of_isAffineHom H.X.hom

/-- The base change of the coordinate algebra of a smooth affine group with connected
underlying space to any field extension is a domain. -/
theorem isDomain_algebra_tensor_field [Smooth H.X.hom] [ConnectedSpace H.X.left]
    (K : Type u) [Field K] [Algebra k K] : IsDomain (algebra H ⊗[k] K) := by
  let eH := groupSchemeIso H
  have : IsIso eH.inv.hom.hom.left :=
    inferInstanceAs (IsIso (((Grp.forget (Over _)) ⋙ Over.forget _).map eH.inv))
  have : Smooth (Corepresented.groupScheme (functor H) (corepresentation H)).X.hom := by
    rw [← Over.w eH.hom.hom.hom]
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in
    infer_instance
  have : ConnectedSpace (Corepresented.groupScheme (functor H) (corepresentation H)).X.left :=
    Function.Surjective.connectedSpace
      (Scheme.homeoOfIso (asIso eH.inv.hom.hom.left)).surjective
      (Scheme.homeoOfIso (asIso eH.inv.hom.hom.left)).continuous
  have : IsAffineHom (Corepresented.groupScheme (functor H) (corepresentation H)).X.hom := by
    change IsAffineHom (Spec.map (CommRingCat.ofHom (algebraMap k (algebra H))))
    infer_instance
  have hgi : GeometricallyIntegral
      (Corepresented.groupScheme (functor H) (corepresentation H)).X.hom :=
    smoothConnectedAffineGeometry.1 k _ inferInstance inferInstance inferInstance
  have hpb := isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_tensorProduct k (algebra H) K)
  have hint : IsIntegral (Spec (CommRingCat.of (algebra H ⊗[k] K))) :=
    hgi.geometrically_isIntegral (Spec.map (CommRingCat.ofHom (algebraMap k K))) _ _ hpb
  exact (affine_isIntegral_iff (CommRingCat.of (algebra H ⊗[k] K))).1 hint

/-- For smooth affine groups `H` and `G` with connected underlying spaces, the base
change of `algebra H ⊗ algebra G` to any field extension is a domain. -/
theorem isDomain_field_tensor_algebra_tensor [Smooth H.X.hom] [ConnectedSpace H.X.left]
    [Smooth G.X.hom] [ConnectedSpace G.X.left] (K : Type u) [Field K] [Algebra k K] :
    IsDomain (K ⊗[k] (algebra H ⊗[k] algebra G)) := by
  have := isDomain_algebra_tensor_field G K
  let L := FractionRing (algebra G ⊗[k] K)
  have := isDomain_algebra_tensor_field H L
  let j : algebra H ⊗[k] (algebra G ⊗[k] K) →ₐ[k] algebra H ⊗[k] L :=
    Algebra.TensorProduct.map (AlgHom.id k (algebra H))
      (IsScalarTower.toAlgHom k (algebra G ⊗[k] K) L)
  have hinj : Function.Injective j :=
    Module.Flat.lTensor_preserves_injective_linearMap (M := algebra H)
      (IsScalarTower.toAlgHom k (algebra G ⊗[k] K) L).toLinearMap
      (IsFractionRing.injective (algebra G ⊗[k] K) L)
  have : IsDomain (algebra H ⊗[k] (algebra G ⊗[k] K)) := hinj.isDomain j.toRingHom
  let e : K ⊗[k] (algebra H ⊗[k] algebra G) ≃ₐ[k] algebra H ⊗[k] (algebra G ⊗[k] K) :=
    (Algebra.TensorProduct.comm k K _).trans (Algebra.TensorProduct.assoc k k k _ _ _)
  exact e.toMulEquiv.isDomain

variable {H G}

/-- Over an arbitrary field, a coordinate with counit one is left covariant for a
coordinate `χ` with counit one as soon as its `n`-th power satisfies the `n`-th power
of the covariance equation on every scheme test, provided the base change of the
tensor product of the two coordinate algebras to an algebraic closure is a domain. -/
theorem mem_leftCovariantSubspace_of_pow_of_isDomain_baseChange
    [IsDomain (AlgebraicClosure k ⊗[k] (algebra H ⊗[k] algebra G))] (i : H ⟶ G)
    (χ : algebra H) {f : algebra G} {n : ℕ} (hn : 0 < n)
    (hpow : ∀ (T : Over (Spec (CommRingCat.of k))) (h : T ⟶ H.X) (g : T ⟶ G.X),
      pointAlgebraHom G T ((h ≫ i.hom.hom) * g) f ^ n =
        (pointAlgebraHom H T h χ * pointAlgebraHom G T g f) ^ n)
    (hχ : AffineLinearEmbedding.counit (corepresentation H) χ = 1)
    (hf : AffineLinearEmbedding.counit (corepresentation G) f = 1) :
    f ∈ leftCovariantSubspace i χ := by
  let : Coalgebra k (algebra G) :=
    (AffineLinearEmbedding.bialgebra (corepresentation G)).toCoalgebra
  let r : algebra G →ₐ[k] algebra H := (AffineHomImageHopfAdapter.pullback i).hom.toAlgHom
  let B : CommAlgCat (CommRingCat.of k) := CommAlgCat.of _ (algebra H ⊗[k] algebra G)
  let ε : algebra H ⊗[k] algebra G →ₐ[k]
      ((algΓ (CommRingCat.of k)).obj ((algSpec (CommRingCat.of k)).obj (op B))).unop :=
    ((algΓAlgSpecAdjunction (CommRingCat.of k)).counit.app (op B)).unop.hom
  let φL : algebra H ⟶ B := CommAlgCat.ofHom Algebra.TensorProduct.includeLeft
  let φR : algebra G ⟶ B := CommAlgCat.ofHom Algebra.TensorProduct.includeRight
  have e := hpow _ (algPoint H φL) (algPoint G φR)
  rw [pointAlgebraHom_mul, AffineHomImageHopfAdapter.pointAlgebraHom_pullback,
    pointAlgebraHom_algPoint, pointAlgebraHom_algPoint] at e
  have e' : (r.toLinearMap.rTensor (algebra G) (Coalgebra.comul f)) ^ n =
      (χ ⊗ₜ[k] f) ^ n := by
    apply counit_unop_injective B
    rw [map_pow, map_pow]
    change ε (r.toLinearMap.rTensor (algebra G) (Coalgebra.comul f)) ^ n =
      ε (χ ⊗ₜ[k] f) ^ n
    refine (congrArg (· ^ n) ((productMap_comp_include ε _).symm.trans
      (productMap_rTensor' r _ _ _))).trans (e.trans ?_)
    change (ε (χ ⊗ₜ[k] 1) * ε (1 ⊗ₜ[k] f)) ^ n = _
    rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  let ε₀ : algebra H ⊗[k] algebra G →ₐ[k] k :=
    Algebra.TensorProduct.productMap (AffineLinearEmbedding.counit (corepresentation H))
      (AffineLinearEmbedding.counit (corepresentation G))
  have hz : ε₀ (χ ⊗ₜ[k] f) ≠ 0 := by
    change AffineLinearEmbedding.counit (corepresentation H) χ *
      AffineLinearEmbedding.counit (corepresentation G) f ≠ 0
    rw [hχ, hf, one_mul]
    exact one_ne_zero
  obtain ⟨ζ, hζ⟩ := exists_eq_algebraMap_mul_of_pow_eq_of_isDomain_baseChange
    (AlgebraicClosure k) ε₀ hn e' hz
  have hmem : f ∈ leftCovariantSubspace i (ζ • χ) := by
    rw [mem_leftCovariantSubspace]
    refine hζ.trans ?_
    rw [Algebra.algebraMap_eq_smul_one (R := k) (A := algebra H ⊗[k] algebra G) ζ,
      smul_mul_assoc, one_mul, TensorProduct.smul_tmul']
  have hζ1 : ζ = 1 := by
    have := nontrivial_algΓ_identityTest (k := k)
    have he := pointAlgebraHom_leftCovariant i (ζ • χ) hmem
      (Over.mk (𝟙 (Spec (CommRingCat.of k)))) 1 1
    rw [MonObj.one_comp, mul_one, pointAlgebraHom_one_apply, pointAlgebraHom_one_apply,
      map_smul, hχ, hf, smul_eq_mul, mul_one, map_one, mul_one] at he
    exact ((algebraMap k _).injective (he.symm.trans (map_one _).symm))
  rw [hζ1, one_smul] at hmem
  exact hmem

/-- Over an arbitrary field, a coordinate with counit one is right invariant under a
group-scheme morphism as soon as its `n`-th power is, on every scheme test, provided
the base change of the tensor product of the two coordinate algebras to an algebraic
closure is a domain. -/
theorem mem_rightInvariantSubspace_of_pow_of_isDomain_baseChange
    [IsDomain (AlgebraicClosure k ⊗[k] (algebra H ⊗[k] algebra G))] (j : H ⟶ G)
    {f : algebra G} {n : ℕ} (hn : 0 < n)
    (hpow : ∀ (T : Over (Spec (CommRingCat.of k))) (u : T ⟶ H.X) (g : T ⟶ G.X),
      pointAlgebraHom G T (g * (u ≫ j.hom.hom)) f ^ n = pointAlgebraHom G T g f ^ n)
    (hf : AffineLinearEmbedding.counit (corepresentation G) f = 1) :
    f ∈ rightInvariantSubspace j := by
  have hS : ∀ (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ G.X),
      pointAlgebraHom G T g⁻¹ (antipodeCoord G f) = pointAlgebraHom G T g f := by
    intro T g
    rw [pointAlgebraHom_antipode, inv_inv]
  have hf' : AffineLinearEmbedding.counit (corepresentation G) (antipodeCoord G f) = 1 := by
    have := nontrivial_algΓ_identityTest (k := k)
    apply (algebraMap k ((algΓ (CommRingCat.of k)).obj
      (Over.mk (𝟙 (Spec (CommRingCat.of k))))).unop).injective
    rw [← pointAlgebraHom_one_apply, pointAlgebraHom_antipode, inv_one,
      pointAlgebraHom_one_apply, hf]
  have hcov : antipodeCoord G f ∈ leftCovariantSubspace j 1 := by
    refine mem_leftCovariantSubspace_of_pow_of_isDomain_baseChange j 1 hn (fun T u g => ?_)
      (map_one _) hf'
    rw [map_one, one_mul, pointAlgebraHom_antipode, pointAlgebraHom_antipode, mul_inv_rev,
      ← GrpObj.inv_comp]
    exact hpow T u⁻¹ g⁻¹
  intro T u g
  have h := pointAlgebraHom_leftCovariant j 1 hcov T u⁻¹ g⁻¹
  rw [map_one, one_mul, GrpObj.inv_comp, ← mul_inv_rev, hS, hS] at h
  exact h

end AffineCoordinates

namespace SplitPinning

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (p : SplitPinning G)

local instance splitBorelCellSaturationInst3 : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom

/-- The base change to an algebraic closure of the tensor product of the coordinate
algebras of the negative Borel subgroup and of `G` is a domain. -/
theorem isDomain_algebraicClosure_negativeBorel_tensor :
    IsDomain (AlgebraicClosure k ⊗[k] (AffineCoordinates.algebra p.negativeBorel ⊗[k]
      AffineCoordinates.algebra G)) := by
  have := p.smooth_negativeBorel
  have := p.connectedSpace_negativeBorel
  have := p.isConnectedReductive.smooth
  have := p.isConnectedReductive.connectedSpace
  exact AffineCoordinates.isDomain_field_tensor_algebra_tensor _ _ _

/-- The base change to an algebraic closure of the tensor product of the coordinate
algebras of the positive unipotent subgroup and of `G` is a domain. -/
theorem isDomain_algebraicClosure_positiveUnipotent_tensor :
    IsDomain (AlgebraicClosure k ⊗[k] (AffineCoordinates.algebra p.positiveUnipotent ⊗[k]
      AffineCoordinates.algebra G)) := by
  have := p.isConnectedReductive.smooth
  have := p.isConnectedReductive.connectedSpace
  have : Smooth p.positiveUnipotent.X.hom :=
    (dynamicSmooth k G p.positiveGm _ _).2.2 p.isRepresentedBy_positiveUnipotentHom
  have : ConnectedSpace p.positiveUnipotent.X.left :=
    DynamicConnected.connectedSpace_of_isRepresentedBy_unipotent G p.positiveGm
      p.isRepresentedBy_positiveUnipotentHom
  exact AffineCoordinates.isDomain_field_tensor_algebra_tensor _ _ _

variable {p}

/-- Over an arbitrary field, a coordinate with counit one whose `n`-th power is a
coordinate realizing `n • lam` realizes `lam`. -/
theorem IsRealizedBy.of_pow' {lam : characterLattice p.torus} {n : ℕ}
    (hn : 0 < n) {f F : AffineCoordinates.algebra G} (hF : p.IsRealizedBy (n • lam) F)
    (hfn : f ^ n = F)
    (hf : AffineLinearEmbedding.counit (AffineCoordinates.corepresentation G) f = 1) :
    p.IsRealizedBy lam f := by
  have := p.isDomain_algebraicClosure_negativeBorel_tensor
  have := p.isDomain_algebraicClosure_positiveUnipotent_tensor
  refine ⟨?_, ?_, hf⟩
  · refine AffineCoordinates.mem_leftCovariantSubspace_of_pow_of_isDomain_baseChange
      p.negativeBorelHom (p.borelCharacterCoordinate lam) hn (fun T h g => ?_)
      (p.counit_borelCharacterCoordinate lam) hf
    rw [← map_pow, hfn, mul_pow, ← pointAlgebraHom_borelCharacterCoordinate_nsmul, ← map_pow, hfn]
    exact AffineCoordinates.pointAlgebraHom_leftCovariant _ _ hF.1 T h g
  · refine AffineCoordinates.mem_rightInvariantSubspace_of_pow_of_isDomain_baseChange
      p.positiveUnipotentHom hn (fun T u g => ?_) hf
    rw [← map_pow, ← map_pow, hfn]
    exact hF.2.1 T u g

/-- Over an arbitrary field, the realized weights are saturated: if a positive multiple
of a torus character is realized, then so is the character. -/
theorem IsRealizedWeight.of_nsmul' {lam : characterLattice p.torus} {n : ℕ}
    (hn : 0 < n) (h : p.IsRealizedWeight (n • lam)) : p.IsRealizedWeight lam := by
  obtain ⟨F, hF⟩ := h
  have := AffineCoordinates.isDomain_of_isConnectedReductive G p.isConnectedReductive
  have := isIntegrallyClosed_algebra_of_isConnectedReductive p.isConnectedReductive
  let R := AffineCoordinates.algebra G
  let K := FractionRing R
  obtain ⟨x, hx⟩ := hF.exists_pow_eq_algebraMap
  have hq : IsUnit (algebraMap R K p.cellCoordinate) :=
    (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr
      (nonZeroDivisors.ne_zero p.cellCoordinate_mem_nonZeroDivisors) |>.isUnit
  let φ := IsLocalization.Away.lift p.cellCoordinate (S := Localization.Away p.cellCoordinate) hq
  have hy : (φ x) ^ n = algebraMap R K F := by
    rw [← map_pow, hx, IsLocalization.Away.lift_eq]
  obtain ⟨f₀, hf₀⟩ := IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow (R := R) hn
    (hy ▸ isIntegral_algebraMap)
  have hf₀n : f₀ ^ n = F := by
    apply IsFractionRing.injective R K
    rw [map_pow, hf₀, hy]
  let c := AffineLinearEmbedding.counit (AffineCoordinates.corepresentation G) f₀
  have hc : c ^ n = 1 := by
    change AffineLinearEmbedding.counit (AffineCoordinates.corepresentation G) f₀ ^ n = 1
    rw [← map_pow, hf₀n, hF.2.2]
  have hc0 : c ≠ 0 := by
    rintro h0
    rw [h0, zero_pow hn.ne'] at hc
    exact zero_ne_one hc
  refine ⟨c⁻¹ • f₀, hF.of_pow' hn ?_ ?_⟩
  · rw [smul_pow, hf₀n, inv_pow, hc, inv_one, one_smul]
  · rw [map_smul, smul_eq_mul]
    exact inv_mul_cancel₀ hc0

/-- Over an arbitrary field, the monoid of realized weights is saturated. -/
theorem nsmul_mem_realizedWeights_iff' {lam : characterLattice p.torus}
    {n : ℕ} (hn : 0 < n) : n • lam ∈ p.realizedWeights ↔ lam ∈ p.realizedWeights :=
  ⟨IsRealizedWeight.of_nsmul' hn, fun h => AddSubmonoid.nsmul_mem _ h n⟩

end SplitPinning

end Langlands.GroupScheme
