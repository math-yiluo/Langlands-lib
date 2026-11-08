import Langlands.GroupScheme.Reductive.SplitBorelCell
import Langlands.GroupScheme.Reductive.CovariantCellFixedLine
import Langlands.GroupScheme.Reductive.CovariantPowerDescent
import Langlands.GroupScheme.Dynamic.SmoothProof
import Langlands.GroupScheme.Dynamic.ConnectedProof
import Langlands.GroupScheme.Dynamic.UnipotentConnected
import Langlands.GroupScheme.CorepresentedSmooth
import Langlands.GroupScheme.AffineCoordinatesFiniteType
import Langlands.AlgebraicGeometry.SmoothIntegralNormalStalksProof
import Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_geometricallyIntegral_of_isAlgClosed

/-! # Realizing coordinates on the unit locus of the cell coordinate -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite TensorProduct
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme
namespace SplitPinning

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (p : SplitPinning G)

local instance splitBorelCellPowerIsAffine : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom

/-- Evaluation of the extended character of a multiple is the power of the
evaluation. -/
theorem pointAlgebraHom_borelCharacterCoordinate_nsmul (lam : characterLattice p.torus)
    (n : ℕ) (T : Over (Spec (CommRingCat.of k))) (h : T ⟶ p.negativeBorel.X) :
    AffineCoordinates.pointAlgebraHom p.negativeBorel T h
        (p.borelCharacterCoordinate (n • lam)) =
      AffineCoordinates.pointAlgebraHom p.negativeBorel T h (p.borelCharacterCoordinate lam) ^ n := by
  induction n with
  | zero => rw [zero_nsmul, pow_zero, pointAlgebraHom_borelCharacterCoordinate_zero]
  | succ n ih =>
    rw [succ_nsmul, pointAlgebraHom_borelCharacterCoordinate_add, ih, pow_succ]

variable {p}

/-- A realizing coordinate takes the value of the extended character at the
negative Borel factor of a cell product, on every test scheme. -/
theorem IsRealizedBy.pointAlgebraHom_cell {lam : characterLattice p.torus}
    {f : AffineCoordinates.algebra G} (hf : p.IsRealizedBy lam f)
    (T : Over (Spec (CommRingCat.of k))) (a : T ⟶ p.negativeBorel.X)
    (u : T ⟶ p.positiveUnipotent.X) :
    AffineCoordinates.pointAlgebraHom G T
        ((a ≫ p.negativeBorelHom.hom.hom) * (u ≫ p.positiveUnipotentHom.hom.hom)) f =
      AffineCoordinates.pointAlgebraHom p.negativeBorel T a (p.borelCharacterCoordinate lam) := by
  rw [hf.2.1 T u _]
  have he := AffineCoordinates.pointAlgebraHom_leftCovariant _ _ hf.1 T a 1
  rw [mul_one, AffineCoordinates.pointAlgebraHom_one_apply, hf.2.2, map_one, mul_one] at he
  exact he

/-- The spectrum counit of a commutative algebra is bijective. -/
theorem bijective_algSpecCounit (B : CommAlgCat (CommRingCat.of k)) :
    Function.Bijective
      ((algΓAlgSpecAdjunction (CommRingCat.of k)).counit.app (op B)).unop.hom := by
  have : IsIso ((algΓAlgSpecAdjunction (CommRingCat.of k)).counit.app (op B)) := by
    have : (algSpec (CommRingCat.of k)).Full := algSpec.fullyFaithful.full
    have : (algSpec (CommRingCat.of k)).Faithful := algSpec.fullyFaithful.faithful
    infer_instance
  exact ConcreteCategory.bijective_of_isIso
    ((algΓAlgSpecAdjunction (CommRingCat.of k)).counit.app (op B)).unop

/-- A coordinate realizing `n • lam` is an `n`-th power after inverting the cell
coordinate. -/
theorem IsRealizedBy.exists_pow_eq_algebraMap {lam : characterLattice p.torus} {n : ℕ}
    {F : AffineCoordinates.algebra G} (hF : p.IsRealizedBy (n • lam) F) :
    ∃ x : Localization.Away p.cellCoordinate,
      x ^ n = algebraMap (AffineCoordinates.algebra G) _ F := by
  let B : CommAlgCat (CommRingCat.of k) :=
    CommAlgCat.of (CommRingCat.of k) (Localization.Away p.cellCoordinate)
  let φ : AffineCoordinates.algebra G ⟶ B :=
    CommAlgCat.ofHom (IsScalarTower.toAlgHom k (AffineCoordinates.algebra G)
      (Localization.Away p.cellCoordinate))
  have hε := bijective_algSpecCounit B
  let g := AffineCoordinates.algPoint G φ
  have hg := AffineCoordinates.pointAlgebraHom_algPoint G φ
  have hq : IsUnit (AffineCoordinates.pointAlgebraHom G _ g p.cellCoordinate) := by
    rw [hg]
    exact (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away p.cellCoordinate)
      p.cellCoordinate).map
      ((algΓAlgSpecAdjunction (CommRingCat.of k)).counit.app (op B)).unop.hom
  obtain ⟨a, u, hau⟩ := p.exists_factors_of_isUnit_cellCoordinate _ g hq
  obtain ⟨x, hx⟩ := hε.2
    (AffineCoordinates.pointAlgebraHom p.negativeBorel _ a (p.borelCharacterCoordinate lam))
  refine ⟨x, hε.1 ?_⟩
  rw [map_pow, hx, ← pointAlgebraHom_borelCharacterCoordinate_nsmul,
    ← hF.pointAlgebraHom_cell, ← hau, hg]
  rfl

/-! ### Saturation of realized weights -/

/-- The coordinate algebra of a smooth affine group with connected underlying space
is a domain. -/
theorem isDomain_algebra_of_smooth (H : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom H.X.hom] [Smooth H.X.hom] [ConnectedSpace H.X.left] :
    IsDomain (AffineCoordinates.algebra H) := by
  have : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom
  have : IsLocallyNoetherian H.X.left := LocallyOfFiniteType.isLocallyNoetherian H.X.hom
  have : IsIntegral H.X.left := CharacterLatticeProof.isIntegral_of_smooth k H.X.hom
  exact AutomorphicAction.coordinate_isDomain (H := H)

/-- The tensor product of the coordinate algebra of a smooth affine group with
connected underlying space with a domain is a domain over an algebraically closed
field. -/
theorem isDomain_tensor_algebra_of_smooth [IsAlgClosed k]
    (H : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom H.X.hom] [Smooth H.X.hom] [ConnectedSpace H.X.left]
    (B : Type u) [CommRing B] [Algebra k B] [IsDomain B] :
    IsDomain (AffineCoordinates.algebra H ⊗[k] B) := by
  have : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom
  have := isDomain_algebra_of_smooth H
  have : Algebra.FiniteType k (AffineCoordinates.algebra H) :=
    AffineCoordinates.algebraFiniteType H
  exact P2MW.S_AlgebraicGeometry_geometricallyIntegral_of_isAlgClosed.GeomIntegralOfIsAlgClosed.isDomain_tensorProduct_of_isAlgClosed
    (K := k) _ B

/-- The coordinate algebra of a connected reductive group is integrally closed. -/
theorem isIntegrallyClosed_algebra_of_isConnectedReductive
    (hG : IsConnectedReductive G) : IsIntegrallyClosed (AffineCoordinates.algebra G) := by
  have := AffineCoordinates.isDomain_of_isConnectedReductive G hG
  have : Smooth G.X.hom := hG.smooth
  have : Algebra.Smooth k (AffineCoordinates.algebra G) :=
    AffineCoordinates.smooth_algebra G inferInstance
  exact IsIntegrallyClosed.of_localization_maximal fun P _ _ =>
    Langlands.CommutativeAlgebra.SmoothIntegralNormalStalks.integrallyClosed_localization_of_smooth_domain
      k _ P

variable (p)

theorem smooth_negativeBorel : Smooth p.negativeBorel.X.hom := by
  have := p.isConnectedReductive.smooth
  exact (dynamicSmooth k G (Dynamic.oppositeCocharacter p.positiveGm) _ _).1
    p.isRepresentedBy_negativeBorelHom

theorem connectedSpace_negativeBorel : ConnectedSpace p.negativeBorel.X.left := by
  have := p.isConnectedReductive.smooth
  have := p.isConnectedReductive.connectedSpace
  exact DynamicConnected.connectedSpace_of_isRepresentedBy_parabolic G _
    p.isRepresentedBy_negativeBorelHom

theorem isDomain_negativeBorel_tensor [IsAlgClosed k] :
    IsDomain (AffineCoordinates.algebra p.negativeBorel ⊗[k] AffineCoordinates.algebra G) := by
  have := p.smooth_negativeBorel
  have := p.connectedSpace_negativeBorel
  have := AffineCoordinates.isDomain_of_isConnectedReductive G p.isConnectedReductive
  exact isDomain_tensor_algebra_of_smooth _ _

theorem isDomain_positiveUnipotent_tensor [IsAlgClosed k] :
    IsDomain (AffineCoordinates.algebra p.positiveUnipotent ⊗[k]
      AffineCoordinates.algebra G) := by
  have := p.isConnectedReductive.smooth
  have : Smooth p.positiveUnipotent.X.hom :=
    (dynamicSmooth k G p.positiveGm _ _).2.2 p.isRepresentedBy_positiveUnipotentHom
  have : ConnectedSpace p.positiveUnipotent.X.left :=
    DynamicConnected.connectedSpace_of_isRepresentedBy_unipotent G p.positiveGm
      p.isRepresentedBy_positiveUnipotentHom
  have := AffineCoordinates.isDomain_of_isConnectedReductive G p.isConnectedReductive
  exact isDomain_tensor_algebra_of_smooth _ _

/-- The extended character coordinate has counit one. -/
theorem counit_borelCharacterCoordinate (lam : characterLattice p.torus) :
    AffineLinearEmbedding.counit (AffineCoordinates.corepresentation p.negativeBorel)
      (p.borelCharacterCoordinate lam) = 1 := by
  have := AffineCoordinates.nontrivial_algΓ_identityTest (k := k)
  apply (algebraMap k ((algΓ (CommRingCat.of k)).obj
    (Over.mk (𝟙 (Spec (CommRingCat.of k))))).unop).injective
  rw [← AffineCoordinates.pointAlgebraHom_one_apply, pointAlgebraHom_borelCharacterCoordinate,
    map_one, Units.val_one, map_one]

variable {p}

/-- Over an algebraically closed field, a coordinate whose `n`-th power is a
realizing coordinate is itself realizing. -/
theorem IsRealizedBy.of_pow [IsAlgClosed k] {lam : characterLattice p.torus} {n : ℕ}
    (hn : 0 < n) {f F : AffineCoordinates.algebra G} (hF : p.IsRealizedBy (n • lam) F)
    (hfn : f ^ n = F) (hf : AffineLinearEmbedding.counit (AffineCoordinates.corepresentation G) f = 1) :
    p.IsRealizedBy lam f := by
  have := p.isDomain_negativeBorel_tensor
  have := p.isDomain_positiveUnipotent_tensor
  refine ⟨?_, ?_, hf⟩
  · refine AffineCoordinates.mem_leftCovariantSubspace_of_pow p.negativeBorelHom
      (p.borelCharacterCoordinate lam) hn (fun T h g => ?_)
      (p.counit_borelCharacterCoordinate lam) hf
    rw [← map_pow, hfn, mul_pow, ← pointAlgebraHom_borelCharacterCoordinate_nsmul, ← map_pow, hfn]
    exact AffineCoordinates.pointAlgebraHom_leftCovariant _ _ hF.1 T h g
  · refine AffineCoordinates.mem_rightInvariantSubspace_of_pow p.positiveUnipotentHom hn
      (fun T u g => ?_) hf
    rw [← map_pow, ← map_pow, hfn]
    exact hF.2.1 T u g

/-- Over an algebraically closed field, the realized weights are saturated: if a
positive multiple of a torus character is realized, then so is the character. -/
theorem IsRealizedWeight.of_nsmul [IsAlgClosed k] {lam : characterLattice p.torus} {n : ℕ}
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
  refine ⟨c⁻¹ • f₀, hF.of_pow hn ?_ ?_⟩
  · rw [smul_pow, hf₀n, inv_pow, hc, inv_one, one_smul]
  · rw [map_smul, smul_eq_mul]
    exact inv_mul_cancel₀ hc0

variable (p) in
/-- The realized weights form an additive submonoid of the character lattice. -/
def realizedWeights : AddSubmonoid (characterLattice p.torus) where
  carrier := {lam | p.IsRealizedWeight lam}
  add_mem' := IsRealizedWeight.add
  zero_mem' := p.isRealizedWeight_zero

theorem mem_realizedWeights {lam : characterLattice p.torus} :
    lam ∈ p.realizedWeights ↔ p.IsRealizedWeight lam :=
  Iff.rfl

/-- Over an algebraically closed field, the monoid of realized weights is saturated. -/
theorem nsmul_mem_realizedWeights_iff [IsAlgClosed k] {lam : characterLattice p.torus}
    {n : ℕ} (hn : 0 < n) : n • lam ∈ p.realizedWeights ↔ lam ∈ p.realizedWeights :=
  ⟨IsRealizedWeight.of_nsmul hn, fun h => AddSubmonoid.nsmul_mem _ h n⟩

end SplitPinning
end Langlands.GroupScheme
