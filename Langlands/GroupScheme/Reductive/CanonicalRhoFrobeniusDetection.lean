import Langlands.GroupScheme.Reductive.CanonicalRhoUnipotentRestriction
import Langlands.GroupScheme.Reductive.UnipotentCoordinateInvariance
import Langlands.GroupScheme.HomogeneousCharacterProducts

/-! # Fixed-height detection of the entire canonical induced space -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048

namespace Langlands.GroupScheme.SplitPinning

open AffineCoordinates FrobeniusRootCurveCutoff FrobeniusCovariantInvariants

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (p : SplitPinning G) [Fintype p.rootIndex]
    (hspan : p.rootDatum.corootSpan ℤ = ⊤)

local notation "ν₀" =>
  p.rootDatum.Polarization (Langlands.IntegralWeylVector.rho p.rootDatum p.base hspan)
local notation "λ₀" => CommGroupScheme.groupHom ν₀ ≫ p.inclusion
local notation "λ₋" => CommGroupScheme.groupHom (-ν₀) ≫ p.inclusion
local notation "D" => Dynamic.Affine.unipotentScheme λ₋
local notation "iD" => Dynamic.Affine.unipotentHom λ₋
local notation "U" => Standard.unipotentScheme p.inclusion (-ν₀) ∅
local notation "iU" => Standard.unipotentHom p.inclusion (-ν₀) ∅
local notation "iP" => Dynamic.Affine.parabolicHom λ₀
local notation "χ₀" => Dynamic.negativeRhoCoordinate
  (Dynamic.Affine.isRepresentedBy_parabolicHom λ₀)
  (p.isRootDatum.isRepresentedBy_centralizer_polarization_rho p.base hspan
    p.isConnectedReductive p.isSplitTorus p.isMaximalTorus)
  p.rootDatum p.base hspan

local instance {K : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom K.X.hom] :
    IsAffine K.X.left := isAffine_of_isAffineHom K.X.hom

local instance : IsAffineHom (D).X.hom :=
  (Dynamic.Affine.isClosedSubgroup_unipotentHom λ₋).isAffineHom

local instance : IsAffineHom (Dynamic.Affine.parabolicScheme λ₀).X.hom :=
  (Dynamic.Affine.isClosedSubgroup_parabolicHom λ₀).isAffineHom

/-- Every intrinsic simple root of the opposite-rho chamber is the negative
of an actual simple root of the supplied base. -/
theorem exists_simple_of_mem_simpleRelativeRoots_oppositeRho
    {a : characterLattice p.torus} (ha : a ∈ simpleRelativeRoots p.inclusion (-ν₀)) :
    ∃ s : p.base.support, -(p.rootDatum.root s) = a := by
  have hneg : -a ∈ roots p.inclusion := p.isRootDatum.neg_mem_roots ha.1.1
  obtain ⟨r, hr⟩ : ∃ r, p.rootDatum.root r = -a := by
    rwa [← p.isRootDatum.2.1, Set.mem_range] at hneg
  have hpos : p.base.IsPos r := by
    apply (p.isRootDatum.latticePairing_root_polarization_rho_pos_iff
      p.base hspan r).mp
    rw [hr]
    simpa only [map_neg, LinearMap.neg_apply] using ha.1.2
  have hs : p.base.IsPos r ∧
      (p.rootDatum.root r = -a → r ∈ p.base.support) := by
    apply hpos.induction_on_add
    · intro s hs
      exact ⟨p.base.isPos_of_mem_support hs, fun _ => hs⟩
    · intro s t z hz hs ht
      refine ⟨hs.1.add (p.base.isPos_of_mem_support ht) hz, ?_⟩
      intro hza
      exfalso
      apply ha.2
      have hroot (s : p.rootIndex) (hs : p.base.IsPos s) :
          -p.rootDatum.root s ∈ positiveRelativeRoots p.inclusion (-ν₀) := by
        refine ⟨p.isRootDatum.neg_mem_roots (p.root_mem_relativeRoots s), ?_⟩
        simpa only [map_neg, LinearMap.neg_apply, neg_neg] using
          (p.isRootDatum.latticePairing_root_polarization_rho_pos_iff
            p.base hspan s).mpr hs
      refine ⟨-p.rootDatum.root s, hroot s hs.1,
        -p.rootDatum.root t, hroot t (p.base.isPos_of_mem_support ht), ?_⟩
      rw [← neg_add, ← hz, hza, neg_neg]
  exact ⟨⟨r, hs.2 hr⟩, by simp only [hr, neg_neg]⟩

variable [IsAlgClosed k]

/-- Right invariance under the actual height-r origin subgroup forces a
Steinberg covariant to have its identity value on the whole opposite group. -/
theorem canonicalRho_eq_identityValue_of_originInvariant
    (q : ℕ) [ExpChar k q] (r : ℕ)
    {f : algebra G}
    (hf : f ∈ p.canonicalRhoCovariantSubspace hspan (q ^ r - 1))
    (hfrob : ∀ (V : Over (Spec (CommRingCat.of k))) (g : V ⟶ G.X)
      (h : V ⟶ (U).X), IsOriginTestPoint U q r V h →
        pointAlgebraHom G V (g * (h ≫ (iU).hom.hom)) f =
          pointAlgebraHom G V g f)
    (V : Over (Spec (CommRingCat.of k))) (x : V ⟶ (U).X) :
    pointAlgebraHom G V (x ≫ (iU).hom.hom) f =
      pointAlgebraHom G V 1 f := by
  let : Smooth G.X.hom := p.isConnectedReductive.smooth
  let : ConnectedSpace G.X.left := p.isConnectedReductive.connectedSpace
  let : Smooth (D).X.hom := (dynamicSmooth k G λ₋ D iD).2.2
    (Dynamic.Affine.isRepresentedBy_unipotentHom λ₋)
  let hU := Standard.isRepresentedBy_unipotentHom_empty p.inclusion (-ν₀) p.isSplitTorus
  let hD := Dynamic.Affine.isRepresentedBy_unipotentHom λ₋
  let e := hU.isoOfIsRepresentedBy hD
  have he : e.hom ≫ iD = iU := hU.isoOfIsRepresentedBy_hom_comp hD
  have hei : e.inv ≫ iU = iD := by
    rw [← he, ← Category.assoc, e.inv_hom_id, Category.id_comp]
  let b := p.canonicalRhoUnipotentRestriction hspan f
  have hb : ∀ (W : Over (Spec (CommRingCat.of k))) (g h : W ⟶ (D).X),
      IsOriginTestPoint D q r W h →
        pointAlgebraHom D W (g * h) b = pointAlgebraHom D W g b := by
    intro W g h hh
    have hhU := isOriginTestPoint_map q r e.inv W h hh
    have hhf := hfrob W (g ≫ (iD).hom.hom) (h ≫ e.inv.hom.hom) hhU
    dsimp only [b]
    rw [p.pointAlgebraHom_canonicalRhoUnipotentRestriction hspan W (g * h) f,
      p.pointAlgebraHom_canonicalRhoUnipotentRestriction hspan W g f]
    simpa only [MonObj.mul_comp, Category.assoc,
      ← Grp.comp_hom_hom e.inv iU, hei] using hhf
  have hgen : ∀ a ∈ simpleRelativeRoots p.inclusion (-ν₀),
      ∀ (y g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ (D).X),
        y ≫ (iD).hom.hom ∈ (RelativeRoot.subgroup p.inclusion a).carrier _ →
          pointAlgebraHom D _ (y * g) b = pointAlgebraHom D _ g b := by
    intro a ha y g hy
    obtain ⟨s, rfl⟩ := p.exists_simple_of_mem_simpleRelativeRoots_oppositeRho hspan ha
    rw [← (p.linkedRootParametrization s).negative_represents.2] at hy
    obtain ⟨z, hz⟩ := SubgroupFunctor.mem_range.mp hy
    have hyz : z ≫ (p.linkedNegativeSimpleUnipotentMap hspan s).hom.hom = y := by
      have : Mono (iD).hom.hom := hD.1
      apply (cancel_mono (iD).hom.hom).mp
      rw [Category.assoc, ← Grp.comp_hom_hom,
        linkedNegativeSimpleUnipotentMap_comp]
      exact hz
    rw [← hyz]
    exact p.canonicalRhoUnipotentRestriction_steinberg_leftInvariant
      hspan q r hf hb s _ z g
  have hgeneric : IsGenericCocharacter p.inclusion (-ν₀) := by
    intro a ha
    simpa only [map_neg, neg_ne_zero] using
      p.isRootDatum.polarization_rho_isGeneric p.base hspan a ha
  have hc := UnipotentCoordinateInvariance.eq_identityValue_of_simpleRoots
    p.isConnectedReductive p.isSplitTorus p.isMaximalTorus p.isRootDatum hgeneric
    iD hD (Dynamic.Affine.isClosedSubgroup_unipotentHom λ₋) b hgen
    V (x ≫ e.hom.hom.hom)
  dsimp only [b] at hc
  rw [p.pointAlgebraHom_canonicalRhoUnipotentRestriction hspan V (x ≫ e.hom.hom.hom) f,
    p.pointAlgebraHom_canonicalRhoUnipotentRestriction hspan V 1 f] at hc
  simpa only [Category.assoc, ← Grp.comp_hom_hom e.hom iD, he, MonObj.one_comp] using hc

/-- Actual height-r Frobenius restriction of the entire canonical induced
space at the Steinberg exponent. -/
def canonicalRhoFrobeniusRestriction (q : ℕ) [ExpChar k q] (r : ℕ) :
    p.canonicalRhoCovariantSubspace hspan (q ^ r - 1) →ₗ[k]
      MatrixRepresentation.FrobeniusCoordinateModel.quotientAlgebra U q r :=
  Dynamic.oppositeUnipotentFrobeniusRestriction p.inclusion ν₀ (χ₀ ^ (q ^ r - 1)) q r

/-- The same-height Frobenius restriction is injective on the entire
canonical covariant space, with no dimension or irreducibility premise. -/
theorem canonicalRhoFrobeniusRestriction_injective
    (q : ℕ) [ExpChar k q] (r : ℕ) :
    Function.Injective (p.canonicalRhoFrobeniusRestriction hspan q r) := by
  classical
  let : Smooth G.X.hom := p.isConnectedReductive.smooth
  by_contra hnot
  obtain ⟨f, hne, hz, hfrob⟩ :=
    exists_originInvariant_of_not_injective p.inclusion ν₀ (χ₀ ^ (q ^ r - 1))
      q r p.isSplitTorus hnot
  have hq : FrobeniusCovariantKernel.restrictionCoalgebra iU q r
      (f : algebra G) = 0 := by
    rw [FrobeniusCovariantKernel.restrictionCoalgebra_eq_oppositeUnipotentFrobeniusRestriction]
    exact hz
  let : Coalgebra k (algebra G) :=
    (AffineLinearEmbedding.bialgebra (corepresentation G)).toCoalgebra
  have hε : AffineLinearEmbedding.counit (corepresentation G) (f : algebra G) = 0 := by
    have hc := LinearMap.congr_fun
      (FrobeniusCovariantKernel.restrictionCoalgebra iU q r).counit_comp
      (f : algebra G)
    change Coalgebra.counit (R := k)
      (FrobeniusCovariantKernel.restrictionCoalgebra iU q r (f : algebra G)) =
        AffineLinearEmbedding.counit (corepresentation G) (f : algebra G) at hc
    rw [hq, map_zero] at hc
    exact hc.symm
  have hrest : covariantCellRestriction iP iU (χ₀ ^ (q ^ r - 1)) f = 0 := by
    apply (globalAlgHom_bijective U).1
    rw [map_zero, ← pointAlgebraHom_id_apply]
    have hc := p.canonicalRho_eq_identityValue_of_originInvariant hspan q r
      f.property hfrob (U).X (𝟙 (U).X)
    rw [pointAlgebraHom_one, AlgHom.comp_apply, hε, map_zero] at hc
    rw [AffineHomImageHopfAdapter.pointAlgebraHom_pullback iU (U).X (𝟙 (U).X),
      AlgHom.comp_apply] at hc
    exact hc
  apply hne
  apply Dynamic.oppositeUnipotentRestriction_injective p.inclusion ν₀
    p.isConnectedReductive p.isSplitTorus (χ₀ ^ (q ^ r - 1))
  change lieCoordinateAlgEquiv U
    (covariantCellRestriction iP iU (χ₀ ^ (q ^ r - 1)) f) = _
  rw [hrest, map_zero, map_zero]

/-- Fixed-height detection proves that the entire canonical induced space
is finite dimensional. -/
theorem finite_canonicalRhoCovariantSubspace
    (q : ℕ) [ExpChar k q] (r : ℕ) :
    Module.Finite k (p.canonicalRhoCovariantSubspace hspan (q ^ r - 1)) := by
  let : Smooth G.X.hom := p.isConnectedReductive.smooth
  let coords := Standard.unipotentPolynomialCoordinates p.inclusion (-ν₀) p.isSplitTorus
  let := coords.finite_frobeniusQuotient q r
  exact Module.Finite.of_injective (p.canonicalRhoFrobeniusRestriction hspan q r)
    (p.canonicalRhoFrobeniusRestriction_injective hspan q r)

/-- The intrinsic Lie dimension of the actual opposite unipotent group gives
the Steinberg upper bound for the entire canonical covariant space. -/
theorem finrank_canonicalRhoCovariantSubspace_le
    (q : ℕ) [ExpChar k q] (r : ℕ) :
    Module.finrank k (p.canonicalRhoCovariantSubspace hspan (q ^ r - 1)) ≤
      (q ^ r) ^ Module.finrank k (Additive (lieKernel U k)) := by
  let : Smooth G.X.hom := p.isConnectedReductive.smooth
  let coords := Standard.unipotentPolynomialCoordinates p.inclusion (-ν₀) p.isSplitTorus
  let := coords.finite_frobeniusQuotient q r
  have h := LinearMap.finrank_le_finrank_of_injective
    (p.canonicalRhoFrobeniusRestriction_injective hspan q r)
  rwa [coords.finrank_frobeniusQuotient_eq_lie q r] at h

end Langlands.GroupScheme.SplitPinning
