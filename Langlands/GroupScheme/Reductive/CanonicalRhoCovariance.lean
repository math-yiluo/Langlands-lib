import Langlands.GroupScheme.Reductive.NegativeRhoCharacter
import Langlands.GroupScheme.Reductive.CanonicalRhoDynamics
import Langlands.GroupScheme.Reductive.LinkedRootParametrization
import Langlands.GroupScheme.Dynamic.AffineRepresentability

/-! # Actual root covariance of the canonical negative-rho induced space -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]

/-- Evaluating a torus character on a cocharacter is the actual integer power
prescribed by their lattice pairing, on every relative test scheme. -/
theorem characterEval_cocharacter
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    (χ : characterLattice T) (eta : cocharacterLattice T)
    (Z : Over (Spec (CommRingCat.of k))) (z : Γ(Z.left, ⊤)ˣ) :
    characterEval ((rationalCharacters.equivCharacterLattice T).symm χ) Z
      ((Gm.pointsEquiv _ Z).symm z ≫ (CommGroupScheme.groupHom eta).hom.hom) =
        z ^ latticePairing T χ eta := by
  have he : eta ≫ χ = (gmEndEquiv k).symm (latticePairing T χ eta) := by
    rw [latticePairing_apply, AddEquiv.symm_apply_apply]
  change Gm.pointsEquiv _ Z
    (((Gm.pointsEquiv _ Z).symm z ≫ (CommGroupScheme.groupHom eta).hom.hom) ≫
      (CommGroupScheme.groupHom χ).hom.hom) = _
  rw [← comp_groupHom_comp, he, gmEndEquiv_symm_comp, map_zpow,
    MulEquiv.apply_symm_apply]

namespace Dynamic

variable {G H : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {ν : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G}
    {i : H ⟶ G} {j : T.toGrp ⟶ G}
    (hH : (parabolic ν).IsRepresentedBy i)
    (hT : (centralizer ν).IsRepresentedBy j)

include hH hT

/-- A point of the dynamic unipotent subgroup is killed by the actual Levi
retraction, when viewed in the supplied parabolic. -/
theorem limitGroupHom_eq_one_of_mem_unipotent
    (Z : Over (Spec (CommRingCat.of k))) (x : Z ⟶ H.X)
    (hx : x ≫ i.hom.hom ∈ (unipotent ν).carrier Z) :
    x ≫ (limitGroupHom hH hT).hom.hom = 1 := by
  have : Mono j.hom.hom := hT.1
  apply (cancel_mono j.hom.hom).mp
  rw [limitGroupHom_comp, MonObj.one_comp]
  exact (limit_eq_one_iff ν (hH.pointsEquiv Z x)).mpr hx

/-- An extended centralizer character is one on every dynamic unipotent point,
including nonaffine and nonreduced test schemes. -/
theorem characterEval_extendCentralizerCharacter_eq_one_of_mem_unipotent
    (χ : characterLattice T) (Z : Over (Spec (CommRingCat.of k)))
    (x : Z ⟶ H.X) (hx : x ≫ i.hom.hom ∈ (unipotent ν).carrier Z) :
    characterEval (extendCentralizerCharacter hH hT χ) Z x = 1 := by
  rw [characterEval_extendCentralizerCharacter,
    limitGroupHom_eq_one_of_mem_unipotent hH hT Z x hx, map_one]

variable [IsAffineHom H.X.hom]

local instance : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom
local instance : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom

variable {J : Type v} (Q : RootDatum J (characterLattice T) (cocharacterLattice T))
    (b : Q.Base) (hspan : Q.corootSpan ℤ = ⊤)

/-- Every coordinate in the entire induced space for a power of canonical
negative rho is left invariant under the positive dynamic unipotent subgroup. -/
theorem pointAlgebraHom_negativeRho_left_unipotent
    (m : ℕ) {f : AffineCoordinates.algebra G}
    (hf : f ∈ AffineCoordinates.leftCovariantSubspace i
      (negativeRhoCoordinate hH hT Q b hspan ^ m))
    (Z : Over (Spec (CommRingCat.of k))) (x g : Z ⟶ G.X)
    (hx : x ∈ (unipotent ν).carrier Z) :
    AffineCoordinates.pointAlgebraHom G Z (x * g) f =
      AffineCoordinates.pointAlgebraHom G Z g f := by
  let y := (hH.pointsEquiv Z).symm ⟨x, unipotent_le_parabolic ν Z hx⟩
  have hy : y ≫ i.hom.hom = x :=
    SubgroupFunctor.IsRepresentedBy.pointsEquiv_symm_comp hH _
  have hc := characterEval_extendCentralizerCharacter_eq_one_of_mem_unipotent
    hH hT (-IntegralWeylVector.rho Q b hspan) Z y (by rwa [hy])
  have he := AffineCoordinates.pointAlgebraHom_leftCovariant i
    (negativeRhoCoordinate hH hT Q b hspan ^ m) hf Z y g
  rw [hy, map_pow, negativeRhoCoordinate,
    AffineCoordinates.pointAlgebraHom_characterCoordinate] at he
  change characterEval (negativeRhoCharacter hH hT Q b hspan) Z y = 1 at hc
  rw [hc, Units.val_one, one_pow, one_mul] at he
  exact he

/-- On the actual coroot of any simple root, every coordinate of the entire
canonical induced space transforms by the inverse m-th power on all tests. -/
theorem pointAlgebraHom_negativeRho_left_simpleCoroot
    (hQ : IsRootDatumOf j Q) (r : b.support)
    (m : ℕ) {f : AffineCoordinates.algebra G}
    (hf : f ∈ AffineCoordinates.leftCovariantSubspace i
      (negativeRhoCoordinate hH hT Q b hspan ^ m))
    (Z : Over (Spec (CommRingCat.of k))) (z : Γ(Z.left, ⊤)ˣ) (g : Z ⟶ G.X) :
    AffineCoordinates.pointAlgebraHom G Z
      (((Gm.pointsEquiv _ Z).symm z ≫
        (CommGroupScheme.groupHom (Q.coroot r)).hom.hom ≫ j.hom.hom) * g) f =
      (↑z⁻¹ : Γ(Z.left, ⊤)) ^ m *
        id (α := Γ(Z.left, ⊤)) (AffineCoordinates.pointAlgebraHom G Z g f) := by
  let t := (Gm.pointsEquiv _ Z).symm z ≫
    (CommGroupScheme.groupHom (Q.coroot r)).hom.hom
  have hp : latticePairing T (-IntegralWeylVector.rho Q b hspan) (Q.coroot r) = -1 := by
    rw [← hQ.1, map_neg, LinearMap.neg_apply, IntegralWeylVector.pairing_rho_simple]
  have he := AffineCoordinates.pointAlgebraHom_leftCovariant i
    (negativeRhoCoordinate hH hT Q b hspan ^ m) hf Z
      (t ≫ (centralizerToParabolic hH hT).hom.hom) g
  rw [Category.assoc, ← Grp.comp_hom_hom, centralizerToParabolic_comp,
    map_pow, pointAlgebraHom_negativeRhoCoordinate_centralizer,
    characterEval_cocharacter, hp, zpow_neg_one] at he
  exact he

end Dynamic

namespace SplitPinning

variable {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (p : SplitPinning G) [Fintype p.rootIndex]
    (hspan : p.rootDatum.corootSpan ℤ = ⊤)

local notation "ν₀" =>
  p.rootDatum.Polarization (IntegralWeylVector.rho p.rootDatum p.base hspan)
local notation "λ₀" => CommGroupScheme.groupHom ν₀ ≫ p.inclusion

local instance {K : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom K.X.hom] :
    IsAffine K.X.left := isAffine_of_isAffineHom K.X.hom

attribute [local irreducible] RootPairing.Polarization

local instance : IsAffineHom (Dynamic.Affine.parabolicScheme λ₀).X.hom := by
  let : IsClosedImmersion (Dynamic.Affine.parabolicHom λ₀).hom.hom.left :=
    Dynamic.Affine.isClosedSubgroup_parabolicHom λ₀
  rw [← Over.w (Dynamic.Affine.parabolicHom λ₀).hom.hom]
  infer_instance

local notation "χ₀" => Dynamic.negativeRhoCoordinate
  (Dynamic.Affine.isRepresentedBy_parabolicHom λ₀)
  (p.isRootDatum.isRepresentedBy_centralizer_polarization_rho p.base hspan
    p.isConnectedReductive p.isSplitTorus p.isMaximalTorus)
  p.rootDatum p.base hspan

/-- The entire actual coordinate subspace induced from the m-th power of the
negative-rho character of the canonical polarized-rho parabolic. -/
def canonicalRhoCovariantSubspace (m : ℕ) :
    Submodule k (AffineCoordinates.algebra G) :=
  AffineCoordinates.leftCovariantSubspace (Dynamic.Affine.parabolicHom λ₀) (χ₀ ^ m)

/-- Every member of the canonical induced space is invariant under every
positive intrinsic root subgroup, on arbitrary relative test schemes. -/
theorem canonicalRhoCovariantSubspace_left_root
    (m : ℕ) {f : AffineCoordinates.algebra G}
    (hf : f ∈ p.canonicalRhoCovariantSubspace hspan m)
    (r : p.rootIndex) (hr : p.base.IsPos r)
    (Z : Over (Spec (CommRingCat.of k))) (x g : Z ⟶ G.X)
    (hx : x ∈ (RelativeRoot.subgroup p.inclusion (p.rootDatum.root r)).carrier Z) :
    AffineCoordinates.pointAlgebraHom G Z (x * g) f =
      AffineCoordinates.pointAlgebraHom G Z g f := by
  exact Dynamic.pointAlgebraHom_negativeRho_left_unipotent
    (Dynamic.Affine.isRepresentedBy_parabolicHom λ₀)
    (p.isRootDatum.isRepresentedBy_centralizer_polarization_rho p.base hspan
      p.isConnectedReductive p.isSplitTorus p.isMaximalTorus)
    p.rootDatum p.base hspan m hf Z x g
    (RelativeRoot.subgroup_le_dynamicUnipotent p.inclusion ν₀
      ((p.isRootDatum.latticePairing_root_polarization_rho_pos_iff
        p.base hspan r).mpr hr) Z hx)

/-- The fixed linked positive root maps therefore fix every coordinate in the
entire canonical induced space on every test scheme. -/
theorem canonicalRhoCovariantSubspace_left_linkedPositive
    (m : ℕ) {f : AffineCoordinates.algebra G}
    (hf : f ∈ p.canonicalRhoCovariantSubspace hspan m)
    (r : p.rootIndex) (hr : p.base.IsPos r)
    (Z : Over (Spec (CommRingCat.of k)))
    (a : Z ⟶ (VectorGroup.groupScheme (CommRingCat.of k) 1).X) (g : Z ⟶ G.X) :
    AffineCoordinates.pointAlgebraHom G Z
      ((a ≫ (p.linkedRootParametrization r).positive.hom.hom) * g) f =
        AffineCoordinates.pointAlgebraHom G Z g f := by
  apply p.canonicalRhoCovariantSubspace_left_root hspan m hf r hr Z _ g
  rw [← (p.linkedRootParametrization r).positive_represents.2]
  exact ⟨a, rfl⟩

/-- Every member of the entire canonical induced space has the prescribed
inverse-power covariance along each actual simple coroot, on all tests. -/
theorem canonicalRhoCovariantSubspace_left_simpleCoroot
    (m : ℕ) {f : AffineCoordinates.algebra G}
    (hf : f ∈ p.canonicalRhoCovariantSubspace hspan m)
    (r : p.base.support)
    (Z : Over (Spec (CommRingCat.of k))) (z : Γ(Z.left, ⊤)ˣ) (g : Z ⟶ G.X) :
    AffineCoordinates.pointAlgebraHom G Z
      (((Gm.pointsEquiv _ Z).symm z ≫
        (CommGroupScheme.groupHom (p.rootDatum.coroot r)).hom.hom ≫
          p.inclusion.hom.hom) * g) f =
      (↑z⁻¹ : Γ(Z.left, ⊤)) ^ m *
        id (α := Γ(Z.left, ⊤)) (AffineCoordinates.pointAlgebraHom G Z g f) := by
  exact Dynamic.pointAlgebraHom_negativeRho_left_simpleCoroot
    (Dynamic.Affine.isRepresentedBy_parabolicHom λ₀)
    (p.isRootDatum.isRepresentedBy_centralizer_polarization_rho p.base hspan
      p.isConnectedReductive p.isSplitTorus p.isMaximalTorus)
    p.rootDatum p.base hspan p.isRootDatum r m hf Z z g

end SplitPinning

end Langlands.GroupScheme
