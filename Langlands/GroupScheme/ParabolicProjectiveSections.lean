import Langlands.GroupScheme.Absolute.ParabolicDynamicForward
import Langlands.GroupScheme.Dynamic.FlagQuotientProof
import Langlands.GroupScheme.ProjectiveOrbitRationalPoints
import Langlands.GroupScheme.ProjectiveQuotientEmbedding
import Langlands.GroupScheme.Rational.RankOneStandardParabolicLineCharacter

/-! # Sections of the flag quotient in prescribed projective coordinates -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k]
  {G P : GroupScheme (Spec (CommRingCat.of k))} (p : P ⟶ G)
  {m : ℕ} (σ : MatrixRepresentation G (Fin (m + 1))) (j : Fin (m + 1))

/-- A proper flag quotient with sections at rational points and the projective
embedding given by a prescribed exact coordinate-line stabilizer. -/
structure ParabolicProjectiveSections where
  quotient : Over (Spec (CommRingCat.of k))
  projection : G.X ⟶ quotient
  proper : IsProper quotient.hom
  smoothProjection : Smooth projection.left
  surjectiveProjection : Surjective projection.left
  quasiCompactProjection : QuasiCompact projection.left
  fibers : ∀ (T : Over (Spec (CommRingCat.of k))) (x y : T ⟶ G.X),
    x ≫ projection = y ≫ projection ↔ x⁻¹ * y ∈ (SubgroupFunctor.range p).carrier T
  localSections : ∀ x : RingPoint k quotient k,
    ∃ (V : quotient.left.Opens) (s : openOver k quotient V ⟶ G.X),
      Set.range x.left ⊆ V ∧ s ≫ projection = openOverι k quotient V
  embedding : quotient ⟶ ProjectiveOrbit.ambient m (CommRingCat.of k)
  closed : IsClosedImmersion embedding.left
  orbit_fac : projection ≫ embedding = ProjectiveOrbit.lineOrbitMap m j σ

/-- Construct the proper quotient and rational-point sections from an opposite
cell, and descend the prescribed coordinate-line orbit map to that quotient. -/
def parabolicProjectiveSections [Infinite k]
    (hG : IsConnectedReductive G) (hp : IsParabolicSubgroup p)
    (hstab : σ.HasExactCoordinateLineStabilizer (SubgroupFunctor.range p) j) :
    ParabolicProjectiveSections p σ j := Classical.choice <| by
  have : Smooth G.X.hom := hG.smooth
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : IsClosedImmersion p.hom.hom.left := hp.isClosedSubgroup
  have : Mono p.hom.hom := Over.mono_of_mono_left _
  obtain ⟨Q, q, hsep, hft, hqc, hsm, hsurj, hqcc, hfib⟩ :=
    smoothSubgroupQuotientExistence k G P p hp.isClosedSubgroup hp.smooth
  have hproper : IsProper Q.hom := parabolicSubgroupQuotientProper k G hG.connectedSpace P p hp Q q
    hsep hft hqc hsm hsurj hqcc hfib
  have : Smooth q.left := hsm
  have : Surjective q.left := hsurj
  have : QuasiCompact q.left := hqcc
  obtain ⟨χ, hχ⟩ := exists_cocharacter_range_eq_parabolic_of_isParabolicSubgroup k G hG P p hp
  have hpχ : (Dynamic.parabolic χ).IsRepresentedBy p :=
    ⟨inferInstance, hχ⟩
  let χneg := CommGroupScheme.groupHom (Gm.powerHom (Spec (CommRingCat.of k)) (-1)) ≫ χ
  let U := Dynamic.Affine.unipotentScheme χneg
  let iU : U ⟶ G := Dynamic.Affine.unipotentHom χneg
  have : IsOpenImmersion (QuotientCell.multiplication p iU.hom.hom).left :=
    oppositeCellStatement k G χ U P iU p
      (Dynamic.Affine.isRepresentedBy_unipotentHom χneg) hpχ
  let seed := Dynamic.flagQuotientCell k p iU q hfib
  have hseed := Dynamic.range_identity_subset_flagQuotientCell k p iU q hfib
  rw [rationalPointEquiv_left] at hseed
  have hlift := Dynamic.rational_lifts_of_reductive_density k G (SubgroupFunctor.range p) q hfib
    reductiveRationalPointDensity.{u} hG seed.1 seed.2 hseed
    (Dynamic.flagQuotientCell_comp k p iU q hfib)
  exact ⟨{
    quotient := Q
    projection := q
    proper := hproper
    smoothProjection := hsm
    surjectiveProjection := hsurj
    quasiCompactProjection := hqcc
    fibers := hfib
    localSections := Dynamic.localSections_of_open_multiplication k p iU q hfib hlift
    embedding := ProjectiveOrbit.quotientOrbitMap m p j σ hstab q hfib
    closed := ProjectiveOrbit.isClosedImmersion_quotientOrbitMap m p j σ hstab q hfib
      hp.isClosedSubgroup hp.smooth
    orbit_fac := ProjectiveOrbit.fac_quotientOrbitMap m p j σ hstab q hfib }⟩

namespace ParabolicProjectiveSections

variable {p σ j} (D : ParabolicProjectiveSections p σ j)

/-- The same closed embedding in the polynomial model of projective space. -/
def polynomialEmbedding : D.quotient.left ⟶ ProjectiveSpace k m :=
  D.embedding.left ≫ RelativeProjectiveSpace.toPolynomial m (𝟙 (Spec (CommRingCat.of k)))

theorem isClosedImmersion_polynomialEmbedding : IsClosedImmersion D.polynomialEmbedding := by
  let : IsClosedImmersion D.embedding.left := D.closed
  unfold polynomialEmbedding RelativeProjectiveSpace.toPolynomial
  rw [RelativeProjectiveSpace.map_id, Category.id_comp]
  infer_instance

@[reassoc]
theorem polynomialEmbedding_toSpec :
    D.polynomialEmbedding ≫ projectiveSpaceToSpec k m = D.quotient.hom := by
  rw [polynomialEmbedding, Category.assoc, RelativeProjectiveSpace.toPolynomial_toSpec,
    Category.comp_id]
  exact Over.w D.embedding

/-- The projective embedding on the image of a rational point has the
homogeneous coordinates of the prescribed representation orbit. -/
theorem hasCoordinates (x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) :
    ProjectiveSpace.HasCoordinates
      (((x ≫ D.projection).left ≫ D.polynomialEmbedding) (IsLocalRing.closedPoint k))
        ((σ.rationalMatrix x).val *ᵥ Pi.single j 1) := by
  rw [polynomialEmbedding, ← Category.assoc, ← Over.comp_left, Category.assoc, D.orbit_fac]
  exact ProjectiveOrbit.hasCoordinates_orbitMap m σ j x

end ParabolicProjectiveSections

end Langlands.GroupScheme
