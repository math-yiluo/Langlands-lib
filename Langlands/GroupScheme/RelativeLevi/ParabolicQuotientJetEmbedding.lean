import Langlands.GroupScheme.SelfNormalizingAmbient.QuotientJetEmbedding
import Langlands.GroupScheme.RelativeLevi.ParabolicAffineQuotientChart

/-! # Explicit jet embeddings of actual affine parabolic quotients -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped TensorProduct CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

open Corepresented AffineCoordinates
open HomogeneousQuotientFromEmbedding

namespace SelfNormalizingAmbient

variable {R : CommRingCat.{u}} {G H : GroupScheme (Spec R)} [IsAffine G.X.left]
  (i : H ⟶ G) (Q : HomogeneousQuotient i)

/-- Coordinate ideal, stabilizing order and explicit closed embedding for the
supplied actual homogeneous quotient. -/
structure ProperQuotientJetData where
  ideal : Ideal (algebra G)
  ideal_range : ∀ (T : Over (Spec R)) (y : T ⟶ (groupScheme (functor G) (corepresentation G)).X),
    y ∈ (SubgroupFunctor.range (coordinateHom i)).carrier T ↔
      ∀ b ∈ ideal, ((corepresentation G).homEquiv.symm
        (pointsEquiv (functor G) (corepresentation G) T y)).hom b = 0
  smooth_quotient : Algebra.Smooth R (algebra G ⧸ ideal)
  order : ℕ
  stabilizer : ∀ (A : CommAlgCat.{u} R) (x : (functor G).obj A),
    Stabilizes (corepresentation G) (jetIdeal (corepresentation G) ideal order) x ↔
      x ∈ affineSubgroups (SubgroupFunctor.range (coordinateHom i)) A
  finite_ambient : Module.Finite R (algebra G ⧸ augIdeal (corepresentation G) ^ (order + 1))
  projective_ambient : Module.Projective R
    (algebra G ⧸ augIdeal (corepresentation G) ^ (order + 1))
  finite_jet : Module.Finite R (algebra G ⧸ jetIdeal (corepresentation G) ideal order)
  projective_jet : Module.Projective R (algebra G ⧸ jetIdeal (corepresentation G) ideal order)
  embeddingData : QuotientJetEmbeddingData (corepresentation G)
    (jetIdeal (corepresentation G) ideal order) order le_sup_right
    ((groupSchemeIso G).hom.hom.hom ≫ Q.projection)

variable [Smooth G.X.hom] (hi : IsClosedSubgroup i)
  (hsH : Smooth H.X.hom) (hcH : GeometricallyConnected H.X.hom)
  (hN : (SubgroupFunctor.range i).normalizer = SubgroupFunctor.range i)
  [IsProper Q.scheme.hom]

/-- Select a finite stabilizing jet and retain its actual quotient embedding. -/
def properQuotientJetData : ProperQuotientJetData i Q := Classical.choice (by
  have : IsClosedImmersion i.hom.hom.left := hi
  let Φ := groupSchemeIso G
  have : IsIso Φ.hom.hom.hom.left :=
    (inferInstance : IsIso ((Over.forget _).mapIso ((Grp.forget _).mapIso Φ)).hom)
  have hsG : Algebra.Smooth R (algebra G) := by
    apply smooth_of_smooth_groupScheme
    rw [← Over.w Φ.hom.hom.hom]
    infer_instance
  obtain ⟨I, hI, hsI, hdom⟩ := exists_ideal_range_smooth (coordinateHom i) hsH hcH
  have hH := isCutOutBy_range hI
  have hle : ∀ (T : Over (Spec R))
      (x : T ⟶ (groupScheme (functor G) (corepresentation G)).X),
      x ∈ (SubgroupFunctor.range (coordinateHom i)).normalizer.carrier T →
        x ∈ (SubgroupFunctor.range (coordinateHom i)).carrier T := by
    intro T x hx
    have hx' : x ≫ Φ.hom.hom.hom ∈ (SubgroupFunctor.range i).normalizer.carrier T := by
      rw [SubgroupFunctor.normalizer_range_eq_comap_of_iso i Φ.symm, SubgroupFunctor.mem_comap,
        Iso.symm_hom, SubgroupFunctor.comp_hom_comp_inv_hom]
      exact hx
    rw [hN] at hx'
    have h := (SubgroupFunctor.mem_range_comp_iso_iff i Φ.symm _).2 hx'
    rwa [Iso.symm_hom, SubgroupFunctor.comp_hom_comp_inv_hom] at h
  have hself : ∀ A, normalizerFamily (affineSubgroups (SubgroupFunctor.range (coordinateHom i))) A
      ≤ affineSubgroups (SubgroupFunctor.range (coordinateHom i)) A := by
    intro A g hg
    rw [← affineSubgroups_normalizer hI A] at hg
    exact hle _ _ hg
  have hIfg : I.FG := by
    have h := Algebra.FinitePresentation.ker_fG_of_surjective (Ideal.Quotient.mkₐ R I)
      (Ideal.Quotient.mkₐ_surjective R I)
    rwa [AlgHom.toRingHom_eq_coe, Ideal.Quotient.mkₐ_ker] at h
  have hjet : ∀ n, Module.Projective R (algebra G ⧸ jetIdeal (corepresentation G) I n) :=
    fun n => (finite_projective_quotient_jetIdeal hH n).2
  obtain ⟨N, hstab⟩ := exists_stabilizes_jetIdeal_iff hH hdom hIfg hself
  obtain ⟨hfK, hpK⟩ := finite_projective_quotient_jetIdeal hH N
  obtain ⟨hfa, hpa⟩ := Algebra.Smooth.finite_projective_quotient_ker_pow (R := R)
    (A := algebra G) (LinearEmbedding.counit (corepresentation G)).hom N
  let : Module.Finite R (algebra G ⧸ augIdeal (corepresentation G) ^ (N + 1)) := hfa
  let : Module.Projective R (algebra G ⧸ augIdeal (corepresentation G) ^ (N + 1)) := hpa
  let : Module.Finite R (algebra G ⧸ jetIdeal (corepresentation G) I N) := hfK
  let : Module.Projective R (algebra G ⧸ jetIdeal (corepresentation G) I N) := hpK
  let : Smooth Q.projection.left := Q.smooth_projection
  let : Surjective Q.projection.left := Q.surjective_projection
  let : QuasiCompact Q.projection.left := Q.quasiCompact_projection
  let q : (groupScheme (functor G) (corepresentation G)).X ⟶ Q.scheme :=
    Φ.hom.hom.hom ≫ Q.projection
  have : Flat q.left := by
    change Flat (Φ.hom.hom.hom.left ≫ Q.projection.left)
    infer_instance
  have : Surjective q.left := by
    change Surjective (Φ.hom.hom.hom.left ≫ Q.projection.left)
    infer_instance
  have : QuasiCompact q.left := by
    change QuasiCompact (Φ.hom.hom.hom.left ≫ Q.projection.left)
    infer_instance
  have hq : ∀ (T : Over (Spec R))
      (g h : T ⟶ (groupScheme (functor G) (corepresentation G)).X),
      g ≫ q = h ≫ q ↔ Stabilizes (corepresentation G) (jetIdeal (corepresentation G) I N)
        (pointsEquiv (functor G) (corepresentation G) T (g⁻¹ * h)) := by
    intro T g h
    change g ≫ (Φ.hom.hom.hom ≫ Q.projection) =
      h ≫ (Φ.hom.hom.hom ≫ Q.projection) ↔ _
    have hmul : (g ≫ Φ.hom.hom.hom)⁻¹ * (h ≫ Φ.hom.hom.hom) =
        (g⁻¹ * h) ≫ Φ.hom.hom.hom := by
      simp only [MonObj.mul_comp, GrpObj.inv_comp]
    rw [← Category.assoc, ← Category.assoc, Q.fibers, hstab,
      ← mem_range_iff_mem_affineSubgroups hI, hmul]
    simpa only [Iso.symm_hom, SubgroupFunctor.comp_hom_comp_inv_hom] using
      (SubgroupFunctor.mem_range_comp_iso_iff i Φ.symm
        ((g⁻¹ * h) ≫ Φ.hom.hom.hom)).symm
  exact ⟨⟨I, hI, hsI, N, hstab, hfa, hpa, hfK, hpK,
    quotientJetEmbeddingData (corepresentation G) (jetIdeal (corepresentation G) I N)
      N le_sup_right q hq⟩⟩)

end SelfNormalizingAmbient

namespace ParabolicSubgroupModuli

variable {R : Type u} [CommRing R]
  {G P : GroupScheme (Spec (CommRingCat.of R))}
  (hG : IsReductive G) (i : P ⟶ G) (hi : IsRelativeParabolicSubgroup i)

/-- The concrete jet data for the existing actual affine parabolic quotient. -/
def affineParabolicQuotientJetData :
    letI : IsAffineHom G.X.hom := hG.isAffineHom
    letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    SelfNormalizingAmbient.ProperQuotientJetData i
      (affineParabolicQuotient hG i hi).quotient := by
  letI : IsAffineHom G.X.hom := hG.isAffineHom
  letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  letI : Smooth G.X.hom := hG.smooth
  let Q := affineParabolicQuotient hG i hi
  letI : IsProper Q.quotient.scheme.hom := Q.proper
  exact SelfNormalizingAmbient.properQuotientJetData i Q.quotient
    (relativeParabolicClosed _ G P i hG hi) hi.smooth (hi.geometricallyConnected hG)
    (affineParabolic_normalizer_eq hG i hi)

end ParabolicSubgroupModuli

end Langlands.GroupScheme
