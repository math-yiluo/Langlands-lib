import Langlands.GroupScheme.RelativeLevi.ParabolicQuotientJetEmbedding

/-! # Stabilizing quotient jets above any prescribed order -/

noncomputable section

universe u

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Opposite
open scoped TensorProduct CategoryTheory.MonObj

namespace Langlands.GroupScheme

open Corepresented AffineCoordinates HomogeneousQuotientFromEmbedding

namespace Corepresented

variable {R : CommRingCat.{u}} {F : CommAlgCat.{u} R ⥤ GrpCat.{u}}
  {B : CommAlgCat.{u} R} {e : (F ⋙ forget GrpCat).CorepresentableBy B}
  {J : Ideal B} {n m : ℕ} {A : CommAlgCat.{u} R} {x : F.obj A}

/-- Stabilizing a higher identity jet implies stabilizing every lower one. -/
theorem Stabilizes.of_le (hnm : n ≤ m) (hx : Stabilizes e (jetIdeal e J m) x) :
    Stabilizes e (jetIdeal e J n) x := by
  induction hnm with
  | refl => exact hx
  | @step m h ih => exact ih hx.of_succ

end Corepresented

namespace SelfNormalizingAmbient

variable {R : CommRingCat.{u}} {G H : GroupScheme (Spec R)} [IsAffine G.X.left]
  {i : H ⟶ G} {Q : HomogeneousQuotient i}
  [Smooth G.X.hom] [IsProper Q.scheme.hom]

/-- Enlarge the stabilizing order, retaining the same actual subgroup and quotient. -/
def ProperQuotientJetData.atLeast (D : ProperQuotientJetData i Q) (m : ℕ) :
    {D' : ProperQuotientJetData i Q // m ≤ D'.order} := by
  let e := corepresentation G
  let I := D.ideal
  let N := max D.order m
  letI : Algebra.Smooth R (algebra G ⧸ I) := D.smooth_quotient
  have hH := isCutOutBy_range D.ideal_range
  have hstab : ∀ (A : CommAlgCat.{u} R) (x : (functor G).obj A),
      Stabilizes e (jetIdeal e I N) x ↔
        x ∈ affineSubgroups (SubgroupFunctor.range (coordinateHom i)) A := by
    intro A x
    constructor
    · intro hx
      exact (D.stabilizer A x).mp (hx.of_le (Nat.le_max_left _ _))
    · exact stabilizes_of_mem hH
  have hsG : Algebra.Smooth R (algebra G) := by
    apply smooth_of_smooth_groupScheme
    rw [← Over.w (groupSchemeIso G).hom.hom.hom]
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in
    infer_instance
  letI : Algebra.Smooth R (algebra G) := hsG
  obtain ⟨hfK, hpK⟩ := finite_projective_quotient_jetIdeal hH N
  obtain ⟨hfa, hpa⟩ := Algebra.Smooth.finite_projective_quotient_ker_pow (R := R)
    (A := algebra G) (LinearEmbedding.counit e).hom N
  letI : Module.Finite R (algebra G ⧸ augIdeal e ^ (N + 1)) := hfa
  letI : Module.Projective R (algebra G ⧸ augIdeal e ^ (N + 1)) := hpa
  letI : Module.Finite R (algebra G ⧸ jetIdeal e I N) := hfK
  letI : Module.Projective R (algebra G ⧸ jetIdeal e I N) := hpK
  letI : Smooth Q.projection.left := Q.smooth_projection
  letI : Surjective Q.projection.left := Q.surjective_projection
  letI : QuasiCompact Q.projection.left := Q.quasiCompact_projection
  let Φ := groupSchemeIso G
  have : IsIso Φ.hom.hom.hom.left :=
    (inferInstance : IsIso ((Over.forget _).mapIso ((Grp.forget _).mapIso Φ)).hom)
  let q : (groupScheme (functor G) e).X ⟶ Q.scheme := Φ.hom.hom.hom ≫ Q.projection
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
      (g h : T ⟶ (groupScheme (functor G) e).X),
      g ≫ q = h ≫ q ↔ Stabilizes e (jetIdeal e I N)
        (pointsEquiv (functor G) e T (g⁻¹ * h)) := by
    intro T g h
    change g ≫ (Φ.hom.hom.hom ≫ Q.projection) =
      h ≫ (Φ.hom.hom.hom ≫ Q.projection) ↔ _
    have hmul : (g ≫ Φ.hom.hom.hom)⁻¹ * (h ≫ Φ.hom.hom.hom) =
        (g⁻¹ * h) ≫ Φ.hom.hom.hom := by
      simp only [MonObj.mul_comp, GrpObj.inv_comp]
    rw [← Category.assoc, ← Category.assoc, Q.fibers, hstab,
      ← mem_range_iff_mem_affineSubgroups D.ideal_range, hmul]
    simpa only [Iso.symm_hom, SubgroupFunctor.comp_hom_comp_inv_hom] using
      (SubgroupFunctor.mem_range_comp_iso_iff i Φ.symm
        ((g⁻¹ * h) ≫ Φ.hom.hom.hom)).symm
  refine ⟨⟨I, D.ideal_range, D.smooth_quotient, N, hstab, hfa, hpa, hfK, hpK,
    quotientJetEmbeddingData e (jetIdeal e I N) N le_sup_right q hq⟩, ?_⟩
  exact Nat.le_max_right _ _

end SelfNormalizingAmbient

namespace ParabolicSubgroupModuli

variable {R : Type u} [CommRing R]
  {G P : GroupScheme (Spec (CommRingCat.of R))}
  (hG : IsReductive G) (i : P ⟶ G) (hi : IsRelativeParabolicSubgroup i)

/-- Concrete actual parabolic quotient jet data above any prescribed order. -/
def affineParabolicQuotientJetDataAtLeast (m : ℕ) :
    letI : IsAffineHom G.X.hom := hG.isAffineHom
    letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    {D : SelfNormalizingAmbient.ProperQuotientJetData i
      (affineParabolicQuotient hG i hi).quotient // m ≤ D.order} := by
  letI : IsAffineHom G.X.hom := hG.isAffineHom
  letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  letI : Smooth G.X.hom := hG.smooth
  letI : IsProper (affineParabolicQuotient hG i hi).quotient.scheme.hom :=
    (affineParabolicQuotient hG i hi).proper
  exact (affineParabolicQuotientJetData hG i hi).atLeast m

end ParabolicSubgroupModuli
end Langlands.GroupScheme
