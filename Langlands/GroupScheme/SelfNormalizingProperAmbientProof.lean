import Langlands.GroupScheme.SelfNormalizingProperAmbientStatement
import Langlands.GroupScheme.RelativeSelfNormalizerProof
import Langlands.GroupScheme.SelfNormalizingAmbient.KeyStep
import Langlands.GroupScheme.SelfNormalizingAmbient.OrbitMap
import Langlands.GroupScheme.SelfNormalizingAmbient.Translation

/-! # Proper ambient maps for self-normalizing subgroups

See the paired Markdown.
-/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped TensorProduct CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace Corepresented

variable {R : CommRingCat.{u}} {F : CommAlgCat.{u} R ⥤ GrpCat.{u}} {B : CommAlgCat.{u} R}
  {e : (F ⋙ forget GrpCat).CorepresentableBy B}
  {H : ∀ A : CommAlgCat.{u} R, Subgroup (F.obj A)} {J : Ideal B}

/-- The counit vanishes on an ideal cutting out a family of subgroups. -/
theorem counit_apply_eq_zero (hH : IsCutOutBy e H J) {b : B} (hb : b ∈ J) :
    (LinearEmbedding.counit e).hom b = 0 :=
  (hH _ 1).1 (one_mem _) b hb

/-- **Jet quotients are finite projective.** If `J` cuts out a family of subgroups and `B ⧸ J`
is smooth, then every jet quotient `B ⧸ (J ⊔ I ^ (n + 1))` is a finite projective module. -/
theorem finite_projective_quotient_jetIdeal [Algebra.Smooth R (B ⧸ J)] (hH : IsCutOutBy e H J)
    (n : ℕ) :
    Module.Finite R (B ⧸ jetIdeal e J n) ∧ Module.Projective R (B ⧸ jetIdeal e J n) := by
  let ε : B ⧸ J →ₐ[R] R := Ideal.Quotient.liftₐ J (LinearEmbedding.counit e).hom
    fun b hb => counit_apply_eq_zero hH hb
  obtain ⟨h1, h2⟩ := Algebra.Smooth.finite_projective_quotient_ker_pow ε n
  have hcomap : (RingHom.ker ε).comap (Ideal.Quotient.mkₐ R J) = augIdeal e := by
    ext b
    rfl
  have hker : RingHom.ker ε ^ (n + 1) = (augIdeal e ^ (n + 1)).map (Ideal.Quotient.mkₐ R J) := by
    rw [Ideal.map_pow, ← hcomap,
      Ideal.map_comap_of_surjective _ (Ideal.Quotient.mkₐ_surjective R J)]
  let φ : ((B ⧸ J) ⧸ RingHom.ker ε ^ (n + 1)) ≃ₐ[R] B ⧸ jetIdeal e J n :=
    (Ideal.quotientEquivAlgOfEq R hker).trans (DoubleQuot.quotQuotEquivQuotSupₐ R J _)
  exact ⟨Module.Finite.equiv φ.toLinearEquiv, Module.Projective.of_equiv φ.toLinearEquiv⟩

end Corepresented

open Corepresented AffineCoordinates SelfNormalizingAmbient

/-- **Proper ambient maps for self-normalizing subgroups.** Over an affine base, a smooth
self-normalizing closed subgroup with geometrically connected fibres of a smooth affine group
admits a map into a proper, locally finitely presented scheme whose fibres are exactly the
cosets of the subgroup. -/
theorem selfNormalizingProperAmbient : SelfNormalizingProperAmbientStatement.{u} := by
  intro R _ G H _ _ i _ hi hsH hcH hN
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : IsClosedImmersion i.hom.hom.left := hi
  set Φ := groupSchemeIso G with hΦ
  -- The coordinate algebra of `G` is smooth.
  have hsG : Algebra.Smooth (CommRingCat.of R) (algebra G) := by
    apply smooth_of_smooth_groupScheme
    have : IsIso Φ.hom.hom.hom.left :=
      (inferInstance : IsIso ((Over.forget _).mapIso ((Grp.forget _).mapIso Φ)).hom)
    rw [← Over.w Φ.hom.hom.hom]
    infer_instance
  -- The subgroup in coordinates: an ideal `I` with smooth quotient and domain fibres.
  obtain ⟨I, hI, hsI, hdom⟩ := exists_ideal_range_smooth (coordinateHom i) hsH hcH
  have hH := isCutOutBy_range hI
  -- Self-normalizing in coordinates.
  have hle : ∀ (T : Over (Spec (CommRingCat.of R)))
      (x : T ⟶ (Corepresented.groupScheme (functor G) (corepresentation G)).X),
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
  -- Finiteness and projectivity of the jet quotients.
  have hIfg : I.FG := by
    have h := Algebra.FinitePresentation.ker_fG_of_surjective (Ideal.Quotient.mkₐ (CommRingCat.of R) I)
      (Ideal.Quotient.mkₐ_surjective (CommRingCat.of R) I)
    rwa [AlgHom.toRingHom_eq_coe, Ideal.Quotient.mkₐ_ker] at h
  have hjet : ∀ n, Module.Projective (CommRingCat.of R) (algebra G ⧸ jetIdeal (corepresentation G) I n) :=
    fun n => (finite_projective_quotient_jetIdeal hH n).2
  -- Finite stabilization.
  obtain ⟨N, hstab⟩ := exists_stabilizes_jetIdeal_iff hH hdom hIfg hself
  obtain ⟨hfK, hpK⟩ := finite_projective_quotient_jetIdeal hH N
  obtain ⟨hfa, hpa⟩ := Algebra.Smooth.finite_projective_quotient_ker_pow (R := CommRingCat.of R)
    (A := algebra G) (LinearEmbedding.counit (corepresentation G)).hom N
  have : Module.Finite (CommRingCat.of R)
      (algebra G ⧸ augIdeal (corepresentation G) ^ (N + 1)) := hfa
  have : Module.Projective (CommRingCat.of R)
      (algebra G ⧸ augIdeal (corepresentation G) ^ (N + 1)) := hpa
  -- The orbit map.
  obtain ⟨Y, r, hprop, hlfp, hfib⟩ := exists_proper_orbit_map (functor G) (corepresentation G)
    (jetIdeal (corepresentation G) I N) N le_sup_right
  refine ⟨Y, Φ.inv.hom.hom ≫ r, hprop, hlfp, fun T g h => ?_⟩
  have hmul : (g ≫ Φ.inv.hom.hom)⁻¹ * (h ≫ Φ.inv.hom.hom) = (g⁻¹ * h) ≫ Φ.inv.hom.hom := by
    simp only [MonObj.mul_comp, GrpObj.inv_comp]
  rw [← Category.assoc, ← Category.assoc, hfib, hstab, ← mem_range_iff_mem_affineSubgroups hI, hmul]
  exact SubgroupFunctor.mem_range_comp_iso_iff i Φ.symm (g⁻¹ * h)

end Langlands.GroupScheme
