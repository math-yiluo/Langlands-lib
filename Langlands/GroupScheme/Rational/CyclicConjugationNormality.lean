import Langlands.GroupScheme.Rational.CyclicConjugationCutoff
import Langlands.GroupScheme.Dynamic.LeviCocharacterCombination

/-! # Centralizer normalization of arbitrary intrinsic conjugation cutoffs -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.Corepresented

open AffineLine UnipotentPrimitive

variable {R : CommRingCat.{u}} {F : CommAlgCat.{u} R ⥤ GrpCat.{u}}
  {B : CommAlgCat.{u} R} (e : (F ⋙ forget GrpCat).CorepresentableBy B)
  (χ : (Gm (Spec R)).toGrp ⟶ groupScheme F e)

/-- Affine model points commute with change of coefficient algebra. -/
theorem affinePoint_map_coeff {A A' : CommAlgCat.{u} R} (f : A ⟶ A') (z : F.obj A) :
    affinePoint e (F.map f z) = (algSpec R).map f.op ≫ affinePoint e z := by
  apply (affinePointsEquiv F e A').injective
  rw [affinePointsEquiv_naturality]
  simp only [affinePoint, MulEquiv.apply_symm_apply]

/-- An arbitrary coefficient point in the actual centralizer is fixed by the
rank-one conjugation action; no natural global family of points is assumed. -/
theorem rankOneAction_fixed_of_mem_centralizer {A : CommAlgCat.{u} R}
    (z : F.obj A) (hz : z ∈ affineSubgroups (Dynamic.centralizer χ) A)
    (s : PUnit → Aˣ) : (rankOneAction e χ).act s z = z := by
  apply (affinePointsEquiv F e A).symm.injective
  change affinePoint e ((rankOneAction e χ).act s z) = affinePoint e z
  rw [affinePoint_rankOneAction]
  have hzz : affinePoint e z ∈ (Dynamic.centralizer χ).carrier
      ((algSpec R).obj (op A)) := hz
  have hc := Dynamic.commute_cocharacter_of_mem_centralizer χ hzz
    (unitPoint (Spec.map (CommRingCat.ofHom (algebraMap R A))) (s PUnit.unit))
  rw [← hc.eq, mul_inv_cancel_right]

/-- The twisted point of any coefficient centralizer point is constant. -/
theorem rankOne_hat_eq_of_mem_centralizer {A : CommAlgCat.{u} R}
    (z : F.obj A) (hz : z ∈ affineSubgroups (Dynamic.centralizer χ) A) :
    hat (rankOneAction e χ) z = F.map (constHom PUnit A) z := by
  change (rankOneAction e χ).act (universalUnits PUnit A) (F.map (constHom PUnit A) z) = _
  apply rankOneAction_fixed_of_mem_centralizer e χ
  change affinePoint e (F.map (constHom PUnit A) z) ∈
    (Dynamic.centralizer χ).carrier ((algSpec R).obj (op (laurent PUnit A)))
  rw [affinePoint_map_coeff]
  exact (Dynamic.centralizer χ).comp_mem _ hz

/-- Every actual intrinsic subgroup for cocharacter conjugation is normalized
by the actual centralizer on every scheme test. -/
theorem rankOneCutoff_isNormalizedBy_centralizer
    (P : AddSubsemigroup (PUnit.{u + 1} → ℤ)) :
    (cutSubgroupFunctor (isCutOutBy_weightIdeal e (rankOneAction e χ) P)).IsNormalizedBy
      (Dynamic.centralizer χ) := by
  intro T z x hz hx
  have hz' : z ∈ (cutSubgroupFunctor (isCutOutBy_affineSubgroups
      (isAffineCutOutBy_centralizer χ))).carrier T := by
    rwa [cutSubgroupFunctor_affineSubgroups (isAffineCutOutBy_centralizer χ)]
  rw [mem_cutSubgroupFunctor] at hz' hx ⊢
  simp only [map_mul, map_inv]
  exact conj_mem_weightSubgroup_of_hat_eq e (rankOneAction e χ) P
    (rankOne_hat_eq_of_mem_centralizer e χ _ hz') hx

/-- The actual centralizer action on the affine representative of any intrinsic
rank-one weight subgroup. -/
def rankOneCutoffCentralizerAction (P : AddSubsemigroup (PUnit.{u + 1} → ℤ)) :
    AutomorphicAction (centralizerScheme χ)
      (cutGroupScheme (isCutOutBy_weightIdeal e (rankOneAction e χ) P)) := by
  let hcut := isCutOutBy_weightIdeal e (rankOneAction e χ) P
  let b := AutomorphicAction.conjugation (centralizerHom χ)
  have hs : b.IsStable (cutSubgroupFunctor hcut) := by
    intro T z x hx
    have hz : z ≫ (centralizerHom χ).hom.hom ∈ (Dynamic.centralizer χ).carrier T :=
      (Dynamic.centralizer χ).comp_mem z
        (cutHom_mem (isAffineCutOutBy_centralizer χ))
    dsimp only [b]
    rw [AutomorphicAction.conjugation_act]
    exact rankOneCutoff_isNormalizedBy_centralizer e χ P T _ x hz hx
  exact b.onRepresentedSubgroup (F := cutSubgroupFunctor hcut) (cutHom hcut)
    (isRepresentedBy_cutHom hcut) hs

end Langlands.GroupScheme.Corepresented

namespace Langlands.GroupScheme.AffineCorepresentation

open Corepresented

variable {R : CommRingCat.{u}} {G : GroupScheme (Spec R)} {B : CommAlgCat.{u} R}
  (ψ : (algSpec R).obj (op B) ≅ G.X) (χ : (Gm (Spec R)).toGrp ⟶ G)

/-- The intrinsic cyclic cutoff on the actual original affine group is
normalized by its actual dynamic centralizer on ALL scheme tests. -/
theorem cyclicConjugationCutoff_isNormalizedBy_centralizer (r : ℕ) :
    (cyclicConjugationCutoff ψ χ r).IsNormalizedBy (Dynamic.centralizer χ) := by
  intro T z x hz hx
  have hz' := Dynamic.centralizer_le_comap χ (modelGroupIso ψ).inv T hz
  have h := rankOneCutoff_isNormalizedBy_centralizer (corep G ψ)
    (χ ≫ (modelGroupIso ψ).inv) (cyclicTail (fun _ : PUnit => (1 : ℤ)) r)
    T (z ≫ (modelGroupIso ψ).inv.hom.hom) (x ≫ (modelGroupIso ψ).inv.hom.hom) hz' hx
  change (z * x * z⁻¹) ≫ (modelGroupIso ψ).inv.hom.hom ∈
    (cutSubgroupFunctor (isCutOutBy_weightIdeal (corep G ψ)
      (rankOneAction (corep G ψ) (χ ≫ (modelGroupIso ψ).inv))
      (cyclicTail (fun _ : PUnit => (1 : ℤ)) r))).carrier T
  simpa only [MonObj.mul_comp, GrpObj.inv_comp] using h

end Langlands.GroupScheme.AffineCorepresentation
