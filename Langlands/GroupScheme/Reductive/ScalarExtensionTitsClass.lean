import Langlands.GroupScheme.Reductive.GaloisPinningBaseChangeScalarExtension
import Langlands.GroupScheme.SimplyConnected.TitsObstructionTransport

/-! # Comparison of Tits classes for two scalar-extension pinnings -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.GaloisPinningData.ScalarExtension

variable {k E K : Type u} [Field k] [Field E] [Field K]
  [Algebra k E] [Algebra E K] [Algebra k K] [IsScalarTower k E K]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {d : GaloisPinningData k K G}
  (P Q : ScalarExtension (E := E) d)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Compare two scalar-extension pinnings through their common original
split torus and root datum, with identity conjugation on the split group. -/
def conj : P.pinning.Conj Q.pinning where
  point := 1
  torusIso := P.torusIso ≪≫ Q.torusIso.symm
  square := by
    rw [GroupScheme.innerIso_one_hom, Category.comp_id]
    apply (cancel_mono Q.groupIso.hom).mp
    rw [Category.assoc]
    change (GroupScheme.baseChange (algebraBaseMap E K)).map P.pinning.inclusion ≫ Q.groupIso.hom =
      CommGroupScheme.groupHom (P.torusIso ≪≫ Q.torusIso.symm).hom ≫
        ((GroupScheme.baseChange (algebraBaseMap E K)).map Q.pinning.inclusion ≫ Q.groupIso.hom)
    rw [Q.inclusion_comp, ← Category.assoc]
    have ht : (P.torusIso ≪≫ Q.torusIso.symm).hom ≫ Q.torusIso.hom = P.torusIso.hom := by
      simp
    change _ = CommGroupScheme.groupHom
      ((P.torusIso ≪≫ Q.torusIso.symm).hom ≫ Q.torusIso.hom) ≫ _
    rw [ht, ← P.inclusion_comp, P.groupIso_eq, Q.groupIso_eq]
  rootDatumEquiv := Q.rootEquiv.comp P.rootEquiv.symm
  weightMap_eq := by
    intro χ
    obtain ⟨ψ, rfl⟩ := P.rootEquiv.weightEquiv.surjective χ
    change Q.rootEquiv.weightEquiv
        (P.rootEquiv.weightEquiv.symm (P.rootEquiv.weightEquiv ψ)) =
      (Q.torusIso.hom ≫ P.torusIso.inv) ≫ P.rootEquiv.weightEquiv ψ
    rw [LinearEquiv.symm_apply_apply]
    change Q.rootEquiv.weightMap ψ =
      (Q.torusIso.hom ≫ P.torusIso.inv) ≫ P.rootEquiv.weightMap ψ
    rw [Q.weight_eq, P.weight_eq]
    simp
  base_iff := by
    intro a
    change a ∈ P.pinning.base.support ↔
      Q.rootEquiv.indexEquiv (P.rootEquiv.indexEquiv.symm a) ∈ Q.pinning.base.support
    simpa only [Equiv.apply_symm_apply] using
      (P.base_eq (P.rootEquiv.indexEquiv.symm a)).symm.trans (Q.base_eq _)

@[simp] theorem conj_weightMap (χ : characterLattice d.toSplitPinning.torus) :
    (P.conj Q).weightMap (P.rootEquiv.weightEquiv χ) = Q.rootEquiv.weightEquiv χ := by
  change Q.rootEquiv.weightEquiv
    (P.rootEquiv.weightEquiv.symm (P.rootEquiv.weightEquiv χ)) = _
  rw [LinearEquiv.symm_apply_apply]

/-- The two transported dominant weights have the same actual Tits class. -/
theorem dominantTitsClass_transport [IsGalois E K]
    (χ : characterLattice d.toSplitPinning.torus)
    (hP : P.pinning.toSplitPinning.IsDominantWeight (P.rootEquiv.weightEquiv χ))
    (hQ : Q.pinning.toSplitPinning.IsDominantWeight (Q.rootEquiv.weightEquiv χ))
    (hPfix : P.pinning.IsStarFixedWeight (P.rootEquiv.weightEquiv χ))
    (hQfix : Q.pinning.IsStarFixedWeight (Q.rootEquiv.weightEquiv χ)) :
    Q.pinning.dominantTitsClass (Q.rootEquiv.weightEquiv χ) hQ hQfix =
      P.pinning.dominantTitsClass (P.rootEquiv.weightEquiv χ) hP hPfix := by
  have h := P.conj_weightMap Q χ
  simpa only [h] using (P.conj Q).dominantTitsClass_weightMap _
    hP hPfix (h.symm ▸ hQ) (h.symm ▸ hQfix)

end Langlands.GroupScheme.GaloisPinningData.ScalarExtension
