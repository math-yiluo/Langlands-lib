import Langlands.GroupScheme.Dynamic.CommonCentralizerDeterminantBalance
import Langlands.GroupScheme.Dynamic.ClosedSubgroup
import Langlands.GroupScheme.Rational.LeviFactorization
import Langlands.GroupScheme.SubgroupFunctor.IntersectionNormalizer

/-! # Identity-limit subgroups inside represented centralizers -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme.Dynamic

section Restriction

variable {S : Scheme.{u}} {G M U Z : GroupScheme S}
  (chi psi : (Gm S).toGrp ⟶ G) {iM : M ⟶ G}
  (hM : (centralizer psi).IsRepresentedBy iM) (hMc : IsClosedSubgroup iM)
  (chiM : (Gm S).toGrp ⟶ M) (hchi : chiM ≫ iM = chi)
  {iU : U ⟶ G}
  (hU : (unipotent chi ⊓ centralizer psi).IsRepresentedBy iU)
  (fU : U ⟶ M) (hfU : fU ≫ iM = iU)

include hM hMc hchi hU hfU

/-- A representative of the ambient positive/zero intersection is the actual
identity-limit subgroup of the factored cocharacter inside the centralizer. -/
theorem isRepresentedBy_unipotent_centralizer_factor :
    (unipotent chiM).IsRepresentedBy fU := by
  have : Mono iM.hom.hom := hM.1
  have : Mono iU.hom.hom := hU.1
  have hfac : fU.hom.hom ≫ iM.hom.hom = iU.hom.hom := by
    rw [← Grp.comp_hom_hom, hfU]
  refine ⟨mono_of_mono_fac hfac, ?_⟩
  have hrange : SubgroupFunctor.range (fU ≫ iM) =
      SubgroupFunctor.range iM ⊓ unipotent chi := by
    rw [hfU, hU.2, hM.2]
    apply SubgroupFunctor.ext
    intro T
    exact inf_comm _ _
  have hr := SubgroupFunctor.range_eq_comap_of_range_comp_eq_inf
    fU iM (unipotent chi) hrange
  rw [← hchi, ← unipotent_eq_comap_of_isClosedSubgroup chiM iM hMc] at hr
  exact hr

variable (iZ : Z ⟶ G)
  (hZ : SubgroupFunctor.range iZ ≤ centralizer chi)
  (hZ' : SubgroupFunctor.range iZ ≤ centralizer psi)
  (fZ : Z ⟶ M) (hfZ : fZ ≫ iM = iZ)

include hMc hchi hZ hfZ

omit hM hU hfU in
/-- Factoring a homomorphism through the represented centralizer preserves
centralization of the other cocharacter. -/
theorem range_factor_le_centralizer :
    SubgroupFunctor.range fZ ≤ centralizer chiM := by
  rw [centralizer_eq_comap_of_isClosedSubgroup chiM iM hMc, hchi]
  intro T z hz
  obtain ⟨x, rfl⟩ := SubgroupFunctor.mem_range.mp hz
  change (x ≫ fZ.hom.hom) ≫ iM.hom.hom ∈ (centralizer chi).carrier T
  rw [Category.assoc, ← Grp.comp_hom_hom, hfZ]
  exact hZ T ⟨x, rfl⟩

include hM hU hfU hZ' in
/-- The action computed inside the centralizer equals the actual ambient
intersection action, on the same represented group scheme. -/
theorem centralizingUnipotentAction_eq_intersectionAction :
    centralizingUnipotentAction chiM fZ
        (range_factor_le_centralizer (chi := chi) (hMc := hMc)
          (chiM := chiM) (hchi := hchi) (iZ := iZ) (hZ := hZ)
          (fZ := fZ) (hfZ := hfZ))
        (isRepresentedBy_unipotent_centralizer_factor chi psi hM hMc chiM hchi hU fU hfU) =
      centralizingUnipotentCentralizerIntersectionAction chi psi iZ hZ hZ' hU := by
  have : Mono iU.hom.hom := hU.1
  apply AutomorphicAction.ext_act
  intro T z x
  apply (cancel_mono iU.hom.hom).mp
  calc
    _ = (_ ≫ fU.hom.hom) ≫ iM.hom.hom := by
      rw [Category.assoc, ← Grp.comp_hom_hom, hfU]
    _ = (z ≫ iZ.hom.hom) * (x ≫ iU.hom.hom) * (z ≫ iZ.hom.hom)⁻¹ := by
      rw [centralizingUnipotentAction_act_comp,
        MonObj.mul_comp, MonObj.mul_comp, GrpObj.inv_comp,
        Category.assoc, Category.assoc, ← Grp.comp_hom_hom, ← Grp.comp_hom_hom,
        hfZ, hfU]
    _ = _ := (centralizingUnipotentCentralizerIntersectionAction_act_comp
      chi psi iZ hZ hZ' hU z x).symm

end Restriction

section RationalPoints

variable {k : Type u} [Field k] {G Z : GroupScheme (Spec (CommRingCat.of k))}
  (chi psi : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G) (iZ : Z ⟶ G)
  (hZ : SubgroupFunctor.range iZ ≤ centralizer chi)
  (hZ' : SubgroupFunctor.range iZ ≤ centralizer psi)

/-- The original rational-point map into the normalizer of the literal
positive/zero intersection. -/
def centralizingUnipotentCentralizerNormalizerHom :
    rationalPoints Z →*
      Subgroup.normalizer
        ((unipotent chi ⊓ centralizer psi).carrier (Over.mk (𝟙 _)) :
          Set (rationalPoints G)) :=
  (rationalPoints.map iZ).codRestrict _ (fun z =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨centralizer_le_normalizer_unipotent chi _ (hZ _ ⟨z, rfl⟩),
        ((centralizer psi).carrier _).le_normalizer (hZ' _ ⟨z, rfl⟩)⟩)

@[simp] theorem centralizingUnipotentCentralizerNormalizerHom_coe
    (z : rationalPoints Z) :
    (centralizingUnipotentCentralizerNormalizerHom chi psi iZ hZ hZ' z :
      rationalPoints G) = z ≫ iZ.hom.hom := rfl

end RationalPoints

end Langlands.GroupScheme.Dynamic
