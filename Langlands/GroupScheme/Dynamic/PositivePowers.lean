import Langlands.GroupScheme.Dynamic.PositiveScaling

/-! # Positive powers preserve actual contracting subgroups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace AffineLine

/-- A nonzero integral power substitution preserves the constant coefficient. -/
theorem coeff_laurentPower_zero (A : CommRingCat.{u}) {n : ℤ} (hn : n ≠ 0)
    (q : LaurentPolynomial A) :
    (laurentPower A n q).coeff 0 = q.coeff 0 := by
  simpa only [mul_zero] using coeff_laurentPower_mul A hn q 0

end AffineLine

namespace Corepresented

open AffineLine

variable {R : CommRingCat.{u}} {F : CommAlgCat.{u} R ⥤ GrpCat.{u}}
    {B : CommAlgCat.{u} R} {e : (F ⋙ forget GrpCat).CorepresentableBy B}

/-- Positive power substitution preserves the actual identity-limit ideal. -/
theorem unipotentIdeal_precomp_power
    (χ : (Gm (Spec R)).toGrp ⟶ groupScheme F e) {n : ℤ} (hn : 0 < n) :
    unipotentIdeal (CommGroupScheme.groupHom (Gm.powerHom (Spec R) n) ≫ χ) =
      unipotentIdeal χ := by
  have hz :
      {d : B | ∃ b,
        (coaction (CommGroupScheme.groupHom (Gm.powerHom (Spec R) n) ≫ χ) b).coeff 0 -
          algebraMap R B (counit e b) = d} =
      {d : B | ∃ b, (coaction χ b).coeff 0 - algebraMap R B (counit e b) = d} := by
    ext d
    apply exists_congr
    intro b
    rw [coaction_precomp_power]
    change (laurentPower (CommRingCat.of B) n (coaction χ b)).coeff 0 -
      algebraMap R B (counit e b) = d ↔ _
    rw [coeff_laurentPower_zero _ hn.ne']
  rw [unipotentIdeal, unipotentIdeal, Ideal.span_union, Ideal.span_union, hz]
  change parabolicIdeal _ ⊔ _ = parabolicIdeal _ ⊔ _
  rw [parabolicIdeal_precomp_power χ hn]

/-- Positive powers preserve the contracting subgroup on every scheme test. -/
theorem unipotent_precomp_power
    (χ : (Gm (Spec R)).toGrp ⟶ groupScheme F e) {n : ℤ} (hn : 0 < n) :
    Dynamic.unipotent (CommGroupScheme.groupHom (Gm.powerHom (Spec R) n) ≫ χ) =
      Dynamic.unipotent χ := by
  apply IsAffineCutOutBy.eq_of_sameIdeal (I := unipotentIdeal χ)
  · rw [← unipotentIdeal_precomp_power χ hn]
    exact isAffineCutOutBy_unipotent _
  · exact isAffineCutOutBy_unipotent χ

end Corepresented

namespace Dynamic

variable {R : CommRingCat.{u}} {G : GroupScheme (Spec R)} [IsAffine G.X.left]

/-- Positive powers preserve the contracting subgroup of any affine group. -/
theorem unipotent_precomp_power (χ : (Gm (Spec R)).toGrp ⟶ G)
    {n : ℤ} (hn : 0 < n) :
    unipotent (CommGroupScheme.groupHom (Gm.powerHom (Spec R) n) ≫ χ) =
      unipotent χ := by
  let e := (AffineCoordinates.groupSchemeIso G).symm
  rw [unipotent_eq_comap_of_iso _ e, unipotent_eq_comap_of_iso χ e]
  simpa only [Category.assoc] using
    congrArg (fun F => F.comap e.hom) (Corepresented.unipotent_precomp_power (χ ≫ e.hom) hn)

/-- Positive integral multiples of an actual cocharacter have the same
contracting subgroup. -/
theorem unipotent_zsmul (T : CommGroupScheme (Spec R)) (j : T.toGrp ⟶ G)
    (ν : cocharacterLattice T) {n : ℤ} (hn : 0 < n) :
    unipotent (CommGroupScheme.groupHom (n • ν) ≫ j) =
      unipotent (CommGroupScheme.groupHom ν ≫ j) := by
  have hν : CommGroupScheme.groupHom (n • ν) =
      CommGroupScheme.groupHom (Gm.powerHom (Spec R) n) ≫ CommGroupScheme.groupHom ν := by
    change CommGroupScheme.groupHom (n • ν) =
      CommGroupScheme.groupHom (Gm.powerHom (Spec R) n ≫ ν)
    rw [Gm.powerHom_apply, Preadditive.zsmul_comp, Category.id_comp]
  rw [hν, Category.assoc]
  exact unipotent_precomp_power _ hn

namespace Affine

/-- Canonical isomorphism of the actual contracting subgroup representatives
for a cocharacter and any positive integral power. -/
def unipotentPowerIso (χ : (Gm (Spec R)).toGrp ⟶ G) {n : ℤ} (hn : 0 < n) :
    unipotentScheme (CommGroupScheme.groupHom (Gm.powerHom (Spec R) n) ≫ χ) ≅
      unipotentScheme χ :=
  (isRepresentedBy_unipotentHom
    (CommGroupScheme.groupHom (Gm.powerHom (Spec R) n) ≫ χ)).isoOfIsRepresentedBy
      (by rw [unipotent_precomp_power χ hn]; exact isRepresentedBy_unipotentHom χ)

/-- The canonical power isomorphism commutes with the original inclusions. -/
theorem unipotentPowerIso_hom_comp (χ : (Gm (Spec R)).toGrp ⟶ G)
    {n : ℤ} (hn : 0 < n) :
    (unipotentPowerIso χ hn).hom ≫ unipotentHom χ =
      unipotentHom (CommGroupScheme.groupHom (Gm.powerHom (Spec R) n) ≫ χ) := by
  exact SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy_hom_comp _ _

end Affine
end Dynamic
end Langlands.GroupScheme
