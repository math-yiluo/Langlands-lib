import Langlands.GroupScheme.CentralIsogeny.TorusCentralizerReflection
import Langlands.GroupScheme.Absolute.MaximalTorusCentralizerProof
import Langlands.GroupScheme.Rational.LeviFactorization
import Langlands.GroupScheme.ClosedSubgroupMonomorphism

/-! # Factoring lifted homomorphisms through a compatible maximal torus -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.IsCentralIsogeny

variable {k : Type u} [Field k]
  {G H : GroupScheme (Spec (CommRingCat.of k))}
  {p : G ⟶ H} (hp : IsCentralIsogeny p) (hG : IsConnectedReductive G)
  {T T' C : CommGroupScheme (Spec (CommRingCat.of k))}
  {i : T.toGrp ⟶ G} (hi : IsMaximalTorus i)
  {i' : T'.toGrp ⟶ H} (t : T ⟶ T')
  (ht : i ≫ p = CommGroupScheme.groupHom t ≫ i')
  (a : C.toGrp ⟶ G) (b : C ⟶ T')
  (ha : a ≫ p = CommGroupScheme.groupHom b ≫ i')

include hp hG hi ht ha

/-- A homomorphism whose projection factors through a commutative target containing the
projected maximal torus already lands in that source maximal torus on every test scheme. -/
theorem range_le_range_maximalTorus :
    SubgroupFunctor.range a ≤ SubgroupFunctor.range i := by
  rw [← maximalTorusCentralizer k G hG T i hi]
  intro U y hy
  obtain ⟨x, rfl⟩ := SubgroupFunctor.mem_range.mp hy
  apply (hp.mem_torusCentralizer_iff hi.1 i _).mp
  intro V v z
  have hc := (Commute.all (v ≫ x ≫ (CommGroupScheme.groupHom b).hom.hom)
    (z ≫ (CommGroupScheme.groupHom t).hom.hom)).map
      (IsMonHom.monoidHom i'.hom.hom V)
  have ha' := congrArg (fun f => f.hom.hom) ha
  have ht' := congrArg (fun f => f.hom.hom) ht
  simp only [Grp.comp_hom_hom] at ha' ht'
  simpa only [IsMonHom.monoidHom, MonoidHom.coe_mk, OneHom.coe_mk,
    Grp.comp_hom_hom, Category.assoc, ha', ht'] using hc

/-- The canonical factor of the lifted homomorphism through the compatible source maximal
torus. The construction uses its represented subgroup functor. -/
def maximalTorusFactor : C ⟶ T :=
  Additive.ofMul
    ((show (SubgroupFunctor.range i).IsRepresentedBy i from
      ⟨hi.2.1.mono_overHom, rfl⟩).factorHom a
        (hp.range_le_range_maximalTorus hG hi t ht a b ha))

/-- The factor has the original ambient homomorphism as its composite. -/
theorem maximalTorusFactor_comp :
    CommGroupScheme.groupHom (hp.maximalTorusFactor hG hi t ht a b ha) ≫ i = a :=
  SubgroupFunctor.IsRepresentedBy.factorHom_comp _ _ _

/-- If the target torus map is a closed embedding, the factor also has the prescribed
composite with the torus restriction of the central isogeny. -/
theorem maximalTorusFactor_comp_t (hi' : IsClosedSubgroup i') :
    hp.maximalTorusFactor hG hi t ht a b ha ≫ t = b := by
  have := hi'.mono_overHom
  apply Additive.toMul.injective
  apply Grp.hom_ext
  apply (cancel_mono i'.hom.hom).mp
  change ((CommGroupScheme.groupHom
    (hp.maximalTorusFactor hG hi t ht a b ha) ≫ CommGroupScheme.groupHom t) ≫ i').hom.hom =
      (CommGroupScheme.groupHom b ≫ i').hom.hom
  rw [Category.assoc, ← ht, ← Category.assoc, hp.maximalTorusFactor_comp, ha]

/-- The source closed embedding makes the factor unique. -/
theorem maximalTorusFactor_unique {c : C ⟶ T}
    (hc : CommGroupScheme.groupHom c ≫ i = a) :
    c = hp.maximalTorusFactor hG hi t ht a b ha := by
  have := hi.2.1.mono_overHom
  apply Additive.toMul.injective
  apply Grp.hom_ext
  apply (cancel_mono i.hom.hom).mp
  change (CommGroupScheme.groupHom c ≫ i).hom.hom =
    (CommGroupScheme.groupHom (hp.maximalTorusFactor hG hi t ht a b ha) ≫ i).hom.hom
  rw [hc, hp.maximalTorusFactor_comp]

end Langlands.GroupScheme.IsCentralIsogeny
