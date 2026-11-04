import Langlands.GroupScheme.Derived.Basic
import Langlands.GroupScheme.Rational.WeylPositiveCocharacter

/-! # Membership in normal subgroup functors under integral Weyl averaging -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj BigOperators

namespace Langlands.GroupScheme

section Evaluation

variable {S : Scheme.{u}} {T : CommGroupScheme S} {G : GroupScheme S}
    (i : T.toGrp ⟶ G) (F : SubgroupFunctor G) {U : Over S}
    (z : U ⟶ (Gm S).X)

/-- Integral cocharacters whose actual value at the given point belongs to
the given subgroup functor after the actual ambient map. -/
def cocharactersEvaluatingIn : Submodule ℤ (cocharacterLattice T) where
  carrier := {ν | z ≫ (CommGroupScheme.groupHom ν ≫ i).hom.hom ∈ F.carrier U}
  zero_mem' := by
    change z ≫ (CommGroupScheme.groupHom (0 : cocharacterLattice T) ≫ i).hom.hom ∈
      F.carrier U
    rw [Grp.comp_hom_hom, ← Category.assoc, comp_groupHom_zero, MonObj.one_comp]
    exact (F.carrier U).one_mem
  add_mem' := by
    intro ν eta hν heta
    change z ≫ (CommGroupScheme.groupHom (ν + eta) ≫ i).hom.hom ∈ F.carrier U
    rw [Grp.comp_hom_hom, ← Category.assoc, comp_groupHom_add, MonObj.mul_comp]
    exact (F.carrier U).mul_mem hν heta
  smul_mem' := by
    intro n ν hν
    change z ≫ (CommGroupScheme.groupHom (n • ν) ≫ i).hom.hom ∈ F.carrier U
    rw [Grp.comp_hom_hom, ← Category.assoc, comp_groupHom_zsmul, GrpObj.zpow_comp]
    exact (F.carrier U).zpow_mem hν n

@[simp] theorem mem_cocharactersEvaluatingIn (ν : cocharacterLattice T) :
    ν ∈ cocharactersEvaluatingIn i F z ↔
      z ≫ (CommGroupScheme.groupHom ν ≫ i).hom.hom ∈ F.carrier U := Iff.rfl

end Evaluation

section Weyl

variable {k : Type u} [Field k]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}
    (i : T.toGrp ⟶ G) {F : SubgroupFunctor G}
    {U : Over (Spec (CommRingCat.of k))}
    (z : U ⟶ (Gm (Spec (CommRingCat.of k))).X)

/-- Actual normalizer conjugation preserves membership in a normal subgroup
functor at the fixed evaluation point. -/
theorem mem_cocharactersEvaluatingIn_normalizingAut (hF : F.IsNormal)
    (n : normalizerPoints i) {ν : cocharacterLattice T}
    (hν : ν ∈ cocharactersEvaluatingIn i F z) :
    cocharacterAut (normalizingAut i n) ν ∈ cocharactersEvaluatingIn i F z := by
  rw [mem_cocharactersEvaluatingIn, groupHom_cocharacterAut_comp,
    Grp.comp_hom_hom, ← Category.assoc, comp_innerIso_hom]
  exact hF U _ _ (Subgroup.mem_top _) hν

variable [Mono i.hom.hom.left]

/-- The action of the actual quotient `N(k)/Z(k)` preserves that membership. -/
theorem mem_cocharactersEvaluatingIn_relativeWeyl (hF : F.IsNormal)
    (w : relativeWeylGroup i) {ν : cocharacterLattice T}
    (hν : ν ∈ cocharactersEvaluatingIn i F z) :
    relativeWeylCocharacterAction i w ν ∈ cocharactersEvaluatingIn i F z := by
  obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective w
  exact mem_cocharactersEvaluatingIn_normalizingAut i z hF n hν

variable [Fintype (relativeWeylGroup i)]

/-- An integral Weyl sum still evaluates into any normal subgroup functor
containing the original evaluated point. -/
theorem relativeWeylCocharacterSum_mem_cocharactersEvaluatingIn (hF : F.IsNormal)
    {ν : cocharacterLattice T} (hν : ν ∈ cocharactersEvaluatingIn i F z) :
    relativeWeylCocharacterSum i ν ∈ cocharactersEvaluatingIn i F z := by
  rw [relativeWeylCocharacterSum_apply]
  exact (cocharactersEvaluatingIn i F z).sum_mem fun w _ =>
    mem_cocharactersEvaluatingIn_relativeWeyl i z hF w hν

/-- On every test scheme, integral Weyl averaging preserves actual
scheme-theoretic derived-point membership at the fixed evaluation point. -/
theorem relativeWeylCocharacterSum_eval_mem_derived
    {ν : cocharacterLattice T}
    (hν : z ≫ (CommGroupScheme.groupHom ν ≫ i).hom.hom ∈ (derivedSubgroup G).carrier U) :
    z ≫ (CommGroupScheme.groupHom (relativeWeylCocharacterSum i ν) ≫ i).hom.hom ∈
      (derivedSubgroup G).carrier U :=
  relativeWeylCocharacterSum_mem_cocharactersEvaluatingIn i z
    (derivedSubgroup_isNormal G) hν

end Weyl

end Langlands.GroupScheme
