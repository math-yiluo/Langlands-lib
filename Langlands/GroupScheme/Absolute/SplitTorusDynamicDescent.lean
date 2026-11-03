import Langlands.GroupScheme.Torus.SplitLatticeBaseChange
import Langlands.GroupScheme.SubgroupFunctor.FpqcDescent
import Langlands.GroupScheme.Absolute.ParabolicTransport
import Langlands.GroupScheme.Dynamic.AffineRepresentability

/-! # Descending fixed-torus dynamic presentations along field extensions -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace Dynamic
variable {S S' : Scheme.{u}} (b : S' ⟶ S) {T G : GroupScheme S}

/-- Base change of an ambient cocharacter commutes with the chosen torus map. -/
theorem baseChangeCocharacter_comp (ν : (Gm S).toGrp ⟶ T) (j : T ⟶ G) :
    baseChangeCocharacter b (ν ≫ j) =
      baseChangeCocharacter b ν ≫ (GroupScheme.baseChange b).map j := by
  simp [baseChangeCocharacter, Functor.map_comp]

end Dynamic

section Descent
variable {k K : Type u} [Field k] [Field K] [Algebra k K]
    {G P : GroupScheme (Spec (CommRingCat.of k))} [IsAffine G.X.left]
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (j : T.toGrp ⟶ G)
    (i : P ⟶ G) [Mono i.hom.hom]

/-- Equality with an actual dynamic parabolic can be tested after any field extension. -/
theorem range_eq_parabolic_iff_baseChange (ν : cocharacterLattice T) :
    SubgroupFunctor.range i = Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ j) ↔
      SubgroupFunctor.range ((GroupScheme.baseChange (algebraBaseMap k K)).map i) =
        Dynamic.parabolic (CommGroupScheme.groupHom
          (cocharacterLattice.baseChange (algebraBaseMap k K) T ν) ≫
            (GroupScheme.baseChange (algebraBaseMap k K)).map j) := by
  let b := algebraBaseMap k K
  have hb : Flat b ∧ Surjective b :=
    (flat_and_surjective_SpecMap_iff (CommRingCat.ofHom (algebraMap k K))).mpr
      (RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance)
  let : Flat b := hb.1
  let : Surjective b := hb.2
  let χ := CommGroupScheme.groupHom ν ≫ j
  have hbc : Dynamic.parabolic (CommGroupScheme.groupHom
      (cocharacterLattice.baseChange b T ν) ≫ (GroupScheme.baseChange b).map j) =
        (Dynamic.parabolic χ).baseChange b := by
    rw [cocharacterLattice.groupHom_baseChange_dynamic,
      ← Dynamic.baseChangeCocharacter_comp, Dynamic.parabolic_baseChange]
  change SubgroupFunctor.range i = Dynamic.parabolic χ ↔ _
  rw [hbc, ← SubgroupFunctor.range_baseChange]
  constructor
  · exact congrArg (fun F : SubgroupFunctor G => F.baseChange b)
  · intro h
    exact SubgroupFunctor.eq_of_isRepresentedBy_baseChange_eq b
      (show (SubgroupFunctor.range i).IsRepresentedBy i from ⟨inferInstance, rfl⟩)
      (Dynamic.Affine.isRepresentedBy_parabolicHom χ) h

/-- The actual integral cocharacters of the fixed torus that present a chosen subgroup. -/
def FixedTorusDynamicPresentations : Type u :=
  {ν : cocharacterLattice T //
    SubgroupFunctor.range i = Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ j)}

variable (hT : IsSplitTorus T.toGrp)

/-- Pullback gives an equivalence on actual fixed-torus dynamic presentations. -/
def fixedTorusDynamicPresentationBaseChangeEquiv :
    FixedTorusDynamicPresentations T j i ≃
      FixedTorusDynamicPresentations
        ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)
        ((GroupScheme.baseChange (algebraBaseMap k K)).map j)
        ((GroupScheme.baseChange (algebraBaseMap k K)).map i) where
  toFun ν := ⟨cocharacterLattice.baseChange (algebraBaseMap k K) T ν.val,
    (range_eq_parabolic_iff_baseChange (K := K) T j i ν.val).mp ν.property⟩
  invFun ν' := ⟨(cocharacterLattice.baseChangeEquiv (algebraBaseMap k K) T hT).symm ν'.val, by
    apply (range_eq_parabolic_iff_baseChange (K := K) T j i _).mpr
    change SubgroupFunctor.range ((GroupScheme.baseChange (algebraBaseMap k K)).map i) =
      Dynamic.parabolic (CommGroupScheme.groupHom
        ((cocharacterLattice.baseChangeEquiv (algebraBaseMap k K) T hT)
          ((cocharacterLattice.baseChangeEquiv (algebraBaseMap k K) T hT).symm ν'.val)) ≫
            (GroupScheme.baseChange (algebraBaseMap k K)).map j)
    rw [AddEquiv.apply_symm_apply]
    exact ν'.property⟩
  left_inv ν := Subtype.ext
    ((cocharacterLattice.baseChangeEquiv (algebraBaseMap k K) T hT).symm_apply_apply ν.val)
  right_inv ν' := Subtype.ext
    ((cocharacterLattice.baseChangeEquiv (algebraBaseMap k K) T hT).apply_symm_apply ν'.val)

include hT in
/-- A fixed-torus dynamic presentation exists precisely when one exists after scalar
extension, with equality on all test schemes over either field. -/
theorem exists_range_eq_parabolic_iff_baseChange :
    (∃ ν : cocharacterLattice T,
      SubgroupFunctor.range i = Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ j)) ↔
    (∃ ν' : cocharacterLattice ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T),
      SubgroupFunctor.range ((GroupScheme.baseChange (algebraBaseMap k K)).map i) =
        Dynamic.parabolic (CommGroupScheme.groupHom ν' ≫
          (GroupScheme.baseChange (algebraBaseMap k K)).map j)) := by
  constructor
  · rintro ⟨ν, hν⟩
    exact ⟨cocharacterLattice.baseChange (algebraBaseMap k K) T ν,
      (range_eq_parabolic_iff_baseChange (K := K) T j i ν).mp hν⟩
  · rintro ⟨ν', hν'⟩
    let p := (fixedTorusDynamicPresentationBaseChangeEquiv (K := K) T j i hT).symm ⟨ν', hν'⟩
    exact ⟨p.val, p.property⟩

end Descent
end Langlands.GroupScheme
