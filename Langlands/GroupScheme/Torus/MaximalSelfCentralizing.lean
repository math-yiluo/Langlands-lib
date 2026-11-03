import Langlands.GroupScheme.Torus.MaximalBaseChangeForwardReduction

/-! # Self-centralizing tori are geometrically maximal -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section Base

variable {S : Scheme.{u}} {T T' : CommGroupScheme S} {G : GroupScheme S}
  {j : T.toGrp ⟶ G} {j' : T'.toGrp ⟶ G} {f : T.toGrp ⟶ T'.toGrp}

/-- A comparison into a closed commutative overgroup of a closed self-centralizing
commutative subgroup is an isomorphism, with the given comparison as its forward map. -/
def selfCentralizingComparisonIso (hj : IsClosedSubgroup j)
    (hself : torusCentralizer j = SubgroupFunctor.range j)
    (hj' : IsClosedSubgroup j') (hf : f ≫ j' = j) : T.toGrp ≅ T'.toGrp := by
  have hle : SubgroupFunctor.range j' ≤ SubgroupFunctor.range j := by
    rw [← hself, ← hf]
    intro U g hg V a t
    have h := range_le_torusCentralizer j' U hg V a (t ≫ f.hom.hom)
    simpa only [Grp.comp_hom_hom, Category.assoc] using h
  let : IsClosedImmersion j.hom.hom.left := hj
  let : Mono j.hom.hom := Over.mono_of_mono_left _
  let : IsClosedImmersion j'.hom.hom.left := hj'
  let : Mono j'.hom.hom := Over.mono_of_mono_left _
  have hr : (SubgroupFunctor.range j).IsRepresentedBy j := ⟨inferInstance, rfl⟩
  have hr' : (SubgroupFunctor.range j').IsRepresentedBy j' := ⟨inferInstance, rfl⟩
  let g : T'.toGrp ⟶ T.toGrp := hr.factorHom j' hle
  have hg : g ≫ j = j' := hr.factorHom_comp j' hle
  refine ⟨f, g, hr.hom_ext ?_, hr'.hom_ext ?_⟩
  · exact (Category.assoc f g j).trans
      ((congrArg (f ≫ ·) hg).trans (hf.trans (Category.id_comp j).symm))
  · exact (Category.assoc g f j').trans
      ((congrArg (g ≫ ·) hf).trans (hg.trans (Category.id_comp j').symm))

@[simp]
theorem selfCentralizingComparisonIso_hom (hj : IsClosedSubgroup j)
    (hself : torusCentralizer j = SubgroupFunctor.range j)
    (hj' : IsClosedSubgroup j') (hf : f ≫ j' = j) :
    (selfCentralizingComparisonIso hj hself hj' hf).hom = f :=
  rfl

theorem selfCentralizingComparisonIso_hom_comp (hj : IsClosedSubgroup j)
    (hself : torusCentralizer j = SubgroupFunctor.range j)
    (hj' : IsClosedSubgroup j') (hf : f ≫ j' = j) :
    (selfCentralizingComparisonIso hj hself hj' hf).hom ≫ j' = j :=
  hf

end Base

section Field

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} {j : T.toGrp ⟶ G}

/-- A closed torus equal to its whole-group centralizer is maximal. -/
theorem isMaximalTorus_of_torusCentralizer_eq
    (hT : IsTorus T.toGrp) (hj : IsClosedSubgroup j)
    (hself : torusCentralizer j = SubgroupFunctor.range j) : IsMaximalTorus j := by
  refine ⟨hT, hj, ?_⟩
  intro T' j' f _ hj' hf
  change IsIso (selfCentralizingComparisonIso hj hself hj' hf).hom
  infer_instance

variable (K : Type u) [Field K] [Algebra k K]

/-- A closed self-centralizing torus is maximal after every field extension. -/
theorem isMaximalTorus_baseChange_of_torusCentralizer_eq
    (hT : IsTorus T.toGrp) (hj : IsClosedSubgroup j)
    (hself : torusCentralizer j = SubgroupFunctor.range j) :
    IsMaximalTorus
      (T := (CommGroupScheme.baseChange
        (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj T)
      ((GroupScheme.baseChange
        (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map j) := by
  apply isMaximalTorus_of_torusCentralizer_eq hT.baseChange (hj.baseChange _)
  rw [torusCentralizer_baseChange, hself]
  exact (SubgroupFunctor.range_baseChangeHom _ j).symm

end Field

end Langlands.GroupScheme
