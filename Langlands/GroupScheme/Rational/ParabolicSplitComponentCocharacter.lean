import Langlands.GroupScheme.Rational.ParabolicRootPresentation
import Langlands.GroupScheme.Rational.TorusCentralizerFactorization
import Langlands.GroupScheme.Rational.SplitTorusFactorization

/-! # Defining cocharacters in the specified Levi split component -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {A : CommGroupScheme (Spec (CommRingCat.of k))}
  {G M : GroupScheme (Spec (CommRingCat.of k))}

/-- A defining cocharacter of a represented dynamic centralizer factors through
each specified split component of that representative. -/
theorem IsSplitComponent.exists_cocharacter_factor_of_dynamicCentralizer
    [IsAffineHom M.X.hom] {a : A.toGrp ⟶ M} (ha : IsSplitComponent a)
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G) {j : M ⟶ G}
    (hj : (Dynamic.centralizer χ).IsRepresentedBy j) :
    ∃ ν : cocharacterLattice A, CommGroupScheme.groupHom ν ≫ a ≫ j = χ := by
  have hjT : (torusCentralizer χ).IsRepresentedBy j := by
    rwa [torusCentralizer_gm_eq_dynamicCentralizer]
  obtain ⟨g, hg⟩ := ha.exists_factor isSplitTorus_gm
    (isCentral_torusCentralizerFactor χ hjT)
  refine ⟨Additive.ofMul g, ?_⟩
  change g ≫ a ≫ j = χ
  rw [← Category.assoc, hg, torusCentralizerFactor_comp]

namespace ParabolicRootPresentation

variable {P : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom]
  {p : P ⟶ G} {l : M ⟶ P} {a : A.toGrp ⟶ M}
  (r : ParabolicRootPresentation p l a)

/-- A cocharacter realizing the specified Levi lifts integrally through its
split component, with exactly the same image in the presentation torus. -/
theorem exists_splitComponentCocharacter_lift (ζ : cocharacterLattice r.data.T)
    (hζ : SubgroupFunctor.range (l ≫ p) =
      Dynamic.centralizer (CommGroupScheme.groupHom ζ ≫ r.data.i)) :
    ∃ ν : cocharacterLattice A,
      RealTorusSpace.cocharacterMapInt r.data.f ν = ζ ∧
      CommGroupScheme.groupHom ν ≫ a ≫ l ≫ p =
        CommGroupScheme.groupHom ζ ≫ r.data.i := by
  let : IsAffineHom M.X.hom := r.isCompatible.levi.isConnectedReductive.isAffineHom
  have hjc : IsClosedSubgroup (l ≫ p) :=
    r.isCompatible.levi.isClosedSubgroup.comp r.isCompatible.parabolic.isClosedSubgroup
  let := hjc.mono
  obtain ⟨ν, hν⟩ :=
    r.isCompatible.splitComponent.exists_cocharacter_factor_of_dynamicCentralizer
      (CommGroupScheme.groupHom ζ ≫ r.data.i) ⟨Over.mono_of_mono_left _, hζ⟩
  refine ⟨ν, ?_, hν⟩
  let := r.isCompatible.maximalSplit.isSplitSubtorus.mono
  have : Mono r.data.i.hom.hom := Over.mono_of_mono_left _
  apply congrArg Additive.ofMul
  apply Grp.hom_ext
  apply (cancel_mono r.data.i.hom.hom).mp
  have hcomp :
      CommGroupScheme.groupHom (RealTorusSpace.cocharacterMapInt r.data.f ν) ≫
          r.data.i = CommGroupScheme.groupHom ζ ≫ r.data.i := by
    change (CommGroupScheme.groupHom ν ≫ CommGroupScheme.groupHom r.data.f) ≫
      r.data.i = _
    rw [Category.assoc, r.isCompatible.factor_comp]
    exact hν
  exact congrArg (fun q => q.hom.hom) hcomp

/-- The specified parabolic and Levi are realized by one actual cocharacter
of their specified split component, still standard in the original torus. -/
theorem exists_splitComponentCocharacter :
    ∃ ν : cocharacterLattice A,
      IsStandardCocharacter r.data.i r.data.ν r.data.J
        (RealTorusSpace.cocharacterMapInt r.data.f ν) ∧
      SubgroupFunctor.range p =
        Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ a ≫ l ≫ p) ∧
      SubgroupFunctor.range (l ≫ p) =
        Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ a ≫ l ≫ p) := by
  obtain ⟨ζ, hstandard, hp, hlevi⟩ := r.isCompatible.realization
  obtain ⟨ν, hlift, hcomp⟩ := r.exists_splitComponentCocharacter_lift ζ hlevi
  refine ⟨ν, ?_, ?_, ?_⟩
  · rwa [hlift]
  · rw [hcomp]
    exact hp
  · rw [hcomp]
    exact hlevi

/-- A chosen defining cocharacter in the specified actual split component.
Its existence is derived from the supplied compatible presentation. -/
def splitComponentCocharacter : cocharacterLattice A :=
  r.exists_splitComponentCocharacter.choose

/-- Its image in the original presentation torus is a standard cocharacter. -/
theorem isStandard_splitComponentCocharacter :
    IsStandardCocharacter r.data.i r.data.ν r.data.J
      (RealTorusSpace.cocharacterMapInt r.data.f r.splitComponentCocharacter) :=
  r.exists_splitComponentCocharacter.choose_spec.1

/-- The chosen split-component cocharacter defines the specified parabolic
as an equality of subgroup functors on all test schemes. -/
theorem parabolic_eq_splitComponentCocharacter :
    SubgroupFunctor.range p =
      Dynamic.parabolic (CommGroupScheme.groupHom r.splitComponentCocharacter ≫
        a ≫ l ≫ p) :=
  r.exists_splitComponentCocharacter.choose_spec.2.1

/-- The same chosen cocharacter has exactly the specified Levi centralizer. -/
theorem levi_eq_splitComponentCocharacter :
    SubgroupFunctor.range (l ≫ p) =
      Dynamic.centralizer (CommGroupScheme.groupHom r.splitComponentCocharacter ≫
        a ≫ l ≫ p) :=
  r.exists_splitComponentCocharacter.choose_spec.2.2

end ParabolicRootPresentation

end Langlands.GroupScheme
