import Langlands.GroupScheme.Rational.RootAnnihilatorRange
import Langlands.GroupScheme.Rational.SplitTorusFactorization

/-! # Integral cocharacters of actual split components -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section CentralCocharacters

variable {S : Scheme.{u}} {T : CommGroupScheme S} {M : GroupScheme S}

/-- Actual cocharacters of `T` whose composites with `t` are central on every
test scheme, with the pointwise group law written additively. -/
def centralCocharacters (t : T.toGrp ⟶ M) :
    Submodule ℤ (cocharacterLattice T) where
  carrier := {ν | IsCentral (CommGroupScheme.groupHom ν ≫ t)}
  zero_mem' := by
    intro U x
    rw [Grp.comp_hom_hom, ← Category.assoc, comp_groupHom_zero, MonObj.one_comp]
    exact Subgroup.one_mem _
  add_mem' := by
    intro ν eta hν heta U x
    rw [Grp.comp_hom_hom, ← Category.assoc, comp_groupHom_add, MonObj.mul_comp]
    exact Subgroup.mul_mem _ (hν U x) (heta U x)
  smul_mem' := by
    intro n ν hν U x
    rw [Grp.comp_hom_hom, ← Category.assoc, comp_groupHom_zsmul, GrpObj.zpow_comp]
    exact Subgroup.zpow_mem _ (hν U x) n

@[simp] theorem mem_centralCocharacters (t : T.toGrp ⟶ M)
    (ν : cocharacterLattice T) :
    ν ∈ centralCocharacters t ↔ IsCentral (CommGroupScheme.groupHom ν ≫ t) :=
  Iff.rfl

end CentralCocharacters

variable {k : Type u} [Field k]
  {A T : CommGroupScheme (Spec (CommRingCat.of k))}
  {M : GroupScheme (Spec (CommRingCat.of k))}
  {a : A.toGrp ⟶ M} {t : T.toGrp ⟶ M}

/-- The integral image of a central morphism, factored through `T`, consists
of cocharacters central in the ambient group. -/
theorem cocharacterMapInt_range_le_centralCocharacters
    (ha : IsCentral a) (f : A ⟶ T)
    (hf : CommGroupScheme.groupHom f ≫ t = a) :
    (RealTorusSpace.cocharacterMapInt f).range ≤ centralCocharacters t := by
  rintro _ ⟨zeta, rfl⟩
  change IsCentral ((CommGroupScheme.groupHom zeta ≫ CommGroupScheme.groupHom f) ≫ t)
  rw [Category.assoc, hf]
  exact ha.comp (CommGroupScheme.groupHom zeta)

/-- Every actual cocharacter central in an affine group factors through each
split component. A monic torus lift identifies that factorization integrally. -/
theorem IsSplitComponent.range_cocharacterMapInt_eq_centralCocharacters
    [IsAffineHom M.X.hom] [Mono t.hom.hom.left]
    (ha : IsSplitComponent a) (f : A ⟶ T)
    (hf : CommGroupScheme.groupHom f ≫ t = a) :
    (RealTorusSpace.cocharacterMapInt f).range = centralCocharacters t := by
  apply le_antisymm (cocharacterMapInt_range_le_centralCocharacters ha.1.2 f hf)
  intro ν hν
  obtain ⟨g, hg⟩ := ha.exists_factor isSplitTorus_gm hν
  refine ⟨Additive.ofMul g, ?_⟩
  apply congrArg Additive.ofMul
  apply Grp.hom_ext
  have : Mono t.hom.hom := Over.mono_of_mono_left _
  apply (cancel_mono t.hom.hom).mp
  have hcomp : (g ≫ CommGroupScheme.groupHom f) ≫ t =
      CommGroupScheme.groupHom ν ≫ t := by
    rw [Category.assoc, hf, hg]
  exact congrArg (fun q => q.hom.hom) hcomp

/-- If every selected-root-annihilating integral cocharacter is central, the
actual split component contains the entire real selected-root annihilator. -/
theorem IsSplitComponent.rootAnnihilator_le_range_cocharacterMapReal
    [IsAffineHom M.X.hom] [Mono t.hom.hom.left]
    (ha : IsSplitComponent a) (f : A ⟶ T)
    (hf : CommGroupScheme.groupHom f ≫ t = a)
    (J : Set (characterLattice T)) [Finite J]
    (hcentral : ∀ ν : cocharacterLattice T,
      (∀ α ∈ J, latticePairing T α ν = 0) →
        IsCentral (CommGroupScheme.groupHom ν ≫ t)) :
    RealTorusSpace.rootAnnihilator T J ≤
      (RealTorusSpace.cocharacterMapReal f).range := by
  apply RealTorusSpace.rootAnnihilator_le_range_cocharacterMapReal f J
  rw [ha.range_cocharacterMapInt_eq_centralCocharacters f hf]
  intro ν hν
  exact hcentral ν ((RealTorusSpace.mem_rootAnnihilatorInt J ν).mp hν)

end Langlands.GroupScheme
