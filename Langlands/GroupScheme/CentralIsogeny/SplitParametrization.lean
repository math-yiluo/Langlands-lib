import Langlands.GroupScheme.Rational.TorusCentralizerImage
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap

/-! # Closed split-torus lifts from split-torus parametrizations -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- A split-torus parametrization surjecting onto a closed subgroup gives a
closed split-torus lift with a surjective restriction map. -/
theorem exists_splitSubtorus_lift_of_surjective_splitParametrization
    {k : Type u} [Field k]
    {G H : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (π : G ⟶ H)
    {D S : CommGroupScheme (Spec (CommRingCat.of k))}
    (a : D.toGrp ⟶ G) (b : D ⟶ S) (i : S.toGrp ⟶ H)
    (hD : IsSplitTorus D.toGrp) (hi : IsClosedSubgroup i)
    (hb : Surjective (CommGroupScheme.groupHom b).hom.hom.left)
    (hcomm : a ≫ π = CommGroupScheme.groupHom b ≫ i) :
    ∃ (T : CommGroupScheme (Spec (CommRingCat.of k)))
      (j : T.toGrp ⟶ G) (f : T ⟶ S),
      IsSplitSubtorus j ∧
        Surjective (CommGroupScheme.groupHom f).hom.hom.left ∧
        j ≫ π = CommGroupScheme.groupHom f ≫ i := by
  let d := hD.dominantFactorization a
  have : IsSchemeTheoreticallyDominant d.factor.hom.hom.left := d.dominant
  have hfac : d.factor ≫ (d.inclusion ≫ π) = CommGroupScheme.groupHom b ≫ i := by
    rw [← Category.assoc, d.factor_comp, hcomm]
  have hr : SubgroupFunctor.range (d.factor ≫ (d.inclusion ≫ π)) ≤
      SubgroupFunctor.range i := by
    rw [hfac]
    intro U x hx
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    exact SubgroupFunctor.mem_range.mpr
      ⟨y ≫ (CommGroupScheme.groupHom b).hom.hom, Category.assoc _ _ _⟩
  have hr' : SubgroupFunctor.range (d.inclusion ≫ π) ≤ SubgroupFunctor.range i :=
    (SubgroupFunctor.range_comp_le_iff_of_isSchemeTheoreticallyDominant
      d.factor (d.inclusion ≫ π) i hi).mp hr
  have : IsClosedImmersion i.hom.hom.left := hi
  let ri : (SubgroupFunctor.range i).IsRepresentedBy i :=
    ⟨Over.mono_of_mono_left _, rfl⟩
  let f := ri.factorHom (d.inclusion ≫ π) hr'
  have hfi : f ≫ i = d.inclusion ≫ π :=
    ri.factorHom_comp _ _
  have hbf : d.factor ≫ f = CommGroupScheme.groupHom b := by
    apply ri.hom_ext
    rw [Category.assoc, hfi, hfac]
  have : Surjective (CommGroupScheme.groupHom b).hom.hom.left := hb
  have : Surjective (d.factor.hom.hom.left ≫ f.hom.hom.left) := by
    change Surjective (d.factor ≫ f).hom.hom.left
    rw [hbf]
    infer_instance
  exact ⟨d.image, d.inclusion, Additive.ofMul f, d.isSplitSubtorus,
    Surjective.of_comp d.factor.hom.hom.left f.hom.hom.left, hfi.symm⟩

/-- The universe-general internal interface for passing from a split-torus
parametrization to a closed split-torus lift. -/
def SplitParametrizationLiftStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (G H : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]
    (π : G ⟶ H)
    (D S : CommGroupScheme (Spec (CommRingCat.of k)))
    (a : D.toGrp ⟶ G) (b : D ⟶ S) (i : S.toGrp ⟶ H),
    IsSplitTorus D.toGrp → IsClosedSubgroup i →
    Surjective (CommGroupScheme.groupHom b).hom.hom.left →
    a ≫ π = CommGroupScheme.groupHom b ≫ i →
    ∃ (T : CommGroupScheme (Spec (CommRingCat.of k)))
      (j : T.toGrp ⟶ G) (f : T ⟶ S),
      IsSplitSubtorus j ∧
        Surjective (CommGroupScheme.groupHom f).hom.hom.left ∧
        j ≫ π = CommGroupScheme.groupHom f ≫ i

/-- The internal parametrization interface follows from the dominant split image
and descent of containment through its dominant projection. -/
theorem splitParametrizationLiftStatement : SplitParametrizationLiftStatement.{u} := by
  intro k _ G H _ π D S a b i hD hi hb hcomm
  exact exists_splitSubtorus_lift_of_surjective_splitParametrization
    π a b i hD hi hb hcomm

end Langlands.GroupScheme
