import Langlands.GroupScheme.Rational.SplitActionRigidity
import Langlands.GroupScheme.Rational.AdditiveGroupQuotient
import Langlands.GroupScheme.HomogeneousQuotientFiber

/-! # Affine-line rigidity and homomorphisms from split unipotent groups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k]
    (G : GroupScheme (Spec (CommRingCat.of k)))

/-- Every ground-field morphism from the affine line is a constant morphism.
For smooth connected unipotent groups this is the usual woundness property. -/
def HasConstantAffineLineMaps : Prop :=
  ∀ f : AffineLine.scheme (Spec (CommRingCat.of k)) ⟶ G.X,
    ∃ c : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ G.X,
      f = toUnit _ ≫ c

namespace HasConstantAffineLineMaps

variable {G} (hG : HasConstantAffineLineMaps G)

include hG

/-- Every morphism from a one-dimensional vector group is constant. -/
theorem exists_constant_of_isVectorGroupOfDimension_one
    {V : GroupScheme (Spec (CommRingCat.of k))}
    (hV : RelativeRoot.IsVectorGroupOfDimension V 1) (f : V.X ⟶ G.X) :
    ∃ c : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ G.X, f = toUnit _ ≫ c := by
  obtain ⟨e, he⟩ := hV
  let i := RelativeRoot.AdditiveGroupQuotient.lineIso e he
  obtain ⟨c, hc⟩ := hG (i.inv ≫ f)
  refine ⟨c, ?_⟩
  have h := congrArg (fun z => i.hom ≫ z) hc
  simpa only [← Category.assoc, i.hom_inv_id, Category.id_comp, comp_toUnit] using h

/-- Every actual group homomorphism from a one-dimensional vector group is zero. -/
theorem hom_eq_zero_of_isVectorGroupOfDimension_one
    {V : GroupScheme (Spec (CommRingCat.of k))}
    (hV : RelativeRoot.IsVectorGroupOfDimension V 1) (f : V ⟶ G) : f = 0 := by
  obtain ⟨c, hc⟩ := hG.exists_constant_of_isVectorGroupOfDimension_one hV f.hom.hom
  have hc1 : c = η[G.X] := by
    have h := congrArg (fun z => η[V.X] ≫ z) hc
    simpa only [IsMonHom.one_hom, ← Category.assoc, comp_toUnit,
      toUnit_unit, Category.id_comp] using h.symm
  apply Grp.hom_ext
  change f.hom.hom = 1
  rw [hc, hc1]
  rfl

/-- Every actual homomorphism from an affine group with a finite Ga-series is zero.
The induction descends through each supplied fppf quotient after killing its full kernel. -/
theorem hom_eq_zero_of_hasSplitSeries (n : ℕ) :
    ∀ (H : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom H.X.hom],
      RelativeRoot.HasSplitSeries n H → ∀ f : H ⟶ G, f = 0 := by
  induction n with
  | zero =>
    intro H _ hH f
    have hid : (𝟙 H.X : H.X ⟶ H.X) = 1 := by
      have hmem : (𝟙 H.X : H.X ⟶ H.X) ∈
          (SubgroupFunctor.range (𝟙 H)).carrier H.X :=
        SubgroupFunctor.mem_range.mpr ⟨𝟙 H.X, Category.comp_id _⟩
      rw [hH, SubgroupFunctor.bot_carrier, Subgroup.mem_bot] at hmem
      exact hmem
    apply Grp.hom_ext
    change f.hom.hom = 1
    calc
      f.hom.hom = (𝟙 H.X) ≫ f.hom.hom := (Category.id_comp _).symm
      _ = (1 : H.X ⟶ H.X) ≫ f.hom.hom := congrArg (fun z => z ≫ f.hom.hom) hid
      _ = 1 := MonObj.one_comp _
  | succ n ih =>
    intro H _ hH f
    obtain ⟨K, V, j, q, hj, _, _, _, hq, hV, hK⟩ := hH
    let : IsAffineHom K.X.hom := HomogeneousQuotient.affine_subgroup_of_closed H K j hj
    have hjf : j ≫ f = 0 := ih K hK (j ≫ f)
    have hk : kernelι q ≫ f = 0 := by
      apply Grp.hom_ext
      change (kernelι q).hom.hom ≫ f.hom.hom = 1
      have hmem : (kernelι q).hom.hom ∈ (SubgroupFunctor.range j).carrier (kernel q).X := by
        rw [← hq.2.2.2]
        exact SubgroupFunctor.mem_range.mpr ⟨𝟙 _, Category.id_comp _⟩
      obtain ⟨x, hx⟩ := SubgroupFunctor.mem_range.mp hmem
      rw [← hx, Category.assoc, ← Grp.comp_hom_hom, hjf]
      exact MonObj.comp_one _
    let : Flat q.hom.hom.left := hq.1
    let : Surjective q.hom.hom.left := hq.2.1
    let : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom
    have hVa : IsAffine V.X.left := by
      obtain ⟨e, he⟩ := hV
      exact RelativeRoot.AdditiveGroupQuotient.isAffine e he
    let : IsAffineHom V.X.hom := inferInstance
    have : QuasiCompact (q.hom.hom.left ≫ V.X.hom) := by
      rw [Over.w]
      infer_instance
    let : QuasiCompact q.hom.hom.left := QuasiCompact.of_comp _ V.X.hom
    have hd := hG.hom_eq_zero_of_isVectorGroupOfDimension_one hV
      (FpqcHomDescent.hom q f hk)
    rw [← FpqcHomDescent.fac q f hk, hd]
    apply Grp.hom_ext
    exact MonObj.comp_one _

/-- An affine split-unipotent source has no nonzero actual homomorphism to an
actual group scheme with only constant affine-line morphisms. -/
theorem hom_eq_zero_of_isSplitUnipotent
    {H : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom H.X.hom]
    (hH : RelativeRoot.IsSplitUnipotent H) (f : H ⟶ G) : f = 0 := by
  obtain ⟨n, hn⟩ := hH
  exact hG.hom_eq_zero_of_hasSplitSeries n H hn f

/-- Affine-line rigidity implies trivial full image for every smooth connected
split-unipotent closed subgroup, with no normality requirement. -/
theorem hasNoNontrivialSplitUnipotentSubgroup [IsAffineHom G.X.hom] :
    HasNoNontrivialSplitUnipotentSubgroup G := by
  intro H j hj _ _ _ hH
  let : IsAffineHom H.X.hom := HomogeneousQuotient.affine_subgroup_of_closed G H j hj
  have hj0 := hG.hom_eq_zero_of_isSplitUnipotent hH j
  apply SubgroupFunctor.ext
  intro T
  ext x
  constructor
  · intro hx
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    rw [SubgroupFunctor.bot_carrier, Subgroup.mem_bot]
    rw [hj0]
    exact MonObj.comp_one _
  · intro hx
    rw [SubgroupFunctor.bot_carrier, Subgroup.mem_bot] at hx
    subst x
    exact Subgroup.one_mem _

/-- The actual action of every split torus on a smooth connected affine group
with affine-line rigidity is trivial on every relative scheme test. -/
theorem splitTorus_action_eq_trivial [IsAffineHom G.X.hom] [Smooth G.X.hom]
    [ConnectedSpace G.X.left] {S : CommGroupScheme (Spec (CommRingCat.of k))}
    (b : AutomorphicAction S.toGrp G) (hS : IsSplitTorus S.toGrp) :
    b = AutomorphicAction.trivial S.toGrp G :=
  b.eq_trivial_of_no_split_unipotent_subgroup hS
    hG.hasNoNontrivialSplitUnipotentSubgroup

end HasConstantAffineLineMaps

end Langlands.GroupScheme
