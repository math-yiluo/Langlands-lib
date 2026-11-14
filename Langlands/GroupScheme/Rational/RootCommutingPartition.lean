import Langlands.GroupScheme.GeneratedFamilyStability
import Langlands.GroupScheme.Rational.RootSubgroupRealizationProof
import Langlands.GroupScheme.Rational.RootSubgroupNontrivial
import Langlands.GroupScheme.Rational.IsotropicRootSubgroupGenerationProof
import Langlands.GroupScheme.Lie.TorusCentralizer
import Langlands.GroupScheme.Absolute.RegularCocharacterWeights

/-! # Commuting partitions of the actual relative roots -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    (i : S.toGrp ⟶ G)

/-- The root groups indexed by `s` commute with every root group outside `s`,
on every scheme over the ground field. -/
def IsCommutingRootPartition (s : Set (characterLattice S)) : Prop :=
  ∀ a ∈ s, ∀ b ∈ relativeRoots i, b ∉ s →
    ∀ (Z : Over (Spec (CommRingCat.of k))) (x y : Z ⟶ G.X),
      x ∈ (RelativeRoot.subgroup i a).carrier Z →
      y ∈ (RelativeRoot.subgroup i b).carrier Z → Commute x y

/-- A nonzero actual root group cannot centralize the acting split torus. -/
theorem RelativeRoot.subgroup_not_le_torusCentralizer
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    {a : characterLattice S} (ha : a ∈ relativeRoots i) :
    ¬ RelativeRoot.subgroup i a ≤ torusCentralizer i := by
  intro hle
  let : Smooth G.X.hom := hG.smooth
  obtain ⟨U, j, hj, hclosed, hsm, hconn, hu, hs, hstable, hLie⟩ :=
    RelativeRoot.rootSubgroupRealization k G hG S i hi a ha
  obtain ⟨X, hX, hX0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot ha.2
  have hpoint := (hLie X).mpr
    (RelativeRoot.weightSpace_le_positiveWeightSpan i a hX)
  have hzero := Lie.mem_weightSpace_zero_of_mem_torusCentralizer i X.toMul (hle _ hpoint)
  exact hX0 ((Submodule.disjoint_def.mp
    (weightSpace_disjoint hi.1.1 i ha.1)) X hX hzero)

/-- A torus-stable closed subgroup normalized by every actual root group is
normal in an almost-simple group with a nonempty relative root set. -/
theorem isNormal_of_relativeRootGroups_normalize
    (hG : IsAlmostSimple G) (hi : IsMaximalSplitTorus i)
    (hne : (relativeRoots i).Nonempty)
    {H : GroupScheme (Spec (CommRingCat.of k))} (h : H ⟶ G)
    (hclosed : IsClosedSubgroup h)
    (hstable : (AutomorphicAction.conjugation i).IsStable (SubgroupFunctor.range h))
    (hroot : ∀ a ∈ relativeRoots i,
      RelativeRoot.subgroup i a ≤ (SubgroupFunctor.range h).normalizer) :
    (SubgroupFunctor.range h).IsNormal := by
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  obtain ⟨N, j, hj, hrep⟩ :=
    (hasClosedRepresentative_normalizer_centralizer_range h hclosed).1
  have htorus : SubgroupFunctor.range i ≤ (SubgroupFunctor.range h).normalizer := by
    intro Z g hg V f x hx
    obtain ⟨s, rfl⟩ := SubgroupFunctor.mem_range.mp hg
    constructor
    · simpa only [AutomorphicAction.conjugation_act, Category.assoc] using
        hstable V (f ≫ s) x hx
    · simpa only [AutomorphicAction.conjugation_act, GrpObj.inv_comp,
        Category.assoc, inv_inv] using hstable V (f ≫ s)⁻¹ x hx
  have hani : ¬ IsAnisotropic G := by
    intro han
    obtain ⟨a, ha⟩ := hne
    rw [han.relativeRoots_eq_empty hi.1] at ha
    exact ha
  have htop : (SubgroupFunctor.range h).normalizer = ⊤ := by
    rw [← hrep.2]
    exact isotropicRootSubgroupGeneration k G hG hani S i hi N j hj
      (by rwa [hrep.2]) (fun a ha => by rw [hrep.2]; exact hroot a ha)
  intro Z g x _ hx
  apply SubgroupFunctor.conj_mem_of_mem_normalizer (F := SubgroupFunctor.range h) _ hx
  rw [htop]
  trivial

/-- A nonempty commuting part generates the entire almost-simple group. -/
theorem IsCommutingRootPartition.generated_range_eq_top
    (hG : IsAlmostSimple G) (hi : IsMaximalSplitTorus i)
    {s : Set (characterLattice S)} (hs : s ⊆ relativeRoots i)
    (hne : s.Nonempty) (hcomm : IsCommutingRootPartition i s)
    {A : s → GroupScheme (Spec (CommRingCat.of k))} {a : ∀ r, A r ⟶ G}
    (hrep : ∀ r : s, (RelativeRoot.subgroup i r.val).IsRepresentedBy (a r))
    {H : GroupScheme (Spec (CommRingCat.of k))} {h : H ⟶ G}
    (hgen : IsGeneratedByFamily A a h)
    (hsm : Smooth H.X.hom) (hconn : ConnectedSpace H.X.left) :
    SubgroupFunctor.range h = ⊤ := by
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have hcontains (r : s) : RelativeRoot.subgroup i r.val ≤ SubgroupFunctor.range h := by
    rw [← (hrep r).2]
    exact hgen.family_range_le r
  have hcentral (b : characterLattice S) (hb : b ∈ relativeRoots i) (hbs : b ∉ s) :
      RelativeRoot.subgroup i b ≤ (SubgroupFunctor.range h).centralizer := by
    apply SubgroupFunctor.le_centralizer_iff.mp
    obtain ⟨B, j, hj, hclosed, hsmB, hconnB, hu, hsplit, hstable, hLie⟩ :=
      RelativeRoot.rootSubgroupRealization k G hG.isSemisimple.isConnectedReductive
        S i hi b hb
    rw [← hj.2]
    apply hgen.range_le_centralizer j hclosed
    intro r
    rw [(hrep r).2, hj.2]
    intro Z x hx V f y hy
    exact hcomm r.val r.property b hb hbs V (f ≫ x) y
      ((RelativeRoot.subgroup i r.val).comp_mem f hx) hy
  have hnormal : (SubgroupFunctor.range h).IsNormal := by
    apply isNormal_of_relativeRootGroups_normalize i hG hi
      (hne.mono hs) h hgen.1
    · apply hgen.isStable (AutomorphicAction.conjugation i) hi.1.1.isAffineHom
      intro r
      rw [(hrep r).2]
      exact RelativeRoot.subgroup_isStable i r.val
    · intro b hb
      by_cases hbs : b ∈ s
      · exact (hcontains ⟨b, hbs⟩).trans (SubgroupFunctor.le_normalizer _)
      · exact (hcentral b hb hbs).trans (SubgroupFunctor.centralizer_le_normalizer _)
  rcases hG.normalSubgroup_trivial_or_full H h hgen.1 hsm hconn hnormal with hbot | htop
  · obtain ⟨b, hb⟩ := hne
    exfalso
    apply RelativeRoot.subgroup_not_le_torusCentralizer i
      hG.isSemisimple.isConnectedReductive hi (hs hb)
    have hle := hcontains ⟨b, hb⟩
    rw [hbot] at hle
    intro Z x hx
    have hx1 : x = 1 := hle Z hx
    rw [hx1]
    exact one_mem _
  · exact htop

/-- The actual roots of an almost-simple group admit no nontrivial partition
whose two parts commute on every scheme test. -/
theorem IsCommutingRootPartition.eq_empty_or_eq_relativeRoots
    (hG : IsAlmostSimple G) (hi : IsMaximalSplitTorus i)
    {s : Set (characterLattice S)} (hs : s ⊆ relativeRoots i)
    (hcomm : IsCommutingRootPartition i s) : s = ∅ ∨ s = relativeRoots i := by
  classical
  by_cases hne : s.Nonempty
  · right
    apply Set.Subset.antisymm hs
    intro b hb
    by_contra hbs
    have hGred := hG.isSemisimple.isConnectedReductive
    let : Smooth G.X.hom := hGred.smooth
    let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    choose A a hrep hclosed hsm hconn hu hsplit hstable hLie using
      (fun r : s => RelativeRoot.rootSubgroupRealization k G hGred S i hi r.val (hs r.property))
    obtain ⟨H, h, hsmH, haffH, hconnH, hgen⟩ :=
      FiniteGeneration.exists_smooth_generated_family
        (A := A) (a := a) (fun r => ⟨hsm r, (hclosed r).isAffineHom, hconn r⟩)
    have htop := hcomm.generated_range_eq_top i hG hi hs hne hrep hgen hsmH hconnH
    obtain ⟨B, j, hj, hjclosed, hsmB, hconnB, huB, hsB, hstableB, hLieB⟩ :=
      RelativeRoot.rootSubgroupRealization k G hGred S i hi b hb
    have hcentral : SubgroupFunctor.range h ≤ (RelativeRoot.subgroup i b).centralizer := by
      rw [← hj.2]
      apply hgen.range_le_centralizer j hjclosed
      intro r
      rw [(hrep r).2, hj.2]
      intro Z x hx V f y hy
      exact hcomm r.val r.property b hb hbs V (f ≫ x) y
        ((RelativeRoot.subgroup i r.val).comp_mem f hx) hy
    have hreverse := SubgroupFunctor.le_centralizer_iff.mp hcentral
    apply RelativeRoot.subgroup_not_le_torusCentralizer i hGred hi hb
    intro Z x hx V f t
    have h := hreverse Z hx V f (t ≫ i.hom.hom) (by rw [htop]; trivial)
    exact h
  · exact Or.inl (Set.not_nonempty_iff_eq_empty.mp hne)

end Langlands.GroupScheme
