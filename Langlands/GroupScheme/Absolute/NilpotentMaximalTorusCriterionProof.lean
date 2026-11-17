import Langlands.GroupScheme.Absolute.NilpotentMaximalTorusCriterionStatement
import Langlands.GroupScheme.Absolute.MaximalTorusConjugacyProof
import Langlands.GroupScheme.Absolute.BorelMaximalTorusProof
import Langlands.GroupScheme.Absolute.PrescribedBorelQuotient
import Langlands.GroupScheme.Absolute.RationalSubgroupContainment
import Langlands.GroupScheme.SolvableProperFixedPointProof
import Langlands.GroupScheme.Torus.AffineCentralizerQuotient
import Langlands.GroupScheme.Nilpotent.EmptyRoots
import Langlands.GroupScheme.Nilpotent.TorusDescent
import Langlands.GroupScheme.Rational.NormalSplitTorusCentrality
import Mathlib.Tactic.TFAE

/-! # Nilpotence criteria through maximal tori and Borel subgroups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace NilpotentMaximalTorusCriterion

variable {k : Type u} [Field k] [IsAlgClosed k]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]

/-- A closed subgroup centralized by a Borel is central in the ambient group.
The affine coefficient orbit descends through the proper Borel quotient. -/
theorem isCentral_of_borel_centralizes
    {B H : GroupScheme (Spec (CommRingCat.of k))}
    {b : B ⟶ G} (hb : IsBorelSubgroup b)
    (j : H ⟶ G) (hj : IsClosedSubgroup j)
    (hcentral : SubgroupFunctor.range b ≤ (SubgroupFunctor.range j).centralizer) :
    IsCentral j := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : IsReduced G.X.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field
      k G.X.left G.X.hom
  obtain ⟨Y, r, hY, hr⟩ := exists_affine_centralizer_orbit_of_projective j hj
  have : IsAffineHom Y.hom := hY
  have : IsAffine Y.left := isAffine_of_isAffineHom Y.hom
  obtain ⟨Q, q, hQ, hqs, hqsurj, hqq, hq⟩ :=
    hb.exists_properQuotient_of_solvableProperFixedPoint solvableProperFixedPoint
  have : IsProper Q.hom := hQ
  have : Smooth q.left := hqs
  have : Surjective q.left := hqsurj
  have : QuasiCompact q.left := hqq
  have : ConnectedSpace Q.left := q.left.surjective.connectedSpace q.left.continuous
  have : IsReduced Q.left :=
    Langlands.AlgebraicGeometry.GeometricallyReducedOfAlgClosedProof.isReduced_of_flat_of_surjective
      q.left
  have hf : ∀ (U : Over (Spec (CommRingCat.of k))) (g h : U ⟶ G.X),
      g ≫ q = h ≫ q → g ≫ r = h ≫ r :=
    fun U g h he => (hr U g h).mpr (hcentral U ((hq U g h).mp he))
  let ρ := HomogeneousQuotientComparison.desc q r hf
  have hρ : q ≫ ρ = r := HomogeneousQuotientComparison.fac_desc q r hf
  let s : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Q :=
    (1 : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) ≫ q
  have hc : ρ = toUnit Q ≫ s ≫ ρ := by
    apply Over.OverMorphism.ext
    exact Langlands.AlgebraicGeometry.affineMap_eq_constant_of_proper_connected_reduced
      Q.hom s.left (Over.w s) ρ.left
  have hcent (U : Over (Spec (CommRingCat.of k))) (g : U ⟶ G.X) :
      g ∈ (SubgroupFunctor.range j).centralizer.carrier U := by
    have he : g ≫ r = (1 : U ⟶ G.X) ≫ r := by
      rw [← hρ, hc]
      simp only [comp_toUnit_assoc]
    have hh := (hr U 1 g).mp he.symm
    simpa only [inv_one, one_mul] using hh
  intro U x V a g
  have h := hcent V g V (𝟙 V) ((a ≫ x) ≫ j.hom.hom)
    (SubgroupFunctor.mem_range.mpr ⟨a ≫ x, rfl⟩)
  simpa only [Category.id_comp, Category.assoc] using h.symm

/-- A nilpotent Borel contains an ambient maximal torus which is central
in the whole group, hence the whole group is nilpotent. -/
theorem nilpotent_of_nilpotent_borel
    {B : GroupScheme (Spec (CommRingCat.of k))}
    {b : B ⟶ G} (hb : IsBorelSubgroup b) (hB : IsNilpotentGroupScheme B) :
    IsNilpotentGroupScheme G := by
  have : Smooth B.X.hom := hb.smooth
  have : ConnectedSpace B.X.left := hb.connectedSpace
  have : IsClosedImmersion b.hom.hom.left := hb.isClosedSubgroup
  have : IsAffineHom B.X.hom := by
    rw [← Over.w b.hom.hom]
    infer_instance
  obtain ⟨T, j, _, hj, t, ht⟩ := borelMaximalTorus k G B b hb
  have htcentral := hB.isCentral_of_isTorus T hj.1 t
  apply hj.isNilpotentGroupScheme_of_isCentral_of_isAlgClosed
  apply isCentral_of_borel_centralizes hb j hj.2.1
  intro U y hy V a x hx
  obtain ⟨z, rfl⟩ := SubgroupFunctor.mem_range.mp hy
  obtain ⟨w, rfl⟩ := SubgroupFunctor.mem_range.mp hx
  have hc := htcentral V w V (𝟙 V) (a ≫ z)
  change (w ≫ t.hom.hom) * (a ≫ z) = (a ≫ z) * (w ≫ t.hom.hom) at hc
  change Commute ((a ≫ z) ≫ b.hom.hom) (w ≫ j.hom.hom)
  rw [← ht, Grp.comp_hom_hom, ← Category.assoc]
  have hh := congrArg (fun x : V ⟶ B.X => x ≫ b.hom.hom) hc.symm
  apply (commute_iff_eq _ _).mpr
  simpa only [MonObj.mul_comp] using hh

/-- Uniqueness of the maximal torus makes each maximal torus normal.
Connected normalizers of split tori centralize them. -/
theorem central_of_unique_maximal_tori
    (hunique : ∀ (T T' : CommGroupScheme (Spec (CommRingCat.of k)))
      (j : T.toGrp ⟶ G) (j' : T'.toGrp ⟶ G), IsMaximalTorus j →
      IsMaximalTorus j' → SubgroupFunctor.range j = SubgroupFunctor.range j')
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {j : T.toGrp ⟶ G} (hj : IsMaximalTorus j) : IsCentral j := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : IsReduced G.X.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field
      k G.X.left G.X.hom
  have : IsClosedImmersion j.hom.hom.left := hj.2.1
  have hconj (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)
      (V : Over (Spec (CommRingCat.of k))) (x : V ⟶ G.X)
      (hx : x ∈ (SubgroupFunctor.range j).carrier V) :
      G.constantPoint g V * x * (G.constantPoint g V)⁻¹ ∈
        (SubgroupFunctor.range j).carrier V := by
    rw [hunique T T j (j ≫ (G.innerIso g).hom) hj (hj.comp_iso _)]
    obtain ⟨t, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    apply SubgroupFunctor.mem_range.mpr
    refine ⟨t, ?_⟩
    rw [Grp.comp_hom_hom, ← Category.assoc, comp_innerIso_hom]
  obtain ⟨N, n, hnc, hr⟩ :=
    (hasClosedRepresentative_normalizer_centralizer_range j hj.2.1).1
  have hle : SubgroupFunctor.range (𝟙 G) ≤ SubgroupFunctor.range n := by
    apply SubgroupFunctor.range_le_of_algClosed_points hnc
    intro g _
    rw [hr.2]
    intro V a x hx
    rw [comp_eq_constantPoint a g]
    refine ⟨hconj g V x hx, ?_⟩
    simpa only [constantPoint_inv, inv_inv] using hconj g⁻¹ V x hx
  have hn : (SubgroupFunctor.range j).IsNormal := by
    intro V g x _ hx
    have hg : g ∈ (SubgroupFunctor.range n).carrier V :=
      hle V (SubgroupFunctor.mem_range.mpr ⟨g, by
        simp only [Grp.id_hom_hom, Category.comp_id]⟩)
    rw [hr.2] at hg
    exact SubgroupFunctor.conj_mem_of_mem_normalizer hg hx
  exact isCentral_of_isNormal_of_isSplitTorus j
    (hj.1.isSplitTorus_of_finiteGaloisSplitting torusFiniteGaloisSplitting) hn

/-- Central maximal tori have the same all-test range, by conjugacy. -/
theorem range_eq_of_central_maximal_tori
    {T T' : CommGroupScheme (Spec (CommRingCat.of k))}
    {j : T.toGrp ⟶ G} {j' : T'.toGrp ⟶ G}
    (hj : IsMaximalTorus j) (hj' : IsMaximalTorus j') (hc : IsCentral j) :
    SubgroupFunctor.range j = SubgroupFunctor.range j' := by
  obtain ⟨g, e, he⟩ := maximalTorusConjugacy k G T T' j j' hj hj'
  have hfix : j ≫ (G.innerIso g).hom = j := by
    apply hom_ext_points
    intro U t
    rw [Grp.comp_hom_hom, ← Category.assoc, comp_innerIso_hom]
    have ht := hc U t U (𝟙 U) (G.constantPoint g U)
    simp only [Category.id_comp] at ht
    rw [← ht, mul_inv_cancel_right]
  rw [hfix] at he
  let e' : T.toGrp ≅ T'.toGrp :=
    { hom := CommGroupScheme.groupHom e.hom
      inv := CommGroupScheme.groupHom e.inv
      hom_inv_id := congrArg CommGroupScheme.groupHom e.hom_inv_id
      inv_hom_id := congrArg CommGroupScheme.groupHom e.inv_hom_id }
  rw [he, SubgroupFunctor.range_iso_comp e']

omit [IsAlgClosed k] [IsAffineHom G.X.hom] in
/-- A smooth connected solvable group is its own Borel subgroup. -/
theorem borel_id_of_solvable (hG : IsSolvableGroupScheme G) :
    IsBorelSubgroup (𝟙 G) := by
  refine ⟨?_, inferInstance, inferInstance, hG, ?_⟩
  · change IsClosedImmersion (𝟙 G.X.left)
    infer_instance
  · intro B' i' f hi' _ _ _ hf
    have : IsClosedImmersion i'.hom.hom.left := hi'
    have : Mono i'.hom.hom := Over.mono_of_mono_left _
    refine ⟨⟨i', hf, Grp.hom_ext _ _ ?_⟩⟩
    apply (cancel_mono i'.hom.hom).1
    rw [← Grp.comp_hom_hom, Category.assoc, hf, Category.comp_id, Grp.id_hom_hom,
      Category.id_comp]

end NilpotentMaximalTorusCriterion

open NilpotentMaximalTorusCriterion in
/-- Milne, Proposition 17.23: uniqueness of the maximal torus, existence of
a nilpotent Borel, nilpotence and centrality of all maximal tori are equivalent. -/
theorem nilpotentMaximalTorusCriterion : NilpotentMaximalTorusCriterionStatement.{u} := by
  intro k _ _ G _ _ _
  tfae_have 1 → 4 := by
    intro h T j hj
    exact central_of_unique_maximal_tori h hj
  tfae_have 4 → 3 := by
    intro h
    obtain ⟨T, j, hj⟩ := exists_isMaximalTorus G
    exact hj.isNilpotentGroupScheme_of_isCentral_of_isAlgClosed (h T j hj)
  tfae_have 3 → 4 := by
    intro h T j hj
    exact h.isCentral_of_isTorus T hj.1 j
  tfae_have 4 → 1 := by
    intro h T T' j j' hj hj'
    exact range_eq_of_central_maximal_tori hj hj' (h T j hj)
  tfae_have 2 → 3 := by
    rintro ⟨B, b, hb, hB⟩
    exact nilpotent_of_nilpotent_borel hb hB
  tfae_have 3 → 2 := by
    intro h
    exact ⟨G, 𝟙 G, borel_id_of_solvable h.isSolvableGroupScheme, h⟩
  tfae_finish

end Langlands.GroupScheme
