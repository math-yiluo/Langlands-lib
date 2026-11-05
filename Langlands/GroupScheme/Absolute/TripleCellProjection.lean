import Langlands.GroupScheme.Absolute.TripleCellGeneration
import Langlands.GroupScheme.DominantHomFaithfullyFlat
import Langlands.GroupScheme.FppfQuotientComparison

/-! # Faithfully flat projections from dynamic-factor lifts -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Dynamic

section Dominance

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    {M Z U : GroupScheme (Spec (CommRingCat.of k))}
    {iM : M ⟶ G} {iZ : Z ⟶ G} {iU : U ⟶ G}
    (hM : (unipotent (CommGroupScheme.groupHom
      (Gm.powerHom (Spec (CommRingCat.of k)) (-1)) ≫ χ)).IsRepresentedBy iM)
    (hZ : (centralizer χ).IsRepresentedBy iZ)
    (hU : (unipotent χ).IsRepresentedBy iU)

include hM hZ hU

/-- A homomorphism whose range contains the three dynamic factors is dominant.
No geometric assumption on its source is needed. -/
theorem isDominant_of_contains_tripleCell
    {D : GroupScheme (Spec (CommRingCat.of k))} (p : D ⟶ G)
    (hpM : SubgroupFunctor.range iM ≤ SubgroupFunctor.range p)
    (hpZ : SubgroupFunctor.range iZ ≤ SubgroupFunctor.range p)
    (hpU : SubgroupFunctor.range iU ≤ SubgroupFunctor.range p) :
    IsDominant p.hom.hom.left := by
  obtain ⟨a, ha⟩ := SubgroupFunctor.mem_range.mp
    (tripleCellMultiplication_mem iM iZ iU (SubgroupFunctor.range p) hpM hpZ hpU)
  have : IsDominant (a.left ≫ p.hom.hom.left) := by
    rw [← Over.comp_left, ha]
    exact isDominant_tripleCellMultiplication χ hM hZ hU
  exact IsDominant.of_comp a.left p.hom.hom.left

/-- The same factor-containment criterion gives scheme-theoretic dominance. -/
theorem isSchemeTheoreticallyDominant_of_contains_tripleCell
    {D : GroupScheme (Spec (CommRingCat.of k))} (p : D ⟶ G)
    (hpM : SubgroupFunctor.range iM ≤ SubgroupFunctor.range p)
    (hpZ : SubgroupFunctor.range iZ ≤ SubgroupFunctor.range p)
    (hpU : SubgroupFunctor.range iU ≤ SubgroupFunctor.range p) :
    IsSchemeTheoreticallyDominant p.hom.hom.left := by
  have : GeometricallyIntegral G.X.hom :=
    smoothConnectedAffineGeometry.1 k G inferInstance inferInstance inferInstance
  have : IsIntegral G.X.left :=
    GeometricallyIntegral.isIntegral_of_subsingleton G.X.hom
  have := isDominant_of_contains_tripleCell χ hM hZ hU p hpM hpZ hpU
  exact IsSchemeTheoreticallyDominant.of_isDominant _

end Dominance

section Intrinsic

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]

/-- Intrinsic dynamic-factor containment gives scheme-theoretic dominance,
without choosing representatives in the hypotheses. -/
theorem isSchemeTheoreticallyDominant_of_contains_dynamicFactors
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    {D : GroupScheme (Spec (CommRingCat.of k))} (p : D ⟶ G)
    (hM : unipotent (CommGroupScheme.groupHom
      (Gm.powerHom (Spec (CommRingCat.of k)) (-1)) ≫ χ) ≤ SubgroupFunctor.range p)
    (hZ : centralizer χ ≤ SubgroupFunctor.range p)
    (hU : unipotent χ ≤ SubgroupFunctor.range p) :
    IsSchemeTheoreticallyDominant p.hom.hom.left := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let χ' := CommGroupScheme.groupHom
    (Gm.powerHom (Spec (CommRingCat.of k)) (-1)) ≫ χ
  have hMr := Affine.isRepresentedBy_unipotentHom χ'
  have hZr := Affine.isRepresentedBy_centralizerHom χ
  have hUr := Affine.isRepresentedBy_unipotentHom χ
  exact isSchemeTheoreticallyDominant_of_contains_tripleCell χ hMr hZr hUr p
    (by rw [hMr.2]; exact hM) (by rw [hZr.2]; exact hZ) (by rw [hUr.2]; exact hU)

/-- An affine finite-type source whose range contains the dynamic factors
projects faithfully flat, locally of finite presentation and quasi-compactly. -/
theorem projection_geometry_of_contains_dynamicFactors
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    {D : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom D.X.hom] [LocallyOfFiniteType D.X.hom] (p : D ⟶ G)
    (hM : unipotent (CommGroupScheme.groupHom
      (Gm.powerHom (Spec (CommRingCat.of k)) (-1)) ≫ χ) ≤ SubgroupFunctor.range p)
    (hZ : centralizer χ ≤ SubgroupFunctor.range p)
    (hU : unipotent χ ≤ SubgroupFunctor.range p) :
    Flat p.hom.hom.left ∧ Surjective p.hom.hom.left ∧
      LocallyOfFinitePresentation p.hom.hom.left ∧ QuasiCompact p.hom.hom.left := by
  have := isSchemeTheoreticallyDominant_of_contains_dynamicFactors χ p hM hZ hU
  obtain ⟨hflat, hsurj⟩ := DominantHom.flat_surjective p
  have : LocallyOfFiniteType p.hom.hom.left := by
    have : LocallyOfFiniteType (p.hom.hom.left ≫ G.X.hom) := by
      rw [Over.w]
      infer_instance
    exact locallyOfFiniteType_of_comp p.hom.hom.left G.X.hom
  have : IsLocallyNoetherian G.X.left :=
    LocallyOfFiniteType.isLocallyNoetherian G.X.hom
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : IsAffine D.X.left := isAffine_of_isAffineHom D.X.hom
  have : IsAffineHom p.hom.hom.left := inferInstance
  exact ⟨hflat, hsurj, inferInstance, inferInstance⟩

end Intrinsic

section Comparison

variable {k : Type u} [Field k]
    {D G H : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom D.X.hom] [LocallyOfFiniteType D.X.hom]
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    [Smooth H.X.hom] [IsAffineHom H.X.hom] [ConnectedSpace H.X.left]
    (χG : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (χH : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ H)
    (p : D ⟶ G) (q : D ⟶ H)
    (hpM : unipotent (CommGroupScheme.groupHom
      (Gm.powerHom (Spec (CommRingCat.of k)) (-1)) ≫ χG) ≤ SubgroupFunctor.range p)
    (hpZ : centralizer χG ≤ SubgroupFunctor.range p)
    (hpU : unipotent χG ≤ SubgroupFunctor.range p)
    (hqM : unipotent (CommGroupScheme.groupHom
      (Gm.powerHom (Spec (CommRingCat.of k)) (-1)) ≫ χH) ≤ SubgroupFunctor.range q)
    (hqZ : centralizer χH ≤ SubgroupFunctor.range q)
    (hqU : unipotent χH ≤ SubgroupFunctor.range q)
    (hkernel : SubgroupFunctor.range (kernelι p) = SubgroupFunctor.range (kernelι q))

/-- Two projections containing their targets' intrinsic dynamic factors and
having the same full kernel give an actual isomorphism of the targets. -/
def comparisonIsoOfDynamicFactors : G ≅ H := by
  have hp := projection_geometry_of_contains_dynamicFactors χG p hpM hpZ hpU
  have hq := projection_geometry_of_contains_dynamicFactors χH q hqM hqZ hqU
  have := hp.2.2.2
  have := hq.2.2.2
  exact FppfQuotientComparison.iso
    (show RelativeRoot.IsFppfQuotient (SubgroupFunctor.range (kernelι p)) p from
      ⟨hp.1, hp.2.1, hp.2.2.1, rfl⟩)
    (show RelativeRoot.IsFppfQuotient (SubgroupFunctor.range (kernelι p)) q from
      ⟨hq.1, hq.2.1, hq.2.2.1, hkernel.symm⟩)

/-- The comparison isomorphism lies over the common source. -/
@[reassoc]
theorem comparisonIsoOfDynamicFactors_fac :
    p ≫ (comparisonIsoOfDynamicFactors χG χH p q
      hpM hpZ hpU hqM hqZ hqU hkernel).hom = q := by
  have := (projection_geometry_of_contains_dynamicFactors χG p hpM hpZ hpU).2.2.2
  have := (projection_geometry_of_contains_dynamicFactors χH q hqM hqZ hqU).2.2.2
  unfold comparisonIsoOfDynamicFactors
  exact FppfQuotientComparison.iso_fac _ _

/-- The equation over the common source determines the actual isomorphism. -/
theorem comparisonIsoOfDynamicFactors_unique (e : G ≅ H) (he : p ≫ e.hom = q) :
    e = comparisonIsoOfDynamicFactors χG χH p q
      hpM hpZ hpU hqM hqZ hqU hkernel := by
  have := (projection_geometry_of_contains_dynamicFactors χG p hpM hpZ hpU).2.2.2
  have := (projection_geometry_of_contains_dynamicFactors χH q hqM hqZ hqU).2.2.2
  unfold comparisonIsoOfDynamicFactors
  exact FppfQuotientComparison.iso_unique _ _ e he

/-- Any pair of morphisms induced from one map to the common source is
compatible with the comparison; this includes a common torus. -/
theorem comparisonIsoOfDynamicFactors_compatible
    {T : GroupScheme (Spec (CommRingCat.of k))}
    (t : T ⟶ D) (iG : T ⟶ G) (iH : T ⟶ H)
    (htG : t ≫ p = iG) (htH : t ≫ q = iH) :
    iG ≫ (comparisonIsoOfDynamicFactors χG χH p q
      hpM hpZ hpU hqM hqZ hqU hkernel).hom = iH := by
  rw [← htG, Category.assoc, comparisonIsoOfDynamicFactors_fac, htH]

end Comparison

end Langlands.GroupScheme.Dynamic
