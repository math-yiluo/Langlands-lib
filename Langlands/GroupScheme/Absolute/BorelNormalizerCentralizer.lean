import Langlands.GroupScheme.Absolute.BorelNormalizerInduction
import Langlands.GroupScheme.Torus.CommutatorEnd
import Langlands.GroupScheme.Rational.RootAnnihilatorCentralityStatement

/-! # The commutator-kernel proper-centralizer branch -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section ArbitraryBase

variable {S : Scheme.{u}} {G M : GroupScheme S}

/-- If a representative of a cocharacter centralizer is an isomorphism, the
cocharacter is central on all test schemes. -/
theorem isCentral_of_isIso_dynamicCentralizer
    (χ : (Gm S).toGrp ⟶ G) (j : M ⟶ G)
    (hrep : (Dynamic.centralizer χ).IsRepresentedBy j) [IsIso j] :
    IsCentral χ := by
  apply (isCentral_iff_dynamicCentralizer_eq_top χ).mpr
  rw [← hrep.2]
  apply SubgroupFunctor.ext
  intro U
  apply top_unique
  intro x _
  apply SubgroupFunctor.mem_range.mpr
  refine ⟨x ≫ (inv j).hom.hom, ?_⟩
  rw [Category.assoc, ← Grp.comp_hom_hom, IsIso.inv_hom_id,
    Grp.id_hom_hom, Category.comp_id]

/-- Noncentrality makes every representative of the actual centralizer proper
in the sense required by Lie-dimension induction. -/
theorem not_isIso_dynamicCentralizer_of_not_isCentral
    (χ : (Gm S).toGrp ⟶ G) (j : M ⟶ G)
    (hrep : (Dynamic.centralizer χ).IsRepresentedBy j) (hχ : ¬ IsCentral χ) :
    ¬ IsIso j := by
  intro hj
  let _ := hj
  exact hχ (isCentral_of_isIso_dynamicCentralizer χ j hrep)

end ArbitraryBase

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {B M G : GroupScheme (Spec (CommRingCat.of k))}

/-- A noncentral cocharacter killed by the actual torus commutator gives the
proper-centralizer induction step for the original normalizing point. -/
theorem mem_borelRange_of_noncentral_commutatorKernel
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    [ConnectedSpace M.X.left]
    (ih : ∀ (H : GroupScheme (Spec (CommRingCat.of k)))
      [Smooth H.X.hom] [IsAffineHom H.X.hom] [ConnectedSpace H.X.left],
      Lie.dimension H < Lie.dimension G → BorelNormalizerProperty H)
    (b : B ⟶ G) (i : T.toGrp ⟶ G) [Mono i.hom.hom.left]
    (n : normalizerPoints i) (ν : cocharacterLattice T)
    (hzero : ν ≫ torusCommutatorEnd i n = 0)
    (hν : ¬ IsCentral (CommGroupScheme.groupHom ν ≫ i))
    (j : M ⟶ G) (hj : IsClosedSubgroup j)
    (hrep : (Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ i)).IsRepresentedBy j)
    (hc : IsBorelSubgroup (subgroupIntersectionFst j b))
    (hn : n.val ∈ Subgroup.normalizer
      ((SubgroupFunctor.range b).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))) :
        Set (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X))) :
    n.val ∈ (SubgroupFunctor.range b).carrier
      (Over.mk (𝟙 (Spec (CommRingCat.of k)))) := by
  apply mem_borelRange_of_proper_cocharacterCentralizer ih b
    (CommGroupScheme.groupHom ν ≫ i) j hj hrep
    (not_isIso_dynamicCentralizer_of_not_isCentral _ j hrep hν) hc hn
  exact (normalizerPoint_mem_dynamicCentralizer_iff_commutator_eq_zero i n ν).mpr hzero

/-- An actual lift through the Borel inclusion in the noncentral
commutator-kernel branch, retaining its image as the original point. -/
def borelPointOfNoncentralCommutatorKernel
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    [ConnectedSpace M.X.left]
    (ih : ∀ (H : GroupScheme (Spec (CommRingCat.of k)))
      [Smooth H.X.hom] [IsAffineHom H.X.hom] [ConnectedSpace H.X.left],
      Lie.dimension H < Lie.dimension G → BorelNormalizerProperty H)
    (b : B ⟶ G) (i : T.toGrp ⟶ G) [Mono i.hom.hom.left]
    (n : normalizerPoints i) (ν : cocharacterLattice T)
    (hzero : ν ≫ torusCommutatorEnd i n = 0)
    (hν : ¬ IsCentral (CommGroupScheme.groupHom ν ≫ i))
    (j : M ⟶ G) (hj : IsClosedSubgroup j)
    (hrep : (Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ i)).IsRepresentedBy j)
    (hc : IsBorelSubgroup (subgroupIntersectionFst j b))
    (hn : n.val ∈ Subgroup.normalizer
      ((SubgroupFunctor.range b).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))) :
        Set (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X))) :
    {p : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ B.X //
      p ≫ b.hom.hom = n.val} := by
  let h := SubgroupFunctor.mem_range.mp
    (mem_borelRange_of_noncentral_commutatorKernel ih b i n ν hzero hν j hj hrep hc hn)
  exact ⟨Classical.choose h, Classical.choose_spec h⟩

end Langlands.GroupScheme
