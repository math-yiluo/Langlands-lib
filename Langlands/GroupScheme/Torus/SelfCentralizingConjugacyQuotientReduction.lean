import Langlands.GroupScheme.Torus.SelfCentralizingConjugacyQuotientStatement
import Langlands.GroupScheme.Torus.SelfCentralizingQuotientAffineOfRepresentationStatement
import Langlands.GroupScheme.MatrixRepresentation.LocalCentralKernelStatement
import Langlands.GroupScheme.Torus.SeparatedNormalizerStatement
import Langlands.GroupScheme.HomScheme.SmoothAffineFiberTorusSubgroupRepresentabilityStatement
import Langlands.GroupScheme.HomScheme.AdmissiblePresheaf
import Langlands.GroupScheme.SubgroupFunctor.ConjugateFamilyNormalizer
import Langlands.GroupScheme.HomogeneousQuotientFromEmbedding

/-! # Reducing the affine normalizer quotient to four statements -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.TorusSubgroupModuli

variable {S : Scheme.{u}} {G : GroupScheme S} {M U : Over S} {K : GroupScheme M.left}
  {H : GroupScheme S}

/-- A universal family of closed torus subgroups has injective evaluation. -/
theorem IsUniversal.evaluate_injective
    {j : K ⟶ (baseChange M.hom).obj G} (huni : IsUniversal j)
    (hK : RelativeTorus.IsTorus K) (hj : IsClosedSubgroup j) :
    Function.Injective (evaluate j (T := U)) := by
  intro a b hab
  obtain ⟨c, hc, huc⟩ := huni U (evaluate j b) (isAdmissible_evaluate j hj hK b)
  exact (huc a hab).trans (huc b rfl).symm

/-- Classify all conjugates of a fixed closed torus using the universal point of `G`. -/
def torusOrbit (j : K ⟶ (baseChange M.hom).obj G) (huni : IsUniversal j)
    (i : H ⟶ G) (hH : RelativeTorus.IsTorus H) (hi : IsClosedSubgroup i) : G.X ⟶ M :=
  Classical.choose (huni G.X
    (SubgroupFunctor.range (SubgroupFunctor.conjugateFamily i (𝟙 G.X)))
    (isAdmissible_range _
      (SubgroupFunctor.isClosedSubgroup_conjugatePullback G.X.hom i hi _)
      (hH.baseChange G.X.hom)))

/-- The orbit morphism pulls back the universal family to the conjugate family. -/
theorem evaluate_torusOrbit_id (j : K ⟶ (baseChange M.hom).obj G) (huni : IsUniversal j)
    (i : H ⟶ G) (hH : RelativeTorus.IsTorus H) (hi : IsClosedSubgroup i) :
    evaluate j (torusOrbit j huni i hH hi) =
      SubgroupFunctor.range (SubgroupFunctor.conjugateFamily i (𝟙 G.X)) :=
  (Classical.choose_spec (huni G.X
    (SubgroupFunctor.range (SubgroupFunctor.conjugateFamily i (𝟙 G.X)))
    (isAdmissible_range _
      (SubgroupFunctor.isClosedSubgroup_conjugatePullback G.X.hom i hi _)
      (hH.baseChange G.X.hom)))).1

/-- On every test, the orbit parameter classifies conjugation by that test's point. -/
theorem evaluate_torusOrbit (j : K ⟶ (baseChange M.hom).obj G) (huni : IsUniversal j)
    (i : H ⟶ G) (hH : RelativeTorus.IsTorus H) (hi : IsClosedSubgroup i) (g : U ⟶ G.X) :
    evaluate j (g ≫ torusOrbit j huni i hH hi) =
      SubgroupFunctor.range (SubgroupFunctor.conjugateFamily i g) := by
  rw [← evaluate_comp]
  rw [evaluate_eq_of_range_eq _ _ (evaluate_torusOrbit_id j huni i hH hi) g]
  simpa only [Category.comp_id] using SubgroupFunctor.evaluate_conjugateFamily i (𝟙 G.X) g

/-- The all-test fibres of the orbit are the cosets of the full normalizer. -/
theorem torusOrbit_fibers (j : K ⟶ (baseChange M.hom).obj G) (huni : IsUniversal j)
    (hK : RelativeTorus.IsTorus K) (hj : IsClosedSubgroup j)
    (i : H ⟶ G) (hH : RelativeTorus.IsTorus H) (hi : IsClosedSubgroup i) (g h : U ⟶ G.X) :
    g ≫ torusOrbit j huni i hH hi = h ≫ torusOrbit j huni i hH hi ↔
      g⁻¹ * h ∈ (SubgroupFunctor.range i).normalizer.carrier U := by
  calc
    _ ↔ evaluate j (g ≫ torusOrbit j huni i hH hi) =
        evaluate j (h ≫ torusOrbit j huni i hH hi) :=
      (huni.evaluate_injective hK hj).eq_iff.symm
    _ ↔ _ := by
      rw [evaluate_torusOrbit, evaluate_torusOrbit]
      exact SubgroupFunctor.range_conjugateFamily_eq_iff i g h

end Langlands.GroupScheme.TorusSubgroupModuli

namespace Langlands.GroupScheme

open Langlands.AlgebraicGeometry.AlgebraicSpace.SmoothRelationQuotient

/-- The target follows from torus-subgroup moduli, smooth normalizers, local
central-kernel representations, and the affineness core. -/
theorem selfCentralizingTorusConjugacyQuotientAffine_of
    (h1 : TorusSubgroupModuli.SmoothAffineFiberTorusSubgroupRepresentabilityStatement.{u})
    (h2 : SeparatedTorusNormalizerStatement.{u})
    (h3 : LocalCentralKernelRepresentationStatement.{u})
    (h4 : SelfCentralizingQuotientAffineOfRepresentationStatement.{u}) :
    SelfCentralizingTorusConjugacyQuotientAffineStatement.{u} := by
  intro S G hsm hsep hqc hfib T t hT ht hmax hcent
  have : Smooth G.X.hom := hsm
  have : IsSeparated G.X.hom := hsep
  have : QuasiCompact G.X.hom := hqc
  obtain ⟨M, K, j, hj, hK, huni, -⟩ := h1 S G (fun s => (hfib s).2)
  obtain ⟨N, n, -, hNsm, hnrep⟩ := h2 S G hsm hsep hqc T t hT ht
  have : Mono n.hom.hom := hnrep.1
  let r := TorusSubgroupModuli.torusOrbit j huni t hT ht
  have hker : ∀ (V : Over S) (x y : V ⟶ G.X),
      x ≫ r = y ≫ r ↔ relation (HomogeneousQuotientFromEmbedding.arrowSpace n)
        (HomogeneousQuotientFromEmbedding.source n)
        (HomogeneousQuotientFromEmbedding.target n) V ⟨x⟩ ⟨y⟩ := by
    intro V x y
    rw [HomogeneousQuotientFromEmbedding.relation_iff, hnrep.2]
    exact TorusSubgroupModuli.torusOrbit_fibers j huni hK hj t hT ht x y
  let Q := schemeQuotientOfMapKernel
    (HomogeneousQuotientFromEmbedding.isEquivalenceRelation n)
    (HomogeneousQuotientFromEmbedding.hasSmoothProjections n hNsm)
    (inferInstance : LocallyOfFiniteType G.X.hom) M r hker
  have : Smooth Q.projection.left := Q.smooth_projection
  have hflat : Flat Q.projection.left := inferInstance
  have hlfp : LocallyOfFinitePresentation Q.projection.left := inferInstance
  have hfibQ : ∀ (V : Over S) (g h : V ⟶ G.X),
      g ≫ Q.projection = h ≫ Q.projection ↔
        g⁻¹ * h ∈ (torusNormalizer t).carrier V := by
    intro V g h
    rw [Q.fibers, HomogeneousQuotientFromEmbedding.relation_iff, hnrep.2]
  have hrep := h3 S G hsm hsep hqc (fun s => (hfib s).1)
  exact ⟨Q.scheme, Q.projection,
    h4 S G hsm hsep hqc hfib hrep T t hT ht hmax hcent Q.scheme Q.projection
      hflat Q.surjective_projection hlfp hfibQ,
    hflat, Q.surjective_projection, hlfp, hfibQ⟩

end Langlands.GroupScheme
