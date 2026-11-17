import Langlands.GroupScheme.Absolute.BorelCenterEqualityStatement
import Langlands.GroupScheme.Absolute.BorelCentralizerCenterStatement
import Langlands.GroupScheme.Absolute.BorelContainingSubgroupSelfNormalizerStatement
import Langlands.GroupScheme.Derived.CenterReduction
import Langlands.GroupScheme.Reductive.NormalCenterDescent
import Langlands.GroupScheme.Rational.UnipotentSmoothCenter

/-! # Borel-centre equality from centralizers and self-normalization -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- For a monomorphic self-normalizing subgroup, ambient central points are exactly
images of central subgroup points if central subgroup points stay central. -/
theorem center_points_iff_of_selfNormalizer
    {S : Scheme.{u}} {G B : GroupScheme S} (i : B ⟶ G) [Mono i.hom.hom]
    (hn : (SubgroupFunctor.range i).normalizer = SubgroupFunctor.range i)
    (hc : center B ≤ (center G).comap i)
    (T : Over S) (x : T ⟶ G.X) :
    x ∈ (center G).carrier T ↔
      ∃ y : T ⟶ B.X, y ∈ (center B).carrier T ∧ y ≫ i.hom.hom = x := by
  constructor
  · intro hx
    have hxN := (SubgroupFunctor.centralizer_le_normalizer (SubgroupFunctor.range i)) T
      (SubgroupFunctor.center_le_centralizer (SubgroupFunctor.range i) T hx)
    rw [hn] at hxN
    obtain ⟨y, hy⟩ := SubgroupFunctor.mem_range.mp hxN
    refine ⟨y, center_comap_le_of_mono i T ?_, hy⟩
    change y ≫ i.hom.hom ∈ (center G).carrier T
    rwa [hy]
  · rintro ⟨y, hy, rfl⟩
    exact hc T hy

/-- Algebraically closed Borel-centralizer equality implies that the centre of a
geometric Borel maps into the ambient centre over every field. -/
theorem geometricBorel_center_le_comap_of_borelCentralizerCenter
    (hCentralizer : BorelCentralizerCenterStatement.{u})
    {k : Type u} [Field k]
    {G B : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (i : B ⟶ G) (hi : IsGeometricBorelSubgroup i) :
    center B ≤ (center G).comap i := by
  let b := toAlgebraicClosure k
  obtain ⟨Z, z, hz, hrep⟩ := center_hasClosedRepresentative (G := G)
  have hcenter : IsSchemeTheoreticCenter z := ⟨hz, hrep.2⟩
  obtain ⟨hsurj, hflat, hqc⟩ := fieldExtension_fpqc k (AlgebraicClosure k)
  let : Surjective b := hsurj
  let : Flat b := hflat
  let : QuasiCompact b := hqc
  apply center_le_comap_of_baseChange_le b i z hcenter
  let : Smooth ((GroupScheme.baseChange b).obj G).X.hom :=
    inferInstanceAs (Smooth (pullback.snd G.X.hom b))
  let : IsAffineHom ((GroupScheme.baseChange b).obj G).X.hom :=
    inferInstanceAs (IsAffineHom (pullback.snd G.X.hom b))
  let : ConnectedSpace ((GroupScheme.baseChange b).obj G).X.left :=
    G.connectedSpace_baseChange_of_smooth_affine b
  obtain ⟨hmap, heq⟩ := hCentralizer (AlgebraicClosure k)
    ((GroupScheme.baseChange b).obj G) ((GroupScheme.baseChange b).obj B)
    ((GroupScheme.baseChange b).map i) hi.2
  intro T x hx
  change x ≫ ((GroupScheme.baseChange b).map i).hom.hom ∈
    (center ((GroupScheme.baseChange b).obj G)).carrier T
  rw [← heq]
  exact hmap T x hx

/-- The two independent structural inputs needed by this reduction. -/
def BorelCenterEqualityReductionStatement : Prop :=
  BorelCentralizerCenterStatement.{u} →
    BorelContainingSubgroupSelfNormalizerStatement.{u} →
      BorelCenterEqualityStatement.{u}

/-- Self-normalization gives centre containment, and Borel-centralizer equality
after algebraic closure gives the other inclusion by fpqc descent. -/
theorem borelCenterEqualityReduction : BorelCenterEqualityReductionStatement.{u} := by
  intro hCentralizer hNormalizer k _ G _ _ _ B i hi T x
  let : IsClosedImmersion i.hom.hom.left := hi.1.isClosedSubgroup
  let : Mono i.hom.hom := Over.mono_of_mono_left _
  have hn := (hNormalizer k G B B i i (𝟙 B)
    hi.1.isClosedSubgroup hi.1.smooth hi (Category.id_comp i)).2
  exact center_points_iff_of_selfNormalizer i hn
    (geometricBorel_center_le_comap_of_borelCentralizerCenter hCentralizer i hi) T x

end Langlands.GroupScheme
