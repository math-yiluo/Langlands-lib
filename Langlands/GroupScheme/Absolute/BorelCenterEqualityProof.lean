import Langlands.GroupScheme.Absolute.BorelCenterEqualityStatement
import Langlands.GroupScheme.Absolute.BorelCentralizerCenterReduction
import Langlands.GroupScheme.Absolute.BorelHomomorphismRigidityProof
import Langlands.GroupScheme.Absolute.TorusCentralizerBorelContainmentProof
import Langlands.GroupScheme.Absolute.BorelMaximalTorusProof
import Langlands.GroupScheme.Cartan.StructureProof
import Langlands.GroupScheme.Cartan.Basic
import Langlands.GroupScheme.Reductive.NormalCenterDescent
import Langlands.GroupScheme.Reductive.FiniteCenterReflection
import Langlands.GroupScheme.Rational.LeviFactorization
import Langlands.GroupScheme.Derived.CenterReduction
import Langlands.GroupScheme.GeometricConnectedness

/-! # The centre of a connected group variety is the centre of a Borel subgroup (Milne 17.45) -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace BorelCenterEquality

/-- If `j` factors as `f ≫ i`, every point of `j` is a point of `i`. -/
theorem range_le_range_of_comp_eq {S : Scheme.{u}} {A B G : GroupScheme S}
    {f : A ⟶ B} {i : B ⟶ G} {j : A ⟶ G} (h : f ≫ i = j) :
    SubgroupFunctor.range j ≤ SubgroupFunctor.range i := by
  intro T x hx
  obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
  refine SubgroupFunctor.mem_range.mpr ⟨y ≫ f.hom.hom, ?_⟩
  rw [← h, Grp.comp_hom_hom, Category.assoc]

variable {k : Type u} [Field k]

/-- Over an algebraically closed field, the centre of a smooth connected affine group lies in
every Borel subgroup, given the containment of maximal-torus centralizers in Borel subgroups. -/
theorem center_le_range_of_isAlgClosed
    (hT : TorusCentralizerBorelContainmentStatement.{u}) [IsAlgClosed k]
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    {B : GroupScheme (Spec (CommRingCat.of k))} {i : B ⟶ G} (hi : IsBorelSubgroup i) :
    center G ≤ SubgroupFunctor.range i := by
  obtain ⟨T, j, -, hj, f, hf⟩ := borelMaximalTorus k G B i hi
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  obtain ⟨H, c, hc, hrep⟩ := exists_isCartanSubgroup_of_isMaximalTorus hj
  obtain ⟨-, hconn, -⟩ := cartanStructure k G H c hc
  have hle : SubgroupFunctor.range c ≤ SubgroupFunctor.range i :=
    hT k G T j hj B i hi (range_le_range_of_comp_eq hf) H c hc.1 hconn hrep.2.le
  calc center G ≤ torusCentralizer j := center_le_torusCentralizer j
    _ = SubgroupFunctor.range c := hrep.2.symm
    _ ≤ SubgroupFunctor.range i := hle

/-- Over an algebraically closed field, central points of a Borel subgroup are central in the
ambient group, given that the centralizer of a Borel subgroup is the centre. -/
theorem center_le_comap_of_isAlgClosed
    (hC : BorelCentralizerCenterStatement.{u}) [IsAlgClosed k]
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    {B : GroupScheme (Spec (CommRingCat.of k))} {i : B ⟶ G} (hi : IsBorelSubgroup i) :
    center B ≤ (center G).comap i := by
  obtain ⟨h₁, h₂⟩ := hC k G B i hi
  intro T x hx
  rw [SubgroupFunctor.mem_comap, ← h₂]
  exact h₁ T x hx

/-- Over any field, the centre of `G` lies in a geometric Borel subgroup `B`, and the centre of
`B` maps into the centre of `G`, by descent from the algebraic closure. -/
theorem center_le_range_and_comap
    (hT : TorusCentralizerBorelContainmentStatement.{u})
    (hC : BorelCentralizerCenterStatement.{u})
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    {B : GroupScheme (Spec (CommRingCat.of k))} {i : B ⟶ G}
    (hi : IsGeometricBorelSubgroup i) :
    center G ≤ SubgroupFunctor.range i ∧ center B ≤ (center G).comap i := by
  let b := toAlgebraicClosure k
  obtain ⟨hsurj, hflat, hqc⟩ := fieldExtension_fpqc k (AlgebraicClosure k)
  let : Surjective b := hsurj
  let : Flat b := hflat
  let : QuasiCompact b := hqc
  have : Smooth ((GroupScheme.baseChange b).obj G).X.hom := by
    change Smooth (pullback.snd G.X.hom b)
    infer_instance
  have : IsAffineHom ((GroupScheme.baseChange b).obj G).X.hom := by
    change IsAffineHom (pullback.snd G.X.hom b)
    infer_instance
  have : ConnectedSpace ((GroupScheme.baseChange b).obj G).X.left :=
    G.connectedSpace_baseChange_of_smooth_affine b
  have : IsClosedImmersion i.hom.hom.left := hi.1.isClosedSubgroup
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  constructor
  · apply SubgroupFunctor.le_range_of_baseChange_le b i
    rw [← center_baseChange, ← SubgroupFunctor.range_baseChangeHom]
    exact center_le_range_of_isAlgClosed hT _ hi.2
  · obtain ⟨Z, z, hz⟩ := schemeTheoreticCenterExistence_of_isAffineHom (G := G) inferInstance
    exact center_le_comap_of_baseChange_le b i z hz
      (center_le_comap_of_isAlgClosed hC _ hi.2)

end BorelCenterEquality

open BorelCenterEquality in
/-- Milne 17.45 over any field, from Milne 17.22 and 17.29 over algebraically closed fields. -/
theorem borelCenterEquality_of_borelCentralizerCenter_of_torusCentralizerBorelContainment
    (hC : BorelCentralizerCenterStatement.{u})
    (hT : TorusCentralizerBorelContainmentStatement.{u}) :
    BorelCenterEqualityStatement.{u} := by
  intro k _ G _ _ _ B i hi T x
  obtain ⟨hle, hcomap⟩ := center_le_range_and_comap hT hC G hi
  have : IsClosedImmersion i.hom.hom.left := hi.1.isClosedSubgroup
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  constructor
  · intro hx
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp (hle T hx)
    exact ⟨y, center_comap_le_of_mono i T hx, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact hcomap T hy

/-- Milne 17.45: the centre of a smooth connected affine group over a field is the centre of
any geometric Borel subgroup. -/
theorem borelCenterEquality : BorelCenterEqualityStatement.{u} :=
  borelCenterEquality_of_borelCentralizerCenter_of_torusCentralizerBorelContainment
    (borelCentralizerCenter_of_homomorphismRigidity borelHomomorphismRigidity)
    torusCentralizerBorelContainment

end Langlands.GroupScheme
