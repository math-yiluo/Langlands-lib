import Langlands.GroupScheme.NormalSubgroupQuotientStatement
import Langlands.GroupScheme.Rational.FppfQuotientSmooth
import Langlands.GroupScheme.HomogeneousQuotientComparison
import Langlands.AlgebraicGeometry.ProperConnectedAffineConstancy
import Langlands.AlgebraicGeometry.GeometricallyReducedOfAlgClosedProof
import Langlands.AlgebraicGeometry.SmoothReducedProof

/-! # Normal subgroups with proper homogeneous quotient -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
    {G N R : GroupScheme (Spec (CommRingCat.of k))}
    {Q : Over (Spec (CommRingCat.of k))}

/-- The actual map from a homogeneous scheme quotient to a represented
group quotient with the same kernel. -/
def normalQuotientComparisonMap
    (i : N ⟶ G) [Mono i.hom.hom]
    (r : G ⟶ R) (hr : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) r)
    (q : G.X ⟶ Q) [Flat q.left] [Surjective q.left] [QuasiCompact q.left]
    (hq : ∀ (T : Over (Spec (CommRingCat.of k))) (g h : T ⟶ G.X),
      g ≫ q = h ≫ q → g⁻¹ * h ∈ (SubgroupFunctor.range i).carrier T) :
    Q ⟶ R.X :=
  HomogeneousQuotientComparison.desc q r.hom.hom
    (fun T g h he => (hr.fibers_iff ⟨inferInstance, rfl⟩ T g h).mpr (hq T g h he))

/-- Pulling back the comparison map recovers the given group quotient map. -/
theorem comp_normalQuotientComparisonMap
    (i : N ⟶ G) [Mono i.hom.hom]
    (r : G ⟶ R) (hr : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) r)
    (q : G.X ⟶ Q) [Flat q.left] [Surjective q.left] [QuasiCompact q.left]
    (hq : ∀ (T : Over (Spec (CommRingCat.of k))) (g h : T ⟶ G.X),
      g ≫ q = h ≫ q → g⁻¹ * h ∈ (SubgroupFunctor.range i).carrier T) :
    q ≫ normalQuotientComparisonMap i r hr q hq = r.hom.hom :=
  HomogeneousQuotientComparison.fac_desc q r.hom.hom _

/-- If a connected reduced group has a proper homogeneous quotient by the
kernel of an affine group quotient, that group quotient kills every point
on every scheme test. -/
theorem comp_eq_one_of_proper_homogeneousQuotient
    [IsAlgClosed k] [ConnectedSpace G.X.left] [IsReduced G.X.left]
    [IsAffine R.X.left]
    (i : N ⟶ G) [Mono i.hom.hom]
    (r : G ⟶ R) (hr : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) r)
    (q : G.X ⟶ Q) [Flat q.left] [Surjective q.left] [QuasiCompact q.left]
    [IsProper Q.hom]
    (hq : ∀ (T : Over (Spec (CommRingCat.of k))) (g h : T ⟶ G.X),
      g ≫ q = h ≫ q → g⁻¹ * h ∈ (SubgroupFunctor.range i).carrier T)
    (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ G.X) :
    g ≫ r.hom.hom = 1 := by
  have : ConnectedSpace Q.left := q.left.surjective.connectedSpace q.left.continuous
  have : IsReduced Q.left :=
    Langlands.AlgebraicGeometry.GeometricallyReducedOfAlgClosedProof.isReduced_of_flat_of_surjective
      q.left
  let ρ := normalQuotientComparisonMap i r hr q hq
  have hρ : q ≫ ρ = r.hom.hom := comp_normalQuotientComparisonMap i r hr q hq
  let s : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Q :=
    (1 : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) ≫ q
  have hsρ : s ≫ ρ = 1 := by
    change (1 : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) ≫ q ≫ ρ = 1
    rw [hρ, MonObj.one_comp]
  have hc : ρ = toUnit Q ≫ s ≫ ρ := by
    apply Over.OverMorphism.ext
    exact Langlands.AlgebraicGeometry.affineMap_eq_constant_of_proper_connected_reduced
      Q.hom s.left (Over.w s) ρ.left
  calc
    g ≫ r.hom.hom = g ≫ q ≫ ρ := by rw [hρ]
    _ = g ≫ q ≫ (toUnit Q ≫ s ≫ ρ) := congrArg (fun f => g ≫ q ≫ f) hc
    _ = 1 := by rw [comp_toUnit_assoc, comp_toUnit_assoc, hsρ, MonObj.comp_one]

/-- A supplied affine represented group quotient, together with a proper
homogeneous quotient with the same kernel, makes the kernel all of `G`. -/
theorem range_eq_top_of_proper_homogeneousQuotient
    [IsAlgClosed k] [ConnectedSpace G.X.left] [IsReduced G.X.left]
    [IsAffine R.X.left]
    (i : N ⟶ G) [Mono i.hom.hom]
    (r : G ⟶ R) (hr : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) r)
    (q : G.X ⟶ Q) [Flat q.left] [Surjective q.left] [QuasiCompact q.left]
    [IsProper Q.hom]
    (hq : ∀ (T : Over (Spec (CommRingCat.of k))) (g h : T ⟶ G.X),
      g ≫ q = h ≫ q → g⁻¹ * h ∈ (SubgroupFunctor.range i).carrier T) :
    SubgroupFunctor.range i = ⊤ := by
  apply SubgroupFunctor.ext
  intro T
  apply Subgroup.ext
  intro g
  constructor
  · intro _
    trivial
  · intro _
    rw [← hr.2.2.2, mem_range_kernelι_iff]
    exact comp_eq_one_of_proper_homogeneousQuotient i r hr q hq T g

/-- Conditional on existence of affine normal-subgroup quotients, every
normal closed subgroup with a proper homogeneous quotient is the whole
smooth connected affine group. -/
theorem isIso_of_normal_of_proper_homogeneousQuotient
    [IsAlgClosed k] [Smooth G.X.hom] [IsAffineHom G.X.hom]
    [ConnectedSpace G.X.left]
    (hquot : NormalSubgroupQuotientStatement.{u})
    (i : N ⟶ G) (hi : IsClosedSubgroup i)
    (hnormal : (SubgroupFunctor.range i).IsNormal)
    (q : G.X ⟶ Q) [Flat q.left] [Surjective q.left] [QuasiCompact q.left]
    [IsProper Q.hom]
    (hq : ∀ (T : Over (Spec (CommRingCat.of k))) (g h : T ⟶ G.X),
      g ≫ q = h ≫ q → g⁻¹ * h ∈ (SubgroupFunctor.range i).carrier T) :
    IsIso i := by
  have : IsClosedImmersion i.hom.hom.left := hi
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  obtain ⟨R, r, hRs, hRa, hr⟩ := hquot k G N i hi hnormal
  let : IsAffineHom R.X.hom := hRa
  have : IsAffine R.X.left := isAffine_of_isAffineHom R.X.hom
  have : IsReduced G.X.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field k _ G.X.hom
  have hrange := range_eq_top_of_proper_homogeneousQuotient i r hr q hq
  have hirep : (⊤ : SubgroupFunctor G).IsRepresentedBy i := ⟨inferInstance, hrange⟩
  have hidrep : (⊤ : SubgroupFunctor G).IsRepresentedBy (𝟙 G) := by
    refine ⟨inferInstance, ?_⟩
    apply SubgroupFunctor.ext
    intro T
    apply Subgroup.ext
    intro g
    constructor
    · intro _
      trivial
    · intro _
      exact ⟨g, Category.comp_id g⟩
  let e : N ≅ G := hirep.isoOfIsRepresentedBy hidrep
  have he : e.hom = i := by
    simpa using hirep.isoOfIsRepresentedBy_hom_comp hidrep
  rw [← he]
  infer_instance

end Langlands.GroupScheme
