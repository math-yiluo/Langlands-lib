import Langlands.GroupScheme.Chevalley.UnipotentOrbit
import Langlands.GroupScheme.HomogeneousQuotientComparison
import Langlands.AlgebraicGeometry.ProperConnectedAffineConstancy
import Langlands.AlgebraicGeometry.GeometricallyReducedOfAlgClosedProof

/-! # Unipotent subgroups with proper homogeneous quotients -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k] [IsAlgClosed k]
    {G H : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    [ConnectedSpace G.X.left] [IsReduced G.X.left]
    {Q : Over (Spec (CommRingCat.of k))}

/-- A closed unipotent subgroup of a connected reduced affine finite-type group
with a proper fpqc homogeneous quotient has full range on every scheme test. -/
theorem range_eq_top_of_unipotent_of_proper_homogeneousQuotient
    (i : H ⟶ G) (hi : IsClosedSubgroup i) (hH : IsUnipotent H)
    (q : G.X ⟶ Q) [Flat q.left] [Surjective q.left] [QuasiCompact q.left]
    [IsProper Q.hom]
    (hq : ∀ (T : Over (Spec (CommRingCat.of k))) (g h : T ⟶ G.X),
      g ≫ q = h ≫ q → g⁻¹ * h ∈ (SubgroupFunctor.range i).carrier T) :
    SubgroupFunctor.range i = ⊤ := by
  have : ConnectedSpace Q.left := q.left.surjective.connectedSpace q.left.continuous
  have : IsReduced Q.left :=
    Langlands.AlgebraicGeometry.GeometricallyReducedOfAlgClosedProof.isReduced_of_flat_of_surjective
      q.left
  let D := Chevalley.affineVectorOrbit i hi hH
  let V := (VectorGroup.groupScheme (CommRingCat.of k) (D.dimension + 1)).X
  have : IsAffine V.left := by
    change IsAffine (Spec (CommRingCat.of
      (MvPolynomial (Fin (D.dimension + 1)) (CommRingCat.of k))))
    infer_instance
  let f : G.X ⟶ V := VectorOrbit.orbitMap D.representation D.coordinate
  have hf : ∀ (T : Over (Spec (CommRingCat.of k))) (g h : T ⟶ G.X),
      g ≫ q = h ≫ q → g ≫ f = h ≫ f :=
    fun T g h he => (D.fibers T g h).mpr (hq T g h he)
  let r : Q ⟶ V := HomogeneousQuotientComparison.desc q f hf
  have hr : q ≫ r = f := HomogeneousQuotientComparison.fac_desc q f hf
  let s : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Q :=
    (1 : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) ≫ q
  have hc : r = toUnit Q ≫ s ≫ r := by
    apply Over.OverMorphism.ext
    exact Langlands.AlgebraicGeometry.affineMap_eq_constant_of_proper_connected_reduced
      Q.hom s.left (Over.w s) r.left
  have hconst (T : Over (Spec (CommRingCat.of k))) (g h : T ⟶ G.X) :
      g ≫ f = h ≫ f := by
    rw [← hr, hc, comp_toUnit_assoc, comp_toUnit_assoc, comp_toUnit_assoc]
  apply SubgroupFunctor.ext
  intro T
  apply Subgroup.ext
  intro g
  constructor
  · intro _
    trivial
  · intro _
    simpa only [inv_one, one_mul] using (D.fibers T 1 g).mp (hconst T 1 g)

/-- Such a subgroup inclusion is an actual isomorphism, without a normality
assumption or a connectedness or smoothness assumption on the subgroup. -/
theorem isIso_of_unipotent_of_proper_homogeneousQuotient
    (i : H ⟶ G) (hi : IsClosedSubgroup i) (hH : IsUnipotent H)
    (q : G.X ⟶ Q) [Flat q.left] [Surjective q.left] [QuasiCompact q.left]
    [IsProper Q.hom]
    (hq : ∀ (T : Over (Spec (CommRingCat.of k))) (g h : T ⟶ G.X),
      g ≫ q = h ≫ q → g⁻¹ * h ∈ (SubgroupFunctor.range i).carrier T) :
    IsIso i := by
  have : IsClosedImmersion i.hom.hom.left := hi
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  have hirep : (⊤ : SubgroupFunctor G).IsRepresentedBy i :=
    ⟨inferInstance, range_eq_top_of_unipotent_of_proper_homogeneousQuotient i hi hH q hq⟩
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
  let e : H ≅ G := hirep.isoOfIsRepresentedBy hidrep
  have he : e.hom = i := by
    simpa using hirep.isoOfIsRepresentedBy_hom_comp hidrep
  rw [← he]
  infer_instance

/-- Proper homogeneous quotients by unipotent subgroups of connected reduced
affine finite-type groups over algebraically closed fields are trivial. -/
def UnipotentProperHomogeneousQuotientStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k]
    (G H : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    [ConnectedSpace G.X.left] [IsReduced G.X.left]
    (i : H ⟶ G), IsClosedSubgroup i → IsUnipotent H →
      ∀ (Q : Over (Spec (CommRingCat.of k))) (q : G.X ⟶ Q)
        [Flat q.left] [Surjective q.left] [QuasiCompact q.left] [IsProper Q.hom],
        (∀ (T : Over (Spec (CommRingCat.of k))) (g h : T ⟶ G.X),
          g ≫ q = h ≫ q → g⁻¹ * h ∈ (SubgroupFunctor.range i).carrier T) → IsIso i

/-- The affine vector orbit descends to the proper quotient and is constant. -/
theorem unipotentProperHomogeneousQuotient :
    UnipotentProperHomogeneousQuotientStatement.{u} := by
  intro k _ _ G H _ _ _ _ i hi hH Q q _ _ _ _ hq
  exact isIso_of_unipotent_of_proper_homogeneousQuotient i hi hH q hq

end Langlands.GroupScheme
