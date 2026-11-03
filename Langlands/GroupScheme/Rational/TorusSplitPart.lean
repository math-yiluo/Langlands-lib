import Langlands.GroupScheme.Rational.SplitComponentProof

/-! # The largest split subtorus of a commutative affine group -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section Centrality

variable {S : Scheme.{u}} {G : GroupScheme S} {H : CommGroupScheme S}

/-- A homomorphism into a commutative group scheme is central on all test schemes. -/
theorem isCentral_to_commGroupScheme (f : G ⟶ H.toGrp) : IsCentral f := by
  intro U x U' a y
  exact Commute.all _ _

end Centrality

section Cancellation

variable {S : Scheme.{u}} {G H K : GroupScheme S}

private theorem cancel_closed_subgroup {i : H ⟶ G} (hi : IsClosedSubgroup i)
    {f g : K ⟶ H} (h : f ≫ i = g ≫ i) : f = g := by
  have : IsClosedImmersion i.hom.hom.left := hi
  apply Grp.hom_ext
  apply Over.OverMorphism.ext
  exact (cancel_mono i.hom.hom.left).mp
    (congrArg (fun q : K ⟶ G => q.hom.hom.left) h)

end Cancellation

section SplitPart

variable {k : Type u} [Field k]
  {H A : CommGroupScheme (Spec (CommRingCat.of k))}

/-- A largest split subtorus of a commutative group scheme: every homomorphism from a split
torus factors uniquely through its closed embedding. -/
def IsLargestSplitSubtorus (i : A.toGrp ⟶ H.toGrp) : Prop :=
  IsSplitSubtorus i ∧
    ∀ (B : CommGroupScheme (Spec (CommRingCat.of k))) (f : B.toGrp ⟶ H.toGrp),
      IsSplitTorus B.toGrp → ∃! g : B.toGrp ⟶ A.toGrp, g ≫ i = f

/-- A largest split subtorus is maximal split in the containing commutative group. -/
theorem IsLargestSplitSubtorus.isMaximalSplitTorus {i : A.toGrp ⟶ H.toGrp}
    (hi : IsLargestSplitSubtorus i) : IsMaximalSplitTorus i := by
  refine ⟨hi.1, ?_⟩
  intro B j hj f hf
  obtain ⟨g, hg, _⟩ := hi.2 B j hj.1
  refine ⟨⟨g, ?_, ?_⟩⟩
  · apply cancel_closed_subgroup hi.1.2
    rw [Category.assoc, hg, hf, Category.id_comp]
  · apply cancel_closed_subgroup hj.2
    rw [Category.assoc, hf, hg, Category.id_comp]

/-- An affine commutative group locally of finite type over a field has a largest split
subtorus, universal for all homomorphisms from split tori. -/
theorem exists_largestSplitSubtorus
    (H : CommGroupScheme (Spec (CommRingCat.of k)))
    [IsAffine H.X.left] [LocallyOfFiniteType H.X.hom] :
    ∃ (A : CommGroupScheme (Spec (CommRingCat.of k))) (i : A.toGrp ⟶ H.toGrp),
      IsLargestSplitSubtorus i := by
  obtain ⟨A, i, hi, hu⟩ :=
    exists_largestCentralSplitTorus H.toGrp (finiteType_coordinateAlgebra H.toGrp)
  refine ⟨A, i, hi.1, ?_⟩
  intro B f hf
  obtain ⟨g, hg⟩ := hu B f hf (isCentral_to_commGroupScheme f)
  refine ⟨g, hg, fun g' hg' => ?_⟩
  exact cancel_closed_subgroup hi.1.2 (hg'.trans hg.symm)

/-- Every maximal split torus of an affine commutative group locally of finite type is its
largest split subtorus. In particular, its universal property includes noninjective homomorphisms
from split tori. -/
theorem IsMaximalSplitTorus.isLargestSplitSubtorus
    [IsAffine H.X.left] [LocallyOfFiniteType H.X.hom]
    {i : A.toGrp ⟶ H.toGrp} (hi : IsMaximalSplitTorus i) :
    IsLargestSplitSubtorus i := by
  obtain ⟨B, j, hj⟩ := exists_largestSplitSubtorus H
  obtain ⟨f, hf, _⟩ := hj.2 A i hi.1.1
  have : IsIso f := hi.2 B j hj.1 f hf
  refine ⟨hi.1, ?_⟩
  intro C q hC
  obtain ⟨g, hg, _⟩ := hj.2 C q hC
  have hfac : (g ≫ inv f) ≫ i = q := by
    rw [← hf]
    simpa only [Category.assoc, IsIso.inv_hom_id_assoc] using hg
  exact ⟨g ≫ inv f, hfac,
    fun g' hg' => cancel_closed_subgroup hi.1.2 (hg'.trans hfac.symm)⟩

/-- Largest split subtori are isomorphic over the containing commutative group. -/
theorem IsLargestSplitSubtorus.unique
    {B : CommGroupScheme (Spec (CommRingCat.of k))}
    {i : A.toGrp ⟶ H.toGrp} {j : B.toGrp ⟶ H.toGrp}
    (hi : IsLargestSplitSubtorus i) (hj : IsLargestSplitSubtorus j) :
    ∃ e : A.toGrp ≅ B.toGrp, e.hom ≫ j = i := by
  obtain ⟨f, hf, _⟩ := hj.2 A i hi.1.1
  have : IsIso f := hi.isMaximalSplitTorus.2 B j hj.1 f hf
  exact ⟨asIso f, hf⟩

/-- A closed commutative subgroup of an affine group locally of finite type has a largest
split subtorus. Thus this construction applies to a closed maximal torus of a reductive group
without requiring a separate descent theorem for affineness of arbitrary tori. -/
theorem exists_largestSplitSubtorus_of_isClosedSubgroup
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    (H : CommGroupScheme (Spec (CommRingCat.of k))) (j : H.toGrp ⟶ G)
    (hj : IsClosedSubgroup j) :
    ∃ (A : CommGroupScheme (Spec (CommRingCat.of k))) (i : A.toGrp ⟶ H.toGrp),
      IsLargestSplitSubtorus i := by
  have : IsClosedImmersion j.hom.hom.left := hj
  have : IsAffine H.X.left := isAffine_of_isAffineHom j.hom.hom.left
  have : LocallyOfFiniteType H.X.hom := by
    rw [← Over.w j.hom.hom]
    infer_instance
  exact exists_largestSplitSubtorus H

end SplitPart

end Langlands.GroupScheme
