import Langlands.GroupScheme.Rational.RootSubgroup
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-! # Relative-root kernel, realization, uniqueness and vector quotient targets -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

section Quotients

variable {B : Scheme.{u}} {H Q : GroupScheme B}

/-- A represented fppf sheaf quotient: the map is an fppf cover and its actual
scheme kernel has exactly the specified subgroup functor on every test. This
does not require surjectivity on the point group of each original test. -/
def IsFppfQuotient (N : SubgroupFunctor H) (q : H ⟶ Q) : Prop :=
  Flat q.hom.hom.left ∧ Surjective q.hom.hom.left ∧
    LocallyOfFinitePresentation q.hom.hom.left ∧
      SubgroupFunctor.range (kernelι q) = N

/-- The actual group scheme is a vector group of dimension `n`: its points on
every scheme are naturally the additive group of `n` global functions. -/
def IsVectorGroupOfDimension (H : GroupScheme B) (n : ℕ) : Prop :=
  ∃ e : ∀ T : Over B, (T ⟶ H.X) ≃* Multiplicative (Fin n → Γ(T.left, ⊤)),
    ∀ (T V : Over B) (b : V ⟶ T) (x : T ⟶ H.X),
      (e V (b ≫ x)).toAdd = fun j => b.left.appTop ((e T x).toAdd j)

/-- A finite-dimensional vector group, without a chosen linear coordinate system. -/
def IsVectorGroup (H : GroupScheme B) : Prop :=
  ∃ n : ℕ, IsVectorGroupOfDimension H n

/-- A finite normal series with represented fppf quotients isomorphic to Ga.
The base case is the trivial group on all tests. -/
def HasSplitSeries : ℕ → GroupScheme B → Prop
  | 0, H => SubgroupFunctor.range (𝟙 H) = ⊥
  | n + 1, H => ∃ (K V : GroupScheme B) (j : K ⟶ H) (q : H ⟶ V),
      IsClosedSubgroup j ∧ Smooth K.X.hom ∧ ConnectedSpace K.X.left ∧
        (SubgroupFunctor.range j).IsNormal ∧
        IsFppfQuotient (SubgroupFunctor.range j) q ∧
        IsVectorGroupOfDimension V 1 ∧ HasSplitSeries n K

/-- Split unipotence is witnessed by a finite Ga-series over the ground field. -/
def IsSplitUnipotent (H : GroupScheme B) : Prop :=
  ∃ n : ℕ, HasSplitSeries n H

end Quotients

section Lie

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

/-- The tangent image of an all-test subgroup equals a given submodule when
membership of each actual dual-number identity-kernel point is exactly
membership of its tangent vector in that submodule. -/
def HasLieImage (F : SubgroupFunctor G)
    (W : Submodule k (Additive (lieKernel G k))) : Prop :=
  ∀ X : Additive (lieKernel G k),
    X.toMul.val ∈ F.carrier
      ((algSpec (CommRingCat.of k)).obj
        (op (CommAlgCat.of (CommRingCat.of k) (DualNumber k)))) ↔ X ∈ W

/-- All positive integral multiples, with no reduced-root restriction. -/
def positiveWeightSpan (i : S.toGrp ⟶ G) (a : characterLattice S) :
    Submodule k (Additive (lieKernel G k)) :=
  ⨆ n : {n : ℕ // 0 < n}, weightSpace i (n.val • a)

/-- All integral multiples, including the zero weight, for the kernel centralizer. -/
def integralWeightSpan (i : S.toGrp ⟶ G) (a : characterLattice S) :
    Submodule k (Additive (lieKernel G k)) :=
  ⨆ n : ℤ, weightSpace i (n • a)

end Lie

/-- A nonzero character of a split torus is an fpqc quotient onto Gm. The
character is not required to be primitive and its kernel need not be smooth. -/
def CharacterFpqcStatement : Prop :=
  ∀ (k : Type u) [Field k] (S : CommGroupScheme (Spec (CommRingCat.of k))),
    IsSplitTorus S.toGrp → ∀ a : characterLattice S, a ≠ 0 →
      QuasiCompact (CommGroupScheme.groupHom a).hom.hom.left ∧
      Flat (CommGroupScheme.groupHom a).hom.hom.left ∧
      Surjective (CommGroupScheme.groupHom a).hom.hom.left

/-- Smoothness and the exact Lie image of the all-test kernel centralizer.
This is the multiplicative-type centralizer specialization of CGP A.8.10;
it does not require the kernel to be smooth. -/
def KernelCentralizerStructureStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (_hG : Smooth G.X.hom) (hAff : IsAffineHom G.X.hom)
    (S : CommGroupScheme (Spec (CommRingCat.of k))),
    IsSplitTorus S.toGrp → ∀ (i : S.toGrp ⟶ G) (a : characterLattice S), a ≠ 0 →
      letI := hAff
      ∃ (C : GroupScheme (Spec (CommRingCat.of k))) (j : C ⟶ G),
        (kernelCentralizer i a).IsRepresentedBy j ∧ IsClosedSubgroup j ∧
          Smooth C.X.hom ∧ HasLieImage (kernelCentralizer i a) (integralWeightSpan i a)

/-- The intrinsic root functor agrees, on every test, with the image of the
identity-limit subgroup for the actually descended quotient action. -/
def QuotientActionComparisonStatement : Prop :=
  ∀ (B : Scheme.{u}) (S : CommGroupScheme B) (G C : GroupScheme B)
    (i : S.toGrp ⟶ G) (a : characterLattice S) (j : C ⟶ G)
    (hj : (kernelCentralizer i a).IsRepresentedBy j),
    IsClosedSubgroup j →
    ∀ [QuasiCompact (CommGroupScheme.groupHom a).hom.hom.left]
      [Flat (CommGroupScheme.groupHom a).hom.hom.left]
      [Surjective (CommGroupScheme.groupHom a).hom.hom.left],
      subgroup i a = ((quotientAction i a j hj).unipotent).map j

/-- Actual relative root functors have smooth connected closed, split-unipotent
representatives and exactly all positive integral root weight spaces. -/
def RootSubgroupRealizationStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsConnectedReductive G) (S : CommGroupScheme (Spec (CommRingCat.of k)))
    (i : S.toGrp ⟶ G), IsMaximalSplitTorus i →
    letI := hG.isAffineHom
    ∀ a : characterLattice S, a ∈ relativeRoots i →
      ∃ (U : GroupScheme (Spec (CommRingCat.of k))) (j : U ⟶ G),
        (subgroup i a).IsRepresentedBy j ∧ IsClosedSubgroup j ∧
        Smooth U.X.hom ∧ ConnectedSpace U.X.left ∧ IsUnipotent U ∧
        IsSplitUnipotent U ∧ (AutomorphicAction.conjugation i).IsStable (subgroup i a) ∧
        HasLieImage (subgroup i a) (positiveWeightSpan i a)

/-- Among smooth connected closed subgroups stable under S, the full positive
integral weight image determines the relative root subgroup on every test. -/
def RootSubgroupUniquenessStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsConnectedReductive G) (S : CommGroupScheme (Spec (CommRingCat.of k)))
    (i : S.toGrp ⟶ G), IsMaximalSplitTorus i →
    letI := hG.isAffineHom
    ∀ a : characterLattice S, a ∈ relativeRoots i →
    ∀ (H : GroupScheme (Spec (CommRingCat.of k))) (j : H ⟶ G),
      IsClosedSubgroup j → Smooth H.X.hom → ConnectedSpace H.X.left →
      (AutomorphicAction.conjugation i).IsStable (SubgroupFunctor.range j) →
      HasLieImage (SubgroupFunctor.range j) (positiveWeightSpan i a) →
      SubgroupFunctor.range j = subgroup i a

/-- The general-field two-step root-group structure. The quotient is represented
as an fppf sheaf quotient, rather than a quotient of each test's point group. -/
def RootSubgroupVectorStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsConnectedReductive G) (S : CommGroupScheme (Spec (CommRingCat.of k)))
    (i : S.toGrp ⟶ G), IsMaximalSplitTorus i →
    letI := hG.isAffineHom
    ∀ a : characterLattice S, a ∈ relativeRoots i →
      ((2 • a ∉ relativeRoots i) →
        ∀ (U : GroupScheme (Spec (CommRingCat.of k))) (j : U ⟶ G),
          (subgroup i a).IsRepresentedBy j → IsVectorGroup U) ∧
      ((2 • a ∈ relativeRoots i) →
        subgroup i (2 • a) ≤ subgroup i a ∧
        (∀ (T : Over (Spec (CommRingCat.of k))) (x y : T ⟶ G.X),
          x ∈ (subgroup i (2 • a)).carrier T → y ∈ (subgroup i a).carrier T →
            Commute x y) ∧
        ∀ (U : GroupScheme (Spec (CommRingCat.of k))) (j : U ⟶ G),
          (subgroup i a).IsRepresentedBy j →
          ∃ (V : GroupScheme (Spec (CommRingCat.of k))) (q : U ⟶ V),
            IsFppfQuotient ((subgroup i (2 • a)).comap j) q ∧ IsVectorGroup V)

/-- The combined kernel/action and relative-root structural publication target. -/
def RootSubgroupStructureStatement : Prop :=
  CharacterFpqcStatement.{u} ∧ KernelCentralizerStructureStatement.{u} ∧
    QuotientActionComparisonStatement.{u} ∧ RootSubgroupRealizationStatement.{u} ∧
    RootSubgroupUniquenessStatement.{u} ∧ RootSubgroupVectorStatement.{u}

end Langlands.GroupScheme.RelativeRoot
