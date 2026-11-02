import Langlands.GroupScheme.Rational.RelativeRoots
import Langlands.GroupScheme.RepresentedAction
import Langlands.GroupScheme.Products
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.GroupTheory.Solvable

/-! # Intrinsic action weights and all-test semigroup subgroup functors -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

section ActionWeights

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

/-- Eigenvectors for the actual torus action on dual-number identity kernels,
tested after every coefficient extension and against every torus point. -/
def actionEigenvectors (b : AutomorphicAction S.toGrp G) (χ : characterLattice S) :
    Set (Additive (lieKernel G k)) :=
  {X | ∀ (A : Type u) [CommRing A] [Algebra k A] (s : Lie.AffinePoints S.toGrp A),
    b.act (Lie.constant S.toGrp s)
      (lieKernelMap G (Algebra.ofId k A) X.toMul).val =
    (lieKernelScale G (Lie.characterValue χ s : A)
      (lieKernelMap G (Algebra.ofId k A) X.toMul)).val}

/-- The linear span of intrinsic eigenvectors for the specified action weight. -/
def actionWeightSpace (b : AutomorphicAction S.toGrp G) (χ : characterLattice S) :
    Submodule k (Additive (lieKernel G k)) :=
  Submodule.span k (actionEigenvectors b χ)

/-- Weights in the tangent image of an all-test subgroup. Zero is included
when it occurs, as in CGP's Ψ(G,S). -/
def actionWeightSupport (b : AutomorphicAction S.toGrp G) (F : SubgroupFunctor G) :
    Set (characterLattice S) :=
  {χ | ∃ X : Additive (lieKernel G k), X ≠ 0 ∧ X ∈ actionWeightSpace b χ ∧
    X.toMul.val ∈ F.carrier
      ((algSpec (CommRingCat.of k)).obj
        (op (CommAlgCat.of (CommRingCat.of k) (DualNumber k))))}

/-- A smooth connected closed represented subgroup, without a chosen representative. -/
def IsSmoothConnectedClosed (F : SubgroupFunctor G) : Prop :=
  ∃ (H : GroupScheme (Spec (CommRingCat.of k))) (j : H ⟶ G),
    F.IsRepresentedBy j ∧ IsClosedSubgroup j ∧ Smooth H.X.hom ∧ ConnectedSpace H.X.left

/-- The smooth connected invariant subgroups whose intrinsic Lie weights lie in A. -/
def IsSemigroupGenerator (b : AutomorphicAction S.toGrp G)
    (A : AddSubsemigroup (characterLattice S)) (F : SubgroupFunctor G) : Prop :=
  IsSmoothConnectedClosed F ∧ b.IsStable F ∧ actionWeightSupport b F ⊆ A

/-- Generate a subgroup on each test from all admissible smooth connected
invariant subgroups. Existence of a smooth representative is not an input. -/
def semigroupSubgroup (b : AutomorphicAction S.toGrp G)
    (A : AddSubsemigroup (characterLattice S)) : SubgroupFunctor G where
  carrier T := Subgroup.closure {g | ∃ F : SubgroupFunctor G,
    IsSemigroupGenerator b A F ∧ g ∈ F.carrier T}
  comp_mem f g hg := by
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨F, hF, hx⟩ := hx
      exact Subgroup.subset_closure ⟨F, hF, F.comp_mem f hx⟩
    | one =>
      rw [MonObj.comp_one]
      exact Subgroup.one_mem _
    | mul x y _ _ hx hy =>
      rw [MonObj.comp_mul]
      exact Subgroup.mul_mem _ hx hy
    | inv x _ hx =>
      rw [GrpObj.comp_inv]
      exact Subgroup.inv_mem _ hx

/-- Every admissible subgroup lies in the generated functor on all tests. -/
theorem generator_le_semigroupSubgroup (b : AutomorphicAction S.toGrp G)
    (A : AddSubsemigroup (characterLattice S)) (F : SubgroupFunctor G)
    (hF : IsSemigroupGenerator b A F) : F ≤ semigroupSubgroup b A :=
  fun _ _ hx => Subgroup.subset_closure ⟨F, hF, hx⟩

/-- Semigroup inclusions induce actual inclusions of generated subgroup functors. -/
theorem semigroupSubgroup_mono (b : AutomorphicAction S.toGrp G)
    {A A' : AddSubsemigroup (characterLattice S)} (h : A ≤ A') :
    semigroupSubgroup b A ≤ semigroupSubgroup b A' := by
  intro T g hg
  apply Subgroup.closure_mono (fun x hx => ?_) hg
  obtain ⟨F, hF, hx⟩ := hx
  exact ⟨F, ⟨hF.1, hF.2.1, fun χ hχ => h (hF.2.2 hχ)⟩, hx⟩

/-- The source weight span selected by a subsemigroup. -/
def semigroupWeightSpan (b : AutomorphicAction S.toGrp G)
    (A : AddSubsemigroup (characterLattice S)) :
    Submodule k (Additive (lieKernel G k)) :=
  ⨆ χ : A, actionWeightSpace b χ.val

/-- The positive integer tail {n*a | n≥j and n>0}, a semigroup rather than
a monoid. In particular the zero character is not inserted by definition. -/
def cyclicTail (a : characterLattice S) (j : ℕ) :
    AddSubsemigroup (characterLattice S) where
  carrier := {χ | ∃ n : ℕ, j ≤ n ∧ 0 < n ∧ n • a = χ}
  add_mem' := by
    rintro χ ψ ⟨n, hn, hn0, rfl⟩ ⟨m, _, _, rfl⟩
    exact ⟨n + m, by omega, by omega, add_nsmul a n m⟩

/-- The source descending cyclic-semigroup filtration as actual all-test functors. -/
def weightFiltration (b : AutomorphicAction S.toGrp G) (a : characterLattice S)
    (j : ℕ) : SubgroupFunctor G :=
  semigroupSubgroup b (cyclicTail a j)

/-- The filtration is descending independently of any representation theorem. -/
theorem weightFiltration_antitone (b : AutomorphicAction S.toGrp G)
    (a : characterLattice S) : Antitone (weightFiltration b a) := by
  intro j j' hj
  apply semigroupSubgroup_mono
  rintro χ ⟨n, hn, hn0, he⟩
  exact ⟨n, hj.trans hn, hn0, he⟩

end ActionWeights

section Products

variable {B : Scheme.{u}} {G : GroupScheme B} {n : ℕ}

/-- The ordered multiplication morphism from the actual finite product of schemes.
The product in the hom-set uses the group-scheme multiplication in index order. -/
def orderedMultiplication {H : Fin n → GroupScheme B} (j : ∀ r, H r ⟶ G) :
    (∏ᶜ H).X ⟶ G.X :=
  (List.ofFn fun r : Fin n => (Pi.π H r).hom.hom ≫ (j r).hom.hom).prod

/-- Uniform termination of the actual point-group derived series on all tests.
For smooth connected affine groups this is the scheme-theoretic solvability
condition expressed by group identities. -/
def IsSolvableScheme (G : GroupScheme B) : Prop :=
  ∃ d : ℕ, ∀ T : Over B, derivedSeries (T ⟶ G.X) d = ⊥

end Products

end Langlands.GroupScheme.RelativeRoot
