import Langlands.GroupScheme.Rational.WeightSemigroup
import Langlands.GroupScheme.Rational.RootSubgroupStructureStatement

/-! # Source semigroup realization, cyclic filtration and dynamic comparisons -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

section Helpers

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}

/-- Sums of one element from each semigroup, retaining positive generation. -/
def semigroupSum (A A' : AddSubsemigroup (characterLattice S)) :
    AddSubsemigroup (characterLattice S) where
  carrier := {χ | ∃ α ∈ A, ∃ β ∈ A', α + β = χ}
  add_mem' := by
    rintro χ ψ ⟨α, hα, β, hβ, rfl⟩ ⟨γ, hγ, δ, hδ, rfl⟩
    exact ⟨α + γ, A.add_mem hα hγ, β + δ, A'.add_mem hβ hδ,
      add_add_add_comm α γ β δ⟩

/-- Natural vector coordinates, without specifying a torus action. -/
def IsNaturalVectorCoordinates {V : GroupScheme (Spec (CommRingCat.of k))} {n : ℕ}
    (e : ∀ T : Over (Spec (CommRingCat.of k)),
      (T ⟶ V.X) ≃* Multiplicative (Fin n → Γ(T.left, ⊤))) : Prop :=
  ∀ (T W : Over (Spec (CommRingCat.of k))) (f : W ⟶ T) (v : T ⟶ V.X),
    (e W (f ≫ v)).toAdd = fun j => f.left.appTop ((e T v).toAdd j)

/-- The torus acts on these vector coordinates by the single actual character χ. -/
def IsWeightVectorCoordinates {V : GroupScheme (Spec (CommRingCat.of k))}
    (b : AutomorphicAction S.toGrp V) (χ : characterLattice S) {n : ℕ}
    (e : ∀ T : Over (Spec (CommRingCat.of k)),
      (T ⟶ V.X) ≃* Multiplicative (Fin n → Γ(T.left, ⊤))) : Prop :=
  IsNaturalVectorCoordinates e ∧
    ∀ (T : Over (Spec (CommRingCat.of k))) (s : T ⟶ S.X) (v : T ⟶ V.X),
      (e T (b.act s v)).toAdd =
        (Gm.pointsEquiv _ T (s ≫ (CommGroupScheme.groupHom χ).hom.hom) :
          Γ(T.left, ⊤)) • (e T v).toAdd

/-- Existence of vector coordinates of weight χ and independence of their scalar
multiplication from every choice of such coordinates. Bases need not be unique. -/
def HasUniqueWeightVectorStructure {V : GroupScheme (Spec (CommRingCat.of k))}
    (b : AutomorphicAction S.toGrp V) (χ : characterLattice S) : Prop :=
  (∃ (n : ℕ) (e : ∀ T : Over (Spec (CommRingCat.of k)),
      (T ⟶ V.X) ≃* Multiplicative (Fin n → Γ(T.left, ⊤))),
      IsWeightVectorCoordinates b χ e) ∧
  ∀ (n m : ℕ)
    (e : ∀ T : Over (Spec (CommRingCat.of k)),
      (T ⟶ V.X) ≃* Multiplicative (Fin n → Γ(T.left, ⊤)))
    (e' : ∀ T : Over (Spec (CommRingCat.of k)),
      (T ⟶ V.X) ≃* Multiplicative (Fin m → Γ(T.left, ⊤))),
    IsWeightVectorCoordinates b χ e → IsWeightVectorCoordinates b χ e' →
    ∀ (T : Over (Spec (CommRingCat.of k))) (c : Γ(T.left, ⊤)) (v : T ⟶ V.X),
      (e T).symm (Multiplicative.ofAdd (c • (e T v).toAdd)) =
        (e' T).symm (Multiplicative.ofAdd (c • (e' T v).toAdd))

/-- Nonnegative character halfspace for an arbitrary cocharacter of S. -/
def nonnegativeSemigroup (ν : cocharacterLattice S) :
    AddSubsemigroup (characterLattice S) where
  carrier := {χ | 0 ≤ latticePairing S χ ν}
  add_mem' := by
    intro χ ψ hχ hψ
    change 0 ≤ latticePairing S (χ + ψ) ν
    rw [map_add, LinearMap.add_apply]
    exact add_nonneg hχ hψ

/-- Zero character hyperplane for an arbitrary cocharacter of S. -/
def zeroSemigroup (ν : cocharacterLattice S) :
    AddSubsemigroup (characterLattice S) where
  carrier := {χ | latticePairing S χ ν = 0}
  add_mem' := by
    intro χ ψ hχ hψ
    change latticePairing S (χ + ψ) ν = 0
    rw [map_add, LinearMap.add_apply, hχ, hψ, add_zero]

/-- Strictly positive character halfspace; zero is excluded. -/
def positiveSemigroup (ν : cocharacterLattice S) :
    AddSubsemigroup (characterLattice S) where
  carrier := {χ | 0 < latticePairing S χ ν}
  add_mem' := by
    intro χ ψ hχ hψ
    change 0 < latticePairing S (χ + ψ) ν
    rw [map_add, LinearMap.add_apply]
    exact add_pos hχ hψ

end Helpers

/-- Intrinsic eigenvector spans are precisely the eigenspaces, and conjugation
recovers the Library's original actual adjoint weight spaces. -/
def ActionWeightComparisonStatement : Prop :=
  (∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (hAff : IsAffineHom G.X.hom) (S : CommGroupScheme (Spec (CommRingCat.of k)))
    (b : AutomorphicAction S.toGrp G) (χ : characterLattice S),
      letI := hAff
      (actionWeightSpace b χ : Set (Additive (lieKernel G k))) = actionEigenvectors b χ) ∧
  (∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (hAff : IsAffineHom G.X.hom) (S : CommGroupScheme (Spec (CommRingCat.of k)))
    (i : S.toGrp ⟶ G) (χ : characterLattice S),
      letI := hAff
      actionWeightSpace (AutomorphicAction.conjugation i) χ = weightSpace i χ)

/-- CGP 3.3.6: the constructed semigroup functor has a unique smooth connected
invariant closed realization with the exact Lie image, has the full maximality
property, and is split unipotent when zero is excluded. -/
def SemigroupRealizationStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (_hG : Smooth G.X.hom) (hAff : IsAffineHom G.X.hom)
    (S : CommGroupScheme (Spec (CommRingCat.of k))),
    IsSplitTorus S.toGrp → ∀ b : AutomorphicAction S.toGrp G,
    letI := hAff
    ∀ A : AddSubsemigroup (characterLattice S),
      IsSmoothConnectedClosed (semigroupSubgroup b A) ∧
      b.IsStable (semigroupSubgroup b A) ∧
      HasLieImage (semigroupSubgroup b A) (semigroupWeightSpan b A) ∧
      (∀ (H : GroupScheme (Spec (CommRingCat.of k))) (j : H ⟶ G),
        (semigroupSubgroup b A).IsRepresentedBy j →
        0 ∉ A → IsUnipotent H ∧ IsSplitUnipotent H) ∧
      (∀ F : SubgroupFunctor G, IsSmoothConnectedClosed F → b.IsStable F →
        (actionWeightSupport b F ⊆ A ↔ F ≤ semigroupSubgroup b A)) ∧
      (∀ F : SubgroupFunctor G, IsSmoothConnectedClosed F → b.IsStable F →
        HasLieImage F (semigroupWeightSpan b A) → F = semigroupSubgroup b A)

/-- The source commutator weight bound, formulated on all test schemes. -/
def SemigroupCommutatorStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (_hG : Smooth G.X.hom) (hAff : IsAffineHom G.X.hom)
    (S : CommGroupScheme (Spec (CommRingCat.of k))),
    IsSplitTorus S.toGrp → ∀ b : AutomorphicAction S.toGrp G,
    letI := hAff
    ∀ (A A' : AddSubsemigroup (characterLattice S))
      (T : Over (Spec (CommRingCat.of k))) (x y : T ⟶ G.X),
      x ∈ (semigroupSubgroup b A).carrier T →
      y ∈ (semigroupSubgroup b A').carrier T →
      x * y * x⁻¹ * y⁻¹ ∈ (semigroupSubgroup b (semigroupSum A A')).carrier T

/-- CGP 3.3.8: each positive cyclic tail is normal in the first term; its next
quotient is represented, with the unique equivariant vector structure of weight j*a. -/
def CyclicWeightFiltrationStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (_hG : Smooth G.X.hom) (hAff : IsAffineHom G.X.hom)
    (S : CommGroupScheme (Spec (CommRingCat.of k))),
    IsSplitTorus S.toGrp → ∀ b : AutomorphicAction S.toGrp G,
    letI := hAff
    ∀ a : characterLattice S, a ≠ 0 → ∀ r : ℕ, 0 < r →
      (weightFiltration b a r).IsNormalizedBy (weightFiltration b a 1) ∧
      ∀ (H : GroupScheme (Spec (CommRingCat.of k))) (j : H ⟶ G),
        (weightFiltration b a r).IsRepresentedBy j →
        ∃ (V : GroupScheme (Spec (CommRingCat.of k))) (q : H ⟶ V)
          (c : AutomorphicAction S.toGrp V) (d : AutomorphicAction S.toGrp H),
          IsFppfQuotient ((weightFiltration b a (r + 1)).comap j) q ∧
          HasUniqueWeightVectorStructure c (r • a) ∧
          (∀ (T : Over (Spec (CommRingCat.of k))) (s : T ⟶ S.X) (h : T ⟶ H.X),
            d.act s h ≫ j.hom.hom = b.act s (h ≫ j.hom.hom)) ∧
          (∀ (T : Over (Spec (CommRingCat.of k))) (s : T ⟶ S.X) (h : T ⟶ H.X),
            c.act s (h ≫ q.hom.hom) = d.act s h ≫ q.hom.hom)

/-- The first cyclic-semigroup term is the actual character-orbit root functor. -/
def CyclicRootFunctorComparisonStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (_hG : Smooth G.X.hom) (hAff : IsAffineHom G.X.hom)
    (S : CommGroupScheme (Spec (CommRingCat.of k))),
    IsSplitTorus S.toGrp → ∀ (i : S.toGrp ⟶ G) (a : characterLattice S), a ≠ 0 →
    letI := hAff
    weightFiltration (AutomorphicAction.conjugation i) a 1 = subgroup i a

/-- The three Dynamic functors are the actual semigroup subgroups for the
nonnegative, zero and positive pairing regions, for every cocharacter in S. -/
def DynamicSemigroupComparisonStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (_hG : Smooth G.X.hom) (hAff : IsAffineHom G.X.hom)
    (_hConn : ConnectedSpace G.X.left)
    (S : CommGroupScheme (Spec (CommRingCat.of k))),
    IsSplitTorus S.toGrp → ∀ (i : S.toGrp ⟶ G) (ν : cocharacterLattice S),
    letI := hAff
    Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i) =
      semigroupSubgroup (AutomorphicAction.conjugation i) (nonnegativeSemigroup ν) ∧
    Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ i) =
      semigroupSubgroup (AutomorphicAction.conjugation i) (zeroSemigroup ν) ∧
    Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ i) =
      semigroupSubgroup (AutomorphicAction.conjugation i) (positiveSemigroup ν)

/-- Source semigroup, cyclic filtration and actual dynamic-comparison targets. -/
def WeightSemigroupStatement : Prop :=
  ActionWeightComparisonStatement.{u} ∧ SemigroupRealizationStatement.{u} ∧
    SemigroupCommutatorStatement.{u} ∧ CyclicWeightFiltrationStatement.{u} ∧
    CyclicRootFunctorComparisonStatement.{u} ∧ DynamicSemigroupComparisonStatement.{u}

end Langlands.GroupScheme.RelativeRoot
