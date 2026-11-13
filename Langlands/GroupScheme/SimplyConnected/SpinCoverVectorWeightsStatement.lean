import Langlands.GroupScheme.SimplyConnected.SpinCoverFundamentalWeight
import Langlands.GroupScheme.SimplyConnected.Basic
import Langlands.GroupScheme.Reductive.AbsolutelyAlmostSimple
import Langlands.GroupScheme.Quaternionic.CocharacterWeightSpace

/-!
# The vector weights of an aligned type-`D` spin cover

This unproved statement describes, for a spin cover `π : G ⟶ O(q)` whose numbered Tits
index has Cartan matrix `D_n` and whose vertex numbered `0` is the vector vertex, the
weights of the pinning torus over the separable closure on `D^m`: they are `±ε_1, …, ±ε_n`,
each with multiplicity the degree of `D`, the simple roots are `ε_i - ε_{i+1}` and
`ε_{n-1} + ε_n` in the numbering, and every `±ε_i ± ε_j` with `i ≠ j` is a root. The
multiplicities are recorded through the weight spaces of the `K`-rational cocharacters of
the maximal split torus of the index.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Let `G` be a simply connected, absolutely almost simple group over a field `K` with
Tits index data `d` and a numbering `e` of its vertices by `Fin n`, `n ≥ 4`, identifying
the Cartan matrix with `D_n`. Let `D` be a central division algebra of degree `degree`,
`m * degree = 2n`, `σ` an involution of the first kind of orthogonal dimension type, `q` a
nondegenerate `σ`-quadratic form on `D^m`, and `π : G ⟶ O(q)` a spin cover such that the
fundamental weight of the vertex numbered `0` is trivial on `ker π` in the pinning torus.
Then there are characters `ε_0, …, ε_{n-1}` of the pinning torus over `K^s` such that

* the simple root of the vertex numbered `i` is `ε_i - ε_{i+1}` for `i ≤ n - 2`, and that of
  the vertex numbered `n - 1` is `ε_{n-2} + ε_{n-1}`;
* `s ε_i + t ε_j` is a root for all `i ≠ j` and signs `s, t`;
* for every cocharacter `ν` of the maximal split torus `S` of `d` and every integer `c`, the
  number of pairs `(i, s)`, `s = ±1`, with `s ⟨ε_i|_S, ν⟩ = c` is `degree` times the
  `D`-dimension of the weight space of weight `c` of `ν` on `D^m`. Here `ε_i|_S` is the
  restriction of `ε_i` along the base change of `S ⟶ T`, descended to a character of `S`
  as in `absoluteRootRestriction`. -/
def SpinCoverVectorWeightsStatement : Prop :=
  ∀ (K : Type u) [Field K]
    (G : GroupScheme (Spec (CommRingCat.of K))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G)
    (n : ℕ) (e : d.Vertex ≃ Fin n),
    4 ≤ n →
    IsSimplyConnected G → IsAbsolutelyAlmostSimple G →
    (∀ a b, d.cartan a b = CartanMatrix.D n (e a) (e b)) →
    ∀ (D : Type u) [DivisionRing D] [Algebra K D]
      [Algebra.IsCentral K D] [FiniteDimensional K D]
      (degree m : ℕ),
      0 < degree → Module.finrank K D = degree ^ 2 → m * degree = 2 * n →
      ∀ σ : Quaternionic.FirstKindInvolution K D,
        Module.finrank K σ.symmetricSubspace = degree * (degree + 1) / 2 →
        ∀ q : σ.QuadraticForms (Fin m),
          σ.IsNondegenerateQuadratic q →
          ∀ π : G ⟶ σ.isometryGroup q, σ.IsSpinCover q π →
            (∀ v : d.Vertex, (e v).val = 0 → d.FundamentalWeightTrivialOnKernel v π) →
            ∃ ε : Fin n → characterLattice
                ((CommGroupScheme.baseChange
                  (algebraBaseMap K (SeparableClosure K))).obj d.pinning.torus),
              (∀ (a : d.Vertex) (h : (e a).val + 1 < n),
                d.pinning.rootDatum.root a.val = ε (e a) - ε ⟨(e a).val + 1, h⟩) ∧
              (∀ (a : d.Vertex) (h : (e a).val + 1 = n),
                d.pinning.rootDatum.root a.val =
                  ε ⟨n - 2, by omega⟩ + ε ⟨n - 1, by omega⟩) ∧
              (∀ i j : Fin n, i ≠ j → ∀ s t : ℤˣ, ∃ α : d.pinning.rootIndex,
                d.pinning.rootDatum.root α = (s : ℤ) • ε i + (t : ℤ) • ε j) ∧
              ∀ (ν : cocharacterLattice d.splitTorus) (c : ℤ),
                Nat.card {p : Fin n × ℤˣ //
                    (p.2 : ℤ) * latticePairing d.splitTorus
                      ((characterLattice.baseChangeEquiv
                          (algebraBaseMap K (SeparableClosure K)) d.splitTorus
                          d.maximalSplit.1.1).symm
                        ((CommGroupScheme.baseChange
                            (algebraBaseMap K (SeparableClosure K))).map d.torusMap ≫
                          ε p.1)) ν = c} =
                  degree * Module.finrank D (σ.cocharacterWeightSpace q
                    (CommGroupScheme.groupHom ν ≫ d.splitInclusion ≫ π) c)

end Langlands.GroupScheme
