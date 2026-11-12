import Langlands.Cohomology.HyperextSpectralSequence
import Langlands.Cohomology.HyperextAbutmentFiltration

/-!
# Convergence of the hyperext spectral sequence for bounded objects

Let `t` be a t-structure on a triangulated category `C`, and let `K` and `B` be objects of `C`.
Worker 61's hyperext spectral sequence `hyperextSpectralSequence t K B` applies `Hom(-, B)` to the
truncations of `K`; its object in position `(p, q)` on page 2 is
`Hom(heartPiece t K q, B⟦p + q⟧)`, and `heartPiece t K q` is classically `H^{-q} K` placed in
degree `-q`. Its intended abutment in total degree `n` is `Hom(K, B⟦n⟧)`, filtered by the
subgroups `F^p` of morphisms that factor through `K ⟶ τ_{≥ p - n} K`
(`HyperextAbutment.filtration`), with graded pieces `gr^p = F^p / F^{p+1}`
(`HyperextAbutment.graded`).

The propositions below assert that the spectral sequence converges when `K` is bounded for `t`:
if `K` lies in degrees `≥ a` and `≤ b`, then on every page `r` with `r ≥ 2` and `r ≥ b - a + 2`
all differentials vanish, and the object in position `(p, q)` is isomorphic to the graded piece
`gr^p` of `Hom(K, B⟦p + q⟧)`. Both are conclusions; neither is supplied as data.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
  CategoryTheory.Triangulated

namespace Langlands.Cohomology

namespace HyperextConvergence

universe v u

variable (C : Type u) [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]

/-- Page degeneration. For every t-structure `t` on `C`, every object `K` lying in degrees `≥ a`
and `≤ b` for `t`, and every object `B`, all differentials of page `r` of the hyperext spectral
sequence of `K` and `B` vanish as soon as `r ≥ 2` and `r ≥ b - a + 2`. -/
def HyperextPageDegenerationStatement : Prop :=
  ∀ (t : TStructure C) (K B : C) (a b : ℤ) [t.IsGE K a] [t.IsLE K b] (r : ℤ) (hr : 2 ≤ r),
    b - a + 2 ≤ r → ∀ pq pq' : ℤ × ℤ,
      ((HyperextSpectralSequence.hyperextSpectralSequence t K B).page r hr).d pq pq' = 0

/-- Identification of the stable pages. For every t-structure `t` on `C`, every object `K` lying
in degrees `≥ a` and `≤ b` for `t`, and every object `B`, on every page `r` with `r ≥ 2` and
`r ≥ b - a + 2` the object of the hyperext spectral sequence in position `(p, q)` is isomorphic to
the graded piece `gr^p = F^p / F^{p+1}` of the abutment filtration on `Hom(K, B⟦p + q⟧)`. -/
def HyperextStablePageStatement : Prop :=
  ∀ (t : TStructure C) (K B : C) (a b : ℤ) [t.IsGE K a] [t.IsLE K b] (r : ℤ) (hr : 2 ≤ r),
    b - a + 2 ≤ r → ∀ p q : ℤ,
      Nonempty (((HyperextSpectralSequence.hyperextSpectralSequence t K B).page r hr).X ⟨p, q⟩ ≅
        AddCommGrpCat.of (HyperextAbutment.graded t K B (p + q) p))

/-- Convergence of the hyperext spectral sequence for objects that are bounded for the
t-structure: page degeneration and identification of the stable pages with the graded pieces of
the abutment filtration. -/
def HyperextConvergenceStatements : Prop :=
  HyperextPageDegenerationStatement C ∧ HyperextStablePageStatement C

end HyperextConvergence

end Langlands.Cohomology
