import Langlands.Representation.Exponents.ArbitraryParabolicLeviPoints
import Langlands.Representation.Plancherel.RationalCharacterValuation
import Langlands.GroupScheme.Rational.ParabolicPointConjugation

/-! # The group `W(A) = N_G(M)/M` of a rational Levi: finiteness and faithfulness

Renard 2026, V.4.3 (PDF p.125), equation (V.4.3.3), identifies `W(M, M)/W_M` with
`W(A) = N_G(A)/Z_G(A) = N_G(M)/M` for a Levi subgroup `M` with split component `A`. The
proof of VI.8.5 (PDF p.200) uses that this group is finite and acts faithfully on
`𝔞_M^*` (V.3.5). This module states the two facts for an actual rational Levi
`l : M ⟶ P` of an actual rational parabolic `p : P ⟶ G`, on rational points.

An element `w ∈ G(F)` normalizes `M` when some automorphism `φ` of `M` satisfies
`φ ≫ l ≫ p = l ≫ p ≫ Int(w)`.

* `LeviNormalizerFiniteQuotientStatement`: `N_G(M)(F)/M(F)` is finite. Finitely many
  normalizing elements `g j` represent every normalizing `w` modulo the Levi points.
* `LeviNormalizerNormFixingStatement`: a normalizing `w` whose automorphism preserves the
  norm `‖χ(a)‖` of every rational character `χ` of `M` at every central point `a` of
  `M(F)` lies in `M(F)`.

`LeviNormalizerWeylGroupStatements` is their conjunction.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- Renard V.4.3.3: for an actual rational parabolic `p : P ⟶ G` of a connected reductive
group over a nonarchimedean local field, with rational Levi `l : M ⟶ P`, the group
`N_G(M)(F)/M(F)` is finite: there are finitely many elements `g j ∈ G(F)` normalizing `M`
such that every `w ∈ G(F)` normalizing `M` is `g j · m` for some `j` and some `m ∈ M(F)`. -/
def LeviNormalizerFiniteQuotientStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k]
    (G : GroupScheme (Spec (CommRingCat.of k))), IsConnectedReductive G →
    ∀ (P M : GroupScheme (Spec (CommRingCat.of k))) (p : P ⟶ G) (l : M ⟶ P),
      IsParabolicSubgroup p → IsRationalLeviSubgroup l →
      ∃ (n : ℕ) (g : Fin n → rationalPoints G),
        (∀ j, ∃ φ : M ≅ M, φ.hom ≫ l ≫ p = l ≫ p ≫ (G.innerIso (g j)).hom) ∧
        ∀ (w : rationalPoints G) (φ : M ≅ M),
          φ.hom ≫ l ≫ p = l ≫ p ≫ (G.innerIso w).hom →
            ∃ (j : Fin n) (m : rationalPoints M), w = g j * rationalPoints.map (l ≫ p) m

/-- Renard V.3.5 with V.4.3.3: for an actual rational parabolic `p : P ⟶ G` of a connected
reductive group over a nonarchimedean local field, with rational Levi `l : M ⟶ P`, let
`w ∈ G(F)` normalize `M` through `φ : M ≅ M`. If `‖χ(φ(a))‖ = ‖χ(a)‖` for every rational
character `χ` of `M` and every `a` in the centre of `M(F)`, then `w ∈ M(F)`. -/
def LeviNormalizerNormFixingStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k]
    (G : GroupScheme (Spec (CommRingCat.of k))), IsConnectedReductive G →
    ∀ (P M : GroupScheme (Spec (CommRingCat.of k))) (p : P ⟶ G) (l : M ⟶ P),
      IsParabolicSubgroup p → IsRationalLeviSubgroup l →
      ∀ (w : rationalPoints G) (φ : M ≅ M),
        φ.hom ≫ l ≫ p = l ≫ p ≫ (G.innerIso w).hom →
        (∀ a ∈ Subgroup.center (rationalPoints M), ∀ χ : rationalCharacters M,
          (Plancherel.rationalNormCharacters M χ).toMul (rationalPoints.map φ.hom a) =
            (Plancherel.rationalNormCharacters M χ).toMul a) →
          w ∈ pointImage (l ≫ p)

/-- The two statements above: `N_G(M)(F)/M(F)` is finite and acts faithfully through the
norms of rational characters on the centre of `M(F)`. -/
def LeviNormalizerWeylGroupStatements : Prop :=
  LeviNormalizerFiniteQuotientStatement.{u} ∧ LeviNormalizerNormFixingStatement.{u}

end Langlands.Aubert.General.RepresentedParabolic
