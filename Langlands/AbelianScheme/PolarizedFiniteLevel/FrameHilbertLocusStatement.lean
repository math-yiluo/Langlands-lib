import Langlands.AbelianScheme.PolarizedFiniteLevel.FrameEmbedding
import Langlands.AbelianScheme.PolarizedFiniteLevel.CubicProjectiveEvaluation
import Langlands.AbelianScheme.PolarizedFiniteLevel.Base
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-! # The locally closed locus of frame-normalized polarized data in a projective family -/

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

open Langlands.AlgebraicGeometry

/-- Relative form of Mumford–Fogarty–Kirwan, GIT Proposition 7.3, normalized by a projective
frame of torsion points. Let `m = cubicProjectiveDimension g d`. Let `S` be a locally
noetherian scheme with a family consisting of an ideal sheaf `I` on relative projective
`m`-space over `S`, whose closed subscheme is flat and locally of finite presentation over
`S`, and integral projective points `σ r` indexed by level coefficient tuples `r`. Then there
is an immersion `j : S' ⟶ S` from a level base `S'` with two properties.

* Over `S'` there are a datum `U` with frame locus `⊤` and a frame-normalized cubic embedding
  `ψ` of `U` realizing the pullback of the family along `j`.
* Whenever a datum `b` over a level base `T` has frame locus `⊤` and a frame-normalized cubic
  embedding realizing the pullback of the family along some `t : T ⟶ S`, the morphism `t`
  factors through `j`.

This proposition is a statement, not a proof of it. -/
def FrameHilbertLocusStatement : Prop :=
  ∀ (P : Prerequisites.{0}) (g d n : ℕ) (_hd : 0 < d) (_hn : 3 ≤ n)
    (ρ : Fin (cubicProjectiveDimension g d + 2) → Fin (2 * g) → ZMod n)
    (S : Scheme.{0}) [IsLocallyNoetherian S]
    (I : (RelativeProjectiveSpace S (cubicProjectiveDimension g d)).IdealSheafData)
    (σ : (Fin (2 * g) → ZMod n) →
      (S ⟶ ProjectiveSpace (ULift.{0} ℤ) (cubicProjectiveDimension g d))),
    Flat (I.subschemeι ≫ RelativeProjectiveSpace.toBase S (cubicProjectiveDimension g d)) →
    LocallyOfFinitePresentation
      (I.subschemeι ≫ RelativeProjectiveSpace.toBase S (cubicProjectiveDimension g d)) →
    ∃ (S' : LevelBase n) (j : S'.obj ⟶ S), IsImmersion j ∧
      (∃ (U : Datum P S'.obj g d n)
        (ψ : U.abelian.X.left ⟶ RelativeProjectiveSpace S'.obj (cubicProjectiveDimension g d)),
        U.frameLocus ρ = ⊤ ∧ U.IsFrameEmbedding ρ ψ ∧
          U.Realizes ψ (I.comap (RelativeProjectiveSpace.map (cubicProjectiveDimension g d) j))
            (fun r => j ≫ σ r)) ∧
      ∀ (T : LevelBase n) (t : T.obj ⟶ S) (b : Datum P T.obj g d n)
        (ψ : b.abelian.X.left ⟶ RelativeProjectiveSpace T.obj (cubicProjectiveDimension g d)),
        b.frameLocus ρ = ⊤ → b.IsFrameEmbedding ρ ψ →
        b.Realizes ψ (I.comap (RelativeProjectiveSpace.map (cubicProjectiveDimension g d) t))
          (fun r => t ≫ σ r) →
        ∃ t' : T.obj ⟶ S'.obj, t' ≫ j = t

end Langlands.AbelianScheme.PolarizedFiniteLevel
