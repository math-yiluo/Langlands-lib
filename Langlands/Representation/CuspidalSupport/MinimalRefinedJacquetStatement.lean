import Langlands.Representation.CuspidalSupport.MinimalJacquetProof
import Langlands.Representation.Geometric.RefinementFunctors
import Langlands.Group.GL.RefinementCoordinates

/-! Nonzero quasicuspidal refined Jacquet descent inside an actual standard
product Levi, from BZ77 sections 2.3(c) and 2.14(1). -/

namespace Langlands.CuspidalSupport

open GeneralLinear Geometric

universe uF uV

/-- Every nonzero smooth complex representation `A` of an actual standard
product Levi `B.Levi F` has a block refinement `S` whose entire refined Jacquet
quotient is nonzero and whose normalized refined Jacquet action, pulled back
along the actual coordinate equivalence from the Levi of the flattened shape
`B.flatten S` onto the refined Levi, is quasicuspidal. All ranks and block
shapes are included, the empty shape at rank zero among them. The quotient
keeps the carrier universe `uV`, independent of `uF`. -/
def MinimalNonzeroRefinedJacquetTheorem {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) : Prop :=
  letI := T.topology
  ∀ (n : ℕ) (B : BlockShape n) (A : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier)),
    Nontrivial A → ∃ S : BlockRefinement B,
      Nontrivial (RefinedJacquetModule B S A.representation) ∧
        IsLeviQuasicuspidal (B.flatten S)
          ((T.normalizedRefinedJacquet B S A.representation).comp
            (GeneralLinear.BlockShape.leviRefinementEquiv
              (B.flatten S) B S (B.flattenBlockEquiv S)
              (fun q => (B.flatten_size_flattenBlockEquiv S q).symm)
              F.Carrier).toMonoidHom)

end Langlands.CuspidalSupport
