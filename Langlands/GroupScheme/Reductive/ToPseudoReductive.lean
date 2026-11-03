import Langlands.GroupScheme.Reductive.GroundFieldRadical
import Langlands.GroupScheme.Unipotent.BaseChange

/-! # Connected reductive groups are pseudo-reductive -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- A connected reductive group has trivial ground-field unipotent radical. -/
theorem IsConnectedReductive.hasTrivialUnipotentRadical
    {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
    (hG : IsConnectedReductive G) : HasTrivialUnipotentRadical G := by
  apply hG.hasTrivialUnipotentRadical_of_unipotentFieldExtension
  intro k K _ _ _ H hA _ hH
  have : IsAffineHom H.X.hom := hA
  exact hH.baseChange

/-- Every connected reductive group over a field is pseudo-reductive. -/
theorem IsConnectedReductive.isPseudoReductive
    {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
    (hG : IsConnectedReductive G) : IsPseudoReductive G where
  smooth := hG.smooth
  isAffineHom := hG.isAffineHom
  connectedSpace := hG.connectedSpace
  hasTrivialUnipotentRadical := hG.hasTrivialUnipotentRadical

/-- The identity on group schemes embeds connected reductive groups into
pseudo-reductive groups over every field. -/
def connectedReductiveToPseudoReductiveEmbedding
    (k : Type u) [Field k] :
    {G : GroupScheme (Spec (CommRingCat.of k)) // IsConnectedReductive G} ↪
      {G : GroupScheme (Spec (CommRingCat.of k)) // IsPseudoReductive G} where
  toFun G := ⟨G.val, G.property.isPseudoReductive⟩
  inj' := by
    intro G H h
    exact Subtype.ext (congrArg
      (fun Z : {G : GroupScheme (Spec (CommRingCat.of k)) //
        IsPseudoReductive G} => Z.val) h)

end Langlands.GroupScheme
