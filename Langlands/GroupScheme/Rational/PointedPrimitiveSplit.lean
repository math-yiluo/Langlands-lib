import Langlands.GroupScheme.Rational.SplitTorusDominationAssembly
import Langlands.GroupScheme.Rational.PointedPrimitivePolynomialCoordinates
import Langlands.GroupScheme.Rational.SplitTorusDominationRefinement
import Langlands.GroupScheme.Rational.TorusSplitUnipotenceProof
import Langlands.GroupScheme.AffineCorepresented

/-! # Splitness from pointed domination and finite primitive generators -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k] {p : ℕ} [Fact p.Prime] [CharP k p]

include p in
/-- Primitive generators on an affine coordinate model give splitness of the
original smooth group under actual pointed split-torus domination. -/
theorem isSplitUnipotent_of_pointed_finitePrimitiveGenerators
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [IsAffine G.X.left]
    (hdom : HasPointedSplitTorusDomination G)
    (T : Finset (Corepresented.primitiveFunctions (AffineCoordinates.corepresentation G)))
    (hT : Algebra.adjoin k
      (Subtype.val '' (T : Set (Corepresented.primitiveFunctions
        (AffineCoordinates.corepresentation G)))) = ⊤) :
    RelativeRoot.IsSplitUnipotent G := by
  let e := AffineCoordinates.groupSchemeIso G
  let H := Corepresented.groupScheme (AffineCoordinates.functor G)
    (AffineCoordinates.corepresentation G)
  have hdomH : HasPointedSplitTorusDomination H := hdom.of_iso e.symm
  have : Smooth H.X.hom := RelativeRoot.smooth_hom_of_iso e inferInstance
  have : IsAffine H.X.left :=
    inferInstanceAs (IsAffine (Spec (CommRingCat.of (AffineCoordinates.algebra G))))
  have : IsAffineHom H.X.hom := isAffineHom_of_isAffine _
  have : ConnectedSpace H.X.left := hdomH.hasPointedTorusDomination.connectedSpace
  have : GeometricallyIntegral H.X.hom :=
    smoothConnectedAffineGeometry.1 k H inferInstance inferInstance inferInstance
  have : IsReduced H.X.left :=
    GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian H.X.hom
  obtain ⟨N, ⟨v⟩⟩ := Corepresented.exists_vectorGroupIso_of_pointed_primitiveGenerators
    (AffineCoordinates.corepresentation G) (p := p) hdomH T hT
  have hvec : RelativeRoot.IsVectorGroupOfDimension G N :=
    RelativeRoot.isVectorGroupOfDimension_iff_nonempty_iso.2 ⟨e.symm ≪≫ v⟩
  exact hvec.isSplitUnipotent

include p in
/-- Choose the represented additive series from a supplied finite primitive
coordinate generating set and actual pointed domination. -/
def splitSeriesOfPointedFinitePrimitiveGenerators
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [IsAffine G.X.left]
    (hdom : HasPointedSplitTorusDomination G)
    (T : Finset (Corepresented.primitiveFunctions (AffineCoordinates.corepresentation G)))
    (hT : Algebra.adjoin k
      (Subtype.val '' (T : Set (Corepresented.primitiveFunctions
        (AffineCoordinates.corepresentation G)))) = ⊤) :
    {n : ℕ // RelativeRoot.HasSplitSeries n G} :=
  let h := isSplitUnipotent_of_pointed_finitePrimitiveGenerators (p := p) G hdom T hT
  ⟨h.choose, h.choose_spec⟩

end Langlands.GroupScheme
