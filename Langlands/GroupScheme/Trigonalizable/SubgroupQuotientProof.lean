import Langlands.GroupScheme.Trigonalizable.SubgroupQuotientStatement
import Langlands.GroupScheme.Trigonalizable.MatrixCriterion
import Langlands.GroupScheme.AffineCorepresented
import Langlands.GroupScheme.CorepresentedComultiplication
import Langlands.GroupScheme.Chevalley.CoordinateRestriction

/-! # Subgroups and quotients of trigonalizable groups are trigonalizable (Milne 16.3) -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

open CoalgebraTrigonalizable TrigonalizableMatrixCriterion

/-- A closed subgroup of a trigonalizable affine group over a field is trigonalizable. -/
theorem IsTrigonalizable.of_isClosedSubgroup {k : Type u} [Field k]
    {G H : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (hG : IsTrigonalizable G) (i : H ⟶ G) (hi : IsClosedSubgroup i) :
    IsTrigonalizable H := by
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : IsClosedImmersion i.hom.hom.left := hi
  let : IsAffine H.X.left := isAffine_of_isAffineHom i.hom.hom.left
  let eG := AffineCoordinates.groupSchemeIso G
  let eH := AffineCoordinates.groupSchemeIso H
  let φ := eH.hom ≫ i ≫ eG.inv
  have : IsIso eH.hom.hom.hom.left :=
    inferInstanceAs (IsIso (((Grp.forget _) ⋙ Over.forget _).mapIso eH).hom)
  have : IsIso eG.inv.hom.hom.left :=
    inferInstanceAs (IsIso (((Grp.forget _) ⋙ Over.forget _).mapIso eG).inv)
  have hc : IsClosedSubgroup φ := by
    change IsClosedImmersion
      (eH.hom.hom.hom.left ≫ i.hom.hom.left ≫ eG.inv.hom.hom.left)
    infer_instance
  let cG := AffineCoordinates.corepresentation G
  let cH := AffineCoordinates.corepresentation H
  let α := Corepresented.pointsTrans cH cG φ
  have hc' : IsClosedSubgroup (Corepresented.groupSchemeMap cH cG α) := by
    simpa only [α, Corepresented.groupSchemeMap_pointsTrans] using hc
  let := AffineLinearEmbedding.bialgebra cG
  let := AffineLinearEmbedding.bialgebra cH
  have hmG : IsMatrixTrigonalizable k (AffineCoordinates.algebra G) :=
    (isTrigonalizable_iff_isMatrixTrigonalizable k _ _ cG).mp (IsTrigonalizable.of_iso eG hG)
  let q := Chevalley.coordinateRestrictionBialgHom cG cH α
  have hq : Function.Surjective q :=
    Chevalley.coordinateRestriction_surjective cG cH α hc'
  have hmH : IsMatrixTrigonalizable k (AffineCoordinates.algebra H) :=
    hmG.of_surjective q hq
  have htH : IsTrigonalizable (Corepresented.groupScheme (AffineCoordinates.functor H) cH) :=
    (isTrigonalizable_iff_isMatrixTrigonalizable k _ _ cH).mpr hmH
  exact IsTrigonalizable.of_iso eH.symm htH

/-- Milne 2017, Corollary 16.3: closed subgroups and quotients of a trigonalizable affine
algebraic group over a field are trigonalizable. -/
theorem trigonalizableSubgroupQuotient : TrigonalizableSubgroupQuotientStatement.{u} := by
  intro k _ G _ _ hG
  refine ⟨fun H i hi => hG.of_isClosedSubgroup i hi, ?_⟩
  intro Q _ _ q hflat hsurj
  let : Flat q.hom.hom.left := hflat
  let : Surjective q.hom.hom.left := hsurj
  exact hG.of_flat_surjective q

end Langlands.GroupScheme
