import Langlands.GroupScheme.Unipotent.CharZeroCoordinateConnected
import Langlands.GroupScheme.AffineCoordinatesFiniteType
import Langlands.GroupScheme.AffineHopfCoordinates
import Langlands.GroupScheme.Unipotent.BaseChange
import Langlands.GroupScheme.BaseChangeReflection
import Langlands.AnthropicFLT.Theorems.Thm_HopfAlgebra_isReduced_of_finiteType_of_charZero
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Connectedness of unipotent groups in characteristic zero

Cartier reducedness and the coordinate connectedness argument prove the result
over an algebraically closed field. Connectedness descends from an algebraic
closure along the surjective base-change projection.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace Unipotent

variable {k : Type u} [Field k] [CharZero k]
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

/-- The algebraically closed case, using reduced Hopf coordinates. -/
theorem connectedSpace_of_isUnipotent_of_isAlgClosed [IsAlgClosed k]
    (hG : IsUnipotent G) : ConnectedSpace G.X.left := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : Algebra.FiniteType k (AffineCoordinates.hopfAlgebra G) :=
    AffineCoordinates.algebraFiniteType G
  let : Algebra.FiniteType (CommRingCat.of k) (AffineCoordinates.algebra G) :=
    AffineCoordinates.algebraFiniteType G
  have : _root_.IsReduced (AffineCoordinates.algebra G) :=
    HopfAlgebra.isReduced_of_finiteType_of_charZero k (AffineCoordinates.hopfAlgebra G)
  let e := AffineCoordinates.groupSchemeIso G
  have hU : IsUnipotent (Corepresented.groupScheme (AffineCoordinates.functor G)
      (AffineCoordinates.corepresentation G)) := IsUnipotent.of_iso e hG
  let : ConnectedSpace (Corepresented.groupScheme (AffineCoordinates.functor G)
      (AffineCoordinates.corepresentation G)).X.left := by
    change ConnectedSpace (PrimeSpectrum (AffineCoordinates.algebra G))
    exact connectedSpace_primeSpectrum_of_isUnipotent (AffineCoordinates.corepresentation G) hU
  have : IsIso e.hom.hom.hom.left :=
    inferInstanceAs (IsIso (((Grp.forget (Over _)) ⋙ Over.forget _).map e.hom))
  exact Function.Surjective.connectedSpace
    (Scheme.homeoOfIso (asIso e.hom.hom.hom.left)).surjective
    (Scheme.homeoOfIso (asIso e.hom.hom.hom.left)).continuous

end Unipotent

set_option linter.defProp false in
/-- A unipotent affine group scheme of finite type over a characteristic-zero
field has a connected underlying space. -/
@[instance_reducible]
def charZeroUnipotentConnected :
    ∀ (k : Type u) [Field k] [CharZero k] (G : GroupScheme (Spec (CommRingCat.of k))),
      IsAffineHom G.X.hom → LocallyOfFiniteType G.X.hom → IsUnipotent G →
        ConnectedSpace G.X.left := by
  intro k _ _ G hA hft hG
  let := hA
  let := hft
  let b := Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))
  let H := (GroupScheme.baseChange b).obj G
  have : IsAffineHom H.X.hom := by
    change IsAffineHom (pullback.snd G.X.hom b)
    infer_instance
  have : LocallyOfFiniteType H.X.hom := by
    change LocallyOfFiniteType (pullback.snd G.X.hom b)
    infer_instance
  have hH : IsUnipotent H := hG.baseChange
  have hconn : ConnectedSpace H.X.left :=
    Unipotent.connectedSpace_of_isUnipotent_of_isAlgClosed H hH
  let : Surjective b := (fieldExtension_fpqc k (AlgebraicClosure k)).1
  have hs : Surjective (pullback.fst G.X.hom b) := inferInstance
  let : ConnectedSpace (pullback G.X.hom b : Scheme.{u}) := hconn
  exact hs.surj.connectedSpace (pullback.fst G.X.hom b).continuous

end Langlands.GroupScheme
