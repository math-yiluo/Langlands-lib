import Langlands.GroupScheme.ChevalleyIntegral.IntegralRetraction
import Langlands.GroupScheme.ChevalleyIntegral.MatrixMaps
import Langlands.GroupScheme.SplitExistence.UnipotentLie
import Langlands.GroupScheme.SplitExistence.Opposite

/-! # Closed ordered root products over a commutative ring -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite Matrix

namespace Langlands.GroupScheme.SplitExistence.ChevalleyData

variable {J X Y : Type u} [AddCommGroup X] [AddCommGroup Y]
  {P : RootDatum J X Y} {b : P.Base} (D : ChevalleyData P b)
  [DecidableEq J] (R : CommRingCat.{u})

/-- The polynomial algebra with one coordinate for each root occurring in the list. -/
abbrev orderedRootAlgebra (_D : ChevalleyData P b) (R : CommRingCat.{u})
    (l : List J) : CommAlgCat.{u} R :=
  CommAlgCat.of R (MvPolynomial {j : J // j ∈ l} R)

/-- The universal list parameters, extended by zero outside the list. -/
def orderedRootVariables (l : List J) : J → D.orderedRootAlgebra R l := fun j =>
  if hj : j ∈ l then MvPolynomial.X ⟨j, hj⟩ else 0

theorem orderedRootVariables_mem (l : List J) (j : {j : J // j ∈ l}) :
    D.orderedRootVariables R l j = MvPolynomial.X j := by
  simp [orderedRootVariables, j.property]

/-- The coordinate map of the ordered product of the root exponentials. -/
def orderedRootClassify (l : List J) :
    GeneralLinear.CoordinateRing (Fin D.n) R →ₐ[R] D.orderedRootAlgebra R l :=
  GeneralLinear.classify (D.opmGL l (D.orderedRootVariables R l))

/-- The recovered list coordinates, evaluated on the universal invertible matrix. -/
def orderedRootSection (l : List J) :
    D.orderedRootAlgebra R l →ₐ[R] GeneralLinear.CoordinateRing (Fin D.n) R :=
  MvPolynomial.aeval fun j : {j : J // j ∈ l} =>
    D.integralRetrAux l (GeneralLinear.universal (Fin D.n) R).val 0 j

/-- For a distinct, height-sorted list of positive roots, coefficient recovery splits
the coordinate map over any commutative ring. -/
theorem orderedRootClassify_comp_section (l : List J) (hnd : l.Nodup)
    (hsort : l.Pairwise (fun a c => D.ℓ (P.root a) ≤ D.ℓ (P.root c)))
    (hpos : ∀ j ∈ l, 0 < D.ℓ (P.root j)) :
    (D.orderedRootClassify R l).comp (D.orderedRootSection R l) =
      AlgHom.id R (D.orderedRootAlgebra R l) := by
  apply MvPolynomial.algHom_ext
  intro j
  simp only [AlgHom.comp_apply, orderedRootSection, MvPolynomial.aeval_X, AlgHom.id_apply]
  let φ := D.orderedRootClassify R l
  have hM :
      (GeneralLinear.universal (Fin D.n) R).val.map φ.toRingHom =
        D.opm l (D.orderedRootVariables R l) := by
    apply Matrix.ext
    intro p q
    change D.orderedRootClassify R l (GeneralLinear.quotient (Fin D.n) R
      (MvPolynomial.X (GeneralLinear.Coordinate.entry p q))) = _
    rw [orderedRootClassify, GeneralLinear.classify_entry, D.coe_opmGL]
  have hrec := congrFun
    (D.integralRetrAux_map φ.toRingHom l (GeneralLinear.universal (Fin D.n) R).val 0) j
  have hzero : (φ.toRingHom ∘ (0 : J → GeneralLinear.CoordinateRing (Fin D.n) R)) = 0 := by
    funext j
    exact map_zero φ
  rw [hzero, hM, D.integralRetrAux_opm l hnd hsort hpos] at hrec
  simpa [φ, j.property, D.orderedRootVariables_mem R l j] using
    hrec.symm

/-- The ordered-product coordinate map is surjective over every commutative ring. -/
theorem orderedRootClassify_surjective (l : List J) (hnd : l.Nodup)
    (hsort : l.Pairwise (fun a c => D.ℓ (P.root a) ≤ D.ℓ (P.root c)))
    (hpos : ∀ j ∈ l, 0 < D.ℓ (P.root j)) :
    Function.Surjective (D.orderedRootClassify R l) := by
  intro p
  exact ⟨D.orderedRootSection R l p,
    DFunLike.congr_fun (D.orderedRootClassify_comp_section R l hnd hsort hpos) p⟩

/-- The affine parameter scheme for the ordered product. -/
abbrev orderedRootSpace (l : List J) : Over (Spec R) :=
  (algSpec R).obj (op (D.orderedRootAlgebra R l))

/-- The ordered product as a morphism from its parameter scheme to the matrix group. -/
def orderedRootMapOver (l : List J) : D.orderedRootSpace R l ⟶ (D.GLR R).X :=
  (algSpec R).map (CommAlgCat.ofHom (D.orderedRootClassify R l)).op

/-- The integral polynomial recovery map as a morphism of schemes over the base ring. -/
def orderedRootRetractionOver (l : List J) : (D.GLR R).X ⟶ D.orderedRootSpace R l :=
  (algSpec R).map (CommAlgCat.ofHom (D.orderedRootSection R l)).op

set_option backward.isDefEq.respectTransparency false in
theorem orderedRootMapOver_retraction (l : List J) (hnd : l.Nodup)
    (hsort : l.Pairwise (fun a c => D.ℓ (P.root a) ≤ D.ℓ (P.root c)))
    (hpos : ∀ j ∈ l, 0 < D.ℓ (P.root j)) :
    D.orderedRootMapOver R l ≫ D.orderedRootRetractionOver R l =
      𝟙 (D.orderedRootSpace R l) := by
  rw [orderedRootMapOver, orderedRootRetractionOver, ← Functor.map_comp]
  change (algSpec R).map
    (CommAlgCat.ofHom ((D.orderedRootClassify R l).comp (D.orderedRootSection R l))).op = _
  rw [D.orderedRootClassify_comp_section R l hnd hsort hpos]
  exact (algSpec R).map_id _

/-- The ordered product of distinct positive roots in increasing height order is a
closed immersion over any commutative ring. -/
theorem isClosedImmersion_orderedRootMapOver (l : List J) (hnd : l.Nodup)
    (hsort : l.Pairwise (fun a c => D.ℓ (P.root a) ≤ D.ℓ (P.root c)))
    (hpos : ∀ j ∈ l, 0 < D.ℓ (P.root j)) :
    IsClosedImmersion (D.orderedRootMapOver R l).left :=
  IsClosedImmersion.spec_of_surjective _ (D.orderedRootClassify_surjective R l hnd hsort hpos)

/-- On affine test algebras the scheme morphism is exactly the ordered root product. -/
theorem affinePointsEquiv_orderedRootMapOver (l : List J) (A : CommAlgCat.{u} R)
    (f : D.orderedRootAlgebra R l ⟶ A) :
    GeneralLinear.affinePointsEquiv (Fin D.n) R A
      ((algSpec R).map f.op ≫ D.orderedRootMapOver R l) =
        D.opmGL l (fun j => f.hom (D.orderedRootVariables R l j)) := by
  rw [GeneralLinear.affinePointsEquiv_naturality, orderedRootMapOver,
    GeneralLinear.affinePointsEquiv_map]
  change Matrix.GeneralLinearGroup.map f.hom.toRingHom
    (GeneralLinear.point (D.orderedRootClassify R l)) = _
  rw [orderedRootClassify, GeneralLinear.point_classify, D.opmGL_map]
  rfl

variable [Fintype J]

/-- The positive ordered root product is a closed immersion over the base ring. -/
theorem isClosedImmersion_posRootMapOver :
    IsClosedImmersion (D.orderedRootMapOver R D.posList).left :=
  D.isClosedImmersion_orderedRootMapOver R D.posList D.posList_nodup D.posList_sorted
    (fun _ hj => D.ℓ_root_pos (D.mem_posList.1 hj))

/-- The negative ordered root product, using the opposite height order, is a closed
immersion over the base ring. -/
theorem isClosedImmersion_negRootMapOver :
    IsClosedImmersion (D.neg.orderedRootMapOver R D.neg.posList).left :=
  D.neg.isClosedImmersion_posRootMapOver R

end Langlands.GroupScheme.SplitExistence.ChevalleyData
