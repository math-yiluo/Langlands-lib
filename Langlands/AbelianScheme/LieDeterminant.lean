import Langlands.AbelianScheme.LieAction
import Langlands.AbelianScheme.LieRankProof
import Langlands.AlgebraicGeometry.LocalSectionDeterminant

/-! # Determinant polynomials of actual order actions on abelian-scheme Lie modules -/

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite MvPolynomial
open Langlands.Scheme.Modules

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u v w

namespace Langlands.AbelianScheme

variable {S : AlgebraicGeometry.Scheme.{u}}
    {O : Type v} [Ring O] {ι : Type w} [Fintype ι]

/-- Compose an actual order action on the abelian scheme with its Lie functor. -/
def lieOrderAction (A : AbelianScheme S) (α : O →+* End A) :
    O →+* CategoryTheory.End A.Lie :=
  (lieEndAction A).comp α

/-- Restrict the constructed Lie action to a genuine open. -/
def lieLocalOrderAction (A : AbelianScheme S) (α : O →+* End A) (U : S.Opens) :
    O →+* CategoryTheory.End (A.Lie.over U) where
  toFun a := (lieOrderAction A α a).over U
  map_zero' := by rw [map_zero]; rfl
  map_one' := by rw [map_one]; rfl
  map_add' a b := by rw [map_add]; rfl
  map_mul' a b := by rw [map_mul]; rfl

/-- The actual order action on the actual sections of the Lie module. -/
def lieSectionOrderAction (A : AbelianScheme S) (α : O →+* End A)
    {U : S.Opens} (V : Over U) :
    O →+* Module.End Γ(S, V.left) Γ(A.Lie, V.left) :=
  (localSectionEndomorphism A.Lie V).comp (lieLocalOrderAction A α U)

@[simp]
theorem lieSectionOrderAction_apply (A : AbelianScheme S) (α : O →+* End A)
    {U : S.Opens} (V : Over U) (a : O) (x : Γ(A.Lie, V.left)) :
    lieSectionOrderAction A α V a x = (lieMap (α a)).app V.left x := rfl

/-- Sections of the differential action commute with actual restrictions. -/
theorem lieSectionOrderAction_restrict (A : AbelianScheme S) (α : O →+* End A)
    {U : S.Opens} {V W : Over U} (j : V ⟶ W) (a : O)
    (x : Γ(A.Lie, W.left)) :
    lieSectionOrderAction A α V a (A.Lie.presheaf.map j.left.op x) =
      A.Lie.presheaf.map j.left.op (lieSectionOrderAction A α W a x) :=
  localSectionEndomorphism_restrict j (lieLocalOrderAction A α U a) x

/-- The determinant polynomial of an actual finite family in the acting order. -/
def lieSectionDeterminant (A : AbelianScheme S) (α : O →+* End A)
    {U : S.Opens} {I : Type u} [Fintype I]
    (e : SheafOfModules.free (R := S.ringCatSheaf.over U) I ≅ A.Lie.over U)
    (a : ι → O) (V : Over U) : MvPolynomial ι Γ(S, V.left) :=
  localSectionDeterminant e (fun i => lieLocalOrderAction A α U (a i)) V

/-- A finite basis computes exactly the polynomial of the constructed order action. -/
theorem lieSectionDeterminant_eq_basis (A : AbelianScheme S) (α : O →+* End A)
    {U : S.Opens} {I : Type u} [Fintype I]
    (e : SheafOfModules.free (R := S.ringCatSheaf.over U) I ≅ A.Lie.over U)
    (a : ι → O) (V : Over U)
    {J : Type u} [Fintype J] [DecidableEq J]
    (b : Module.Basis J Γ(S, V.left) Γ(A.Lie, V.left)) :
    lieSectionDeterminant A α e a V =
      Langlands.Shimura.HodgeDeterminant.polynomial b
        (fun i => lieSectionOrderAction A α V (a i)) :=
  localSectionDeterminant_eq_basis e _ V b

/-- The two chart polynomials coincide on every open contained in both charts. -/
theorem lieSectionDeterminant_overlap (A : AbelianScheme S) (α : O →+* End A)
    {U U' T : S.Opens} {I J : Type u} [Fintype I] [Fintype J]
    (e : SheafOfModules.free (R := S.ringCatSheaf.over U) I ≅ A.Lie.over U)
    (e' : SheafOfModules.free (R := S.ringCatSheaf.over U') J ≅ A.Lie.over U')
    (a : ι → O) (i : T ⟶ U) (j : T ⟶ U') :
    lieSectionDeterminant A α e a (Over.mk i) =
      lieSectionDeterminant A α e' a (Over.mk j) := by
  let : DecidableEq I := Classical.decEq I
  let : DecidableEq J := Classical.decEq J
  exact Langlands.Shimura.HodgeDeterminant.polynomial_basis_independent_commRing
    (localSectionBasis e (Over.mk i)) (localSectionBasis e' (Over.mk j))
    (fun k => (lieMap (α (a k))).val.app (op T) |>.hom)

/-- Restricting Lie polynomials restricts their actual structure-ring coefficients. -/
theorem lieSectionDeterminant_restrict (A : AbelianScheme S) (α : O →+* End A)
    {U : S.Opens} {I : Type u} [Fintype I]
    (e : SheafOfModules.free (R := S.ringCatSheaf.over U) I ≅ A.Lie.over U)
    (a : ι → O) {V W : Over U} (j : V ⟶ W) :
    MvPolynomial.map (S.presheaf.map j.left.op).hom
        (lieSectionDeterminant A α e a W) = lieSectionDeterminant A α e a V :=
  localSectionDeterminant_restrict e _ j

theorem eval_lieSectionDeterminant (A : AbelianScheme S) (α : O →+* End A)
    {U : S.Opens} {I : Type u} [Fintype I]
    (e : SheafOfModules.free (R := S.ringCatSheaf.over U) I ≅ A.Lie.over U)
    (a : ι → O) (V : Over U) (x : ι → Γ(S, V.left)) :
    eval x (lieSectionDeterminant A α e a V) =
      LinearMap.det (∑ i, x i • lieSectionOrderAction A α V (a i)) :=
  eval_localSectionDeterminant e _ V x

theorem lieSectionDeterminant_isHomogeneous (A : AbelianScheme S)
    (α : O →+* End A) {U : S.Opens} {I : Type u} [Fintype I]
    (e : SheafOfModules.free (R := S.ringCatSheaf.over U) I ≅ A.Lie.over U)
    (a : ι → O) (V : Over U) :
    (lieSectionDeterminant A α e a V).IsHomogeneous (Fintype.card I) :=
  localSectionDeterminant_isHomogeneous e _ V

/-- Actual abelian-scheme Lie modules have a covering family of finite bases. -/
theorem lie_hasFiniteLocalBasis (A : AbelianScheme S) :
    ∃ q : SheafOfModules.LocalGeneratorsData.{u} A.Lie,
      q.IsLocallyFreeData ∧ q.IsFiniteType := by
  have hΩ := Langlands.Scheme.smoothDifferentialsFiniteLocalBasisRank A.X.left S A.X.hom
  have hCotangent := Langlands.Scheme.Modules.pullbackFiniteLocalBasisRank
    S A.X.left (Langlands.GroupScheme.identitySection A.toGrp)
    (Langlands.Scheme.relativeDifferentials A.X.hom)
  exact Langlands.Scheme.Modules.dual_hasFiniteLocalBasis
    (hCotangent.1 (hΩ.1 A.smooth))

/-- Choose only from the proved existence of finite local Lie bases. -/
def lieFiniteLocalBasisData (A : AbelianScheme S) :
    SheafOfModules.LocalGeneratorsData.{u} A.Lie :=
  (lie_hasFiniteLocalBasis A).choose

instance lieFiniteLocalBasisData_isLocallyFreeData (A : AbelianScheme S) :
    (lieFiniteLocalBasisData A).IsLocallyFreeData :=
  (lie_hasFiniteLocalBasis A).choose_spec.1

instance lieFiniteLocalBasisData_isFiniteType (A : AbelianScheme S) :
    (lieFiniteLocalBasisData A).IsFiniteType :=
  (lie_hasFiniteLocalBasis A).choose_spec.2

instance lieFiniteLocalBasisIndex_fintype (A : AbelianScheme S)
    (i : (lieFiniteLocalBasisData A).I) :
    Fintype ((lieFiniteLocalBasisData A).generators i).I := by
  let := ((lieFiniteLocalBasisData_isFiniteType A).isFiniteType i).finite
  exact Fintype.ofFinite _

/-- The actual isomorphism on a member of the proved Lie cover. -/
def lieFiniteLocalBasisTrivialization (A : AbelianScheme S)
    (i : (lieFiniteLocalBasisData A).I) :
    SheafOfModules.free (R := S.ringCatSheaf.over ((lieFiniteLocalBasisData A).X i))
        ((lieFiniteLocalBasisData A).generators i).I ≅
      A.Lie.over ((lieFiniteLocalBasisData A).X i) :=
  asIso ((lieFiniteLocalBasisData A).generators i).π

/-- The polynomial on each member of the constructed covering family. -/
def lieChartDeterminant (A : AbelianScheme S) (α : O →+* End A) (a : ι → O)
    (i : (lieFiniteLocalBasisData A).I)
    (V : Over ((lieFiniteLocalBasisData A).X i)) : MvPolynomial ι Γ(S, V.left) :=
  lieSectionDeterminant A α (lieFiniteLocalBasisTrivialization A i) a V

end Langlands.AbelianScheme
