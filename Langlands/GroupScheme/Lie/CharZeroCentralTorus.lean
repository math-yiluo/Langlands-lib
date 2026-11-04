import Langlands.GroupScheme.CentralIsogeny.WeightDivision
import Langlands.GroupScheme.Lie.AdjointDifferentialCentralizer
import Langlands.GroupScheme.Lie.SplitTorusSemisimple
import Langlands.GroupScheme.Nilpotent.EmptyRoots
import Langlands.GroupScheme.Torus.ExistenceProof

/-! # Central semisimple tangents in characteristic zero -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

/-- If the actual adjoint representation is trivial on a split torus, every
Lie vector is an invariant of its conjugation action on all algebras. -/
theorem IsSplitTorus.conjugation_lieInvariants_eq_top_of_adjoint_eq_zero
    (_hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G)
    (hi : i ≫ Lie.adjointRepresentation (Lie.finiteCoordinates G) = 0) :
    (AutomorphicAction.conjugation i).lieInvariants = ⊤ := by
  apply top_unique
  intro X _ A _ _ t
  rw [AutomorphicAction.differential_conjugation]
  let c := Lie.finiteCoordinates G
  apply (c.equiv (.of (CommRingCat.of k) A)).injective
  rw [← Lie.adjointRepresentation_affineAction]
  have he : (Lie.adjointRepresentation c).restrict i =
      MatrixRepresentation.trivial T.toGrp
        (Fin (Module.finrank k (Additive (lieKernel G k)))) := hi
  have hv := congrArg (fun ρ => ρ.affineAction (.of (CommRingCat.of k) A) t) he
  rw [MatrixRepresentation.affineAction_restrict,
    MatrixRepresentation.trivial_affineAction] at hv
  rw [hv]
  rfl

/-- In characteristic zero, centrality of the tangent images of a split
torus forces its actual adjoint representation to be trivial. -/
theorem IsSplitTorus.adjoint_comp_eq_zero_of_tangentCentralizers_eq_top
    [CharZero k]
    (hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G)
    (hi : ∀ X : lieKernel T.toGrp k,
      Lie.elementCentralizerLie G (Lie.targetMap i k X) = ⊤) :
    i ≫ Lie.adjointRepresentation (Lie.finiteCoordinates G) = 0 := by
  let c := Lie.finiteCoordinates G
  let ρ := Lie.adjointRepresentation c
  apply hT.hom_eq_zero_of_zero_differential_to_group
  intro X
  have hcen := (Lie.elementCentralizerLie_eq_top_iff_adjointDifferential_eq_zero
    c (Lie.targetMap i k X)).mp (hi X)
  rw [Lie.adjointDifferentialFamily_apply] at hcen
  have hM : ρ.tangentMatrix k (Lie.targetMap i k X) = 0 := by
    apply Matrix.toLin'.injective
    rw [map_zero]
    exact hcen
  have hpt := ρ.pointKernelEquiv_tangentMatrix k (Lie.targetMap i k X)
  have hz := congrArg Additive.toMul
    (GeneralLinear.DualNumber.pointKernelLinearEquiv
      (R := CommRingCat.of k) (A := k)
      (n := Fin (Module.finrank k (Additive (lieKernel G k))))).map_zero
  change GeneralLinear.DualNumber.pointKernelEquiv 0 = 1 at hz
  rw [hM, hz] at hpt
  apply Subtype.ext
  change X.val ≫ (i ≫ ρ).hom.hom = 1
  rw [Grp.comp_hom_hom, ← Category.assoc]
  exact congrArg Subtype.val hpt.symm

variable [Smooth G.X.hom] [ConnectedSpace G.X.left]

/-- A split-torus map in characteristic zero is central if all its tangent
images have full actual Lie centralizer. -/
theorem IsSplitTorus.isCentral_of_tangentCentralizers_eq_top
    [CharZero k] (hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G)
    (hi : ∀ X : lieKernel T.toGrp k,
      Lie.elementCentralizerLie G (Lie.targetMap i k X) = ⊤) : IsCentral i := by
  have : IsAffineHom T.toGrp.X.hom := hT.isAffineHom
  have hInv := hT.conjugation_lieInvariants_eq_top_of_adjoint_eq_zero i
    (hT.adjoint_comp_eq_zero_of_tangentCentralizers_eq_top i hi)
  classical
  obtain ⟨I, hfin, ⟨e⟩⟩ := hT
  let := Fintype.ofFinite I
  let := Module.Finite.iff_addGroup_fg.mp (inferInstance : Module.Finite ℤ (I → ℤ))
  let d := e ≪≫
    (Diagonalizable.splitIso (CommRingCat.of k) (AddEquiv.refl (I → ℤ))).symm
  apply (isCentral_iff_torusCentralizer_eq_top i).2
  have h := AutomorphicAction.fixedSubgroup_eq_top_of_diagonalizable_lieInvariants_eq_top
    (AutomorphicAction.conjugation i) d hInv
  rwa [AutomorphicAction.conjugation_fixedSubgroup_eq_torusCentralizer] at h

/-- Over an algebraically closed characteristic-zero field, full Lie
centralizers for all semisimple elements force geometric nilpotence. -/
theorem isNilpotentGroupScheme_of_semisimpleCentralizers_eq_top_of_charZero
    [CharZero k] [IsAlgClosed k]
    (hG : ∀ X : lieKernel G k, Lie.IsSemisimpleElement G X →
      Lie.elementCentralizerLie G X = ⊤) :
    IsNilpotentGroupScheme G := by
  obtain ⟨T, i, hi⟩ := TorusExistence.exists_isMaximalTorus G
  have hT := hi.1.isSplitTorus_of_finiteGaloisSplitting torusFiniteGaloisSplitting
  apply hi.isNilpotentGroupScheme_of_isCentral_of_isAlgClosed
  apply hT.isCentral_of_tangentCentralizers_eq_top
  intro X
  exact hG _ ((Lie.isSemisimpleElement_of_isSplitTorus hT X).map i)

/-- The characteristic-zero geometric nilpotence criterion, at every universe. -/
def CharZeroSemisimpleCentralNilpotenceStatement : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] [IsAlgClosed k]
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] [Smooth G.X.hom] [ConnectedSpace G.X.left],
    (∀ X : lieKernel G k, Lie.IsSemisimpleElement G X →
      Lie.elementCentralizerLie G X = ⊤) → IsNilpotentGroupScheme G

theorem charZeroSemisimpleCentralNilpotence :
    CharZeroSemisimpleCentralNilpotenceStatement.{u} := by
  intro k _ _ _ G _ _ _ hG
  exact isNilpotentGroupScheme_of_semisimpleCentralizers_eq_top_of_charZero hG

end Langlands.GroupScheme
