import Langlands.GroupScheme.Torus.RelativeMultiplicativeTypeTorsion

/-! # Actual finite torsion of relative multiplicative-type groups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.RelativeMultiplicativeType

variable {S S' : Scheme.{u}} {H : GroupScheme S}

/-- Positive torsion of a diagonalizable group retains a finite full character model. -/
theorem IsDiagonalizable.torsion [IsCommMonObj H.X] (hH : IsDiagonalizable H)
    (n : ℕ) (hn : 0 < n) : IsDiagonalizable (GroupScheme.torsion H (n : ℤ)) := by
  obtain ⟨M, _, _, ⟨e⟩⟩ := hH
  have : Finite (Diagonalizable.torsionCharacters M n) :=
    FiniteCharacterSeparation.finite_quotient hn.ne'
  exact ⟨Diagonalizable.torsionCharacters M n, inferInstance, inferInstance,
    ⟨torsionMapIso e (n : ℤ) ≪≫ diagonalizableTorsionIso S M n⟩⟩

/-- Actual natural torsion, using commutativity descended from the splitting cover. -/
def IsMultiplicativeType.torsion (hH : IsMultiplicativeType H) (n : ℕ) : GroupScheme S :=
  GroupScheme.torsion hH.commGroupScheme.toGrp (n : ℤ)

/-- The actual inclusion of the natural torsion subgroup scheme. -/
def IsMultiplicativeType.torsionι (hH : IsMultiplicativeType H) (n : ℕ) :
    hH.torsion n ⟶ H :=
  GroupScheme.torsionι hH.commGroupScheme.toGrp (n : ℤ)

/-- This construction is precisely the existing scheme-theoretic multiplication kernel. -/
theorem IsMultiplicativeType.torsion_eq_kernel (hH : IsMultiplicativeType H) (n : ℕ) :
    hH.torsion n = kernel (multiplication hH.commGroupScheme.toGrp (n : ℤ)) := rfl

/-- The inclusion is precisely the actual kernel inclusion. -/
theorem IsMultiplicativeType.torsionι_eq_kernelι (hH : IsMultiplicativeType H) (n : ℕ) :
    hH.torsionι n = kernelι (multiplication hH.commGroupScheme.toGrp (n : ℤ)) := rfl

/-- The torsion inclusion represents the power condition on every test scheme. -/
theorem IsMultiplicativeType.existsUnique_torsion_lift_iff
    (hH : IsMultiplicativeType H) (n : ℕ) (T : Over S) (x : T ⟶ H.X) :
    (∃! y : T ⟶ (hH.torsion n).X, y ≫ (hH.torsionι n).hom.hom = x) ↔ x ^ n = 1 := by
  simpa only [IsMultiplicativeType.torsion, IsMultiplicativeType.torsionι, zpow_natCast] using
    GroupScheme.existsUnique_torsion_lift_iff hH.commGroupScheme.toGrp (n : ℤ) T x

/-- The inclusion of torsion is a closed immersion over the original base. -/
theorem IsMultiplicativeType.torsionι_isClosedImmersion
    (hH : IsMultiplicativeType H) (n : ℕ) :
    IsClosedImmersion (hH.torsionι n).hom.hom.left := by
  let : IsSeparated hH.commGroupScheme.X.hom := hH.isSeparated
  exact GroupScheme.torsionι_isClosedImmersion hH.commGroupScheme.toGrp (n : ℤ)

/-- Positive torsion is again of relative multiplicative type. -/
theorem IsMultiplicativeType.torsion_isMultiplicativeType
    (hH : IsMultiplicativeType H) (n : ℕ) (hn : 0 < n) :
    IsMultiplicativeType (hH.torsion n) := by
  let : IsCommMonObj H.X := hH.isCommMonObj
  obtain ⟨𝒰, h𝒰⟩ := hH
  refine ⟨𝒰, fun i => ?_⟩
  exact IsDiagonalizable.of_iso (GroupScheme.torsionBaseChangeIso (𝒰.f i) H (n : ℤ))
    ((h𝒰 i).torsion n hn)

/-- Positive torsion is finite over an arbitrary base, with no invertibility hypothesis. -/
theorem IsMultiplicativeType.torsion_isFinite
    (hH : IsMultiplicativeType H) (n : ℕ) (hn : 0 < n) :
    IsFinite (hH.torsion n).X.hom := by
  let : IsCommMonObj H.X := hH.isCommMonObj
  exact (hH.torsion_geometry n hn).1

/-- The actual torsion construction commutes with arbitrary scheme base change. -/
def IsMultiplicativeType.torsionBaseChangeIso (hH : IsMultiplicativeType H)
    (b : S' ⟶ S) (n : ℕ) :
    (GroupScheme.baseChange b).obj (hH.torsion n) ≅ (hH.baseChange b).torsion n :=
  GroupScheme.torsionBaseChangeIso b hH.commGroupScheme.toGrp (n : ℤ)

/-- The base-change comparison preserves the actual subgroup inclusions. -/
@[reassoc (attr := simp)]
theorem IsMultiplicativeType.torsionBaseChangeIso_hom_ι (hH : IsMultiplicativeType H)
    (b : S' ⟶ S) (n : ℕ) :
    (hH.torsionBaseChangeIso b n).hom ≫ (hH.baseChange b).torsionι n =
      (GroupScheme.baseChange b).map (hH.torsionι n) :=
  GroupScheme.torsionBaseChangeIso_hom_ι b hH.commGroupScheme.toGrp (n : ℤ)

/-- The inverse comparison preserves the actual subgroup inclusions. -/
@[reassoc (attr := simp)]
theorem IsMultiplicativeType.torsionBaseChangeIso_inv_ι (hH : IsMultiplicativeType H)
    (b : S' ⟶ S) (n : ℕ) :
    (hH.torsionBaseChangeIso b n).inv ≫ (GroupScheme.baseChange b).map (hH.torsionι n) =
      (hH.baseChange b).torsionι n :=
  GroupScheme.torsionBaseChangeIso_inv_ι b hH.commGroupScheme.toGrp (n : ℤ)

end Langlands.GroupScheme.RelativeMultiplicativeType
