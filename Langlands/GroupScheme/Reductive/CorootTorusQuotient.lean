import Langlands.GroupScheme.Torus.CorootCharacterComparison
import Langlands.GroupScheme.Torus.DiagonalizableFaithfullyFlat
import Langlands.GroupScheme.Torus.Relative
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.Algebra.Module.Projective

/-! # The split coroot torus quotient over a ring -/

noncomputable section
universe u v w

open CategoryTheory AlgebraicGeometry

namespace Langlands.RootDatum

variable {J : Type v} {X : Type u} {Y : Type w}
  [AddCommGroup X] [AddCommGroup Y]

/-- Evaluation on a selected family of coroots. -/
def corootEvaluation (P : RootDatum J X Y) (s : Set J) : X →ₗ[ℤ] (s → ℤ) :=
  LinearMap.pi fun a => P.toLinearMap.flip (P.coroot a)

@[simp]
theorem corootEvaluation_apply (P : RootDatum J X Y) (s : Set J) (x : X) (a : s) :
    corootEvaluation P s x a = P.toLinearMap x (P.coroot a) := rfl

/-- The annihilator is the kernel of evaluation on the coroot family. -/
theorem ker_corootEvaluation (P : RootDatum J X Y) (s : Set J) :
    (corootEvaluation P s).ker = corootAnnihilator P s := by
  ext x
  rw [LinearMap.mem_ker, mem_corootAnnihilator]
  exact ⟨fun h a ha => congrFun h ⟨a, ha⟩,
    fun h => funext fun a => h a a.property⟩

/-- The quotient by the coroot annihilator is free: it is the image of
coroot evaluation inside a finite free lattice. -/
theorem free_quotient_corootAnnihilator [Finite J] (P : RootDatum J X Y) (s : Set J) :
    Module.Free ℤ (X ⧸ corootAnnihilator P s) := by
  classical
  let := Fintype.ofFinite s
  rw [← ker_corootEvaluation P s]
  exact Module.Free.of_equiv (corootEvaluation P s).quotKerEquivRange.symm

end Langlands.RootDatum

namespace Langlands.GroupScheme.RelativeDerived

variable {I J : Type u} [Fintype I]

/-- Characters of the split maximal torus that annihilate every coroot. -/
abbrev cocenterLattice (P : RootDatum J (I → ℤ) (I → ℤ)) :=
  Langlands.RootDatum.corootAnnihilator P Set.univ

/-- The torus quotient's actual diagonalizable group scheme. -/
abbrev corootQuotient (R : CommRingCat.{u}) (P : RootDatum J (I → ℤ) (I → ℤ)) :
    CommGroupScheme (Spec R) :=
  Diagonalizable.groupScheme R (cocenterLattice P)

/-- The diagonalizable group on the coroot-annihilator lattice is a split torus. -/
theorem isSplitTorus_corootQuotient (R : CommRingCat.{u})
    (P : RootDatum J (I → ℤ) (I → ℤ)) : IsSplitTorus (corootQuotient R P).toGrp := by
  classical
  let b := Module.Free.chooseBasis ℤ (cocenterLattice P)
  exact Diagonalizable.isSplitTorus R b.equivFun.toAddEquiv

/-- The candidate cocenter torus is a relative torus over every coefficient ring. -/
theorem isTorus_corootQuotient (R : CommRingCat.{u})
    (P : RootDatum J (I → ℤ) (I → ℤ)) : RelativeTorus.IsTorus (corootQuotient R P).toGrp :=
  RelativeTorus.IsTorus.of_isSplitTorus (isSplitTorus_corootQuotient R P)

end Langlands.GroupScheme.RelativeDerived
