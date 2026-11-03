import Langlands.Representation.Category.Subquotients
import Mathlib.Data.Complex.Basic

/-! # Shared finite-length helpers for smooth representations

These declarations retain their published names and statements after extraction
from the classification and highest-derivative modules.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

universe uG uV uW

namespace Langlands.Classification.SegmentHeadSupport

variable {G : Type uG} [Group G] [TopologicalSpace G]

/-- A nonzero finite-length smooth representation has an irreducible quotient
(the quotient by a coatom of its Noetherian lattice of submodules; the argument
of `SmoothRep.exists_irreducible_quotient_subquotient_of_nonzero`). -/
theorem exists_irreducible_quotient {A : SmoothRep.{0, uG, uV} ℂ G}
    (hA : A.HasFiniteLength) [Nontrivial A] :
    ∃ C : SmoothRep.{0, uG, uV} ℂ G, C.IsIrreducible ∧
      ∃ q : A ⟶ C, Function.Surjective (SmoothRep.hom q) := by
  have : IsNoetherian (MonoidAlgebra ℂ G) A.representation.asModule :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hA).1
  let : Nontrivial A.representation.asModule := ‹Nontrivial A›
  obtain ⟨N, hN⟩ :=
    IsCoatomic.exists_coatom (α := Submodule (MonoidAlgebra ℂ G) A.representation.asModule)
  let S : Subrepresentation A.representation := Subrepresentation.ofSubmodule' N
  let C := SmoothRep.quotient A S
  let r : A ⟶ C := SmoothRep.mkQ A S
  let rg := Representation.IntertwiningMap.equivLinearMapAsModule _ _ (SmoothRep.hom r)
  have hrg : Function.Surjective rg := SmoothRep.mkQ_surjective A S
  have hker : rg.ker = N := by
    ext v
    change Submodule.Quotient.mk v = (0 : A ⧸ S.toSubmodule) ↔ v ∈ N
    exact Submodule.Quotient.mk_eq_zero _
  have hsimp : IsSimpleModule (MonoidAlgebra ℂ G) (A.representation.asModule ⧸ rg.ker) := by
    apply isSimpleModule_iff_isCoatom.mpr
    rwa [hker]
  have hCsimp : IsSimpleModule (MonoidAlgebra ℂ G) C.representation.asModule :=
    IsSimpleModule.congr (rg.quotKerEquivOfSurjective hrg).symm
  exact ⟨C, (Representation.irreducible_iff_isSimpleModule_asModule _).mpr hCsimp, r, hrg⟩

end Langlands.Classification.SegmentHeadSupport

namespace Langlands.Aubert.ZelevinskyHighestDerivative

/-- An injective morphism of smooth representations transfers finite length
from its target to its source. -/
theorem hasFiniteLength_of_injective {G : Type uG} [Group G] [TopologicalSpace G]
    {A B : SmoothRep.{0, uG, uW} ℂ G} (f : A ⟶ B) (hf : Function.Injective (SmoothRep.hom f))
    (hB : B.HasFiniteLength) : A.HasFiniteLength :=
  IsFiniteLength.of_injective hB
    (f := Representation.IntertwiningMap.equivLinearMapAsModule _ _ (SmoothRep.hom f)) hf

end Langlands.Aubert.ZelevinskyHighestDerivative
