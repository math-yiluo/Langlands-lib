import Langlands.Representation.CompactCoefficient.AmbientProjector
import Langlands.Representation.CuspidalSupport.NaturalProjectorDecomposition

/-!
# Conditional decomposition from compact coefficients on a normal subgroup

The analytic hypotheses (intrinsic complements, finite strata, compactness of
the total isotypic part, and exhaustion of compact objects) remain explicit.
-/

noncomputable section

namespace Langlands

universe uG uV

namespace SmoothRep

variable {G : Type uG} [Group G] [TopologicalSpace G]

/-- An actual ambient invariant subspace, viewed as a subrepresentation of
restriction to a subgroup. Its underlying submodule is unchanged. -/
def restrictSubrepresentation (N : Subgroup G)
    {A : SmoothRep.{0, uG, uV} ℂ G} (S : Subrepresentation A.representation) :
    Subrepresentation (restrictSubgroup N A).representation where
  toSubmodule := S.toSubmodule
  apply_mem_toSubmodule n := S.apply_mem_toSubmodule n.val

end SmoothRep

namespace CompactCoefficientClass

open CategoryTheory

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (N : Subgroup G) [N.Normal]
  [NonarchimedeanGroup N] [WeaklyLocallyCompactSpace N]
  (hsplit : ∀ (c : CompactCoefficientClass.{uG, uV} N)
    (D : SmoothRep.{0, uG, uV} ℂ N),
    IsCompl (isotypicSubrepresentation c D).toSubmodule
      (annihilatorSubrepresentation c D).toSubmodule)
  (hstrata : ∀ K : OpenSubgroup N, IsCompact (K : Set N) →
    (fixedStratum.{uG, uV} K.toSubgroup).Finite)

/-- The actual ambient projector constructed from intrinsic complements on the
normal subgroup and finite fixed-level strata. -/
def normalSubgroupProjector (A : SmoothRep.{0, uG, uV} ℂ G) :
    A.representation.IntertwiningMap A.representation :=
  let D := SmoothRep.restrictSubgroup N A
  let P := fun c => isotypicProjectorOfIsCompl c (hsplit c D)
  ambientTotalProjector N P
    (finiteSupport_of_finite_fixedStratum P
      (fun c => (isotypicProjectorOfIsCompl_ker c (hsplit c D)).symm.le) hstrata)
    (fun c => isotypicProjectorOfIsCompl_idempotent c (hsplit c D))
    (fun c => isotypicProjectorOfIsCompl_range c (hsplit c D))
    (fun c => isotypicProjectorOfIsCompl_ker c (hsplit c D))

omit [IsTopologicalGroup G] [N.Normal] [NonarchimedeanGroup N]
  [WeaklyLocallyCompactSpace N] in
private theorem components_orthogonal (D : SmoothRep.{0, uG, uV} ℂ N)
    (c d : CompactCoefficientClass.{uG, uV} N) (hcd : c ≠ d) (v : D) :
    isotypicProjectorOfIsCompl c (hsplit c D)
      (isotypicProjectorOfIsCompl d (hsplit d D) v) = 0 :=
  congrArg (fun f : D.representation.IntertwiningMap D.representation => f v)
    (isotypicProjectorFamilyOfIsCompl_orthogonal hsplit hcd.symm D)

theorem normalSubgroupProjector_idempotent
    (A : SmoothRep.{0, uG, uV} ℂ G) (v : A) :
    normalSubgroupProjector N hsplit hstrata A
      (normalSubgroupProjector N hsplit hstrata A v) =
      normalSubgroupProjector N hsplit hstrata A v :=
  ambientTotalProjector_idempotent N _ _ (fun c => isotypicProjectorOfIsCompl_idempotent c
      (hsplit c (SmoothRep.restrictSubgroup N A)))
    (fun c => isotypicProjectorOfIsCompl_range c
      (hsplit c (SmoothRep.restrictSubgroup N A)))
    (fun c => isotypicProjectorOfIsCompl_ker c
      (hsplit c (SmoothRep.restrictSubgroup N A)))
    (components_orthogonal N hsplit (SmoothRep.restrictSubgroup N A)) v

theorem normalSubgroupProjector_range (A : SmoothRep.{0, uG, uV} ℂ G) :
    SmoothRep.restrictSubrepresentation N
      (normalSubgroupProjector N hsplit hstrata A).range =
      totalIsotypicSubrepresentation.{uG, uV} (SmoothRep.restrictSubgroup N A) := by
  apply Subrepresentation.toSubmodule_injective
  exact ambientTotalProjector_range N _ _ (fun c => isotypicProjectorOfIsCompl_idempotent c
      (hsplit c (SmoothRep.restrictSubgroup N A)))
    (fun c => isotypicProjectorOfIsCompl_range c
      (hsplit c (SmoothRep.restrictSubgroup N A)))
    (fun c => isotypicProjectorOfIsCompl_ker c
      (hsplit c (SmoothRep.restrictSubgroup N A)))
    (components_orthogonal N hsplit (SmoothRep.restrictSubgroup N A))

theorem normalSubgroupProjector_natural
    (A B : SmoothRep.{0, uG, uV} ℂ G)
    (f : A.representation.IntertwiningMap B.representation) (v : A) :
    normalSubgroupProjector N hsplit hstrata B (f v) =
      f (normalSubgroupProjector N hsplit hstrata A v) :=
  ambientTotalProjectors_natural N _ _ (fun c => isotypicProjectorOfIsCompl_idempotent c
      (hsplit c (SmoothRep.restrictSubgroup N A)))
    (fun c => isotypicProjectorOfIsCompl_range c
      (hsplit c (SmoothRep.restrictSubgroup N A)))
    (fun c => isotypicProjectorOfIsCompl_ker c
      (hsplit c (SmoothRep.restrictSubgroup N A)))
    _ _ (fun c => isotypicProjectorOfIsCompl_idempotent c
      (hsplit c (SmoothRep.restrictSubgroup N B)))
    (fun c => isotypicProjectorOfIsCompl_range c
      (hsplit c (SmoothRep.restrictSubgroup N B)))
    (fun c => isotypicProjectorOfIsCompl_ker c
      (hsplit c (SmoothRep.restrictSubgroup N B))) f v

/-- If compact objects are exhausted by their intrinsic total isotypic part,
the ambient projector fixes every object whose restriction is compact. -/
theorem normalSubgroupProjector_eq_self
    (hexhaust : ∀ D : SmoothRep.{0, uG, uV} ℂ N,
      HasCompactSmoothDualCoefficients D.representation →
        totalIsotypicSubrepresentation.{uG, uV} D = ⊤)
    (A : SmoothRep.{0, uG, uV} ℂ G)
    (hA : HasCompactSmoothDualCoefficients (SmoothRep.restrictSubgroup N A).representation)
    (v : A) : normalSubgroupProjector N hsplit hstrata A v = v := by
  have hv : v ∈ (normalSubgroupProjector N hsplit hstrata A).range := by
    change v ∈ SmoothRep.restrictSubrepresentation N
      (normalSubgroupProjector N hsplit hstrata A).range
    rw [normalSubgroupProjector_range, hexhaust _ hA]
    trivial
  obtain ⟨w, rfl⟩ := hv
  exact normalSubgroupProjector_idempotent N hsplit hstrata A w

include hsplit hstrata in
/-- Assemble the actual ambient invariant decomposition, keeping all four
analytic inputs explicit. The complement has no nonzero subquotient whose
restriction has compact smooth-dual coefficients. -/
theorem decomposition_of_normalSubgroup_compactCoefficients
    (hcompact : ∀ D : SmoothRep.{0, uG, uV} ℂ N,
      HasCompactSmoothDualCoefficients
        (totalIsotypicSubrepresentation.{uG, uV} D).toRepresentation)
    (hexhaust : ∀ D : SmoothRep.{0, uG, uV} ℂ N,
      HasCompactSmoothDualCoefficients D.representation →
        totalIsotypicSubrepresentation.{uG, uV} D = ⊤)
    (A : SmoothRep.{0, uG, uV} ℂ G) :
    ∃ S Q : Subrepresentation A.representation,
      IsCompl S.toSubmodule Q.toSubmodule ∧
      HasCompactSmoothDualCoefficients
        (SmoothRep.restrictSubgroup N (SmoothRep.subrepresentation A S)).representation ∧
      ∀ D : SmoothRep.{0, uG, uV} ℂ G,
        SmoothRep.IsSubquotient D (SmoothRep.subrepresentation A Q) →
        HasCompactSmoothDualCoefficients (SmoothRep.restrictSubgroup N D).representation →
        Subsingleton D := by
  apply SmoothRep.decomposition_of_natural_idempotent
    (fun D => HasCompactSmoothDualCoefficients (SmoothRep.restrictSubgroup N D).representation)
    (normalSubgroupProjector N hsplit hstrata)
    (fun D E f v => normalSubgroupProjector_natural N hsplit hstrata D E (SmoothRep.hom f) v)
    (normalSubgroupProjector_idempotent N hsplit hstrata)
    ?_ (normalSubgroupProjector_eq_self N hsplit hstrata hexhaust) A
  intro D
  change HasCompactSmoothDualCoefficients
    (SmoothRep.restrictSubrepresentation N
      (normalSubgroupProjector N hsplit hstrata D).range).toRepresentation
  rw [normalSubgroupProjector_range]
  exact hcompact (SmoothRep.restrictSubgroup N D)

end CompactCoefficientClass
end Langlands
