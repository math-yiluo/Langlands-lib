import Langlands.Geometry.Analytic.OriginalDomainTopology
import Mathlib.CategoryTheory.Sites.Canonical

/-! # Representable sheaves on fixed-original-chart domains -/

noncomputable section

universe u v w

namespace Langlands.Analytic.IndexedAffinoidAtlas.OriginalChartDomain

open CategoryTheory

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Type v} [TopologicalSpace X] {a : IndexedAffinoidAtlas.{u, v, w} K X}
  {S T : OriginalChartDomain a}

/-- Inclusion in a fixed target can be checked on the actual members of a
covering sieve. The proof uses the point witnesses of the quasinet cover. -/
theorem IsCovering.le_of_locally_le {R : Sieve S} (hR : IsCovering R)
    (hT : ∀ (V : OriginalChartDomain a) (hVS : V ≤ S),
      R (homOfLE hVS) → V ≤ T) :
    S ≤ T := by
  intro x hx
  obtain ⟨V, hVS, hRV, hxV⟩ := hR.exists_mem hx
  exact hT V hVS hRV hxV

/-- Every representable on the domain inclusion category is a sheaf.
Its local sections are inclusions, which glue by actual point coverage. -/
theorem isSheaf_yoneda_obj (T : OriginalChartDomain a) :
    Presieve.IsSheaf (quasinetTopology a) (yoneda.obj T) := by
  intro S R hR s _
  have hST : S ≤ T := hR.le_of_locally_le fun V hVS hRV =>
    leOfHom (s (homOfLE hVS) hRV)
  refine ⟨homOfLE hST, ?_, ?_⟩
  · intro V f hf
    exact Subsingleton.elim (α := V ⟶ T) _ _
  · intro t ht
    exact Subsingleton.elim (α := S ⟶ T) _ _

/-- The quasinet topology is subcanonical on the fixed domain category. -/
instance quasinetTopology_subcanonical :
    (quasinetTopology a).Subcanonical :=
  GrothendieckTopology.Subcanonical.of_isSheaf_yoneda_obj _
    isSheaf_yoneda_obj

/-- The Yoneda functor of actual domains takes values in sheaves for their
constructed quasinet topology. -/
def domainYoneda (a : IndexedAffinoidAtlas.{u, v, w} K X) :
    OriginalChartDomain a ⥤ Sheaf (quasinetTopology a) (Type v) :=
  (quasinetTopology a).yoneda

end Langlands.Analytic.IndexedAffinoidAtlas.OriginalChartDomain
