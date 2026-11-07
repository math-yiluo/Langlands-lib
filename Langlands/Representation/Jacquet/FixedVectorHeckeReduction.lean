import Langlands.Representation.Jacquet.FixedVectorHeckeEquivalence
import Langlands.Representation.Jacquet.StandardFixedVectorHeckeEquivalenceStatement
import Langlands.Representation.Jacquet.StandardFixedVectorSubquotientGenerationStatement
import Langlands.Representation.Classification.SupercuspidalSupport
import Langlands.AlgebraicGeometry.PointTopology.RationalPointHaarProof

/-! # The Hecke equivalence from the fixed-vector subquotient Corollary -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.BruhatTits.SpecialCompact

universe uG uF uV

namespace Langlands.Jacquet

section General

variable {G : Type uG} [Group G] [TopologicalSpace G]

/-- The actual fixed-vector generation property is inherited by every smooth subquotient. -/
def fixedVectorSubquotientClosed (K : Subgroup G) : Prop :=
  ∀ V : SmoothRep.{0,uG,uV} ℂ G, fixedVectorGenerated K V →
    ∀ D : SmoothRep.{0,uG,uV} ℂ G, SmoothRep.IsSubquotient D V →
      fixedVectorGenerated K D

/-- The subquotient assertion in particular supplies categorical subobject closure. -/
theorem fixedVectorGenerated_subobjectClosure (K : Subgroup G)
    (h : fixedVectorSubquotientClosed.{uG,uV} K) :
    (fixedVectorGenerated.{uG,uV} K).IsClosedUnderSubobjects where
  prop_of_mono f _ hV := h _ hV _
    (SmoothRep.IsSubrepresentation.isSubquotient
      ⟨f, (SmoothRep.mono_iff_injective f).mp inferInstance⟩)

variable [IsTopologicalGroup G] [SecondCountableTopology G]

/-- An open coset quotient is countable, hence small in any chosen carrier universe. -/
theorem secondCountable_openQuotient_small (K : OpenSubgroup G) :
    Small.{uV} (G ⧸ K.toSubgroup) := by
  let : DiscreteTopology (G ⧸ K.toSubgroup) :=
    QuotientGroup.discreteTopology K.isOpen
  let : Countable (G ⧸ K.toSubgroup) :=
    TopologicalSpace.separableSpace_iff_countable.mp inferInstance
  obtain ⟨f, hf⟩ := exists_injective_nat (G ⧸ K.toSubgroup)
  exact small_of_injective hf

end General

/-- The exact VI.9.4 Corollary implies the exact VI.9.4 Hecke equivalence,
without an extra size or structural hypothesis. -/
theorem standardFixedVectorHeckeEquivalence_of_subquotientGeneration
    (h : StandardFixedVectorSubquotientGenerationStatement.{uF,uV}) :
    StandardFixedVectorHeckeEquivalenceStatement.{uF,uV} := by
  intro F _ _ _ _ G hG
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : Smooth G.X.hom := hG.smooth
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  let : IsTopologicalGroup (rationalPoints G) := rationalPoint_isTopologicalGroup F G
  intro S i hi ν hν hstandard K₀ hK₀ hIwasawa K hK hKK₀ hnormal hIwahori
  let : SecondCountableTopology (rationalPoints G) :=
    rationalPoint_secondCountableTopology F G
  let : Small.{uV} (rationalPoints G ⧸ K.toSubgroup) :=
    secondCountable_openQuotient_small K
  let : (fixedVectorGenerated.{uF,uV} K.toSubgroup).IsClosedUnderSubobjects :=
    fixedVectorGenerated_subobjectClosure K.toSubgroup
      (fun V hV D hD =>
        h F G hG S i hi ν hν hstandard K₀ hK₀ hIwasawa K hK hKK₀ hnormal
          hIwahori V hV D hD)
  exact fixedVectorHecke_isEquivalence K hK

end Langlands.Jacquet
