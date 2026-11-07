import Langlands.Representation.CuspidalSupport.RationalInertiaDecompositionStatement
import Langlands.Representation.CuspidalSupport.RationalNormKernelFiniteRestrictionStatement
import Langlands.Representation.CuspidalSupport.RationalNormKernelOrbitTwistStatement
import Langlands.Representation.CuspidalSupport.OpenNormalFamilyProjector

/-!
# The compact-restriction inertia decomposition from Renard VI.3.2(ii),(iii)

The published finite-restriction and twist-equivalence statements for the
actual common norm kernel imply the compact-restriction inertia decomposition.
The finite spanning family of the restriction of `π` selects a natural ambient
projector; its identity action on an irreducible object is exactly membership
in the inertia class of `π`.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry Topology
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.CuspidalSupport

universe uF uV uG uW uU

/-- The compact-restriction inertia decomposition follows from the published
VI.3.2(ii) finite-restriction and VI.3.2(iii) twist-equivalence statements. -/
theorem rationalCompactRestrictionInertiaDecomposition_of_normKernel
    (hfin : RationalNormKernelFiniteRestrictionStatement.{uF, uV})
    (htw : RationalNormKernelTwistEquivalenceStatement.{uF, uV, uV}) :
    RationalCompactRestrictionInertiaDecompositionStatement.{uF, uV} := by
  intro F _ _ _ _ G hG
  have := hG.isAffineHom
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have := hG.smooth
  let : TopologicalSpace (GroupScheme.rationalPoints G) := rationalPointTopology F G.X
  intro _ _ _ π hπ hc
  let N := Plancherel.rationalCommonNormKernel G
  -- the finite spanning family of the restriction, from VI.3.2(ii)
  obtain ⟨-, -, m, W, hWirr, hWspan⟩ := hfin F G hG π hπ
  have hP : rationalInertiaDecompositionProperties G π =
      SmoothRep.irreducibleSubquotientProperties (IsRationalInertiaRelated G π) := by
    funext b
    cases b <;> rfl
  change Renard.IsCategoryDecomposition (rationalInertiaDecompositionProperties G π)
  rw [hP]
  refine openNormalFamily_categoryDecomposition N (Plancherel.isOpen_rationalCommonNormKernel G)
    π hc W hWirr hWspan _ fun D hD => ?_
  -- nonzero restricted intertwiners are unramified twists, by VI.3.2(iii)
  have h3 := htw F G hG D π hD hπ
  refine (h3.2.symm.trans h3.1).trans ⟨?_, ?_⟩
  · rintro ⟨χ, ⟨i⟩⟩
    exact IsRationalInertiaRelated.symm
      ⟨χ, ⟨(SmoothRep.mkIso (A := rationalUnramifiedTwist G χ D) (B := π) i).symm⟩⟩
  · intro h
    obtain ⟨χ, ⟨i⟩⟩ := h.symm
    exact ⟨χ, ⟨SmoothRep.equivOfIso i.symm⟩⟩

end Langlands.CuspidalSupport
