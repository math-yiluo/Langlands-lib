import Langlands.Representation.Plancherel.RationalNormKernelTopology
import Langlands.Representation.Plancherel.UnramifiedCharacters
import Langlands.Representation.CompactCoefficient.AmbientProjector
import Langlands.Representation.Twist.Definitions
import Langlands.Representation.Category.Basic

/-!
# Renard VI.3.2(i) and (iii) on the actual norm kernel

The subgroup is the actual common kernel of the normalized rational-character
norms, and every restriction keeps the original carrier. The orbit uses the
existing inverse conjugation `h ↦ g⁻¹ * h * g`. The twist uses the existing
unramified characters and the actual scalar twist. Neither proposition is
proved here.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.CuspidalSupport

universe u uV uW

/-- Renard VI.3.2(i): the restriction of an irreducible smooth representation
to the actual norm kernel has an irreducible subrepresentation, every inverse
conjugate of an occurring irreducible type occurs again, and any two
irreducible subrepresentations are related by inverse conjugation by a point. -/
def RationalNormKernelOrbitStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : GroupScheme.IsConnectedReductive G),
    haveI := hG.isAffineHom
    haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    haveI := hG.smooth
    letI : TopologicalSpace (GroupScheme.rationalPoints G) := rationalPointTopology F G.X
    letI : IsTopologicalGroup (GroupScheme.rationalPoints G) :=
      rationalPoint_isTopologicalGroup F G
    ∀ π : SmoothRep.{0, u, uV} ℂ (GroupScheme.rationalPoints G),
      π.IsIrreducible →
      (∃ W : Subrepresentation
          (π.representation.comp (Plancherel.rationalCommonNormKernel G).subtype),
        W.toRepresentation.IsIrreducible) ∧
      (∀ W : Subrepresentation
          (π.representation.comp (Plancherel.rationalCommonNormKernel G).subtype),
        W.toRepresentation.IsIrreducible → ∀ g : GroupScheme.rationalPoints G,
        ∃ W' : Subrepresentation
            (π.representation.comp (Plancherel.rationalCommonNormKernel G).subtype),
          W'.toRepresentation.IsIrreducible ∧
            Nonempty (Representation.Equiv
              (W.toRepresentation.comp
                (SmoothRep.normalSubgroupInverseConjugation
                  (Plancherel.rationalCommonNormKernel G) g).toMonoidHom)
              W'.toRepresentation)) ∧
      ∀ W₁ W₂ : Subrepresentation
          (π.representation.comp (Plancherel.rationalCommonNormKernel G).subtype),
        W₁.toRepresentation.IsIrreducible → W₂.toRepresentation.IsIrreducible →
        ∃ g : GroupScheme.rationalPoints G,
          Nonempty (Representation.Equiv
            (W₁.toRepresentation.comp
              (SmoothRep.normalSubgroupInverseConjugation
                (Plancherel.rationalCommonNormKernel G) g).toMonoidHom)
            W₂.toRepresentation)

/-- Renard VI.3.2(iii): for irreducible smooth representations, isomorphic
restrictions to the actual norm kernel are equivalent to an isomorphism after an
unramified scalar twist, and to a nonzero restricted intertwiner. -/
def RationalNormKernelTwistEquivalenceStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : GroupScheme.IsConnectedReductive G),
    haveI := hG.isAffineHom
    haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    haveI := hG.smooth
    letI : TopologicalSpace (GroupScheme.rationalPoints G) := rationalPointTopology F G.X
    ∀ (π₁ : SmoothRep.{0, u, uV} ℂ (GroupScheme.rationalPoints G))
      (π₂ : SmoothRep.{0, u, uW} ℂ (GroupScheme.rationalPoints G)),
      π₁.IsIrreducible → π₂.IsIrreducible →
      (Nonempty (Representation.Equiv
          (π₁.representation.comp (Plancherel.rationalCommonNormKernel G).subtype)
          (π₂.representation.comp (Plancherel.rationalCommonNormKernel G).subtype)) ↔
        ∃ χ : Plancherel.unramifiedCharacters
            (fun χ => (Plancherel.rationalNormCharacters G χ).toMul),
          Nonempty (Representation.Equiv
            (Langlands.twist χ.val.toMonoidHom π₁.representation) π₂.representation)) ∧
      (Nonempty (Representation.Equiv
          (π₁.representation.comp (Plancherel.rationalCommonNormKernel G).subtype)
          (π₂.representation.comp (Plancherel.rationalCommonNormKernel G).subtype)) ↔
        ∃ f : Representation.IntertwiningMap
            (π₁.representation.comp (Plancherel.rationalCommonNormKernel G).subtype)
            (π₂.representation.comp (Plancherel.rationalCommonNormKernel G).subtype),
          f ≠ 0)

end Langlands.CuspidalSupport
