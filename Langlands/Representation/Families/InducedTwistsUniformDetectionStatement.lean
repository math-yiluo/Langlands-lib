import Langlands.Representation.Families.RenardGenericIrreducibilityStatements
import Langlands.Representation.Smooth.FixedVectors.Definitions
import Langlands.Representation.Category.Subquotients

/-! # A single compact open subgroup detecting every induced twist -/

noncomputable section

set_option autoImplicit false

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Renard.AlgebraicFamily

open Langlands.Aubert.General Langlands.Aubert.General.RepresentedParabolic GroupScheme

/-- Uniform detection used in the proof of Renard VI.8.4: one compact open
subgroup has nonzero fixed vectors in every irreducible actual subquotient of
every unramified twist induced from the given irreducible Levi representation. -/
def InducedTwistsUniformDetectionStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (P M U : GroupScheme (Spec (CommRingCat.of k)))
      (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
      (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
      (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
      (hmul : IsIso (subgroupMultiplication l r)),
      haveI := hl.isConnectedReductive.isAffineHom
      letI : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
      haveI : LocallyCompactSpace (rationalPoints M) := leviPoints_locallyCompactSpace p l hp hl
      haveI : NonarchimedeanGroup (rationalPoints M) := leviPoints_nonarchimedeanGroup p l hp hl
      ∀ ρ : SmoothRep.{0, u, v} ℂ (rationalPoints M), ρ.IsIrreducible →
        ∃ K : OpenSubgroup (rationalPoints G), IsCompact (K : Set (rationalPoints G)) ∧
          ∀ ψ : Plancherel.unramifiedCharacters
              (fun χ : rationalCharacters M => (Plancherel.rationalNormCharacters M χ).toMul),
            ∀ D : SmoothRep.{0, u, max u v} ℂ (rationalPoints G),
              D.IsIrreducible →
              SmoothRep.IsSubquotient D
                ((leviInductionFunctor p l r hp hr hl hmul).obj
                  (ρ.twist ψ.val.toMonoidHom
                    (Plancherel.unramifiedCharacter_isOpen_ker _ ψ))) →
              ∃ w : D, w ∈ fixedVectors D.representation K.toSubgroup ∧ w ≠ 0

end Langlands.Renard.AlgebraicFamily
