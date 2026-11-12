import Langlands.Representation.Intertwining.ComaximalRestriction
import Langlands.Representation.Exponents.LeviFrobeniusReciprocityProof
import Langlands.Representation.LanglandsClassification.LanglandsTripletRegularityStatement

/-! # The dimension consequence of regularity and the identity support piece -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G : GroupScheme (Spec (CommRingCat.of k))} (hG : IsConnectedReductive G)
  [IsAffineHom G.X.hom]

local instance dimensionAmbientPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  {P M N Q U : GroupScheme (Spec (CommRingCat.of k))}
  (p : P ⟶ G) (l : M ⟶ P) (r : N ⟶ P)
  (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
  (hr : LeviSubgroup.IsGeometricUnipotentRadical r) (hmul : IsIso (subgroupMultiplication l r))
  (q : Q ⟶ G) (lQ : M ⟶ Q) (rQ : U ⟶ Q)
  (hq : IsParabolicSubgroup q) (hlQ : IsRationalLeviSubgroup lQ)
  (hrQ : LeviSubgroup.IsGeometricUnipotentRadical rQ)
  (hmulQ : IsIso (subgroupMultiplication lQ rQ))
  {A : CommGroupScheme (Spec (CommRingCat.of k))} (a : A.toGrp ⟶ M)
  (ha : IsSplitComponent a)

/-- Frobenius reciprocity followed by restriction to the identity support image,
for a `PQ`-regular representation. -/
def pqRegularIntertwiningRestrictionEquiv
    (σ : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M))
    (hreg : IsPQRegular p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ a σ) :
    letI := leviPointTopology l hl
    (((leviInductionFunctor p l r hp hr hl hmul).obj σ).representation.IntertwiningMap
      ((leviInductionFunctor q lQ rQ hq hrQ hlQ hmulQ).obj σ).representation) ≃ₗ[ℂ]
    (((boundarySupportImage p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ
      (identityParabolicDoubleCoset p q)).obj σ).toRepresentation.IntertwiningMap
        σ.representation) := by
  letI := leviPointTopology l hl
  let F := (leviFrobeniusReciprocity k G hG Q M U q lQ rQ hq hlQ hrQ hmulQ
    ((leviInductionFunctor p l r hp hr hl hmul).obj σ) σ).choose
  exact F.trans (Intertwining.restrictionEquivOfComaximal
    ((boundarySupportImage p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ
      (identityParabolicDoubleCoset p q)).obj σ) (rationalPoints.map a)
    (fun b g => (Subgroup.mem_center_iff.mp
      (ha.isCentralSplitTorus.isCentral.map_mem_center b) g).symm) hreg)

include hG ha in
/-- The dimension conclusion follows from regularity and an identity-piece equivalence
for any admissible irreducible inducing representation. -/
theorem pqRegular_intertwining_finrank_eq_one
    (σ : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M))
    (hreg : IsPQRegular p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ a σ)
    (e : letI := leviPointTopology l hl
      ((boundarySupportImage p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ
        (identityParabolicDoubleCoset p q)).obj σ).toRepresentation.Equiv σ.representation)
    (hadm : letI := leviPointTopology l hl; σ.IsAdmissible)
    (hirr : letI := leviPointTopology l hl; σ.IsIrreducible) :
    Module.finrank ℂ
      (((leviInductionFunctor p l r hp hr hl hmul).obj σ).representation.IntertwiningMap
        ((leviInductionFunctor q lQ rQ hq hrQ hlQ hmulQ).obj σ).representation) = 1 := by
  let := leviPointTopology l hl
  obtain ⟨E⟩ := admissibleSchur_homEquiv σ.representation hadm hirr σ.representation
    (Representation.Equiv.refl σ.representation)
  let F := (pqRegularIntertwiningRestrictionEquiv hG p l r hp hl hr hmul q lQ rQ hq hlQ
    hrQ hmulQ a ha σ hreg).trans ((Intertwining.endomorphismEquiv e).trans E)
  exact F.finrank_eq.trans (Module.finrank_self ℂ)

end Langlands.Aubert.General.RepresentedParabolic
