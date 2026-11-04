import Langlands.Representation.Plancherel.AmbientCharacterFormNaturality
import Langlands.Representation.Plancherel.CharacterIntertwiningCone

/-! # Character threshold regions from one ambient Weyl form -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Plancherel

section Form

variable {k : Type u} [Field k]
  {A T : CommGroupScheme (Spec (CommRingCat.of k))}
  (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus T.toGrp)
  (f : A ⟶ T) [Mono (CommGroupScheme.groupHom f).hom.hom.left]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  (i : T.toGrp ⟶ G) [Mono i.hom.hom.left] [Fintype (relativeWeylGroup i)]

/-- Strict positivity discharges nondegeneracy of the constructed local form. -/
theorem weylInducedCharacterForm_nondegenerate :
    (weylInducedCharacterForm hA hT f i).Nondegenerate := by
  constructor
  · intro x hx
    by_contra h
    exact (ne_of_gt (weylInducedCharacterForm_pos hA hT f i h)) (hx x)
  · intro x hx
    by_contra h
    exact (ne_of_gt (weylInducedCharacterForm_pos hA hT f i h)) (hx x)

/-- Each local inequality is exactly an ambient inequality at the constructed
orthogonal lift; no independently chosen local metric is used. -/
theorem weylInducedCharacterForm_root_inequality_iff
    (x : RealTorusSpace.Vstar A) (beta : characterLattice T) (R : ℝ) :
    R < RealTorusSpace.relativeWeylInvariantForm i hT
        (weylCharacterRestrictionLift hA hT f i x) ((1 : ℝ) ⊗ₜ[ℤ] beta) ↔
      R < weylInducedCharacterForm hA hT f i x
        ((1 : ℝ) ⊗ₜ[ℤ] characterRestrict (CommGroupScheme.groupHom f) beta) :=
  (weylInducedCharacterForm_compatible hA hT f i).root_inequality_iff x beta R

end Form

section Characters

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {A T : CommGroupScheme (Spec (CommRingCat.of F))}
  (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus T.toGrp)
  (f : A ⟶ T) [Mono (CommGroupScheme.groupHom f).hom.hom.left]
  {M G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G) [Mono i.hom.hom.left] [Fintype (relativeWeylGroup i)]
  [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom]

local instance instAmbientCharacterIntertwiningCone1 : TopologicalSpace (rationalPoints M) :=
  rationalPointTopology F M.X

/-- The existing continuous unramified-character region with its local form
constructed from the single ambient relative Weyl form. -/
def weylUnramifiedIntertwiningRegion (j : A.toGrp ⟶ M)
    (U Uop' : SubgroupFunctor G) (R : ℝ) :
    Set (unramifiedCharacters (fun chi => (rationalNormCharacters M chi).toMul)) :=
  canonicalUnramifiedIntertwiningRegion hA j (CommGroupScheme.groupHom f ≫ i)
    (weylInducedCharacterForm hA hT f i) U Uop' R

/-- Every dynamic threshold contains a canonical continuous character arising
from a positive character of the actual valuation image. -/
theorem exists_positiveImageCharacter_mem_weylUnramifiedIntertwiningRegion_dynamic
    [Smooth G.X.hom] (j : A.toGrp ⟶ M)
    (hM : IsConnectedReductive M) (hj : IsSplitComponent j)
    (nu eta : cocharacterLattice A) (R : ℝ) :
    ∃ psi : rationalImageRealFunctionals M,
      rationalCanonicalImageUnramifiedContinuousEquiv M
        (rationalImagePositiveCharacter M psi) ∈
          weylUnramifiedIntertwiningRegion hA hT f i j
            (Dynamic.unipotent
              (CommGroupScheme.groupHom nu ≫ (CommGroupScheme.groupHom f ≫ i)))
            (Dynamic.unipotent
              (CommGroupScheme.groupHom (-eta) ≫ (CommGroupScheme.groupHom f ≫ i))) R := by
  obtain ⟨psi, hpsi⟩ := exists_positiveImageCharacter_mem_intertwiningRegion_dynamic
    hA j hM hj (CommGroupScheme.groupHom f ≫ i)
    (weylInducedCharacterForm hA hT f i)
    (weylInducedCharacterForm_nondegenerate hA hT f i) nu eta R
  exact ⟨psi, hpsi⟩

theorem weylUnramifiedIntertwiningRegion_dynamic_nonempty
    [Smooth G.X.hom] (j : A.toGrp ⟶ M)
    (hM : IsConnectedReductive M) (hj : IsSplitComponent j)
    (nu eta : cocharacterLattice A) (R : ℝ) :
    (weylUnramifiedIntertwiningRegion hA hT f i j
      (Dynamic.unipotent
        (CommGroupScheme.groupHom nu ≫ (CommGroupScheme.groupHom f ≫ i)))
      (Dynamic.unipotent
        (CommGroupScheme.groupHom (-eta) ≫ (CommGroupScheme.groupHom f ≫ i))) R).Nonempty := by
  obtain ⟨psi, hpsi⟩ :=
    exists_positiveImageCharacter_mem_weylUnramifiedIntertwiningRegion_dynamic
      hA hT f i j hM hj nu eta R
  exact ⟨rationalCanonicalImageUnramifiedContinuousEquiv M
    (rationalImagePositiveCharacter M psi), hpsi⟩

end Characters

end Langlands.Plancherel
