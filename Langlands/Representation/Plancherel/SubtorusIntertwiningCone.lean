import Langlands.GroupScheme.Rational.SubtorusIntertwiningRoots
import Langlands.Representation.Plancherel.AmbientCharacterIntertwiningCone

/-! # Complete dynamic threshold regions under split-torus restriction -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RelativeRoot
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Plancherel

section Forms

variable {k : Type u} [Field k]
  {A T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [Smooth G.X.hom]

/-- Exact root-image comparison turns compatible individual inequalities into
equivalence of the complete dynamic threshold regions. -/
theorem CompatibleCharacterForms.mem_intertwiningRegion_dynamic_iff
    {f : A ⟶ T}
    {B_A : LinearMap.BilinForm ℝ (RealTorusSpace.Vstar A)}
    {B_T : LinearMap.BilinForm ℝ (RealTorusSpace.Vstar T)}
    {L : RealTorusSpace.Vstar A →ₗ[ℝ] RealTorusSpace.Vstar T}
    (h : CompatibleCharacterForms f B_A B_T L)
    (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus T.toGrp)
    (i : T.toGrp ⟶ G) (nu eta : cocharacterLattice A) (R : ℝ)
    (x : RealTorusSpace.Vstar A) :
    L x ∈ intertwiningRegion i B_T
        (Dynamic.unipotent
          (CommGroupScheme.groupHom (RealTorusSpace.cocharacterMapInt f nu) ≫ i))
        (Dynamic.unipotent
          (CommGroupScheme.groupHom (-(RealTorusSpace.cocharacterMapInt f eta)) ≫ i)) R ↔
      x ∈ intertwiningRegion (CommGroupScheme.groupHom f ≫ i) B_A
        (Dynamic.unipotent
          (CommGroupScheme.groupHom nu ≫ (CommGroupScheme.groupHom f ≫ i)))
        (Dynamic.unipotent
          (CommGroupScheme.groupHom (-eta) ≫ (CommGroupScheme.groupHom f ≫ i))) R := by
  unfold intertwiningRegion
  rw [intertwiningRelativeRoots_dynamic_restrict hA hT f i nu eta]
  exact h.mem_rootThresholdRegion_iff _ R x

/-- The local form and orthogonal lift constructed from the single ambient
Weyl form compare the complete actual-root regions. -/
theorem weylInducedCharacterForm_mem_intertwiningRegion_dynamic_iff
    (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus T.toGrp)
    (f : A ⟶ T) [Mono (CommGroupScheme.groupHom f).hom.hom.left]
    (i : T.toGrp ⟶ G) [Mono i.hom.hom.left] [Fintype (relativeWeylGroup i)]
    (nu eta : cocharacterLattice A) (R : ℝ) (x : RealTorusSpace.Vstar A) :
    weylCharacterRestrictionLift hA hT f i x ∈ invariantIntertwiningRegion i hT
        (Dynamic.unipotent
          (CommGroupScheme.groupHom (RealTorusSpace.cocharacterMapInt f nu) ≫ i))
        (Dynamic.unipotent
          (CommGroupScheme.groupHom (-(RealTorusSpace.cocharacterMapInt f eta)) ≫ i)) R ↔
      x ∈ intertwiningRegion (CommGroupScheme.groupHom f ≫ i)
        (weylInducedCharacterForm hA hT f i)
        (Dynamic.unipotent
          (CommGroupScheme.groupHom nu ≫ (CommGroupScheme.groupHom f ≫ i)))
        (Dynamic.unipotent
          (CommGroupScheme.groupHom (-eta) ≫ (CommGroupScheme.groupHom f ≫ i))) R :=
  (weylInducedCharacterForm_compatible hA hT f i).mem_intertwiningRegion_dynamic_iff
    hA hT i nu eta R x

end Forms

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

local instance instSubtorusIntertwiningCone1 : TopologicalSpace (rationalPoints M) :=
  rationalPointTopology F M.X

/-- Canonical continuous characters tested on every ambient dynamic root,
using the orthogonal lift of their actual local normalized real part. -/
def weylAmbientUnramifiedIntertwiningRegion (j : A.toGrp ⟶ M)
    (nu eta : cocharacterLattice A) (R : ℝ) :
    Set (unramifiedCharacters (fun chi => (rationalNormCharacters M chi).toMul)) :=
  {chi | weylCharacterRestrictionLift hA hT f i
      (SplitTorus.normalizedRealPart hA
        (chi.val.toMonoidHom.comp (rationalPoints.map j))) ∈
    invariantIntertwiningRegion i hT
      (Dynamic.unipotent
        (CommGroupScheme.groupHom (RealTorusSpace.cocharacterMapInt f nu) ≫ i))
      (Dynamic.unipotent
        (CommGroupScheme.groupHom (-(RealTorusSpace.cocharacterMapInt f eta)) ≫ i)) R}

omit [LocallyOfFiniteType M.X.hom] in
/-- All ambient inequalities are equivalent to all local inequalities for the
same canonical continuous character and the constructed pair of forms. -/
theorem weylAmbientUnramifiedIntertwiningRegion_eq [Smooth G.X.hom]
    (j : A.toGrp ⟶ M) (nu eta : cocharacterLattice A) (R : ℝ) :
    weylAmbientUnramifiedIntertwiningRegion hA hT f i j nu eta R =
      weylUnramifiedIntertwiningRegion hA hT f i j
        (Dynamic.unipotent
          (CommGroupScheme.groupHom nu ≫ (CommGroupScheme.groupHom f ≫ i)))
        (Dynamic.unipotent
          (CommGroupScheme.groupHom (-eta) ≫ (CommGroupScheme.groupHom f ≫ i))) R := by
  ext chi
  exact weylInducedCharacterForm_mem_intertwiningRegion_dynamic_iff hA hT f i
    nu eta R (SplitTorus.normalizedRealPart hA
      (chi.val.toMonoidHom.comp (rationalPoints.map j)))

/-- A positive character of the actual valuation image simultaneously
satisfies the complete ambient and local threshold conditions. -/
theorem exists_positiveImageCharacter_mem_weylAmbientUnramifiedIntertwiningRegion
    [Smooth G.X.hom] (j : A.toGrp ⟶ M)
    (hM : IsConnectedReductive M) (hj : IsSplitComponent j)
    (nu eta : cocharacterLattice A) (R : ℝ) :
    ∃ psi : rationalImageRealFunctionals M,
      rationalCanonicalImageUnramifiedContinuousEquiv M
        (rationalImagePositiveCharacter M psi) ∈
          weylAmbientUnramifiedIntertwiningRegion hA hT f i j nu eta R := by
  rw [weylAmbientUnramifiedIntertwiningRegion_eq]
  exact exists_positiveImageCharacter_mem_weylUnramifiedIntertwiningRegion_dynamic
    hA hT f i j hM hj nu eta R

theorem weylAmbientUnramifiedIntertwiningRegion_nonempty
    [Smooth G.X.hom] (j : A.toGrp ⟶ M)
    (hM : IsConnectedReductive M) (hj : IsSplitComponent j)
    (nu eta : cocharacterLattice A) (R : ℝ) :
    (weylAmbientUnramifiedIntertwiningRegion hA hT f i j nu eta R).Nonempty := by
  obtain ⟨psi, hpsi⟩ :=
    exists_positiveImageCharacter_mem_weylAmbientUnramifiedIntertwiningRegion
      hA hT f i j hM hj nu eta R
  exact ⟨rationalCanonicalImageUnramifiedContinuousEquiv M
    (rationalImagePositiveCharacter M psi), hpsi⟩

end Characters

end Langlands.Plancherel
