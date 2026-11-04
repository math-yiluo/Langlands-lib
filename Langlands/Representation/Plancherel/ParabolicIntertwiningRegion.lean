import Langlands.GroupScheme.Rational.ParabolicOppositeRootModel
import Langlands.Representation.Plancherel.SubtorusIntertwiningCone

/-! # Actual supplied parabolic radicals in canonical character regions -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Plancherel

section RealParameters

variable {k : Type u} [Field k]
  {A : CommGroupScheme (Spec (CommRingCat.of k))}
  {M G P P' Q U V : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [Smooth G.X.hom]
  {p : P ⟶ G} {l : M ⟶ P} {p' : P' ⟶ G} {l' : M ⟶ P'}
  {a : A.toGrp ⟶ M}
  (r : ParabolicRootPresentation p l a) (r' : ParabolicRootPresentation p' l' a)
  (hM : l ≫ p = l' ≫ p')
  {n : U ⟶ P} (hn : LeviSubgroup.IsGeometricUnipotentRadical n)
  {q : Q ⟶ G}
  (hQ : (Dynamic.parabolic
    (CommGroupScheme.groupHom (-r'.splitComponentCocharacter) ≫ a ≫ l' ≫ p')).IsRepresentedBy q)
  {v : V ⟶ Q} (hv : LeviSubgroup.IsGeometricUnipotentRadical v)

include r r' hM hn hQ hv

/-- The region of the supplied radicals equals the exact dynamic region,
using the same split component and ambient embedding. -/
theorem intertwiningRegion_eq_dynamic_commonLevi
    (B : LinearMap.BilinForm ℝ (RealTorusSpace.Vstar A)) (R : ℝ) :
    intertwiningRegion (a ≫ l ≫ p) B
        (SubgroupFunctor.range (n ≫ p)) (SubgroupFunctor.range (v ≫ q)) R =
      intertwiningRegion (a ≫ l ≫ p) B
        (Dynamic.unipotent (CommGroupScheme.groupHom r.splitComponentCocharacter ≫ a ≫ l ≫ p))
        (Dynamic.unipotent
          (CommGroupScheme.groupHom (-r'.splitComponentCocharacter) ≫ a ≫ l ≫ p)) R := by
  rw [r.range_comp_radical_eq hn, r'.range_comp_oppositeRadical_eq hQ hv, ← hM]

/-- Membership tests every actual root in the full positive/negative support
intersection, with a strict threshold. -/
theorem mem_intertwiningRegion_commonLevi
    (B : LinearMap.BilinForm ℝ (RealTorusSpace.Vstar A)) (R : ℝ)
    (x : RealTorusSpace.Vstar A) :
    x ∈ intertwiningRegion (a ≫ l ≫ p) B
        (SubgroupFunctor.range (n ≫ p)) (SubgroupFunctor.range (v ≫ q)) R ↔
      ∀ α ∈ relativeRoots (a ≫ l ≫ p),
        0 < latticePairing A α r.splitComponentCocharacter →
          latticePairing A α r'.splitComponentCocharacter < 0 →
            R < B x ((1 : ℝ) ⊗ₜ[ℤ] α) := by
  rw [intertwiningRegion_eq_dynamic_commonLevi r r' hM hn hQ hv]
  exact mem_intertwiningRegion_dynamic _ r.isCompatible.splitComponent.1.isSplitSubtorus.1
    B r.splitComponentCocharacter r'.splitComponentCocharacter R x

theorem intertwiningRegion_commonLevi_nonempty
    (B : LinearMap.BilinForm ℝ (RealTorusSpace.Vstar A)) (hB : B.Nondegenerate)
    (R : ℝ) :
    (intertwiningRegion (a ≫ l ≫ p) B
      (SubgroupFunctor.range (n ≫ p)) (SubgroupFunctor.range (v ≫ q)) R).Nonempty := by
  rw [intertwiningRegion_eq_dynamic_commonLevi r r' hM hn hQ hv]
  exact intertwiningRegion_dynamic_nonempty _
    r.isCompatible.splitComponent.1.isSplitSubtorus.1 B hB
    r.splitComponentCocharacter r'.splitComponentCocharacter R

end RealParameters

section CharacterParameters

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {A : CommGroupScheme (Spec (CommRingCat.of F))}
  {M G P P' Q U V : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [Smooth G.X.hom]
  {p : P ⟶ G} {l : M ⟶ P} {p' : P' ⟶ G} {l' : M ⟶ P'}
  {a : A.toGrp ⟶ M}
  (r : ParabolicRootPresentation p l a)

variable [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom]

local instance parabolicIntertwiningRegionLeviPointTopology : TopologicalSpace (rationalPoints M) :=
  rationalPointTopology F M.X

/-- The existing canonical continuous unramified-character space, restricted
by the actual ambient images of two supplied radical maps. -/
def parabolicUnramifiedIntertwiningRegion
    (B : LinearMap.BilinForm ℝ (RealTorusSpace.Vstar A))
    (n : U ⟶ P) (q : Q ⟶ G) (v : V ⟶ Q) (R : ℝ) :
    Set (unramifiedCharacters (fun chi => (rationalNormCharacters M chi).toMul)) :=
  canonicalUnramifiedIntertwiningRegion r.isCompatible.splitComponent.1.isSplitSubtorus.1
    a (a ≫ l ≫ p) B (SubgroupFunctor.range (n ≫ p)) (SubgroupFunctor.range (v ≫ q)) R

variable (r' : ParabolicRootPresentation p' l' a) (hM : l ≫ p = l' ≫ p')
  {n : U ⟶ P} (hn : LeviSubgroup.IsGeometricUnipotentRadical n)
  {q : Q ⟶ G}
  (hQ : (Dynamic.parabolic
    (CommGroupScheme.groupHom (-r'.splitComponentCocharacter) ≫ a ≫ l' ≫ p')).IsRepresentedBy q)
  {v : V ⟶ Q} (hv : LeviSubgroup.IsGeometricUnipotentRadical v)

include r r' hM hn hQ hv

omit [LocallyOfFiniteType M.X.hom] in
theorem mem_parabolicUnramifiedIntertwiningRegion
    (B : LinearMap.BilinForm ℝ (RealTorusSpace.Vstar A)) (R : ℝ)
    (chi : unramifiedCharacters (fun psi => (rationalNormCharacters M psi).toMul)) :
    chi ∈ parabolicUnramifiedIntertwiningRegion r B n q v R ↔
      ∀ α ∈ relativeRoots (a ≫ l ≫ p),
        0 < latticePairing A α r.splitComponentCocharacter →
          latticePairing A α r'.splitComponentCocharacter < 0 →
            R < B (SplitTorus.normalizedRealPart
              r.isCompatible.splitComponent.1.isSplitSubtorus.1
              (chi.val.toMonoidHom.comp (rationalPoints.map a))) ((1 : ℝ) ⊗ₜ[ℤ] α) :=
  mem_intertwiningRegion_commonLevi r r' hM hn hQ hv B R _

/-- The witness is a positive character of the actual valuation image,
transported to the existing continuous unramified-character space. -/
theorem exists_positiveImageCharacter_mem_parabolicUnramifiedIntertwiningRegion
    (B : LinearMap.BilinForm ℝ (RealTorusSpace.Vstar A)) (hB : B.Nondegenerate)
    (R : ℝ) :
    ∃ psi : rationalImageRealFunctionals M,
      rationalCanonicalImageUnramifiedContinuousEquiv M
        (rationalImagePositiveCharacter M psi) ∈
          parabolicUnramifiedIntertwiningRegion r B n q v R := by
  obtain ⟨psi, hpsi⟩ :=
    exists_positiveImageCharacter_mem_intertwiningRegion_of_injective
      r.isCompatible.splitComponent.1.isSplitSubtorus.1 a
      (rationalValuationImageMap_injective a r.isCompatible.levi.isConnectedReductive
        r.isCompatible.splitComponent)
      (a ≫ l ≫ p) B (SubgroupFunctor.range (n ≫ p)) (SubgroupFunctor.range (v ≫ q)) R
      (intertwiningRegion_commonLevi_nonempty r r' hM hn hQ hv B hB R)
  exact ⟨psi, hpsi⟩

theorem parabolicUnramifiedIntertwiningRegion_nonempty
    (B : LinearMap.BilinForm ℝ (RealTorusSpace.Vstar A)) (hB : B.Nondegenerate)
    (R : ℝ) :
    (parabolicUnramifiedIntertwiningRegion r B n q v R).Nonempty := by
  obtain ⟨psi, hpsi⟩ :=
    exists_positiveImageCharacter_mem_parabolicUnramifiedIntertwiningRegion
      r r' hM hn hQ hv B hB R
  exact ⟨rationalCanonicalImageUnramifiedContinuousEquiv M
    (rationalImagePositiveCharacter M psi), hpsi⟩

omit r' hM hn hQ hv

section AmbientForm

local instance parabolicIntertwiningRegionRootInclusionMono : Mono r.data.i.hom.hom.left :=
  r.isCompatible.maximalSplit.isSplitSubtorus.mono

local instance parabolicIntertwiningRegionRootCharacterMono : Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left := by
  let := r.isCompatible.splitComponent.1.isSplitSubtorus.mono
  let := r.isCompatible.levi.isClosedSubgroup.mono
  let := r.isCompatible.parabolic.isClosedSubgroup.mono
  have : Mono (a ≫ l ≫ p).hom.hom.left := by
    change Mono (a.hom.hom.left ≫ l.hom.hom.left ≫ p.hom.hom.left)
    infer_instance
  exact mono_of_mono_fac
    (congrArg (fun z => z.hom.hom.left) r.isCompatible.factor_comp)

variable [Fintype (relativeWeylGroup r.data.i)]

/-- The supplied-radical region with the local form constructed from the
single Weyl-invariant form on the presentation's ambient torus. -/
def parabolicWeylUnramifiedIntertwiningRegion
    (n : U ⟶ P) (q : Q ⟶ G) (v : V ⟶ Q) (R : ℝ) :
    Set (unramifiedCharacters (fun chi => (rationalNormCharacters M chi).toMul)) :=
  parabolicUnramifiedIntertwiningRegion r
    (weylInducedCharacterForm r.isCompatible.splitComponent.1.isSplitSubtorus.1
      r.isCompatible.maximalSplit.isSplitSubtorus.1 r.data.f r.data.i) n q v R

include r' hM hn hQ hv

omit [LocallyOfFiniteType M.X.hom] in
/-- Every canonical character satisfies the supplied-radical inequalities
exactly when its orthogonal lift satisfies all ambient root inequalities. -/
theorem parabolicWeylUnramifiedIntertwiningRegion_eq_ambient (R : ℝ) :
    parabolicWeylUnramifiedIntertwiningRegion r n q v R =
      weylAmbientUnramifiedIntertwiningRegion
        r.isCompatible.splitComponent.1.isSplitSubtorus.1
        r.isCompatible.maximalSplit.isSplitSubtorus.1 r.data.f r.data.i a
        r.splitComponentCocharacter r'.splitComponentCocharacter R := by
  rw [weylAmbientUnramifiedIntertwiningRegion_eq]
  ext chi
  change SplitTorus.normalizedRealPart _ _ ∈
      intertwiningRegion (a ≫ l ≫ p) _
        (SubgroupFunctor.range (n ≫ p)) (SubgroupFunctor.range (v ≫ q)) R ↔
    SplitTorus.normalizedRealPart _ _ ∈
      intertwiningRegion (CommGroupScheme.groupHom r.data.f ≫ r.data.i) _
        (Dynamic.unipotent (CommGroupScheme.groupHom r.splitComponentCocharacter ≫
          (CommGroupScheme.groupHom r.data.f ≫ r.data.i)))
        (Dynamic.unipotent (CommGroupScheme.groupHom (-r'.splitComponentCocharacter) ≫
          (CommGroupScheme.groupHom r.data.f ≫ r.data.i))) R
  rw [intertwiningRegion_eq_dynamic_commonLevi r r' hM hn hQ hv,
    r.isCompatible.factor_comp]

theorem exists_positiveImageCharacter_mem_parabolicWeylUnramifiedIntertwiningRegion
    (R : ℝ) :
    ∃ psi : rationalImageRealFunctionals M,
      rationalCanonicalImageUnramifiedContinuousEquiv M
        (rationalImagePositiveCharacter M psi) ∈
          parabolicWeylUnramifiedIntertwiningRegion r n q v R :=
  exists_positiveImageCharacter_mem_parabolicUnramifiedIntertwiningRegion
    r r' hM hn hQ hv _
    (weylInducedCharacterForm_nondegenerate
      r.isCompatible.splitComponent.1.isSplitSubtorus.1
      r.isCompatible.maximalSplit.isSplitSubtorus.1 r.data.f r.data.i) R

theorem parabolicWeylUnramifiedIntertwiningRegion_nonempty (R : ℝ) :
    (parabolicWeylUnramifiedIntertwiningRegion r n q v R).Nonempty := by
  obtain ⟨psi, hpsi⟩ :=
    exists_positiveImageCharacter_mem_parabolicWeylUnramifiedIntertwiningRegion
      r r' hM hn hQ hv R
  exact ⟨rationalCanonicalImageUnramifiedContinuousEquiv M
    (rationalImagePositiveCharacter M psi), hpsi⟩

end AmbientForm
end CharacterParameters

end Langlands.Plancherel
