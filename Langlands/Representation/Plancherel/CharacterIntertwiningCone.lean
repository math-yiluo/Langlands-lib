import Langlands.Representation.Plancherel.IntertwiningCone
import Langlands.Representation.Plancherel.RationalRealParameterExtension
import Langlands.Representation.Plancherel.RationalUnramifiedCharacterTopology

/-! # Actual unramified characters in intertwining threshold regions -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Plancherel

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {A : CommGroupScheme (Spec (CommRingCat.of F))}
  {M G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]

/-- A nonempty real region has a positive actual-image character witness. -/
theorem exists_positiveImageCharacter_mem_intertwiningRegion_of_injective
    (hA : IsSplitTorus A.toGrp) (j : A.toGrp ⟶ M)
    (hj : Function.Injective (rationalValuationImageMap j))
    (i : A.toGrp ⟶ G) (B : LinearMap.BilinForm ℝ (RealTorusSpace.Vstar A))
    (U Uop' : SubgroupFunctor G) (R : ℝ)
    (hreg : (intertwiningRegion i B U Uop' R).Nonempty) :
    ∃ psi : rationalImageRealFunctionals M,
      rationalImagePositiveCharacter M psi ∈
        imageCharacterIntertwiningRegion hA j i B U Uop' R := by
  obtain ⟨phi, hphi⟩ := hreg
  obtain ⟨psi, hpsi⟩ := exists_positiveImageCharacter_extension_of_injective hA j hj phi
  refine ⟨psi, ?_⟩
  change SplitTorus.normalizedRealPart hA
    ((rationalImageCharacterPullback M (rationalImagePositiveCharacter M psi)).comp
      (rationalPoints.map j)) ∈ intertwiningRegion i B U Uop' R
  rw [hpsi, SplitTorus.normalizedRealPart_positiveCharacter]
  exact hphi

/-- For an injective actual image map, character realization preserves and
reflects nonemptiness of every specified actual-root threshold region. -/
theorem imageCharacterIntertwiningRegion_nonempty_iff_of_injective
    (hA : IsSplitTorus A.toGrp) (j : A.toGrp ⟶ M)
    (hj : Function.Injective (rationalValuationImageMap j))
    (i : A.toGrp ⟶ G) (B : LinearMap.BilinForm ℝ (RealTorusSpace.Vstar A))
    (U Uop' : SubgroupFunctor G) (R : ℝ) :
    (imageCharacterIntertwiningRegion hA j i B U Uop' R).Nonempty ↔
      (intertwiningRegion i B U Uop' R).Nonempty := by
  constructor
  · rintro ⟨chi, hchi⟩
    exact ⟨SplitTorus.normalizedRealPart hA
      ((rationalImageCharacterPullback M chi).comp (rationalPoints.map j)), hchi⟩
  · intro hreg
    obtain ⟨psi, hpsi⟩ :=
      exists_positiveImageCharacter_mem_intertwiningRegion_of_injective
        hA j hj i B U Uop' R hreg
    exact ⟨rationalImagePositiveCharacter M psi, hpsi⟩

/-- Actual split-component hypotheses discharge the image-map injectivity. -/
theorem imageCharacterIntertwiningRegion_nonempty_iff
    (hA : IsSplitTorus A.toGrp) (j : A.toGrp ⟶ M)
    (hM : IsConnectedReductive M) (hj : IsSplitComponent j)
    (i : A.toGrp ⟶ G) (B : LinearMap.BilinForm ℝ (RealTorusSpace.Vstar A))
    (U Uop' : SubgroupFunctor G) (R : ℝ) :
    (imageCharacterIntertwiningRegion hA j i B U Uop' R).Nonempty ↔
      (intertwiningRegion i B U Uop' R).Nonempty :=
  imageCharacterIntertwiningRegion_nonempty_iff_of_injective hA j
    (rationalValuationImageMap_injective j hM hj) i B U Uop' R

/-- Every dynamic threshold has a positive image-character witness on an
actual split component; all actual roots in both supports are tested. -/
theorem exists_positiveImageCharacter_mem_intertwiningRegion_dynamic
    [Smooth G.X.hom]
    (hA : IsSplitTorus A.toGrp) (j : A.toGrp ⟶ M)
    (hM : IsConnectedReductive M) (hj : IsSplitComponent j)
    (i : A.toGrp ⟶ G)
    (B : LinearMap.BilinForm ℝ (RealTorusSpace.Vstar A)) (hB : B.Nondegenerate)
    (nu eta : cocharacterLattice A) (R : ℝ) :
    ∃ psi : rationalImageRealFunctionals M,
      rationalImagePositiveCharacter M psi ∈
        imageCharacterIntertwiningRegion hA j i B
          (Dynamic.unipotent (CommGroupScheme.groupHom nu ≫ i))
          (Dynamic.unipotent (CommGroupScheme.groupHom (-eta) ≫ i)) R :=
  exists_positiveImageCharacter_mem_intertwiningRegion_of_injective hA j
    (rationalValuationImageMap_injective j hM hj) i B _ _ R
    (intertwiningRegion_dynamic_nonempty i hA B hB nu eta R)

theorem imageCharacterIntertwiningRegion_dynamic_nonempty [Smooth G.X.hom]
    (hA : IsSplitTorus A.toGrp) (j : A.toGrp ⟶ M)
    (hM : IsConnectedReductive M) (hj : IsSplitComponent j)
    (i : A.toGrp ⟶ G)
    (B : LinearMap.BilinForm ℝ (RealTorusSpace.Vstar A)) (hB : B.Nondegenerate)
    (nu eta : cocharacterLattice A) (R : ℝ) :
    (imageCharacterIntertwiningRegion hA j i B
      (Dynamic.unipotent (CommGroupScheme.groupHom nu ≫ i))
      (Dynamic.unipotent (CommGroupScheme.groupHom (-eta) ≫ i)) R).Nonempty := by
  obtain ⟨psi, hpsi⟩ := exists_positiveImageCharacter_mem_intertwiningRegion_dynamic
    hA j hM hj i B hB nu eta R
  exact ⟨rationalImagePositiveCharacter M psi, hpsi⟩

theorem characterIntertwiningRegion_dynamic_nonempty [Smooth G.X.hom]
    (hA : IsSplitTorus A.toGrp) (j : A.toGrp ⟶ M)
    (hM : IsConnectedReductive M) (hj : IsSplitComponent j)
    (i : A.toGrp ⟶ G)
    (B : LinearMap.BilinForm ℝ (RealTorusSpace.Vstar A)) (hB : B.Nondegenerate)
    (nu eta : cocharacterLattice A) (R : ℝ) :
    (characterIntertwiningRegion hA j i B
      (Dynamic.unipotent (CommGroupScheme.groupHom nu ≫ i))
      (Dynamic.unipotent (CommGroupScheme.groupHom (-eta) ≫ i)) R).Nonempty := by
  obtain ⟨chi, hchi⟩ := imageCharacterIntertwiningRegion_dynamic_nonempty
    hA j hM hj i B hB nu eta R
  exact ⟨rationalImageCharacterPullback M chi, hchi⟩

section CanonicalTopology

variable [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom]

local instance instCharacterIntertwiningCone1 : TopologicalSpace (rationalPoints M) :=
  rationalPointTopology F M.X

/-- The same actual-root inequalities on the existing continuous unramified
characters, using the canonical rational-point topology. -/
def canonicalUnramifiedIntertwiningRegion
    (hA : IsSplitTorus A.toGrp) (j : A.toGrp ⟶ M)
    (i : A.toGrp ⟶ G) (B : LinearMap.BilinForm ℝ (RealTorusSpace.Vstar A))
    (U Uop' : SubgroupFunctor G) (R : ℝ) :
    Set (unramifiedCharacters (fun chi => (rationalNormCharacters M chi).toMul)) :=
  {chi | chi.val.toMonoidHom ∈ characterIntertwiningRegion hA j i B U Uop' R}

@[simp] theorem mem_canonicalUnramifiedIntertwiningRegion_image
    (hA : IsSplitTorus A.toGrp) (j : A.toGrp ⟶ M)
    (i : A.toGrp ⟶ G) (B : LinearMap.BilinForm ℝ (RealTorusSpace.Vstar A))
    (U Uop' : SubgroupFunctor G) (R : ℝ) (chi : rationalImageCharacters M) :
    rationalCanonicalImageUnramifiedContinuousEquiv M chi ∈
        canonicalUnramifiedIntertwiningRegion hA j i B U Uop' R ↔
      chi ∈ imageCharacterIntertwiningRegion hA j i B U Uop' R := Iff.rfl

theorem canonicalUnramifiedIntertwiningRegion_nonempty_iff_image
    (hA : IsSplitTorus A.toGrp) (j : A.toGrp ⟶ M)
    (i : A.toGrp ⟶ G) (B : LinearMap.BilinForm ℝ (RealTorusSpace.Vstar A))
    (U Uop' : SubgroupFunctor G) (R : ℝ) :
    (canonicalUnramifiedIntertwiningRegion hA j i B U Uop' R).Nonempty ↔
      (imageCharacterIntertwiningRegion hA j i B U Uop' R).Nonempty := by
  constructor
  · rintro ⟨chi, hchi⟩
    obtain ⟨psi, rfl⟩ :=
      (rationalCanonicalImageUnramifiedContinuousEquiv M).surjective chi
    exact ⟨psi, hchi⟩
  · rintro ⟨chi, hchi⟩
    exact ⟨rationalCanonicalImageUnramifiedContinuousEquiv M chi, hchi⟩

theorem canonicalUnramifiedIntertwiningRegion_nonempty_iff
    (hA : IsSplitTorus A.toGrp) (j : A.toGrp ⟶ M)
    (hM : IsConnectedReductive M) (hj : IsSplitComponent j)
    (i : A.toGrp ⟶ G) (B : LinearMap.BilinForm ℝ (RealTorusSpace.Vstar A))
    (U Uop' : SubgroupFunctor G) (R : ℝ) :
    (canonicalUnramifiedIntertwiningRegion hA j i B U Uop' R).Nonempty ↔
      (intertwiningRegion i B U Uop' R).Nonempty := by
  rw [canonicalUnramifiedIntertwiningRegion_nonempty_iff_image,
    imageCharacterIntertwiningRegion_nonempty_iff hA j hM hj]

theorem canonicalUnramifiedIntertwiningRegion_dynamic_nonempty [Smooth G.X.hom]
    (hA : IsSplitTorus A.toGrp) (j : A.toGrp ⟶ M)
    (hM : IsConnectedReductive M) (hj : IsSplitComponent j)
    (i : A.toGrp ⟶ G)
    (B : LinearMap.BilinForm ℝ (RealTorusSpace.Vstar A)) (hB : B.Nondegenerate)
    (nu eta : cocharacterLattice A) (R : ℝ) :
    (canonicalUnramifiedIntertwiningRegion hA j i B
      (Dynamic.unipotent (CommGroupScheme.groupHom nu ≫ i))
      (Dynamic.unipotent (CommGroupScheme.groupHom (-eta) ≫ i)) R).Nonempty :=
  (canonicalUnramifiedIntertwiningRegion_nonempty_iff hA j hM hj i B _ _ R).mpr
    (intertwiningRegion_dynamic_nonempty i hA B hB nu eta R)

end CanonicalTopology

end Langlands.Plancherel
