import Langlands.Geometry.Building.RootReflectionWeyl
import Langlands.Geometry.Building.RootReflectionProof

/-! # Actual root reflections from the apartment axioms -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace

namespace Langlands.Geometry.Building

namespace ValuationBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    (B : ValuationBuildingData G)
    {α : relativeRoots B.i} {g : rationalPoints G}
    {p : rationalPoints G × rationalPoints G}

/-- The actual action of a supplied opposite pair is its geometric reflection,
without an additional fixed-hyperplane premise. -/
theorem normalizerAffineEquiv_reflectionElement
    (hg : g ∈ B.rootGroup α) (hg1 : g ≠ 1)
    (hp : RelativeRoot.IsOppositeFactorPair B.i (α : characterLattice B.S) g p) :
    B.apartment.normalizerAffineEquiv (B.reflectionElement hp) =
      AffineRootSystem.affineReflection (B.reflectionFunctional α g)
        (B.rootForm_reflectionCoroot hg hg1 hp) :=
  B.normalizerAffineEquiv_reflectionElement_of_hasRootReflections
    (RootReflectionProof.hasRootReflections B) hg hg1 hp

/-- Under apartment axioms the actual pair coroot is a coroot for the apartment's
affine-root system, including when the point functional is only extended. -/
theorem isCoroot_reflectionCoroot (hA : B.SatisfiesApartmentAxioms)
    (hg : g ∈ B.rootGroup α) (hg1 : g ≠ 1)
    (hp : RelativeRoot.IsOppositeFactorPair B.i (α : characterLattice B.S) g p) :
    AffineRootSystem.IsCoroot B.affineRoots (B.reflectionFunctional α g)
      (B.reflectionCoroot hg hg1 hp) :=
  B.isCoroot_reflectionCoroot_of_hasRootReflections hA
    (RootReflectionProof.hasRootReflections B) hg hg1 hp

/-- Any affine-system coroot for the same point functional gives the actual action. -/
theorem normalizerAffineEquiv_reflectionElement_eq_of_isCoroot
    (hA : B.SatisfiesApartmentAxioms)
    (hg : g ∈ B.rootGroup α) (hg1 : g ≠ 1)
    (hp : RelativeRoot.IsOppositeFactorPair B.i (α : characterLattice B.S) g p)
    {v : TranslationSpace B.i}
    (hv : AffineRootSystem.IsCoroot B.affineRoots (B.reflectionFunctional α g) v) :
    B.apartment.normalizerAffineEquiv (B.reflectionElement hp) =
      AffineRootSystem.affineReflection (B.reflectionFunctional α g) hv.1 :=
  B.normalizerAffineEquiv_reflectionElement_eq_of_isCoroot_of_hasRootReflections hA
    (RootReflectionProof.hasRootReflections B) hg hg1 hp hv

/-- Apartment axioms place every actual supplied pair in the affine Weyl group. -/
theorem normalizerAffineEquiv_reflectionElement_mem_affineWeylGroup_of_apartment
    (hA : B.SatisfiesApartmentAxioms)
    (hg : g ∈ B.rootGroup α) (hg1 : g ≠ 1)
    (hp : RelativeRoot.IsOppositeFactorPair B.i (α : characterLattice B.S) g p) :
    B.apartment.normalizerAffineEquiv (B.reflectionElement hp) ∈
      AffineRootSystem.affineWeylGroup B.affineRoots :=
  B.normalizerAffineEquiv_reflectionElement_mem_affineWeylGroup hA
    (RootReflectionProof.hasRootReflections B) hg hg1 hp

/-- The actual reflection-generated normalizer acts through the affine Weyl group
under the apartment axioms alone. -/
theorem reflectionNormalizer_map_le_affineWeylGroup_of_apartment
    (hA : B.SatisfiesApartmentAxioms) :
    B.reflectionNormalizer.map B.apartment.normalizerAffineEquiv ≤
      AffineRootSystem.affineWeylGroup B.affineRoots :=
  B.reflectionNormalizer_map_le_affineWeylGroup hA
    (RootReflectionProof.hasRootReflections B)

/-- Restriction of the actual apartment action to the reflection-generated
normalizer, with codomain the affine Weyl group. -/
def reflectionWeylHom (hA : B.SatisfiesApartmentAxioms) :
    B.reflectionNormalizer →* AffineRootSystem.affineWeylGroup B.affineRoots where
  toFun n := ⟨B.apartment.normalizerAffineEquiv n.val,
    B.reflectionNormalizer_map_le_affineWeylGroup_of_apartment hA
      ⟨n.val, n.property, rfl⟩⟩
  map_one' := Subtype.ext (map_one B.apartment.normalizerAffineEquiv)
  map_mul' n m := Subtype.ext (map_mul B.apartment.normalizerAffineEquiv n.val m.val)

@[simp]
theorem reflectionWeylHom_coe (hA : B.SatisfiesApartmentAxioms)
    (n : B.reflectionNormalizer) :
    (B.reflectionWeylHom hA n : B.Apartment ≃ᵃ[ℝ] B.Apartment) =
      B.apartment.normalizerAffineEquiv n.val := rfl

/-- Pair existence is the only remaining extra premise for equality of the
reflection-generated image with the affine Weyl group. -/
theorem reflectionNormalizer_map_eq_affineWeylGroup_of_apartment
    (hA : B.SatisfiesApartmentAxioms)
    (hF : RelativeRoot.HasRankOneFactorization B.i) :
    B.reflectionNormalizer.map B.apartment.normalizerAffineEquiv =
      AffineRootSystem.affineWeylGroup B.affineRoots :=
  B.reflectionNormalizer_map_eq_affineWeylGroup hA
    (RootReflectionProof.hasRootReflections B) hF

/-- Every affine Weyl transformation lifts to the actual reflection-generated
normalizer when actual opposite pairs exist. -/
theorem reflectionWeylHom_surjective (hA : B.SatisfiesApartmentAxioms)
    (hF : RelativeRoot.HasRankOneFactorization B.i) :
    Function.Surjective (B.reflectionWeylHom hA) := by
  intro w
  have hw : w.val ∈ B.reflectionNormalizer.map B.apartment.normalizerAffineEquiv := by
    rw [B.reflectionNormalizer_map_eq_affineWeylGroup_of_apartment hA hF]
    exact w.property
  obtain ⟨n, hn, heq⟩ := hw
  exact ⟨⟨n, hn⟩, Subtype.ext heq⟩

end ValuationBuildingData

namespace ParahoricBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    (P : ParahoricBuildingData G)

/-- Every affine Weyl transformation is the action of a point of the actual
simply connected normalizer image, under explicit actual pair existence. -/
theorem affineWeylGroup_le_simplyConnectedNormalizer_map_of_apartment
    (hA : P.SatisfiesApartmentAxioms)
    (hF : RelativeRoot.HasRankOneFactorization P.i) :
    AffineRootSystem.affineWeylGroup P.affineRoots ≤
      (P.simplyConnectedImage.comap (normalizerPoints P.i).subtype).map
        P.apartment.normalizerAffineEquiv :=
  P.affineWeylGroup_le_simplyConnectedNormalizer_map hA
    (RootReflectionProof.hasRootReflections P.toValuationBuildingData) hF

end ParahoricBuildingData

end Langlands.Geometry.Building
