import Langlands.Geometry.Building.LeviApartmentRestrictionStatement
import Langlands.Geometry.Building.LeviSpecialPointRestrictionStatement
import Langlands.Geometry.Building.OmegaCompatibleApartmentUniquenessProof
import Langlands.Representation.Plancherel.RenardLeviCentralizerCompatibility
import Langlands.GroupScheme.Rational.StandardCocharacterProof
import Langlands.GroupScheme.Dynamic.CentralizerReductiveProof

/-! # Comparing a restricted Levi apartment with a prescribed compatible class -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.Geometry.Building
open Langlands.GroupScheme.RealTorusSpace Langlands.Plancherel

namespace Langlands.Geometry.Building.CentralizerDatum

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {S : CommGroupScheme (Spec (CommRingCat.of F))}
    {G : GroupScheme (Spec (CommRingCat.of F))}
    {i : S.toGrp ⟶ G} (C E : CentralizerDatum i)

/-- The canonical comparison between two representatives of the same actual
torus centralizer. -/
def comparisonIso : C.Z ≅ E.Z :=
  C.isRepresentedBy.isoOfIsRepresentedBy E.isRepresentedBy

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem comparisonIso_hom_comp : (C.comparisonIso E).hom ≫ E.j = C.j :=
  C.isRepresentedBy.isoOfIsRepresentedBy_hom_comp E.isRepresentedBy

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem comparisonIso_torus : C.s ≫ (C.comparisonIso E).hom = E.s := by
  apply E.isRepresentedBy.hom_ext
  rw [Category.assoc, comparisonIso_hom_comp, C.comp_eq, E.comp_eq]

/-- Centralizer comparison preserves the actual character-normalized
translation vector on the unchanged torus. -/
theorem comparisonIso_translation (z : rationalPoints C.Z) :
    (C.translation z).toAdd =
      (E.translation (rationalPoints.map (C.comparisonIso E).hom z)).toAdd := by
  apply E.bijective.injective
  apply AddMonoidHom.ext
  intro χ
  change eval S (BruhatTits.Cartan.characterRestriction E.s χ)
      (C.translation z).toAdd =
    eval S (BruhatTits.Cartan.characterRestriction E.s χ)
      (E.translation (rationalPoints.map (C.comparisonIso E).hom z)).toAdd
  have hχ :
      BruhatTits.Cartan.characterRestriction C.s
          (characterRestrict (C.comparisonIso E).hom χ) =
        BruhatTits.Cartan.characterRestriction E.s χ := by
    apply congrArg (rationalCharacters.equivCharacterLattice S)
    change Additive.ofMul (C.s ≫ ((C.comparisonIso E).hom ≫ χ.toMul)) =
      Additive.ofMul (E.s ≫ χ.toMul)
    rw [← Category.assoc, comparisonIso_torus]
  calc
    _ = eval S (BruhatTits.Cartan.characterRestriction C.s
        (characterRestrict (C.comparisonIso E).hom χ)) (C.translation z).toAdd := by rw [hχ]
    _ = -((rationalCharacterValuation C.Z z).toAdd
        (characterRestrict (C.comparisonIso E).hom χ) : ℝ) :=
      eval_centralizerTranslation C.s C.bijective z _
    _ = -((rationalCharacterValuation E.Z
        (rationalPoints.map (C.comparisonIso E).hom z)).toAdd χ : ℝ) := by
      rw [rationalCharacterValuation_characterRestrict]
    _ = _ := (eval_centralizerTranslation E.s E.bijective _ χ).symm

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem comparisonIso_map_comp (z : rationalPoints C.Z) :
    rationalPoints.map E.j (rationalPoints.map (C.comparisonIso E).hom z) =
      rationalPoints.map C.j z := by
  simpa only [rationalPoints.map_apply, Grp.comp_hom_hom, Category.assoc] using
    congrArg (fun f : C.Z ⟶ G => z ≫ f.hom.hom) (C.comparisonIso_hom_comp E)

end Langlands.Geometry.Building.CentralizerDatum

namespace Langlands.Geometry.Building.KPApartmentData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {S : CommGroupScheme (Spec (CommRingCat.of F))}
    {G : GroupScheme (Spec (CommRingCat.of F))}
    {i : S.toGrp ⟶ G} [Mono i.hom.hom.left] [IsAffineHom G.X.hom]
    {D : KPApartmentData i (localFieldOrder F)}
    {C : CentralizerDatum i} (E : CentralizerDatum i)

/-- Full V6 is independent of the representative of the actual centralizer. -/
theorem IsOmegaCompatible.of_centralizerDatum (hD : D.IsOmegaCompatible C) :
    D.IsOmegaCompatible E := by
  intro φ hφ a ha z u hu
  have hsurj : Function.Surjective (rationalPoints.map (C.comparisonIso E).hom) := by
    intro z
    obtain ⟨w, hw⟩ := (isoPointsEquiv (C.comparisonIso E) (Over.mk (𝟙 _))).surjective z
    exact ⟨w, by simpa only [rationalPoints.map_apply, isoPointsEquiv_apply] using hw⟩
  obtain ⟨z, rfl⟩ := hsurj z
  rw [C.comparisonIso_map_comp E, ← C.comparisonIso_translation E]
  exact hD φ hφ a ha z u hu

theorem isOmegaCompatible_iff_centralizerDatum :
    D.IsOmegaCompatible C ↔ D.IsOmegaCompatible E :=
  ⟨fun h => h.of_centralizerDatum E, fun h => h.of_centralizerDatum C⟩

end Langlands.Geometry.Building.KPApartmentData

namespace Langlands.BruhatTits.SpecialCompact

section StandardLevi

variable {F : Type u} [Field F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    {S : CommGroupScheme (Spec (CommRingCat.of F))}
    (hG : IsConnectedReductive G) (i : S.toGrp ⟶ G)
    (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice S)
    (hν : IsGenericCocharacter i ν) (J : Set (characterLattice S))
    (hJ : J ⊆ simpleRelativeRoots i ν)

include hG hi hν hJ in
/-- Every actual standard Levi is connected reductive, by the published
standard-cocharacter and dynamic-centralizer proofs. -/
theorem standardLevi_isConnectedReductive :
    IsConnectedReductive (Standard.leviScheme i ν J) := by
  have : Mono i.hom.hom.left := hi.isSplitSubtorus.mono
  obtain ⟨⟨ζ, hζ⟩, hcompare⟩ := standardCocharacter F G hG S i hi ν hν J hJ
  have hj := Standard.isRepresentedBy_leviHom i ν J
  rw [(hcompare ζ hζ).2.1] at hj
  exact dynamicCentralizerReductive F G hG (CommGroupScheme.groupHom ζ ≫ i)
    (Standard.leviScheme i ν J) (Standard.leviHom i ν J)
    (Standard.isClosedSubgroup_leviHom i ν J) hj

end StandardLevi

section Comparison

variable (hrestriction : LeviApartmentRestrictionStatement.{u})
    {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    (hG : IsConnectedReductive G)
    {S : CommGroupScheme (Spec (CommRingCat.of F))}
    (i : S.toGrp ⟶ G) [Mono i.hom.hom.left] (hi : IsMaximalSplitTorus i)
    (C : CentralizerDatum i) (D : KPApartmentData i (localFieldOrder F))
    (hD : D.IsOmegaCompatible C)
    (ν : cocharacterLattice S) (hν : IsGenericCocharacter i ν)
    (J : Set (characterLattice S)) (hJ : J ⊆ simpleRelativeRoots i ν)

local instance : IsAffineHom (Standard.leviScheme i ν J).X.hom :=
  (Standard.isClosedSubgroup_leviHom i ν J).isAffineHom

variable [Mono (Standard.leviTorusHom i ν J).hom.hom.left]
    (CM : CentralizerDatum (Standard.leviTorusHom i ν J))
    (DM : KPApartmentData (Standard.leviTorusHom i ν J) (localFieldOrder F))
    (hDM : DM.IsOmegaCompatible CM)

include hrestriction hG hi hν hJ hD hDM in
/-- Restriction and full V6 identify the restricted class with any supplied
omega-compatible standard-Levi class at the prescribed torus. Only the
published apartment-restriction proposition remains a premise. -/
theorem exists_leviRestriction_of_omegaCompatible (x : D.Apartment) :
    ∃ xM : DM.Apartment, IsLeviRestriction (Standard.leviHom i ν J) x xM := by
  obtain ⟨R, hR, hsurj, -⟩ := hrestriction F G hG S i hi ν hν J hJ D
  let CR := RenardCartan.standardLeviCentralizerDatum i C ν J
  have hRω : R.IsOmegaCompatible CR :=
    RenardCartan.isOmegaCompatible_standardLevi_of_restriction i C ν J D R hD hsurj
  have hDMω : DM.IsOmegaCompatible CR := hDM.of_centralizerDatum CR
  have hM := standardLevi_isConnectedReductive hG i hi ν hν J hJ
  have hEq : R = DM :=
    omegaCompatibleApartmentUniqueness F (Standard.leviScheme i ν J) hM S
      (Standard.leviTorusHom i ν J)
      (Standard.isMaximalSplitTorus_leviTorusHom i ν J hi) CR R DM hRω hDMω
  subst R
  exact hR x

end Comparison

end Langlands.BruhatTits.SpecialCompact
