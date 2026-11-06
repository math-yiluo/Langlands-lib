import Langlands.AlgebraicGeometry.AlgebraicSpace.StructuralCompactnessSchemeCompatibilityStatement
import Langlands.AlgebraicGeometry.AlgebraicSpace.StructuralAtlasSchemeCompatibilityProof

/-! # Compactness and finite type compatibility for represented schemes -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- A represented space has a compact atlas exactly when its scheme is compact. -/
theorem isQuasiCompact_schemeToSpace_iff (U : Over S) :
    IsQuasiCompact ((schemeToSpace S).obj U) ↔ CompactSpace U.left := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨W, a, ha, hs, hW⟩ := h.exists_atlas
    obtain ⟨f, _, hfS⟩ := exists_etale_surjective_of_represented_atlas a ha hs
    have := hW
    exact Function.Surjective.compactSpace f.left.continuous hfS.surj
  · have := h
    exact IsQuasiCompact.of_scheme U

/-- Structural quasi-compactness of a represented scheme is quasi-compactness
of its actual structure morphism. -/
theorem quasiCompactOverBase_schemeToSpace_iff (U : Over S) :
    QuasiCompactOverBase ((schemeToSpace S).obj U) ↔ QuasiCompact U.hom := by
  refine ⟨fun h => ?_, fun h T _ g => ?_⟩
  · apply quasiCompact_iff_forall_isAffineOpen.mpr
    intro V hV
    have : IsAffine V := hV
    have hp := h V V.ι
    have hq : IsQuasiCompact ((schemeToSpace V).obj ((Over.pullback V.ι).obj U)) :=
      (IsQuasiCompact.iff_of_iso
        ((forgetToPresheaf V).mapIso (baseChangeSchemeIso V.ι U))).mpr hp
    have : CompactSpace (Limits.pullback U.hom V.ι : Scheme.{u}) :=
      (isQuasiCompact_schemeToSpace_iff _).mp hq
    have : CompactSpace ↥(U.hom ⁻¹ᵁ V) :=
      Function.Surjective.compactSpace
        (pullbackRestrictIsoRestrict U.hom V).hom.continuous Surjective.surj
    exact isCompact_iff_compactSpace.mpr inferInstance
  · have := h
    have : CompactSpace ((Over.pullback g).obj U).left := by
      change CompactSpace (Limits.pullback U.hom g : Scheme.{u})
      infer_instance
    exact (IsQuasiCompact.iff_of_iso
      ((forgetToPresheaf T).mapIso (baseChangeSchemeIso g U))).mp
        (IsQuasiCompact.of_scheme _)

/-- Structural finite type of a represented scheme is local finite type together
with quasi-compactness of its actual structure morphism. -/
theorem finiteTypeOverBase_schemeToSpace_iff (U : Over S) :
    FiniteTypeOverBase ((schemeToSpace S).obj U) ↔
      (LocallyOfFiniteType U.hom ∧ QuasiCompact U.hom) :=
  and_congr (locallyOfFiniteTypeOverBase_schemeToSpace_iff U)
    (quasiCompactOverBase_schemeToSpace_iff U)

/-- All three compactness and finite type comparisons for actual schemes over
arbitrary scheme bases. -/
theorem structuralCompactnessSchemeCompatibility :
    StructuralCompactnessSchemeCompatibilityStatement.{u} := fun _ U =>
  ⟨isQuasiCompact_schemeToSpace_iff U, quasiCompactOverBase_schemeToSpace_iff U,
    finiteTypeOverBase_schemeToSpace_iff U⟩

end Langlands.AlgebraicGeometry.AlgebraicSpace
