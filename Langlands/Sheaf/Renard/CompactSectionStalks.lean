import Langlands.Sheaf.Renard.CompactSectionTestModule
import Langlands.Sheaf.CompactGerms

/-!
# Stalks of a complex vector sheaf as quotients of compact sections

Renard (9 July 2026), II.2.5, Remarque, printed p.42 / PDF p.48:
`F_x = F_c(X) / ⟨f · φ, φ ∈ F_c(X), f ∈ D(X), f(x) = 0⟩`.
This file constructs the span, the canonical map from the quotient to the actual
stalk induced by the published germ map, and its naturality.
-/

noncomputable section

namespace Langlands.Sheaf.Renard.CompactSectionStalks

open CategoryTheory Opposite
open Langlands.HarmonicAnalysis
open Langlands.Sheaf.Renard.VectorSheafScalars Langlands.Sheaf.Renard.CompactSectionTestModule

variable {X : Type} [TopologicalSpace X] (F : VectorSheaf X) (x : X)

/-- The products `f • s` of compact sections by test functions vanishing at `x`. -/
def vanishingGenerators : Set (CompactSupport.submodule F.presheaf) :=
  {t | ∃ (f : PointwiseTestAlgebra.Carrier X) (s : CompactSupport.submodule F.presheaf),
    f x = 0 ∧ f • s = t}

/-- Renard's subspace `⟨f · φ, f(x) = 0⟩` of compact sections. -/
def vanishingSpan : Submodule ℂ (CompactSupport.submodule F.presheaf) :=
  Submodule.span ℂ (vanishingGenerators F x)

theorem smul_mem_vanishingSpan {f : PointwiseTestAlgebra.Carrier X} (hf : f x = 0)
    (s : CompactSupport.submodule F.presheaf) : f • s ∈ vanishingSpan F x :=
  Submodule.subset_span ⟨f, s, hf, rfl⟩

/-- The published germ map on compact sections satisfies `(f s)_x = f(x) s_x`. -/
theorem germ_testSmul (f : PointwiseTestAlgebra.Carrier X)
    (s : CompactSupport.submodule F.presheaf) :
    CompactGerms.germ F x (f • s) = f x • CompactGerms.germ F x s :=
  Γgerm_testSmul F f s x

/-- The germ map kills the span. -/
theorem vanishingSpan_le_ker :
    vanishingSpan F x ≤ LinearMap.ker (CompactGerms.germ F x) := by
  rw [vanishingSpan, Submodule.span_le]
  rintro _ ⟨f, s, hf, rfl⟩
  rw [SetLike.mem_coe, LinearMap.mem_ker, germ_testSmul, hf, zero_smul]

/-- The canonical map `F_c(X) / ⟨f · φ, f(x) = 0⟩ → F_x` induced by the germ map. -/
def stalkQuotientMap :
    (CompactSupport.submodule F.presheaf ⧸ vanishingSpan F x) →ₗ[ℂ] F.presheaf.stalk x :=
  (vanishingSpan F x).liftQ (CompactGerms.germ F x) (vanishingSpan_le_ker F x)

@[simp]
theorem stalkQuotientMap_mk (s : CompactSupport.submodule F.presheaf) :
    stalkQuotientMap F x (Submodule.Quotient.mk s) = CompactGerms.germ F x s := rfl

/-- Surjectivity, from the published surjectivity of the compact germ map. -/
theorem stalkQuotientMap_surjective (hX : Langlands.Topology.IsLocallyProfinite X) :
    Function.Surjective (stalkQuotientMap F x) := by
  intro t
  obtain ⟨s, rfl⟩ := CompactGerms.germ_surjective F hX x t
  exact ⟨Submodule.Quotient.mk s, rfl⟩

section Naturality

variable {F} {G : VectorSheaf X}

/-- Compact-section maps of sheaf morphisms preserve the span. -/
theorem vanishingSpan_le_comap (φ : F ⟶ G) :
    vanishingSpan F x ≤ (vanishingSpan G x).comap (CompactSupport.map φ.hom) := by
  rw [vanishingSpan, Submodule.span_le]
  rintro _ ⟨f, s, hf, rfl⟩
  change CompactSupport.map φ.hom (f • s) ∈ vanishingSpan G x
  rw [← compactSectionMap_eq, Langlands.Algebra.NonUnitalModuleHom.map_smul]
  exact smul_mem_vanishingSpan G x hf _

/-- The induced map of quotients. -/
def quotientMap (φ : F ⟶ G) :
    (CompactSupport.submodule F.presheaf ⧸ vanishingSpan F x) →ₗ[ℂ]
      (CompactSupport.submodule G.presheaf ⧸ vanishingSpan G x) :=
  (vanishingSpan F x).mapQ (vanishingSpan G x) (CompactSupport.map φ.hom)
    (vanishingSpan_le_comap x φ)

@[simp]
theorem quotientMap_mk (φ : F ⟶ G) (s : CompactSupport.submodule F.presheaf) :
    quotientMap x φ (Submodule.Quotient.mk s) =
      Submodule.Quotient.mk (CompactSupport.map φ.hom s) := rfl

/-- The comparison commutes with the stalk maps of sheaf morphisms. -/
theorem stalkQuotientMap_naturality (φ : F ⟶ G)
    (q : CompactSupport.submodule F.presheaf ⧸ vanishingSpan F x) :
    (TopCat.Presheaf.stalkFunctor (ModuleCat.{0} ℂ) x).map φ.hom (stalkQuotientMap F x q) =
      stalkQuotientMap G x (quotientMap x φ q) := by
  induction q using Submodule.Quotient.induction_on with
  | H s => exact CompactGerms.germ_naturality φ x s

end Naturality

end Langlands.Sheaf.Renard.CompactSectionStalks
