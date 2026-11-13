import Langlands.Sheaf.Renard.Distributions
import Langlands.Sheaf.Renard.HomeomorphSheafIso

/-!
# Locally constant scalar compatibility for sheaf isomorphisms

This internal comparison joins the distribution action and the isomorphisms
over homeomorphisms from Renard II.2.5, printed pp.42–43 / PDF pp.48–49.
-/

noncomputable section

namespace Langlands.Sheaf.Renard.DistributionHomeomorph

open CategoryTheory Opposite TopologicalSpace
open Langlands.HarmonicAnalysis
open VectorSheafScalars HomeomorphSheafIso

universe u v

section Scalars

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/-- Pull back the full locally constant scalar algebra along a homeomorphism. -/
def scalarComap (γ : X ≃ₜ Y) :
    LocallyConstant Y ℂ ≃ₐ[ℂ] LocallyConstant X ℂ :=
  LocallyConstant.congrLeftₐ ℂ γ.symm

@[simp]
theorem scalarComap_apply (γ : X ≃ₜ Y) (f : LocallyConstant Y ℂ) (x : X) :
    scalarComap γ f x = f (γ x) := rfl

@[simp]
theorem scalarComap_symm_scalarComap (γ : X ≃ₜ Y) (f : LocallyConstant Y ℂ) :
    scalarComap γ.symm (scalarComap γ f) = f := by
  ext y
  exact congrArg f (γ.apply_symm_apply y)

@[simp]
theorem scalarComap_scalarComap_symm (γ : X ≃ₜ Y) (f : LocallyConstant X ℂ) :
    scalarComap γ (scalarComap γ.symm f) = f := by
  ext x
  exact congrArg f (γ.symm_apply_apply x)

/-- Pullback on tests commutes with multiplication by a full locally constant scalar. -/
theorem testComap_lc_smul (γ : X ≃ₜ Y) (f : LocallyConstant Y ℂ)
    (e : PointwiseTestAlgebra.Carrier Y) :
    testComap γ (f • e) = scalarComap γ f • testComap γ e := by
  ext x
  rfl

end Scalars

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

/-- Identity on global sections, comparing the two published compact-section APIs. -/
def compactSectionEquiv (F : VectorSheaf X) :
    Distributions.CompactSection F ≃ₗ[ℂ] CompactSupport.submodule F.presheaf :=
  LinearEquiv.refl ℂ _

@[simp]
theorem compactSectionEquiv_apply (F : VectorSheaf X) (s : Distributions.CompactSection F) :
    (compactSectionEquiv F s).val = s.val := rfl

/-- The induced identity comparison on the actual complex algebraic duals. -/
def distributionEquiv (F : VectorSheaf X) :
    Distributions.Distribution F ≃ₗ[ℂ] Module.Dual ℂ (CompactSupport.submodule F.presheaf) :=
  (compactSectionEquiv F).symm.dualMap

@[simp]
theorem distributionEquiv_apply (F : VectorSheaf X) (T : Distributions.Distribution F)
    (s : CompactSupport.submodule F.presheaf) :
    distributionEquiv F T s = T ((compactSectionEquiv F).symm s) := rfl

/-- Restricting the full scalar action to tests recovers the published test action. -/
theorem inclusion_smul (F : VectorSheaf X) (e : PointwiseTestAlgebra.Carrier X)
    (s : Distributions.CompactSection F) :
    (PointwiseTestAlgebra.inclusion e • s : Distributions.CompactSection F) = e • s :=
  Subtype.ext rfl

/-- The full scalar action and test action have their common pointwise multiplication. -/
theorem lc_test_smul (F : VectorSheaf X) (f : LocallyConstant X ℂ)
    (e : PointwiseTestAlgebra.Carrier X) (s : Distributions.CompactSection F) :
    (f • e) • s = f • (e • s) := by
  apply Subtype.ext
  change Distributions.topScalar (f * e.val) • s.val =
    Distributions.topScalar f • Distributions.topScalar e.val • s.val
  rw [map_mul, mul_smul]

variable {F : VectorSheaf X} {E : VectorSheaf Y}
    (Φ : SheafIso F E)

/-- The published section isomorphism read in the distribution compact-section API. -/
def sectionEquiv (hX : Langlands.Topology.IsLocallyProfinite X) :
    Distributions.CompactSection F ≃ₗ[ℂ] Distributions.CompactSection E :=
  compactSectionEquiv F ≪≫ₗ Φ.linearEquiv hX ≪≫ₗ (compactSectionEquiv E).symm

@[simp]
theorem sectionEquiv_apply (hX : Langlands.Topology.IsLocallyProfinite X)
    (s : Distributions.CompactSection F) :
    sectionEquiv Φ hX s = Φ.sectionEquiv s := rfl

set_option backward.isDefEq.respectTransparency false in
/-- Test-linearity forces compatibility with every locally constant multiplier. -/
theorem sectionEquiv_smul (hX : Langlands.Topology.IsLocallyProfinite X)
    (f : LocallyConstant X ℂ) (s : Distributions.CompactSection F) :
    sectionEquiv Φ hX (f • s) =
      scalarComap Φ.homeomorph.symm f • sectionEquiv Φ hX s := by
  let : Module (LocallyConstant X ℂ) (CompactSupport.submodule F.presheaf) :=
    Distributions.compactSectionModule F
  let : Module (LocallyConstant Y ℂ) (CompactSupport.submodule E.presheaf) :=
    Distributions.compactSectionModule E
  obtain ⟨e, he⟩ := CompactSectionTestModule.isNondegenerate F hX s
  change Φ.sectionEquiv (f • s) =
    scalarComap Φ.homeomorph.symm f • Φ.sectionEquiv s
  calc
    Φ.sectionEquiv (f • s) =
        Φ.sectionEquiv ((f • (e : PointwiseTestAlgebra.Carrier X)) • s) := by
      rw [lc_test_smul, he]
    _ = testComap Φ.homeomorph.symm (f • (e : PointwiseTestAlgebra.Carrier X)) •
        Φ.sectionEquiv s := Φ.map_smul _ _
    _ = scalarComap Φ.homeomorph.symm f •
        (testComap Φ.homeomorph.symm (e : PointwiseTestAlgebra.Carrier X) •
          Φ.sectionEquiv s) := by
      rw [testComap_lc_smul, lc_test_smul]
    _ = scalarComap Φ.homeomorph.symm f • Φ.sectionEquiv s := by
      rw [← Φ.map_smul, he]

/-- The scalar-compatibility identity using functions on the target space. -/
theorem sectionEquiv_comap_smul (hX : Langlands.Topology.IsLocallyProfinite X)
    (g : LocallyConstant Y ℂ) (s : Distributions.CompactSection F) :
    sectionEquiv Φ hX (scalarComap Φ.homeomorph g • s) =
      g • sectionEquiv Φ hX s := by
  rw [sectionEquiv_smul, scalarComap_symm_scalarComap]

/-- The transpose on Renard's distributions, with its actual inverse. -/
def transpose (hX : Langlands.Topology.IsLocallyProfinite X) :
    Distributions.Distribution E ≃ₗ[ℂ] Distributions.Distribution F :=
  (sectionEquiv Φ hX).dualMap

@[simp]
theorem transpose_apply (hX : Langlands.Topology.IsLocallyProfinite X)
    (T : Distributions.Distribution E) (s : Distributions.CompactSection F) :
    transpose Φ hX T s = T (sectionEquiv Φ hX s) := rfl

/-- This transpose is the published homeomorphism transpose under the identity bridges. -/
theorem distributionEquiv_transpose (hX : Langlands.Topology.IsLocallyProfinite X)
    (T : Distributions.Distribution E) :
    distributionEquiv F (transpose Φ hX T) =
      Φ.transpose hX (distributionEquiv E T) := by
  ext s
  rfl

/-- The transpose intertwines the full locally constant distribution actions. -/
theorem transpose_smul (hX : Langlands.Topology.IsLocallyProfinite X)
    (g : LocallyConstant Y ℂ) (T : Distributions.Distribution E) :
    transpose Φ hX (g • T) = scalarComap Φ.homeomorph g • transpose Φ hX T := by
  ext s
  change T (g • sectionEquiv Φ hX s) =
    T (sectionEquiv Φ hX (scalarComap Φ.homeomorph g • s))
  rw [sectionEquiv_comap_smul]

end Langlands.Sheaf.Renard.DistributionHomeomorph
