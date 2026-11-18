import Langlands.Geometry.FormalGroup.RationalSectionGlobal
import Langlands.Geometry.FormalGroup.FiniteKernelCompositionStatement

/-! # Composition of local quasi-isogenies from finite-kernel composition -/

noncomputable section
universe u v

namespace Langlands.FormalGroup.ModuleLaw
open CategoryTheory Opposite TopologicalSpace

attribute [local instance] coefficientAlgebra coefficientScalarTower

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {F : Type v} [Field F] [Algebra O F]
variable {σ τ υ : Type} [Finite σ] [Finite τ] [Finite υ]
variable {M : ModuleLaw O R σ} {N : ModuleLaw O R τ} {P : ModuleLaw O R υ}
variable {π : O} {U V : Opens (PrimeSpectrum R)}

variable (hfinite : ∀ W : Opens (PrimeSpectrum R),
  Hom.FiniteKernelCompositionStatement
    (M.overAlgebra ((coefficientStructurePresheaf R).obj (op W)))
    (N.overAlgebra ((coefficientStructurePresheaf R).obj (op W)))
    (P.overAlgebra ((coefficientStructurePresheaf R).obj (op W))))

include hfinite in
/-- Compose the actual local numerators on the intersection of their witnessing opens. -/
theorem RationalSection.IsLocallyScalarIsogeny.comp_of_finiteKernelComposition
    {f : RationalSection F M N U} {g : RationalSection F N P U}
    (hg : IsLocallyScalarIsogeny π g) (hf : IsLocallyScalarIsogeny π f) :
    IsLocallyScalarIsogeny π (RationalSection.comp g f) := by
  intro x hx
  obtain ⟨Wf, hxf, i, m, f₀, hf₀, hef⟩ := hf x hx
  obtain ⟨Wg, hxg, j, n, g₀, hg₀, heg⟩ := hg x hx
  let W := Wf ⊓ Wg
  let a : W ⟶ Wf := homOfLE inf_le_left
  let b : W ⟶ Wg := homOfLE inf_le_right
  let k : W ⟶ U := a ≫ i
  have hk : b ≫ j = k := Subsingleton.elim _ _
  let f₁ : OpenIntegralHom M N W :=
    Hom.algebraMapLinear ((coefficientStructurePresheaf R).map a.op) f₀
  let g₁ : OpenIntegralHom N P W :=
    Hom.algebraMapLinear ((coefficientStructurePresheaf R).map b.op) g₀
  have hf₁ : f₁.IsIsogeny := hf₀.algebraMapLinear _
  have hg₁ : g₁.IsIsogeny := hg₀.algebraMapLinear _
  have hsf : (algebraMap O F π) ^ m • RationalSection.restrict k f =
      RationalSection.ofIntegral W f₁ := by
    have h := congrArg (RationalSection.restrict a) hef
    simpa only [map_smul, ← RationalSection.restrict_comp, restrict_ofIntegral] using h
  have hsg : (algebraMap O F π) ^ n • RationalSection.restrict k g =
      RationalSection.ofIntegral W g₁ := by
    have h := congrArg (RationalSection.restrict b) heg
    simpa only [map_smul, ← RationalSection.restrict_comp, hk, restrict_ofIntegral] using h
  refine ⟨W, ⟨hxf, hxg⟩, k, n + m, g₁.comp f₁,
    hg₁.comp_of_finiteKernelComposition (hfinite W) hf₁, ?_⟩
  rw [RationalSection.restrict_comp_hom, pow_add, mul_smul, ← RationalSection.comp_smul,
    ← RationalSection.smul_comp, hsg, hsf, comp_ofIntegral]

namespace LocalQuasiIsogeny

/-- Compose local quasi-isogenies once finite-kernel composition holds on the open algebras. -/
def comp_of_finiteKernelComposition (g : LocalQuasiIsogeny F π N P U)
    (f : LocalQuasiIsogeny F π M N U) : LocalQuasiIsogeny F π M P U where
  scalar_ne_zero := f.scalar_ne_zero
  source_divisible := f.source_divisible
  target_divisible := g.target_divisible
  val := RationalSection.comp g.val f.val
  isLocal := g.isLocal.comp_of_finiteKernelComposition hfinite f.isLocal

@[simp]
theorem comp_of_finiteKernelComposition_val (g : LocalQuasiIsogeny F π N P U)
    (f : LocalQuasiIsogeny F π M N U) :
    (comp_of_finiteKernelComposition hfinite g f).val = RationalSection.comp g.val f.val := rfl

theorem restrict_comp_of_finiteKernelComposition (g : LocalQuasiIsogeny F π N P U)
    (f : LocalQuasiIsogeny F π M N U) (i : V ⟶ U) :
    (comp_of_finiteKernelComposition hfinite g f).restrict i =
      comp_of_finiteKernelComposition hfinite (g.restrict i) (f.restrict i) := by
  apply ext
  exact RationalSection.restrict_comp_hom i g.val f.val

end LocalQuasiIsogeny
end Langlands.FormalGroup.ModuleLaw
