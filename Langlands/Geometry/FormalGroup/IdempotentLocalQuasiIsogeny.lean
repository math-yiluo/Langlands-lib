import Langlands.Geometry.FormalGroup.DivisibleHomFaithfulness
import Langlands.Geometry.FormalGroup.FiniteKernelRetract
import Langlands.Geometry.FormalGroup.RationalIdempotentImage
import Langlands.Geometry.FormalGroup.LocalQuasiIsogenyGroupoid

/-! # Restricting actual local quasi-isogenies to formal idempotent images -/

noncomputable section

universe u v

namespace Langlands.FormalGroup.ModuleLaw.Hom.IdempotentImage

open CategoryTheory Opposite TopologicalSpace

attribute [local instance] coefficientAlgebra coefficientScalarTower

variable {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {F : Type v} [Field F] [Algebra O F] [IsFractionRing O F]
variable {σ τ σ' τ' : Type} [Finite σ] [Finite τ] [Finite σ'] [Finite τ']
variable {M : ModuleLaw O R σ} {N : ModuleLaw O R τ}
variable {M' : ModuleLaw O R σ'} {N' : ModuleLaw O R τ'}
variable {e : Hom M M} {d : Hom N N} {π : O}
variable {U : Opens (PrimeSpectrum R)}
variable (A : IdempotentImage e M') (B : IdempotentImage d N')

/-- The rational restriction of an intertwining section has actual integral isogeny
numerators on a refinement of its original witnessing cover. -/
theorem restrictSection_isLocallyScalarIsogeny (hπ : Irreducible π)
    (hM : M.IsPiDivisible π) {z : RationalSection F M N U}
    (hz : RationalSection.IsLocallyScalarIsogeny π z)
    (he : RationalSection.comp z (RationalSection.ofHom e U) =
      RationalSection.comp (RationalSection.ofHom d U) z) :
    RationalSection.IsLocallyScalarIsogeny π (A.restrictSection B z) := by
  intro x hx
  obtain ⟨V, hxV, i, n, f, hf, hn⟩ := hz x hx
  have heV := congrArg (RationalSection.restrict i) he
  simp only [RationalSection.restrict_comp_hom, RationalSection.restrict_ofHom] at heV
  let φV := IsScalarTower.toAlgHom O R ((coefficientStructurePresheaf R).obj (op V))
  let a := (algebraMap O F π) ^ n
  have hnV : (RationalSection.ofIntegral V (f.comp (e.map φV)) : RationalSection F M N V) =
      RationalSection.ofIntegral V ((d.map φV).comp f) := by
    calc
      _ = RationalSection.comp (a • RationalSection.restrict i z)
          (RationalSection.ofHom e V) := by
        rw [show a • RationalSection.restrict i z = RationalSection.ofIntegral V f from hn]
        exact (RationalSection.comp_ofIntegral f (e.map φV)).symm
      _ = RationalSection.comp (RationalSection.ofHom d V)
          (a • RationalSection.restrict i z) := by
        rw [RationalSection.smul_comp, RationalSection.comp_smul, heV]
      _ = _ := by
        rw [show a • RationalSection.restrict i z = RationalSection.ofIntegral V f from hn]
        exact RationalSection.comp_ofIntegral (d.map φV) f
  obtain ⟨W, hxW, j, hj⟩ := RationalSection.exists_restrict_integral_eq hπ hM _ _ hnV x hxV
  let φW := IsScalarTower.toAlgHom O R ((coefficientStructurePresheaf R).obj (op W))
  let ψ := (coefficientStructurePresheaf R).map j.op
  let fW := Hom.algebraMapLinear ψ f
  have hW : fW.comp (e.map φW) = (d.map φW).comp fW := by
    change Hom.algebraMapLinear ψ (f.comp (e.map φV)) =
      Hom.algebraMapLinear ψ ((d.map φV).comp f) at hj
    rw [Hom.algebraMapLinear_hom_comp ψ f (e.map φV),
      Hom.algebraMapLinear_hom_comp ψ (d.map φV) f,
      Hom.algebraMapLinear_mapStructural ψ e, Hom.algebraMapLinear_mapStructural ψ d] at hj
    exact hj
  have hnum : (algebraMap O F π) ^ n • RationalSection.restrict (j ≫ i) z =
      RationalSection.ofIntegral W fW := by
    simpa only [RationalSection.restrict_comp, map_smul, RationalSection.restrict_ofIntegral] using
      congrArg (RationalSection.restrict j) hn
  refine ⟨W, hxW, j ≫ i, n, (A.map φW).restrictHom (B.map φW) fW,
    (A.map φW).restrictHom_isIsogeny (B.map φW) fW hW (hf.algebraMapLinear _), ?_⟩
  rw [A.restrict_restrictSection, restrictSection, ← RationalSection.comp_smul,
    ← RationalSection.smul_comp, hnum]
  change RationalSection.comp (RationalSection.ofIntegral W (B.projection.map φW))
    (RationalSection.comp (RationalSection.ofIntegral W fW)
      (RationalSection.ofIntegral W (A.inclusion.map φW))) = _
  rw [RationalSection.comp_ofIntegral, RationalSection.comp_ofIntegral]
  rfl

/-- Restriction preserves the full local quasi-isogeny structure, including actual
scalar divisibility of each image and local integral isogeny presentations. -/
def restrictLocalQuasiIsogeny (hπ : Irreducible π) (z : LocalQuasiIsogeny F π M N U)
    (he : RationalSection.comp z.val (RationalSection.ofHom e U) =
      RationalSection.comp (RationalSection.ofHom d U) z.val) :
    LocalQuasiIsogeny F π M' N' U where
  scalar_ne_zero := z.scalar_ne_zero
  source_divisible := A.isPiDivisible z.source_divisible
  target_divisible := B.isPiDivisible z.target_divisible
  val := A.restrictSection B z.val
  isLocal := A.restrictSection_isLocallyScalarIsogeny B hπ z.source_divisible z.isLocal he

/-- Its inverse rational section is the same as the restriction of the original
inverse, by uniqueness of the two-sided inverse. -/
theorem toSectionIso_restrictLocalQuasiIsogeny (hπ : Irreducible π)
    (z : LocalQuasiIsogeny F π M N U)
    (he : RationalSection.comp z.val (RationalSection.ofHom e U) =
      RationalSection.comp (RationalSection.ofHom d U) z.val) :
    (A.restrictLocalQuasiIsogeny B hπ z he).toSectionIso =
      A.restrictSectionIso B z.toSectionIso (by simpa only [LocalQuasiIsogeny.toSectionIso_hom] using he) := by
  apply RationalSectionIso.ext
  change (A.restrictLocalQuasiIsogeny B hπ z he).toSectionIso.hom =
    A.restrictSection B z.toSectionIso.hom
  rw [LocalQuasiIsogeny.toSectionIso_hom, LocalQuasiIsogeny.toSectionIso_hom]
  rfl

end Langlands.FormalGroup.ModuleLaw.Hom.IdempotentImage
