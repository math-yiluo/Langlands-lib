import Langlands.Global.Factors.RelativeWeilAssemblyGlobal
import Langlands.Global.AdelicFunctoriality.AlmostEverywhereSplitNormProof

/-! # Archimedean components of reciprocity characters trivial on `C_E` -/

noncomputable section

set_option autoImplicit false

universe u

namespace Langlands.LocalFactor.NonabelianBrauer

open NumberField ClassField.Global ClassField.Global.RelativeWeilGroup
open Langlands.Global Langlands.Global.AdelicFunctoriality
open scoped NumberField.LiesOver

attribute [local instance] relativeGaloisTopology

/-- At an infinite place `w` unramified over `v`, the local norm is onto. -/
theorem exists_localUnitNorm_eq {F E : Type u} [Field F] [Field E] [Algebra F E]
    (v : NumberField.InfinitePlace F) (w : NumberField.InfinitePlace E) [w.LiesOver v] (hw : w.IsUnramified F)
    (y : v.Completionˣ) :
    ∃ y' : w.Completionˣ, InfiniteExtension.localUnitNorm v w y' = y := by
  refine ⟨Units.map (NumberField.LiesOver.completionMap (v := v) (w := w)).toMonoidHom y,
    Units.ext ?_⟩
  rw [InfiniteExtension.localUnitNorm_val]
  change InfiniteExtension.localNorm v w (NumberField.LiesOver.completionMap (y : v.Completion)) =
    (y : v.Completion)
  rw [InfiniteExtension.localNorm_algebraMap, hw.finrank_eq_one v, pow_one]

/-- A real infinite place is unramified over every place below it. -/
theorem isUnramified_of_isReal {F E : Type u} [Field F] [Field E] [Algebra F E]
    {w : NumberField.InfinitePlace E} (hw : w.IsReal) : w.IsUnramified F := by
  by_contra h
  exact InfinitePlace.not_isReal_iff_isComplex.mpr
    (InfinitePlace.not_isUnramified_iff.mp h).1 hw

/-- **Archimedean components of reciprocity characters.** Let `Θ` be a Hecke character of `F`
whose reciprocity character `Θ ∘ τ_F` on `W_{E/F}` is trivial on `C_E`. Then the archimedean
component of `Θ` is trivial at every infinite place of `F` that has an unramified place of `E`
above it: such a local unit is the local norm of a unit of `E_w`, so its class is the transfer of
an element of `C_E`. -/
theorem infiniteComponent_eq_one_of_reciprocity_inclusion
    {c : FundamentalClass.ClassFamily.{u}} {F E : Type u} [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] [IsGalois F E] (Θ : HeckeCharacter F)
    (hΘ : ∀ a, continuousReciprocityCharacter c F E Θ (inclusion c F E a) = 1)
    (v : NumberField.InfinitePlace F) (w : InfinitePlacesAbove E v) (hw : w.1.IsUnramified F) :
    Θ.infiniteComponent v = 1 := by
  have : w.1.LiesOver v := w.2
  refine DFunLike.ext _ _ fun y => ?_
  obtain ⟨y', hy'⟩ := exists_localUnitNorm_eq v w.1 hw y
  have h1 := hΘ (IdeleClassGroup.ofCompletion (𝓞 E) E w.1 y')
  rw [continuousReciprocityCharacter_apply, transfer_inclusion, inv_eq_one,
    ideleClassNorm_ofCompletion v w y', hy'] at h1
  exact h1

/-- If `E` is totally real, the archimedean components of such a `Θ` are trivial everywhere. -/
theorem infiniteComponent_eq_one_of_isTotallyReal
    {c : FundamentalClass.ClassFamily.{u}} {F E : Type u} [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] [IsGalois F E] [IsTotallyReal E] (Θ : HeckeCharacter F)
    (hΘ : ∀ a, continuousReciprocityCharacter c F E Θ (inclusion c F E a) = 1)
    (v : NumberField.InfinitePlace F) : Θ.infiniteComponent v = 1 := by
  obtain ⟨w⟩ := exists_infinitePlace_above (L := E) v
  exact infiniteComponent_eq_one_of_reciprocity_inclusion Θ hΘ v w
    (isUnramified_of_isReal (IsTotallyReal.isReal w.1))

end Langlands.LocalFactor.NonabelianBrauer
