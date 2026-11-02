import Langlands.AlgebraicGeometry.Modules.CechResolution.CechTermDirectImageStatement
import Langlands.AlgebraicGeometry.Modules.CechResolution.Acyclic
import Langlands.AlgebraicGeometry.Modules.CoherentClosure
import Langlands.AlgebraicGeometry.Modules.DerivedRestrictionVanishing

/-!
# Proof: direct images of the terms of the sheafified Čech complex
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Modules.CechResolution

open Langlands.Cohomology.AcyclicResolution

section Acyclic

variable {X : Scheme.{u}} {R : CommRingCat.{u}} (π : X ⟶ Spec R) [IsSeparated π]

/-- For an affine open `W` of `X` separated over `Spec R` and a quasi-coherent `M`, the module
`sheafOn M W` has vanishing higher direct images along `π`. -/
theorem isZero_higherDirectImage_sheafOn (M : X.Modules) [M.IsQuasicoherent] {W : X.Opens}
    (hW : IsAffineOpen W) (n : ℕ) :
    IsZero ((DerivedSections.higherDirectImage π (n + 1)).obj (sheafOn M W)) := by
  have hWa : IsAffine W.toScheme := hW
  have : IsAffineHom W.ι := IsAffineHom.of_comp W.ι π
  have hM : ∀ q : ℕ, IsZero ((DerivedSections.higherDirectImage W.ι (q + 1)).obj
      ((Scheme.Modules.restrictFunctor W.ι).obj M)) := fun q =>
    affineQuasicoherentHigherDirectImageVanishing _ _ W.ι inferInstance _ inferInstance q
  have := isIso_compComparison (Scheme.Modules.pushforward π)
    (Scheme.Modules.pushforwardComp W.ι π) _ hM
    (fun J _ q => DerivedSections.isZero_higherDirectImage_pushforward_injective π W.ι J q)
    (n + 1)
  exact (affineQuasicoherentHigherDirectImageVanishing _ _ (W.ι ≫ π) inferInstance _
    inferInstance n).of_iso
    (asIso (compComparison (Scheme.Modules.pushforward π)
      (Scheme.Modules.pushforwardComp W.ι π) _ hM (n + 1))).symm

/-- The terms of the sheafified Čech complex of a quasi-coherent module on `X` separated over
`Spec R` have vanishing higher direct images along `π`. -/
theorem isZero_higherDirectImage_cechTerm (𝒰 : X.OrderedAffineCover) (M : X.Modules)
    [M.IsQuasicoherent] (p n : ℕ) :
    IsZero ((DerivedSections.higherDirectImage π (n + 1)).obj (cechTerm 𝒰 M p)) :=
  haveI : (DerivedSections.higherDirectImage π (n + 1)).Additive :=
    rightDerived_additive (Scheme.Modules.pushforward π) (n + 1)
  isZero_obj_biproduct _ _ fun s =>
    isZero_higherDirectImage_sheafOn π M (isAffineOpen_inter π 𝒰 s) n

end Acyclic

section Quasicoherent

set_option backward.isDefEq.respectTransparency false in
/-- Finite direct sums of quasi-coherent modules over an affine scheme are quasi-coherent. -/
lemma isQuasicoherent_biproduct_spec {R : CommRingCat.{u}} {ι : Type u} [Fintype ι]
    (B : ι → (Spec R).Modules) [∀ i, (B i).IsQuasicoherent] : (⨁ B).IsQuasicoherent := by
  have : PreservesBiproduct (fun i => (moduleSpecΓFunctor (R := R)).obj (B i))
      (tilde.functor R) :=
    preservesBiproduct_of_preservesCoproduct _
  let e : (tilde.functor R).obj (⨁ fun i => (moduleSpecΓFunctor (R := R)).obj (B i)) ≅ ⨁ B :=
    (tilde.functor R).mapBiproduct _ ≪≫ biproduct.mapIso fun i => asIso (B i).fromTildeΓ
  exact (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso e inferInstance

variable {X : Scheme.{u}} {R : CommRingCat.{u}} (π : X ⟶ Spec R)

/-- The direct image to `Spec R` of `sheafOn M W` for an affine open `W` is quasi-coherent. -/
lemma isQuasicoherent_pushforward_sheafOn (M : X.Modules) [M.IsQuasicoherent] {W : X.Opens}
    (hW : IsAffineOpen W) :
    ((Scheme.Modules.pushforward π).obj (sheafOn M W)).IsQuasicoherent := by
  have hWa : IsAffine W.toScheme := hW
  have := QuasicoherentLocal.isQuasicoherent_pushforward (W.ι ≫ π)
    ((Scheme.Modules.restrictFunctor W.ι).obj M)
  exact (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso
    ((Scheme.Modules.pushforwardComp W.ι π).app _).symm this

/-- The direct images to `Spec R` of the terms of the sheafified Čech complex of a
quasi-coherent module on `X` separated over `Spec R` are quasi-coherent. -/
theorem isQuasicoherent_pushforward_cechTerm [IsSeparated π] (𝒰 : X.OrderedAffineCover)
    (M : X.Modules) [M.IsQuasicoherent] (q : ℕ) :
    ((Scheme.Modules.pushforward π).obj (cechTerm 𝒰 M q)).IsQuasicoherent := by
  have : ∀ s : 𝒰.Idx q,
      ((Scheme.Modules.pushforward π).obj (sheafOn M (𝒰.inter s))).IsQuasicoherent :=
    fun s => isQuasicoherent_pushforward_sheafOn π M (isAffineOpen_inter π 𝒰 s)
  have hB := isQuasicoherent_biproduct_spec
    (fun s : 𝒰.Idx q => (Scheme.Modules.pushforward π).obj (sheafOn M (𝒰.inter s)))
  have : PreservesBiproduct (fun s : 𝒰.Idx q => sheafOn M (𝒰.inter s))
      (Scheme.Modules.pushforward π) :=
    have := (Scheme.Modules.pullbackPushforwardAdjunction π).isRightAdjoint
    preservesBiproduct_of_preservesProduct _
  exact (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso
    ((Scheme.Modules.pushforward π).mapBiproduct _).symm hB

end Quasicoherent

/-- Proof of `CechTermDirectImageStatement`. -/
theorem cechTermDirectImage : CechTermDirectImageStatement.{u} := by
  intro X R π _ 𝒰 M _ q
  exact ⟨isQuasicoherent_pushforward_cechTerm π 𝒰 M q,
    fun n => isZero_higherDirectImage_cechTerm π 𝒰 M q n⟩

end Langlands.AlgebraicGeometry.Modules.CechResolution
