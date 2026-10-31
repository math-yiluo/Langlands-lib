import Langlands.AlgebraicGeometry.Modules.CechResolution.Complex
import Langlands.AlgebraicGeometry.Modules.AffineQuasicoherentCohomologyVanishingProof
import Langlands.AlgebraicGeometry.Modules.AffineQuasicoherentHigherDirectImageVanishingProof
import Langlands.AlgebraicGeometry.Modules.PushforwardInjectiveAcyclicProof
import Langlands.AlgebraicGeometry.Modules.PushforwardComparison
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# The terms of the sheafified Čech complex are acyclic for `R`-module global sections

Let `π : X ⟶ Spec R` be separated, `𝒰` an ordered affine cover of `X` and `M` a quasi-coherent
`𝒪_X`-module. Every finite intersection `𝒰.inter s` is affine, and for an affine open `W` the
module `sheafOn M W = (W ⟶ X)_* (M|_W)` has vanishing higher `R`-module cohomology: the
pushforward comparison identifies it with the cohomology of `M|_W` on the affine scheme `W`,
which vanishes. Right derived functors are additive, so the finite biproducts
`cechTerm 𝒰 M p` are acyclic as well.
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.Modules.CechResolution

section Additive

variable {C : Type*} [Category C] [Abelian C] [HasInjectiveResolutions C]
  {D : Type*} [Category D] [Abelian D]

/-- Right derived functors of an additive functor are additive. -/
instance rightDerived_additive (F : C ⥤ D) [F.Additive] (n : ℕ) : (F.rightDerived n).Additive where
  map_add {X Y f g} := by
    rw [F.rightDerived_map_eq n (f + g)
        (InjectiveResolution.desc f (injectiveResolution Y) (injectiveResolution X) +
          InjectiveResolution.desc g (injectiveResolution Y) (injectiveResolution X))
        (by rw [Preadditive.comp_add, InjectiveResolution.desc_commutes,
          InjectiveResolution.desc_commutes, Functor.map_add, Preadditive.add_comp]),
      F.rightDerived_map_eq n f _ (InjectiveResolution.desc_commutes _ _ _),
      F.rightDerived_map_eq n g _ (InjectiveResolution.desc_commutes _ _ _),
      Functor.map_add, Preadditive.add_comp, Preadditive.comp_add]

end Additive

/-- An additive functor vanishing on every summand of a finite biproduct vanishes on the
biproduct. -/
lemma isZero_obj_biproduct {C D : Type*} [Category C] [Category D] [Preadditive C]
    [Preadditive D] (G : C ⥤ D) [G.Additive] {J : Type*} [Fintype J] (f : J → C)
    [HasBiproduct f] (h : ∀ j, IsZero (G.obj (f j))) : IsZero (G.obj (⨁ f)) := by
  rw [IsZero.iff_id_eq_zero, ← G.map_id, ← IsBilimit.total (biproduct.isBilimit f), G.map_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [G.map_comp, (h j).eq_of_tgt (G.map _) 0, zero_comp]

variable {X : Scheme.{u}} {R : CommRingCat.{u}} (π : X ⟶ Spec R) [IsSeparated π]

include π in
/-- Over a separated base `X ⟶ Spec R`, the intersection of two affine opens is affine. -/
lemma isAffineOpen_inf {U V : X.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    IsAffineOpen (U ⊓ V) :=
  isAffineHom_diagonal_iff.mp (inferInstance : IsAffineHom (Limits.pullback.diagonal π)) ⊤
    (isAffineOpen_top _) U (by simp) V (by simp) hU hV

include π in
/-- Over a separated base `X ⟶ Spec R`, every finite intersection `𝒰.inter s` of an ordered
affine cover is affine. -/
lemma isAffineOpen_inter (𝒰 : X.OrderedAffineCover) {p : ℕ} (s : 𝒰.Idx p) :
    IsAffineOpen (𝒰.inter s) :=
  InfClosed.iInf_mem_of_nonempty (s := Set.ofPred IsAffineOpen)
    (fun _ h _ h' => isAffineOpen_inf π h h') (fun j => 𝒰.isAffineOpen (s.1 j))

/-- For an affine open `W` of `X` separated over `Spec R` and a quasi-coherent `M`, the module
`sheafOn M W` has vanishing higher `R`-module cohomology. -/
theorem isZero_relativeCohomology_sheafOn (M : X.Modules) [M.IsQuasicoherent] {W : X.Opens}
    (hW : IsAffineOpen W) (n : ℕ) :
    IsZero ((DerivedSections.relativeCohomology π (n + 1)).obj (sheafOn M W)) := by
  have hWa : IsAffine W.toScheme := hW
  have : IsAffineHom W.ι := IsAffineHom.of_comp W.ι π
  have hM : ∀ q : ℕ, IsZero ((DerivedSections.higherDirectImage W.ι (q + 1)).obj
      ((Scheme.Modules.restrictFunctor W.ι).obj M)) := fun q =>
    affineQuasicoherentHigherDirectImageVanishing _ _ W.ι inferInstance _ inferInstance q
  have hJ : ∀ J : W.toScheme.Modules, Injective J → ∀ q : ℕ,
      IsZero ((DerivedSections.relativeCohomology π (q + 1)).obj
        ((Scheme.Modules.pushforward W.ι).obj J)) := fun J hJ q =>
    (pushforwardInjectiveAcyclic _ _ W.ι J hJ q).2 R π
  have := DerivedSections.isIso_pushforwardComparison W.ι π _ hM hJ (n + 1)
  exact ((affineQuasicoherentCohomologyVanishing W.toScheme hWa _ inferInstance n).2 R
    (W.ι ≫ π)).of_iso (asIso (DerivedSections.pushforwardComparison W.ι π _ hM (n + 1))).symm

/-- The terms of the sheafified Čech complex of a quasi-coherent module on `X` separated over
`Spec R` have vanishing higher `R`-module cohomology. -/
theorem isZero_relativeCohomology_cechTerm (𝒰 : X.OrderedAffineCover) (M : X.Modules)
    [M.IsQuasicoherent] (p n : ℕ) :
    IsZero ((DerivedSections.relativeCohomology π (n + 1)).obj (cechTerm 𝒰 M p)) :=
  haveI : (DerivedSections.relativeCohomology π (n + 1)).Additive :=
    rightDerived_additive (DerivedSections.relativeGlobalSections π) (n + 1)
  isZero_obj_biproduct _ _ fun s =>
    isZero_relativeCohomology_sheafOn π M (isAffineOpen_inter π 𝒰 s) n

end Langlands.AlgebraicGeometry.Modules.CechResolution
