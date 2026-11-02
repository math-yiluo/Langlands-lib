import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.RingTheory.TensorProduct.IsBaseChangePi
import Mathlib.RingTheory.Localization.Finiteness

/-! # Descent of finitely presented modules through localization -/

universe u v w

namespace Langlands.CommutativeAlgebra

/-- A finitely generated submodule of a localized module is the localization
of a finitely generated submodule of the original module. -/
theorem exists_fg_submodule_localized'_eq
    {R : Type u} [CommRing R] (S : Submonoid R)
    {A : Type v} [CommRing A] [Algebra R A] [IsLocalization S A]
    {M : Type w} [AddCommGroup M] [Module R M]
    {N : Type*} [AddCommGroup N] [Module R N] [Module A N]
    [IsScalarTower R A N]
    (f : M →ₗ[R] N) [IsLocalizedModule S f]
    (P : Submodule A N) (hP : P.FG) :
    ∃ K : Submodule R M, K.FG ∧ K.localized' A S f = P := by
  classical
  obtain ⟨t, ht⟩ := hP
  have hrep : ∀ y : t, ∃ (a : M) (s : S), IsLocalizedModule.mk' f a s = y.1 := by
    intro y
    obtain ⟨⟨a, s⟩, h⟩ := IsLocalizedModule.mk'_surjective S f y.1
    exact ⟨a, s, h⟩
  choose a s hs using hrep
  let K := Submodule.span R (Set.range a)
  refine ⟨K, Submodule.fg_span (Set.finite_range a), le_antisymm ?_ ?_⟩
  · rw [Submodule.localized'_span, Submodule.span_le]
    rintro _ ⟨_, ⟨y, rfl⟩, rfl⟩
    have hy : y.1 ∈ P := ht ▸ Submodule.subset_span y.2
    have hnum : f (a y) = (s y) • y.1 := by
      rw [← hs y]
      exact (IsLocalizedModule.mk'_cancel' f (a y) (s y)).symm
    rw [hnum]
    exact P.smul_of_tower_mem (s y : R) hy
  · rw [← ht, Submodule.span_le]
    intro y hy
    exact ⟨a ⟨y, hy⟩, Submodule.subset_span ⟨⟨y, hy⟩, rfl⟩,
      s ⟨y, hy⟩, hs ⟨y, hy⟩⟩

/-- A finite presentation over the original ring together with an actual
localization map to the specified module. -/
structure FinitelyPresentedLocalizationModel
    (R : Type u) [CommRing R] (S : Submonoid R)
    (N : Type v) [AddCommGroup N] [Module R N] where
  rank : ℕ
  relations : Submodule R (Fin rank → R)
  relations_fg : relations.FG
  localizationMap : ((Fin rank → R) ⧸ relations) →ₗ[R] N
  isLocalizedModule : IsLocalizedModule S localizationMap

namespace FinitelyPresentedLocalizationModel

/-- The descended module, expressed as a finite presentation over `R`. -/
abbrev Carrier {R : Type u} [CommRing R] {S : Submonoid R}
    {N : Type v} [AddCommGroup N] [Module R N]
    (d : FinitelyPresentedLocalizationModel R S N) :=
  (Fin d.rank → R) ⧸ d.relations

instance finitePresentation {R : Type u} [CommRing R] {S : Submonoid R}
    {N : Type v} [AddCommGroup N] [Module R N]
    (d : FinitelyPresentedLocalizationModel R S N) :
    Module.FinitePresentation R d.Carrier :=
  Module.finitePresentation_of_free_of_surjective d.relations.mkQ
    d.relations.mkQ_surjective (by simpa using d.relations_fg)

instance localizedModule {R : Type u} [CommRing R] {S : Submonoid R}
    {N : Type v} [AddCommGroup N] [Module R N]
    (d : FinitelyPresentedLocalizationModel R S N) :
    IsLocalizedModule S d.localizationMap :=
  d.isLocalizedModule

/-- The canonical localization of the descended module recovers the specified
module, respecting its compatible action by the localized ring. -/
noncomputable def localizationEquiv {R : Type u} [CommRing R] {S : Submonoid R}
    {N : Type v} [AddCommGroup N] [Module R N] [Module (Localization S) N]
    [IsScalarTower R (Localization S) N]
    (d : FinitelyPresentedLocalizationModel R S N) :
    LocalizedModule S d.Carrier ≃ₗ[Localization S] N :=
  LinearEquiv.extendScalarsOfIsLocalization S (Localization S)
    (IsLocalizedModule.linearEquiv S
      (LocalizedModule.mkLinearMap S d.Carrier) d.localizationMap)

end FinitelyPresentedLocalizationModel

/-- Every finitely presented module over a localization has a finite
presentation model over the original ring. -/
theorem nonempty_finitelyPresentedLocalizationModel
    {R : Type u} [CommRing R] (S : Submonoid R)
    {N : Type v} [AddCommGroup N] [Module R N] [Module (Localization S) N]
    [IsScalarTower R (Localization S) N]
    [Module.FinitePresentation (Localization S) N] :
    Nonempty (FinitelyPresentedLocalizationModel R S N) := by
  obtain ⟨n, P, e, hP⟩ := Module.FinitePresentation.exists_fin (Localization S) N
  let f : (Fin n → R) →ₗ[R] (Fin n → Localization S) :=
    LinearMap.pi fun i ↦ (Algebra.linearMap R (Localization S)) ∘ₗ LinearMap.proj i
  have : IsLocalizedModule S f :=
    IsLocalizedModule.pi S (fun _ : Fin n ↦ Algebra.linearMap R (Localization S))
  obtain ⟨K, hK, hKP⟩ := exists_fg_submodule_localized'_eq S f P hP
  let eQ : ((Fin n → Localization S) ⧸ K.localized' (Localization S) S f) ≃ₗ[Localization S]
      ((Fin n → Localization S) ⧸ P) :=
    Submodule.quotEquivOfEq _ _ hKP
  let g := K.toLocalizedQuotient' (Localization S) S f
  let eN := (eQ.trans e.symm).restrictScalars R
  exact ⟨{
    rank := n
    relations := K
    relations_fg := hK
    localizationMap := eN.toLinearMap ∘ₗ g
    isLocalizedModule := IsLocalizedModule.of_linearEquiv S g eN
  }⟩

/-- A chosen finite presentation model of a finitely presented localized module. -/
noncomputable def finitelyPresentedLocalizationModel
    {R : Type u} [CommRing R] (S : Submonoid R)
    (N : Type v) [AddCommGroup N] [Module R N] [Module (Localization S) N]
    [IsScalarTower R (Localization S) N]
    [Module.FinitePresentation (Localization S) N] :
    FinitelyPresentedLocalizationModel R S N :=
  Classical.choice (nonempty_finitelyPresentedLocalizationModel S)

end Langlands.CommutativeAlgebra
