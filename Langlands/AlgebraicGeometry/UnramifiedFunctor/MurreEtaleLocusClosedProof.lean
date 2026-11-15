import Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreEtaleLocusClosed
import Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreChartsLocal
import Mathlib.RingTheory.Unramified.LocalStructure

/-! # Reduction of Murre's Lemma 2 to closed subschemes of étale schemes -/

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

noncomputable section

namespace Langlands.AlgebraicGeometry.UnramifiedFunctor

namespace ClosedReduction

section Open

variable {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type v}

/-- Infinitesimal étaleness at a point of an open subscheme gives infinitesimal étaleness at
its image. -/
theorem infinitesimallyEtaleAt_of_isOpenImmersion {U V : Over S} (ι : V ⟶ U)
    [IsOpenImmersion ι.left] {ξ : F.obj (op U)} {y : V.left}
    (h : InfinitesimallyEtaleAt F (F.map ι.op ξ) y) :
    InfinitesimallyEtaleAt F ξ (ι.left y) := by
  refine Charts.infinitesimallyEtaleAt_of_factor ι ξ _ ?_ ?_
  · intro L _ _ _ w hw
    have hrange : Set.range w ⊆ Set.range ι.left := by
      rintro _ ⟨x, rfl⟩
      exact ⟨y, (hw x).symm⟩
    refine ⟨IsOpenImmersion.lift ι.left w hrange, IsOpenImmersion.lift_fac _ _ _, ?_⟩
    intro w' hw'
    rw [← cancel_mono ι.left, hw', IsOpenImmersion.lift_fac]
  · intro y' hy'
    rwa [ι.left.isOpenEmbedding.injective hy']

/-- For an open immersion `ι : V ⟶ U`, a point of `V` lies in the étale locus of the
restriction of `ξ` exactly when its image lies in the étale locus of `ξ`. -/
theorem infinitesimallyEtaleAt_map_iff {U V : Over S} (ι : V ⟶ U)
    [IsOpenImmersion ι.left] {ξ : F.obj (op U)} {y : V.left} :
    InfinitesimallyEtaleAt F (F.map ι.op ξ) y ↔ InfinitesimallyEtaleAt F ξ (ι.left y) :=
  ⟨infinitesimallyEtaleAt_of_isOpenImmersion ι, Charts.infinitesimallyEtaleAt_restrict ι⟩

end Open

section Chart

variable {R : CommRingCat.{u}}

/-- EGA IV 18.4.7, from Mathlib's local structure of unramified algebras: an `Spec R`-scheme
`U` locally of finite type and formally unramified is covered by open subschemes of the form
`Spec (R'/𝔍)` with `R'` étale over `R`. -/
theorem exists_closed_chart (U : Over (Spec R)) (hU₁ : LocallyOfFiniteType U.hom)
    (hU₂ : FormallyUnramified U.hom) (y : U.left) :
    ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra R R') (_ : Algebra.Etale R R')
      (𝔍 : Ideal R')
      (ι : algebraOver (Spec.map (CommRingCat.ofHom (algebraMap R R'))) (R' ⧸ 𝔍) ⟶ U),
      IsOpenImmersion ι.left ∧ y ∈ Set.range ι.left := by
  obtain ⟨C, f, hf, ⟨y₀, rfl⟩, -⟩ :=
    Scheme.exists_affine_mem_range_and_range_subset (U := ⊤) (x := y) trivial
  let φ : R ⟶ C := Spec.preimage (f ≫ U.hom)
  have hφ : Spec.map φ = f ≫ U.hom := Spec.map_preimage _
  let _ : Algebra R C := φ.hom.toAlgebra
  have hLFT : LocallyOfFiniteType (Spec.map φ) := by
    rw [hφ]
    infer_instance
  have hFU : FormallyUnramified (Spec.map φ) := by
    rw [hφ]
    have : IsIso (pullback.diagonal f) := (pullback.isIso_diagonal_iff f).2 inferInstance
    have : FormallyUnramified f := inferInstance
    exact MorphismProperty.comp_mem @FormallyUnramified f U.hom inferInstance inferInstance
  have : Algebra.FiniteType R C :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).1 hLFT
  have : Algebra.FormallyUnramified R C :=
    (HasRingHomProperty.Spec_iff (P := @FormallyUnramified)).1 hFU
  have := y₀.isPrime
  have : Algebra.IsUnramifiedAt R y₀.asIdeal :=
    Algebra.formallyUnramified_iff_forall.1 inferInstance y₀
  obtain ⟨s, hs, P, ψ, hψ⟩ :=
    Algebra.IsUnramifiedAt.exists_hasStandardEtaleSurjectionOn (R := R) y₀.asIdeal
  let 𝔍 : Ideal P.Ring := RingHom.ker ψ
  let e : (P.Ring ⧸ 𝔍) ≃ₐ[R] Localization.Away s := Ideal.quotientKerAlgEquivOfSurjective hψ
  let k : C →+* P.Ring ⧸ 𝔍 := e.symm.toRingHom.comp (algebraMap C (Localization.Away s))
  let _ : Algebra C (P.Ring ⧸ 𝔍) := k.toAlgebra
  have : IsLocalization.Away s (P.Ring ⧸ 𝔍) :=
    IsLocalization.isLocalization_of_algEquiv (Submonoid.powers s)
      { e.symm with commutes' := fun c => rfl }
  have : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap C (P.Ring ⧸ 𝔍)))) :=
    IsOpenImmersion.of_isLocalization s
  let ι : algebraOver (Spec.map (CommRingCat.ofHom (algebraMap R P.Ring))) (P.Ring ⧸ 𝔍) ⟶ U :=
    Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap C (P.Ring ⧸ 𝔍))) ≫ f) (by
      dsimp
      rw [Category.assoc, ← hφ, ← Spec.map_comp, ← Spec.map_comp]
      congr 1
      ext x
      change k (algebraMap R C x) = algebraMap P.Ring (P.Ring ⧸ 𝔍) (algebraMap R P.Ring x)
      rw [← IsScalarTower.algebraMap_apply]
      simp only [k, RingHom.comp_apply, ← IsScalarTower.algebraMap_apply]
      exact e.symm.commutes x)
  refine ⟨P.Ring, inferInstance, inferInstance, inferInstance, 𝔍, ι,
    inferInstanceAs (IsOpenImmersion (_ ≫ f)), ?_⟩
  have hmem : y₀ ∈ Set.range (PrimeSpectrum.comap (algebraMap C (P.Ring ⧸ 𝔍))) := by
    rw [PrimeSpectrum.localization_away_comap_range (P.Ring ⧸ 𝔍) s]
    exact hs
  obtain ⟨z, hz⟩ := hmem
  exact ⟨z, by
    change f (Spec.map (CommRingCat.ofHom (algebraMap C (P.Ring ⧸ 𝔍))) z) = f y₀
    exact congrArg f hz⟩

end Chart

end ClosedReduction

namespace EtaleLocus

/-- The reduction step of Murre's proof of Lemma 2. -/
theorem murreEtaleLocusOpen_of_closed : ClosedReductionStatement.{u, v} := by
  intro H R _ F hF hloc hclosed U ξ hLFT _ _ hFU
  rw [isOpen_iff_forall_mem_open]
  intro y hy
  obtain ⟨R', _, _, _, 𝔍, ι, hι, ⟨y', rfl⟩⟩ := ClosedReduction.exists_closed_chart U hLFT hFU y
  have hopen := H R F hF hloc hclosed R' 𝔍 (F.map ι.op ξ)
  refine ⟨ι.left '' {z | InfinitesimallyEtaleAt F (F.map ι.op ξ) z}, ?_,
    ι.left.isOpenEmbedding.isOpenMap _ hopen, ⟨y', ?_, rfl⟩⟩
  · rintro _ ⟨z, hz, rfl⟩
    exact (ClosedReduction.infinitesimallyEtaleAt_map_iff ι).1 hz
  · exact (ClosedReduction.infinitesimallyEtaleAt_map_iff ι).2 hy

end EtaleLocus

end Langlands.AlgebraicGeometry.UnramifiedFunctor
