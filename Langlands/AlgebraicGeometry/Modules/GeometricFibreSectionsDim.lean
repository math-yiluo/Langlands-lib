import Langlands.AlgebraicGeometry.Modules.ProperFlatFibreCohomologySemicontinuityProof
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme

/-! # Geometric fibre cohomology dimensions of proper flat families -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.Cohomology Langlands.Cohomology.FibreDimension

namespace Langlands.AlgebraicGeometry.Modules.GeometricFibreSectionsDim

open DerivedSections FibreSemicontinuity

attribute [local instance] HasDerivedCategory.standard

/-- **Geometric fibre cohomology dimensions.** Let `g : Y ⟶ Spec B` be proper and flat over a
noetherian ring, `F` an invertible module on `Y`, `k` a field and `sk : B →+* k`, with image
point `t` of `Spec k`. Then `dim_k Hᵖ(Y_k, F_k) = dim_{κ(t)} Hᵖ(Y_t, F_t)`, where `Y_k` is the
chosen pullback of `g` along `Spec k ⟶ Spec B`. -/
theorem finrank_relativeCohomology_geomFibre {B : Type u} [CommRing B] [IsNoetherianRing B]
    {Y : Scheme.{u}} (g : Y ⟶ Spec (CommRingCat.of B)) [IsProper g] [Flat g] (F : Y.Modules)
    (hF : Scheme.Modules.IsInvertibleFLT F) (k : Type u) [Field k] (sk : B →+* k) (p : ℕ) :
    (Module.finrank k ((relativeCohomology (pullback.snd g (Spec.map (CommRingCat.ofHom sk))) p).obj
        ((Scheme.Modules.pullback (pullback.fst g (Spec.map (CommRingCat.ofHom sk)))).obj F)) :
        ℤ) =
      fibreCohomologyDim g ((Spec.map (CommRingCat.ofHom sk)) (IsLocalRing.closedPoint k)) F p := by
  set t := (Spec.map (CommRingCat.ofHom sk)) (IsLocalRing.closedPoint k)
  let T := Spec (CommRingCat.of B)
  let f := pullback.snd g (T.fromSpecResidueField t)
  let a := pullback.fst g (T.fromSpecResidueField t)
  obtain ⟨K, hK, hmod⟩ := exists_perfectModel f ((Scheme.Modules.pullback a).obj F)
    (Scheme.Modules.IsInvertible.pullbackFLT (hL := hF) a)
  have : ∀ i, Module.Finite (T.residueField t) (K.X i) := fun i => (hK.2 i).1
  -- the fibre over `t` itself: base change along the identity of `κ(t)`
  have hdim₀ : (fibreCohomologyDim g t F p : ℤ) =
      homologyDim K p (kerPrime (CommRingCat.Hom.hom (𝟙 (T.residueField t)))) := by
    obtain ⟨e₀⟩ := hmod _ (𝟙 _)
    have hsq₀ : IsPullback (𝟙 _) f f (Spec.map (𝟙 (T.residueField t))) := by
      rw [Spec.map_id]
      exact IsPullback.id_horiz f
    obtain ⟨c₀⟩ := nonempty_relativeCohomology_iso_chosenPullback hsq₀
      ((Scheme.Modules.pullback a).obj F) p
    let E : fibreCohomology g t F p ≅
        ((ModuleComplex.baseChange (CommRingCat.Hom.hom (𝟙 (T.residueField t)))).obj K).homology p :=
      (relativeCohomology f p).mapIso
          ((Scheme.Modules.pullbackId _).app ((Scheme.Modules.pullback a).obj F)).symm ≪≫ c₀ ≪≫
        (DerivedPlus.homologyIsoOfIsoDerivedComplex _ e₀ p).symm
    rw [fibreCohomologyDim, E.toLinearEquiv.finrank_eq]
    exact finrank_homology_baseChange_eq K _ p
  -- the geometric fibre: base change along `κ(t) ⟶ k`
  let φ := T.descResidueField (Scheme.stalkClosedPointTo (Spec.map (CommRingCat.ofHom sk)))
  have hdim₁ : (Module.finrank k ((relativeCohomology
      (pullback.snd g (Spec.map (CommRingCat.ofHom sk))) p).obj
        ((Scheme.Modules.pullback (pullback.fst g (Spec.map (CommRingCat.ofHom sk)))).obj F)) :
        ℤ) = homologyDim K p (kerPrime φ.hom) := by
    obtain ⟨e₁⟩ := hmod _ φ
    have hbig : IsPullback (pullback.fst f (Spec.map φ) ≫ a) (pullback.snd f (Spec.map φ)) g
        (Spec.map (CommRingCat.ofHom sk)) := by
      have := (IsPullback.of_hasPullback f (Spec.map φ)).paste_horiz
        (IsPullback.of_hasPullback g (T.fromSpecResidueField t))
      rwa [Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField] at this
    obtain ⟨c₁⟩ := nonempty_relativeCohomology_iso_chosenPullback hbig F p
    let E : (relativeCohomology (pullback.snd g (Spec.map (CommRingCat.ofHom sk))) p).obj
        ((Scheme.Modules.pullback (pullback.fst g (Spec.map (CommRingCat.ofHom sk)))).obj F) ≅
        ((ModuleComplex.baseChange φ.hom).obj K).homology p :=
      c₁.symm ≪≫ (relativeCohomology _ p).mapIso
          ((Scheme.Modules.pullbackComp _ _).app F).symm ≪≫
        (DerivedPlus.homologyIsoOfIsoDerivedComplex _ e₁ p).symm
    rw [E.toLinearEquiv.finrank_eq]
    exact finrank_homology_baseChange_eq K _ p
  -- both kernels are zero
  have hker : kerPrime φ.hom = kerPrime (CommRingCat.Hom.hom (𝟙 (T.residueField t))) := by
    apply PrimeSpectrum.ext
    change RingHom.ker _ = RingHom.ker _
    rw [(RingHom.injective_iff_ker_eq_bot _).1 φ.hom.injective,
      (RingHom.injective_iff_ker_eq_bot _).1 (CommRingCat.Hom.hom (𝟙 (T.residueField t))).injective]
  rw [hdim₁, hker, ← hdim₀]

/-- The `H⁰` case in the form of the FLT dimension `geomFibreH0Finrank`. -/
theorem geomFibreH0Finrank_eq {B : Type u} [CommRing B] [IsNoetherianRing B]
    {Y : Scheme.{u}} (g : Y ⟶ Spec (CommRingCat.of B)) [IsProper g] [Flat g] (F : Y.Modules)
    (hF : Scheme.Modules.IsInvertibleFLT F) (k : Type u) [Field k] (sk : B →+* k) :
    (Scheme.Modules.geomFibreH0Finrank g F k sk : ℤ) =
      fibreCohomologyDim g ((Spec.map (CommRingCat.ofHom sk)) (IsLocalRing.closedPoint k)) F 0 := by
  rw [← finrank_relativeCohomology_geomFibre g F hF k sk 0]
  let e := (relativeCohomologyZeroIso (pullback.snd g (Spec.map (CommRingCat.ofHom sk)))).app
    ((Scheme.Modules.pullback (pullback.fst g (Spec.map (CommRingCat.ofHom sk)))).obj F)
  rw [e.toLinearEquiv.finrank_eq]
  have hring : (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
      (pullback.snd g (Spec.map (CommRingCat.ofHom sk))).appLE ⊤ ⊤ le_top =
        structureRingHom (pullback.snd g (Spec.map (CommRingCat.ofHom sk))) := by
    rw [structureRingHom, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  unfold Scheme.Modules.geomFibreH0Finrank
  dsimp only
  rw [hring]
  rfl

end Langlands.AlgebraicGeometry.Modules.GeometricFibreSectionsDim
