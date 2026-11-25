/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import WeilConjectures.AlgebraicGeometry.Modules.AffineExtensionSectionSurjectivity
import WeilConjectures.AlgebraicGeometry.Modules.LocallyFreeRank
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel

/-!
# Local splitting of short exact sequences of finite locally free modules

## References

* Stacks Project, Schemes, Tag 01IE
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
/-- On an affine spectrum, lift the identity of the projective module of quotient
sections through the quotient map on global sections. The tilde--Gamma counit and its
naturality turn this lift into a right inverse of the sheaf quotient map. -/
private theorem exists_section_spec {R : CommRingCat.{u}}
    (T : ShortComplex (Spec R).Modules) (hT : T.ShortExact) (r : ℕ)
    [T.X₁.IsQuasicoherent] [T.X₃.IsFiniteLocallyFreeOfRank r] :
    ∃ s : T.X₃ ⟶ T.X₂, s ≫ T.g = 𝟙 _ := by
  have := SheafOfModules.IsFiniteLocallyFreeOfRank.isLocallyFree T.X₃ r
  have hqc : T.X₃.IsQuasicoherent := inferInstance
  have hiso : IsIso T.X₃.fromTildeΓ := isIso_fromTildeΓ_of_isQuasicoherent T.X₃
  let G := moduleSpecΓFunctor (R := R)
  let L := tilde.functor R
  have : Epi (G.map T.g) := epi_globalSections_of_shortExact T hT
  obtain ⟨hfp, hflat, _⟩ := rankAtStalk_eq_of_isFiniteLocallyFreeOfRank T.X₃ (r := r)
  have : Module.FinitePresentation R (G.obj T.X₃) := hfp
  have : Module.Flat R (G.obj T.X₃) := hflat
  have : Module.Projective R (G.obj T.X₃) := Module.Flat.projective_of_finitePresentation
  let s := Projective.factorThru (𝟙 (G.obj T.X₃)) (G.map T.g)
  have hs : s ≫ G.map T.g = 𝟙 _ := Projective.factorThru_comp _ _
  refine ⟨inv T.X₃.fromTildeΓ ≫ L.map s ≫ T.X₂.fromTildeΓ, ?_⟩
  have hnat : L.map (G.map T.g) ≫ T.X₃.fromTildeΓ = T.X₂.fromTildeΓ ≫ T.g :=
    fromTildeΓNatTrans.naturality T.g
  rw [Category.assoc, Category.assoc, ← hnat, ← Category.assoc (L.map s),
    ← L.map_comp, hs, L.map_id, Category.id_comp, IsIso.inv_hom_id]

/-- A short exact sequence of modules of constant finite ranks splits on an open cover.
The middle-term isomorphism identifies the given maps with the biproduct inclusion and
projection, and the outer-term identifications are identities. -/
theorem exists_openCover_split_shortExact {X : Scheme.{u}} (S : ShortComplex X.Modules)
    (hS : S.ShortExact) (r₁ r₂ r₃ : ℕ)
    [S.X₁.IsFiniteLocallyFreeOfRank r₁] [S.X₂.IsFiniteLocallyFreeOfRank r₂]
    [S.X₃.IsFiniteLocallyFreeOfRank r₃] :
    ∃ (ι : Type u) (U : ι → X.Opens), (⨆ a, U a) = ⊤ ∧
      ∀ a, ∃ e : S.X₂.restrict (U a).ι ≅
          S.X₁.restrict (U a).ι ⊞ S.X₃.restrict (U a).ι,
        (restrictFunctor (U a).ι).map S.f ≫ e.hom = biprod.inl ∧
          e.hom ≫ biprod.snd = (restrictFunctor (U a).ι).map S.g := by
  classical
  -- Realize the local-section step on the affine cover instead of using the
  -- incorrectly oriented statement in LocalSectionQuotientFiniteFree.
  have := SheafOfModules.IsFiniteLocallyFreeOfRank.isLocallyFree S.X₁ r₁
  refine ⟨{U : X.Opens // IsAffineOpen U}, fun U ↦ U.1, ?_, ?_⟩
  · exact iSup_affineOpens_eq_top X
  · intro U
    let F := restrictFunctor U.1.ι
    let T := S.map F
    have hT : T.ShortExact := hS.map_of_exact F
    let H := restrictFunctor U.2.isoSpec.inv
    let K := restrictFunctor U.2.isoSpec.hom
    have hTH : (T.map H).ShortExact := hT.map_of_exact H
    have h₃ : (T.map H).X₃.IsFiniteLocallyFreeOfRank r₃ := by
      dsimp [T, F, H, ShortComplex.map]
      infer_instance
    have h₁ : (T.map H).X₁.IsQuasicoherent := by
      dsimp [T, F, H, ShortComplex.map]
      infer_instance
    obtain ⟨s, hs⟩ := exists_section_spec (T.map H) hTH r₃
    let t := ShortComplex.Splitting.ofExactOfSection (T.map H) hTH.exact s hs hTH.mono_f
    let e : H ⋙ K ≅ 𝟭 _ :=
      (restrictFunctorComp U.2.isoSpec.hom U.2.isoSpec.inv).symm ≪≫
        restrictFunctorCongr U.2.isoSpec.hom_inv_id ≪≫ restrictFunctorId
    let t' : T.Splitting := (t.map K).ofIso (T.mapNatIso e)
    refine ⟨t'.isoBinaryBiproduct, ?_, ?_⟩
    · change T.f ≫ t'.isoBinaryBiproduct.hom = biprod.inl
      apply biprod.hom_ext
      · simp [ShortComplex.Splitting.isoBinaryBiproduct]
      · simp [ShortComplex.Splitting.isoBinaryBiproduct, T.zero]
    · exact biprod.lift_snd _ _

end AlgebraicGeometry.Scheme.Modules
