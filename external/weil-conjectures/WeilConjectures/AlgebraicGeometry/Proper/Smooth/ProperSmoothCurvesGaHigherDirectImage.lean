/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.Topology.KrullDimension
public import Mathlib.Algebra.Category.Grp.Ulift
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.EtaleTensorSectionsSheaf
public import WeilConjectures.AlgebraicGeometry.Sites.ArtinSchreier
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import WeilConjectures.AlgebraicGeometry.Proper.Smooth.ProperSmoothCurvesGaHigherDirectImageVanishing
import WeilConjectures.AlgebraicGeometry.Proper.Smooth.ProperSmoothCurvesGaHigherDirectImageDegreeZero
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility

/-!
# Étale higher direct images of `𝔾ₐ` in a family of curves

For a proper smooth family `f : C ⟶ S` of curves with geometrically connected fibres over a
Noetherian base of characteristic `p`, the étale higher direct images `Rᵠf_* 𝔾ₐ` are the étale
sheaves of the finite locally free modules `Rᵠf_* 𝒪_C`, and the Artin--Schreier map induces
`F - 1` for a Frobenius-linear `F`. Concretely `E = Rᵠf_* 𝒪_C` with `F` induced by the absolute
Frobenius of `C`: `E = 𝒪_S` with `F` the Frobenius for `q = 0` (as `f_* 𝒪_C = 𝒪_S`
universally), `E` is locally free of rank the genus for `q = 1`, and `E = 0` otherwise.

This is an input from coherent cohomology (cohomology and base change for the structure sheaf
of a family of curves, and the comparison of étale and Zariski cohomology of quasi-coherent
modules); it is used in case (b) of Stacks Project, Tag 0GKV.

## Implementation details

The degree-one case `properSmoothCurves_higherDirectImage_ga_frobeniusLinear_one` is stated
without proof: there is not yet a cohomology and base change theorem for `R¹f_* 𝒪_C` of a
family of curves, nor the comparison of its étale sheaf with `R¹f_* 𝔾ₐ` compatibly with
Frobenius.

## References

* Stacks Project, Tag 0GKV, case (b): "`R¹f_*𝒪_X` is finite locally free and its formation
  commutes with base change"
* Cohomology and base change (Stacks, Tags 0BDJ, 0E0L), flat base change (Tag 02KH) and the
  comparison of étale and Zariski cohomology of quasi-coherent modules (Tag 03DW)
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Etale

/-- **The degree-zero case of `properSmoothCurves_higherDirectImage_ga_frobeniusLinear`.**
`H⁰(Rf_* 𝔾ₐ) = f_* 𝔾ₐ` is the universe lift of the étale sheaf of `E = 𝒪_S`, with the map induced
by `℘ = Frob - 1` corresponding to `F - 1` for the Frobenius `F: x ↦ xᵖ`: `f_*` is left exact and
`𝒪_S → f_* 𝒪_C` is an isomorphism universally (Stacks, Tag 0E0L). -/
theorem properSmoothCurves_higherDirectImage_ga_frobeniusLinear_zero
    {C S : Scheme.{u}} [IsNoetherian S]
    (f : C ⟶ S) [IsProper f] [Smooth f] [GeometricallyConnected f]
    (_h_dim : ∀ s : S, topologicalKrullDim (f.fiber s) = 1)
    (p : ℕ) [Fact p.Prime] (hpS : (p : Γ(S, ⊤)) = 0) (hpC : (p : Γ(C, ⊤)) = 0) :
    ∃ (E : S.Modules) (_ : E.IsQuasicoherent) (_ : E.IsFiniteLocallyFree)
      (F : Scheme.Modules.etaleTensorSectionsSheaf E ⟶
        Scheme.Modules.etaleTensorSectionsSheaf E),
      (∀ (U : S.Etale) (a : Γ(U.left, ⊤))
        (e : Γ((Scheme.Modules.tensorPullback U.hom).obj E, ⊤)),
        F.hom.app (op U)
            ((((Scheme.Modules.tensorPullback U.hom).obj E).smul a).asHom.hom e) =
          (((Scheme.Modules.tensorPullback U.hom).obj E).smul (a ^ p)).asHom.hom
            (F.hom.app (op U) e)) ∧
      ∃ e : (DerivedCategory.homologyFunctor _ 0).obj
            ((lowerStar AddCommGrpCat.{u + 1} f).rightDerivedFunctor.obj
              ((DerivedCategory.singleFunctor _ 0).obj C.gaSheaf)) ≅
          (sheafCompose S.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
            (Scheme.Modules.etaleTensorSectionsSheaf E),
        (DerivedCategory.homologyFunctor _ 0).map
            ((lowerStar AddCommGrpCat.{u + 1} f).rightDerivedFunctor.map
              ((DerivedCategory.singleFunctor _ 0).map (C.gaArtinSchreier p hpC))) ≫ e.hom =
          e.hom ≫ (sheafCompose S.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}).map
            (F - 𝟙 _) := by
  exact properSmoothCurves_higherDirectImage_ga_frobeniusLinear_zero_aux f p hpS hpC

/-- **The degree-one case of `properSmoothCurves_higherDirectImage_ga_frobeniusLinear`.**
With the hypotheses of `properSmoothCurves_higherDirectImage_ga_frobeniusLinear`, the étale
sheaf `R¹f_* 𝔾ₐ` is the universe lift of the étale sheaf of a finite locally free
quasi-coherent `𝒪_S`-module `E = R¹f_* 𝒪_C`, with the map induced by `℘ = Frob - 1`
corresponding to `F - 1` for a Frobenius-linear `F` induced by the absolute Frobenius of `C`. -/
theorem properSmoothCurves_higherDirectImage_ga_frobeniusLinear_one
    {C S : Scheme.{u}} [IsNoetherian S]
    (f : C ⟶ S) [IsProper f] [Smooth f] [GeometricallyConnected f]
    (h_dim : ∀ s : S, topologicalKrullDim (f.fiber s) = 1)
    (p : ℕ) [Fact p.Prime] (hpS : (p : Γ(S, ⊤)) = 0) (hpC : (p : Γ(C, ⊤)) = 0) :
    ∃ (E : S.Modules) (_ : E.IsQuasicoherent) (_ : E.IsFiniteLocallyFree)
      (F : Scheme.Modules.etaleTensorSectionsSheaf E ⟶
        Scheme.Modules.etaleTensorSectionsSheaf E),
      (∀ (U : S.Etale) (a : Γ(U.left, ⊤))
        (e : Γ((Scheme.Modules.tensorPullback U.hom).obj E, ⊤)),
        F.hom.app (op U)
            ((((Scheme.Modules.tensorPullback U.hom).obj E).smul a).asHom.hom e) =
          (((Scheme.Modules.tensorPullback U.hom).obj E).smul (a ^ p)).asHom.hom
            (F.hom.app (op U) e)) ∧
      ∃ e : (DerivedCategory.homologyFunctor _ 1).obj
            ((lowerStar AddCommGrpCat.{u + 1} f).rightDerivedFunctor.obj
              ((DerivedCategory.singleFunctor _ 0).obj C.gaSheaf)) ≅
          (sheafCompose S.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
            (Scheme.Modules.etaleTensorSectionsSheaf E),
        (DerivedCategory.homologyFunctor _ 1).map
            ((lowerStar AddCommGrpCat.{u + 1} f).rightDerivedFunctor.map
              ((DerivedCategory.singleFunctor _ 0).map (C.gaArtinSchreier p hpC))) ≫ e.hom =
          e.hom ≫ (sheafCompose S.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}).map
            (F - 𝟙 _) := by
  sorry

/-- **Higher direct images of `𝔾ₐ` in a family of curves are Frobenius-linear vector bundles.**
Let `f: C ⟶ S` be proper and smooth with geometrically connected one-dimensional fibres, over a
Noetherian base `S` on which the prime `p` vanishes. For every degree `q` there are a finite
locally free quasi-coherent `𝒪_S`-module `E` and a Frobenius-linear endomorphism `F` of its
étale sheaf (`F (a e) = aᵖ F e`) such that the degree-`q` étale higher direct image of `𝔾ₐ` is
the universe lift of the étale sheaf of `E`, with the map induced by the Artin--Schreier map
`℘ = Frob - 1` corresponding to `F - 1`. -/
theorem properSmoothCurves_higherDirectImage_ga_frobeniusLinear
    {C S : Scheme.{u}} [IsNoetherian S]
    (f : C ⟶ S) [IsProper f] [Smooth f] [GeometricallyConnected f]
    (h_dim : ∀ s : S, topologicalKrullDim (f.fiber s) = 1)
    (p : ℕ) [Fact p.Prime] (hpS : (p : Γ(S, ⊤)) = 0) (hpC : (p : Γ(C, ⊤)) = 0) (q : ℤ) :
    ∃ (E : S.Modules) (_ : E.IsQuasicoherent) (_ : E.IsFiniteLocallyFree)
      (F : Scheme.Modules.etaleTensorSectionsSheaf E ⟶
        Scheme.Modules.etaleTensorSectionsSheaf E),
      (∀ (U : S.Etale) (a : Γ(U.left, ⊤))
        (e : Γ((Scheme.Modules.tensorPullback U.hom).obj E, ⊤)),
        F.hom.app (op U)
            ((((Scheme.Modules.tensorPullback U.hom).obj E).smul a).asHom.hom e) =
          (((Scheme.Modules.tensorPullback U.hom).obj E).smul (a ^ p)).asHom.hom
            (F.hom.app (op U) e)) ∧
      ∃ e : (DerivedCategory.homologyFunctor _ q).obj
            ((lowerStar AddCommGrpCat.{u + 1} f).rightDerivedFunctor.obj
              ((DerivedCategory.singleFunctor _ 0).obj C.gaSheaf)) ≅
          (sheafCompose S.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
            (Scheme.Modules.etaleTensorSectionsSheaf E),
        (DerivedCategory.homologyFunctor _ q).map
            ((lowerStar AddCommGrpCat.{u + 1} f).rightDerivedFunctor.map
              ((DerivedCategory.singleFunctor _ 0).map (C.gaArtinSchreier p hpC))) ≫ e.hom =
          e.hom ≫ (sheafCompose S.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}).map
            (F - 𝟙 _) := by
  rcases lt_trichotomy q 1 with hq | rfl | hq
  · rcases (show q ≤ 0 by omega).lt_or_eq with hq | rfl
    · exact exists_frobeniusLinear_of_isZero_homology f p hpC q
        ((DerivedCategory.isGE_iff _ 0).mp
          ((lowerStar AddCommGrpCat.{u + 1} f).isGE_rightDerivedFunctor_obj_singleFunctor
            C.gaSheaf) q hq)
    · exact properSmoothCurves_higherDirectImage_ga_frobeniusLinear_zero f h_dim p hpS hpC
  · exact properSmoothCurves_higherDirectImage_ga_frobeniusLinear_one f h_dim p hpS hpC
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ q)
    exact exists_frobeniusLinear_of_isZero_homology f p hpC n
      (isZero_homology_rightDerivedFunctor_lowerStar_gaSheaf f (d := 1)
        (fun s ↦ (h_dim s).le) (by omega))

end AlgebraicGeometry.Etale
