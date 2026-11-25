/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import all WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleLfpClosedReflection
import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-! # Transport of local finite presentation from an immersed stratum -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- Local finite presentation on an immersed stratum pulls back along maps into its image.
Source: Bhatt--Scholze, Lemma 5.4.2 (topological invariance) and Definition 6.8.10;
Hemo--Richarz--Scholbach, proof of Lemma 5.3(2), restriction to stratum interiors.
(auxiliary; not a blueprint node)

Proof: form V = U ×_T Z. Pull the given local finite presentations on Z back to V.
The projection V → U is a surjective immersion, hence a surjective closed immersion:
its image is all of U, so the open part of its locally closed factorization is all of U.
It is a universal homeomorphism. Topological invariance, computed on the affine
ind-etale basis, transports covering presentations from V to U. Under the induced
monoidal equivalence, the pulled
back coefficient ring and module identify with the restrictions of R and M to U.
Finite sums of the regular module and cokernels are preserved and reflected, so the
presentations on the covering of V give presentations on the corresponding covering of U.
Pullback composition and the cartesian square identify these with g^*M. Empty schemes
use empty covering families and zero-rank presentations, so require no surjectivity
witness beyond the stated image containment. The coefficient ring is arbitrary; no
scheme-theoretic factorization of g through i is asserted. -/
theorem localFinitePresentation_upperStar_of_range_subset
    {T Z U : Scheme.{u}} (i : Z ⟶ T) [IsImmersion i] (g : U ⟶ T)
    (hgi : Set.range g ⊆ Set.range i)
    (R : Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) [MonObj R]
    (M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) R)
    (hM : IsLocallyFinitelyPresented ((upperStar Ab.{u + 1} i).obj R)
      (((upperStar Ab.{u + 1} i).mapMod R).obj M)) :
    IsLocallyFinitelyPresented ((upperStar Ab.{u + 1} g).obj R)
      (((upperStar Ab.{u + 1} g).mapMod R).obj M) := by
  have hs : Function.Surjective (pullback.fst g i) := by
    intro x
    obtain ⟨z, hz⟩ := hgi ⟨x, rfl⟩
    obtain ⟨w, hw, _⟩ := Scheme.Pullback.exists_preimage_pullback x z hz.symm
    exact ⟨w, hw⟩
  let a := pullback.fst g i
  let b := pullback.snd g i
  have : IsClosedImmersion a := by
    apply IsClosedImmersion.of_isPreimmersion
    rw [Set.range_eq_univ.mpr hs]
    exact isClosed_univ
  apply localFinitePresentation_of_surjective_closed_pullback a hs
  let e₁ := Functor.mapModCompIso (i)^*[Ab.{u + 1}] (b)^*[Ab.{u + 1}]
    (upperStarComp Ab.{u + 1} b i).inv R
  have hp : IsLocallyFinitelyPresented ((b ≫ i)^*[Ab.{u + 1}].obj R)
      (((b ≫ i)^*[Ab.{u + 1}].mapMod R).obj M) := by
    apply localFinitePresentation_of_comap
      (Functor.compAlgHom (i)^*[Ab.{u + 1}] (b)^*[Ab.{u + 1}]
        (upperStarComp Ab.{u + 1} b i).inv R)
    exact localFinitePresentation_of_iso (e₁.app M)
      (localFinitePresentation_pullback b hM)
  have hp' : IsLocallyFinitelyPresented ((a ≫ g)^*[Ab.{u + 1}].obj R)
      (((a ≫ g)^*[Ab.{u + 1}].mapMod R).obj M) := by
    exact (congrArg (fun f : pullback g i ⟶ T ↦
      IsLocallyFinitelyPresented ((f)^*[Ab.{u + 1}].obj R)
        (((f)^*[Ab.{u + 1}].mapMod R).obj M))
      (show a ≫ g = b ≫ i from pullback.condition)).mpr hp
  let e₃ := Functor.mapModCompIso (g)^*[Ab.{u + 1}] (a)^*[Ab.{u + 1}]
    (upperStarComp Ab.{u + 1} a g).inv R
  exact localFinitePresentation_of_iso (e₃.app M).symm
    (localFinitePresentation_comap _ hp')

end AlgebraicGeometry.ProEtale
