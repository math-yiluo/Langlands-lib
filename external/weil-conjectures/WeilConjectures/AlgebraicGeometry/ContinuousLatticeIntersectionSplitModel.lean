/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ContinuousLatticeIntersection
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.LocallyFree
public import WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficients
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
import WeilConjectures.AlgebraicGeometry.ContinuousLatticeIntersectionSplitData

/-! # Split finite-sheet models of the canonical intersection -/

@[expose] public section

universe u
open CategoryTheory Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- On a compact splitting refinement, the global intersection is the inverse
image of the rational diagonal inside the rationalized sum of the sheet lattices.
Source: Bhatt--Scholze, Lemma 6.8.13; agent finite-sheet variant.
(auxiliary; not a blueprint node)

Proof. Take the finite-sheet coordinates of the two maps from splitData. Exact
normalized inverse image preserves their image-pullback by imagePullbackMapIso.
Transport its objects and maps along the three supplied coordinate isomorphisms
using imagePullbackCongr. This gives exactly the asserted model; the mono and
free cokernel data are those of the rational diagonal. -/
theorem continuousLatticeIntersection_splitModel
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    (X : Scheme.{u})
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) X))
    (hP : IsLocallyFree (condensedRingObj (Profinite.continuousMapRingObj E) X) P)
    {U : Scheme.{u}} (p : U ⟶ X) [IsFinite p] [Etale p] [Surjective p]
    (M : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
      (condensedRingObj (integralCoeff ℓ E) U))
    (hM : IsLocallyFree (condensedRingObj (integralCoeff ℓ E) U) M)
    (e : (Mod.extendScalars (coefficientMap (integralScalarMap ℓ E) U)).obj M ≅
      (upperStar (Profinite.continuousMapRingObj E) p).obj P) :
    ∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ s : C.I₀,
      CompactSpace (C.X s) ∧
      let R := condensedRingObj (integralCoeff ℓ E) (C.X s)
      let T := (ProEtale.upperStar Ab.{u + 1} (C.f s)).mapMod
          (condensedRingObj (integralCoeff ℓ E) X) ⋙
        Mod.comap (inv (condensedPullbackHom (integralCoeff ℓ E) (C.f s)))
      let F := Mod.extendScalars
        (coefficientMap (integralScalarMap ℓ E) (C.X s))
      let G := Mod.comap (D := Sheaf (Scheme.ProEt.topology (C.X s)) Ab.{u + 1})
        (coefficientMap (integralScalarMap ℓ E) (C.X s))
      let adj := Mod.extendRestrictAdjunction
        (coefficientMap (integralScalarMap ℓ E) (C.X s))
      ∃ (r n m : ℕ) (i : F.obj (Mod.finiteFree R r) ⟶ F.obj (Mod.finiteFree R n)),
        Mono i ∧ Nonempty (cokernel i ≅ F.obj (Mod.finiteFree R m)) ∧
        Nonempty (T.obj (latticeIntersection (integralScalarMap ℓ E) X P p M e) ≅
          imagePullback (G.map i) (adj.unit.app (Mod.finiteFree R n)))  := by
  classical
  obtain ⟨C, hC⟩ := continuousLatticeIntersection_splitData ℓ E X P hP p M hM e
  refine ⟨C, fun s ↦ ?_⟩
  obtain ⟨hs, r, n, m, i, hi, hc, eA, eB, eD, hf, hg⟩ := hC s
  refine ⟨hs, r, n, m, i, hi, hc, ⟨?_⟩⟩
  let T := (ProEtale.upperStar Ab.{u + 1} (C.f s)).mapMod
      (condensedRingObj (integralCoeff ℓ E) X) ⋙
    Mod.comap (inv (condensedPullbackHom (integralCoeff ℓ E) (C.f s)))
  exact imagePullbackMapIso T
      (latticeIntersectionUnit (integralScalarMap ℓ E) X P p)
      (latticePushedEmbedding (integralScalarMap ℓ E) X P p M e) ≪≫
    imagePullbackCongr _ _ _ _ eA eB eD hf hg

end AlgebraicGeometry.ProEtale.CondensedRing
