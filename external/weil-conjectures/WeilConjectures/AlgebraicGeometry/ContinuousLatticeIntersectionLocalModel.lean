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
import WeilConjectures.AlgebraicGeometry.ContinuousLatticeIntersectionRationalModel
import WeilConjectures.AlgebraicGeometry.ContinuousFiniteFreeKernelModel

/-! # Local matrix models of the finite-sheet lattice intersection -/

@[expose] public section

universe u
open CategoryTheory Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The canonical intersection is locally the kernel of an integral matrix whose
rationalization is surjective.
Source: Bhatt--Scholze, Lemma 6.8.13, finite-etale descent of integral structures;
the intersection and bounded-denominator matrix argument is an agent variant.
(auxiliary; not a blueprint node)

Proof. Use the rational matrix model on compact covering schemes. Clear its finite
matrix of denominators. The localization unit of a standard finite free integral
module is monic, and multiplication by a power of ℓ is invertible on rational
modules. Thus the kernel of the integral adjoint of the rational matrix is
isomorphic to the kernel of its integral numerator. The latter still rationalizes
to a surjection. Compose this kernel isomorphism with the supplied local model.
Empty pieces and rank-zero matrices are included in the same constructions. -/
theorem continuousLatticeIntersection_localModel
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
      let R := condensedRingObj (integralCoeff ℓ E) (C.X s)
      let T := (ProEtale.upperStar Ab.{u + 1} (C.f s)).mapMod
          (condensedRingObj (integralCoeff ℓ E) X) ⋙
        Mod.comap (inv (condensedPullbackHom (integralCoeff ℓ E) (C.f s)))
      ∃ (n m : ℕ) (f : Mod.finiteFree R n ⟶ Mod.finiteFree R m),
        Epi ((Mod.extendScalars
          (coefficientMap (integralScalarMap ℓ E) (C.X s))).map f) ∧
        Nonempty (T.obj (latticeIntersection (integralScalarMap ℓ E) X P p M e) ≅
          kernel f) := by
  classical
  obtain ⟨C, hC⟩ := continuousLatticeIntersection_rationalModel ℓ E X P hP p M hM e
  refine ⟨C, fun s ↦ ?_⟩
  obtain ⟨hs, n, m, f, hf, ⟨es⟩⟩ := hC s
  let : CompactSpace (C.X s) := hs
  have := hf
  obtain ⟨g, hg, ⟨eg⟩⟩ := integralFiniteFree_kernel_model ℓ E (C.X s) n m f
  exact ⟨n, m, g, hg, ⟨es ≪≫ eg⟩⟩

end AlgebraicGeometry.ProEtale.CondensedRing
