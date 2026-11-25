/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedFourierKernel
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace

/-! # Fourier--Deligne transform with ordinary condensed module coefficients

Source: latest blueprint, sec-fourier-transform/sk-thm-inversion/def-fd-transform.md
(blueprint: sec-Fourier-inversion).
The ordinary etale transform is re-exported by the kernel module.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

/-- The ordinary condensed transform Rp₂! (Lp₁* K tensor Kψ)[r], using the specified
compactification. All operations are the published module-object derived operations.
Source: latest blueprint, def-fd-transform.md, displayed formula
(blueprint: sec-Fourier-inversion). -/
def condensedFourierTransform
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (k₀ : Type u) [Field k₀] [Fintype k₀]
    {S V V' : Scheme.{u}} (π : V ⟶ S) (π' : V' ⟶ S)
    [(pullback π π').Over (Spec (.of k₀))]
    (ψ : AddChar k₀ (MonObj.Γ Λ)) (b : Γ(pullback π π', ⊤))
    (c : Compactification (pullback.snd π π')) (r : ℤ) :
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology V) Ab.{u + 1})
      (condensedRingObj Λ V)) ⥤
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology V') Ab.{u + 1})
      (condensedRingObj Λ V')) :=
  (CondensedRing.upperStar Λ (pullback.fst π π')).leftDerivedFunctor ⋙
    tensorRight ((DerivedCategory.singleFunctor _ 0).obj
      (condensedFourierKernel Λ k₀ π π' ψ b)) ⋙
    CondensedRing.rightDerivedLowerShriekOfCompactification Λ c ⋙ shiftFunctor _ r

/-- The standard affine-space transform for the degree-q character, normalized by
its rank. The structure map of the product is the composite of its first projection
and the given base map, so it introduces no additional geometric datum.
Source: latest blueprint, def-fd-transform.md, affine application
(blueprint: sec-Fourier-inversion). -/
def condensedAffineFourierTransform
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (k₀ : Type u) [Field k₀] [Fintype k₀]
    (S : Scheme.{u}) [S.Over (Spec (.of k₀))]
    (n : Type u) [Fintype n] (ψ : AddChar k₀ (MonObj.Γ Λ))
    (c : Compactification (pullback.snd (AffineSpace n S ↘ S) (AffineSpace n S ↘ S))) :=
  letI : (pullback (AffineSpace n S ↘ S) (AffineSpace n S ↘ S)).Over
      (Spec (.of k₀)) :=
    ⟨pullback.fst (AffineSpace n S ↘ S) (AffineSpace n S ↘ S) ≫
      (AffineSpace n S ↘ S) ≫ (S ↘ Spec (.of k₀))⟩
  condensedFourierTransform Λ k₀ (AffineSpace n S ↘ S) (AffineSpace n S ↘ S)
    ψ (AffineSpace.stdPairing n S) c (Fintype.card n)

/-- The affine-line transform after a field extension of the finite field of the
character. The field inclusion supplies the actual structure morphism.
Source: latest blueprint, def-fd-transform.md, base change application
(blueprint: sec-Fourier-inversion). -/
def condensedFieldFourierTransform
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (k₀ : Type u) [Field k₀] [Fintype k₀]
    (k : Type u) [Field k] [Algebra k₀ k] (ψ : AddChar k₀ (MonObj.Γ Λ))
    (c : Compactification (pullback.snd
      (AffineSpace PUnit (Spec (.of k)) ↘ Spec (.of k))
      (AffineSpace PUnit (Spec (.of k)) ↘ Spec (.of k)))) :=
  letI : (Spec (.of k)).Over (Spec (.of k₀)) :=
    ⟨Spec.map (CommRingCat.ofHom (algebraMap k₀ k))⟩
  condensedAffineFourierTransform Λ k₀ (Spec (.of k)) PUnit ψ c

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.Etale

end AlgebraicGeometry.Etale

namespace AlgebraicGeometry.ProEtale

end AlgebraicGeometry.ProEtale
