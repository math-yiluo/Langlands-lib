/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedArtinSchreier
public import WeilConjectures.FourierTransform.Defs

/-! # The condensed Fourier kernel

Source: latest blueprint, sec-fourier-transform/sk-thm-inversion/def-fd-kernel.md,
condensed coefficient convention (blueprint: sec-Fourier-inversion).
The ordinary etale construction is re-exported from FourierTransform.Defs.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- The degree-q Artin--Schreier sheaf of the pairing, with pulled-back condensed
coefficients. The character is a character of k₀, not its restriction to the prime field.
Source: latest blueprint, def-fd-kernel.md, condensed application
(blueprint: sec-Fourier-inversion). -/
def condensedFourierKernel
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (k₀ : Type u) [Field k₀] [Fintype k₀]
    {S V V' : Scheme.{u}} (π : V ⟶ S) (π' : V' ⟶ S)
    [(pullback π π').Over (Spec (.of k₀))]
    (ψ : AddChar k₀ (MonObj.Γ Λ)) (b : Γ(pullback π π', ⊤)) :=
  condensedArtinSchreierSheafOf Λ k₀ (pullback π π') ψ b

/-- The prime-field kernel for the full characteristic condition p=0 in global
sections, including the empty scheme. The canonical prime-field map factors the
integer map using ringChar divisibility, without requiring characteristic exactly p.
Source: latest blueprint, def-fd-kernel.md, general condensed formula
(blueprint: sec-Fourier-inversion). -/
def condensedPrimeFourierKernel
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (p : ℕ) [Fact p.Prime] {S V V' : Scheme.{u}} (π : V ⟶ S) (π' : V' ⟶ S)
    (hp : (p : Γ(pullback π π', ⊤)) = 0)
    (Ψ : AddChar (ZMod p) (MonObj.Γ Λ)) (b : Γ(pullback π π', ⊤)) :=
  letI : (pullback π π').Over (Spec (.of (ULift.{u} (ZMod p)))) :=
    ⟨(pullback π π').toSpecΓ ≫ Spec.map (CommRingCat.ofHom
      ((ZMod.castHom (ringChar.dvd hp) Γ(pullback π π', ⊤)).comp
        ULift.ringEquiv.toRingHom))⟩
  condensedFourierKernel Λ (ULift.{u} (ZMod p)) π π'
    (Ψ.compAddMonoidHom AddEquiv.ulift.toAddMonoidHom) b

end AlgebraicGeometry.ProEtale
