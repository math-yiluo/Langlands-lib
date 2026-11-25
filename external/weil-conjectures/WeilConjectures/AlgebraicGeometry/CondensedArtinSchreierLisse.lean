/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedArtinSchreier
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartStratificationDefs
public import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import WeilConjectures.AlgebraicGeometry.CondensedArtinSchreierLisseLocalModel
import WeilConjectures.AlgebraicGeometry.CondensedArtinSchreierLisseTensor
import WeilConjectures.AlgebraicGeometry.CondensedArtinSchreierLisseInverse
/-! # Lissity and multiplicativity of the Artin–Schreier sheaves

Source: current blueprint, sec-fourier-transform/sk-lem-as-properties/lem-fd-as-lisse.md
(blueprint: lemma-artin-schreier-character-sheaf--2).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- The Artin–Schreier sheaf is lisse of rank one, is multiplicative in the function,
and its tensor inverse is the sheaf of the negative function, also the sheaf for the
inverse character. The local rank-one clause says that the pullback is the regular
coefficient module, not merely that the underlying sheaf of sets is locally constant.
Source: current blueprint, lem-fd-as-lisse.md (blueprint: lemma-artin-schreier-character-sheaf--2).

The statement is made for every nontrivial character psi of k₀, which contains the
character psi = Psi ∘ Tr of theorem-weight-bound-affine-line--1 (the case of the node).

Proof in words: (1) For psi = Psi ∘ Tr_{k₀/F_p}, as in theorem-weight-bound-affine-line--1, the
comparison lemma-artin-schreier-character-sheaf (2), with a=1, identifies the degree-q character
image of f with the Psi-summand of the prime-degree covering of f. A general nontrivial psi is
z ↦ Psi(Tr(a z)) with a ≠ 0 by lemma-artin-schreier-character-sheaf (1); then (2) with this a
identifies L_{psi,f} with the Psi-summand for a f, i.e. with L_{Psi ∘ Tr, a f}. The rank-one
assertion of lemma-artin-schreier-character-sheaf trivializes it over the Artin–Schreier cover; all
coefficient rings are p_T^* Qbar_l, as in prose-02-51. This gives
IsLisseCoefficientModule and the rank-one local model. (2) Apply the tensor clause of
lemma-artin-schreier-character-sheaf to a f and a g. (3) Its inverse clause identifies the
negative-function sheaf as the tensor inverse. Its inverse-character clause, inverted
if necessary, identifies that sheaf with the inverse-character sheaf (psi⁻¹ is
z ↦ Psi(Tr(-a z))). No assertion that a nontrivial character summand is nonconstant is
used: f=0 is allowed. -/
theorem condensedArtinSchreierSheafOf_lisse_tensor_inv
    (k₀ : Type u) [Field k₀] [Fintype k₀] (ℓ : ℕ) [Fact ℓ.Prime]
    [Fact (ringChar k₀ ≠ ℓ)] (X₀ : Scheme.{u}) [X₀.Over (Spec (.of k₀))]
    (ψ : AddChar k₀ (MonObj.Γ (Profinite.padicAlgClRingObj.{u} ℓ))) (hψ : ψ ≠ 1)
    (f g : Γ(X₀, ⊤)) :
    IsLisseCoefficientModule (Profinite.padicAlgClRingObj ℓ)
        (condensedArtinSchreierSheafOf (Profinite.padicAlgClRingObj ℓ) k₀ X₀ ψ f) ∧
    (∃ U : Scheme.Cover.{u} Scheme.proetalePrecoverage X₀, ∀ i : U.I₀,
      Nonempty ((CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) (U.f i)).obj
        (condensedArtinSchreierSheafOf (Profinite.padicAlgClRingObj ℓ) k₀ X₀ ψ f) ≅
          Mod.regular (condensedRingObj (Profinite.padicAlgClRingObj ℓ) (U.X i)))) ∧
    Nonempty (condensedArtinSchreierSheafOf (Profinite.padicAlgClRingObj ℓ) k₀ X₀ ψ f ⊗
        condensedArtinSchreierSheafOf (Profinite.padicAlgClRingObj ℓ) k₀ X₀ ψ g ≅
      condensedArtinSchreierSheafOf (Profinite.padicAlgClRingObj ℓ) k₀ X₀ ψ (f + g)) ∧
    Nonempty (condensedArtinSchreierSheafOf (Profinite.padicAlgClRingObj ℓ) k₀ X₀ ψ f ⊗
        condensedArtinSchreierSheafOf (Profinite.padicAlgClRingObj ℓ) k₀ X₀ ψ (-f) ≅
      Mod.regular (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X₀)) ∧
    Nonempty (condensedArtinSchreierSheafOf (Profinite.padicAlgClRingObj ℓ) k₀ X₀ ψ (-f) ≅
      condensedArtinSchreierSheafOf (Profinite.padicAlgClRingObj ℓ) k₀ X₀ ψ⁻¹ f)  := by
  obtain ⟨hl, hU⟩ := condensedArtinSchreierSheafOf_lisse_local_model
    k₀ ℓ X₀ ψ hψ f
  obtain ⟨hadd⟩ := condensedArtinSchreierSheafOf_tensor_addition
    k₀ ℓ X₀ ψ hψ f g
  obtain ⟨hinv, hchar⟩ := condensedArtinSchreierSheafOf_inverse
    k₀ ℓ X₀ ψ hψ f
  exact ⟨hl, hU, ⟨hadd⟩, hinv, hchar⟩

end AlgebraicGeometry.ProEtale
