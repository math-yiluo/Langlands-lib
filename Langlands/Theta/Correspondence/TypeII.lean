import Langlands.Theta.DualPair.TypeII
import Langlands.Theta.Correspondence.ThetaLift
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.RepresentationTheory.Irreducible

/-!
# Howe duality for type II dual pairs: the statement

GKT Theorem 18.19 (Howe duality for type II dual pairs, the case `D = F`) in the form of Theorem
13.21 without `Θ` and `θ`. `HoweDualityTypeIIStatement` is Mínguez's theorem for the pairs
`(GL_m(F), GL_n(F))` over nonarchimedean local fields, as a `Prop`: for every smooth irreducible
representation `π` of `GL_n(F)` that is a quotient of the restriction of `typeIIWeil F m n` to
`GL_n(F)`, there is a smooth irreducible representation `π'` of `GL_m(F)`, unique up to
isomorphism, such that the space of intertwining maps from `typeIIWeil F m n` to `π' ⊠ π` has
dimension one. The statement is not proved here.

It is restated on the general notions of `Langlands.Theta.Correspondence.ThetaLift`:
`howeDualityTypeIIStatement_iff` says that it is `ThetaMultiplicityOne` (part (1) of Howe duality,
GKT Theorem 13.21) for `typeIIWeil F m n` with the roles of the factors exchanged (`swapRep`: the
representation `π` is of `GL_n(F)`, its partner of `GL_m(F)`), and
`thetaMultiplicityOne_typeIISplitting` gives it for the Weil representation of the type II splitting
(`ω_ψ ∘ s`, GKT Proposition 12.35) over fields with `⅟2`. `HoweDualityTypeII` is the full statement
(GKT Theorem 18.19 with Theorem 13.21 (1) and (2)); it implies `HoweDualityTypeIIStatement`.
-/

noncomputable section

namespace Langlands.Theta

open HarmonicAnalysis

/-- Howe duality for the type II dual pairs `(GL_m(F), GL_n(F))` (A. Mínguez): let `F` be a
nonarchimedean local field, `m, n ≥ 1`, and `π` a smooth irreducible representation of `GL_n(F)`
admitting a non-zero intertwining map from the restriction of `typeIIWeil F m n` to `GL_n(F)`.
Then there is a smooth irreducible representation `π'` of `GL_m(F)` such that the intertwining maps
from `typeIIWeil F m n` to the external tensor product `π' ⊠ π` form a space of dimension one, and
`π'` is unique up to isomorphism among the smooth irreducible representations `π''` with a non-zero
intertwining map from `typeIIWeil F m n` to `π'' ⊠ π`. -/
def HoweDualityTypeIIStatement : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (m n : ℕ), 1 ≤ m → 1 ≤ n →
    ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (π : Representation ℂ (GeneralLinear n F) W),
      IsSmooth π → π.IsIrreducible →
      (∃ f : Representation.IntertwiningMap ((typeIIWeil F m n).comp (MonoidHom.inr _ _)) π,
        f ≠ 0) →
      ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V)
        (π' : Representation ℂ (GeneralLinear m F) V),
        IsSmooth π' ∧ π'.IsIrreducible ∧
        Module.finrank ℂ ((typeIIWeil F m n).IntertwiningMap
          (Representation.tprod (π'.comp (MonoidHom.fst _ _)) (π.comp (MonoidHom.snd _ _)))) = 1 ∧
        ∀ (V' : Type) [AddCommGroup V'] [Module ℂ V']
          (π'' : Representation ℂ (GeneralLinear m F) V'), IsSmooth π'' → π''.IsIrreducible →
          (∃ f : (typeIIWeil F m n).IntertwiningMap
            (Representation.tprod (π''.comp (MonoidHom.fst _ _)) (π.comp (MonoidHom.snd _ _))),
            f ≠ 0) →
          Nonempty (π''.Equiv π')

/-- **`HoweDualityTypeIIStatement` is Howe duality part (1)** (GKT Theorem 13.21 (1), Theorem
18.19) for the type II Weil representation with its factors exchanged. -/
theorem howeDualityTypeIIStatement_iff :
    HoweDualityTypeIIStatement ↔
      ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
        (m n : ℕ), 1 ≤ m → 1 ≤ n → ThetaMultiplicityOne (swapRep (typeIIWeil F m n)) := by
  constructor
  · intro h F _ _ _ _ m n hm hn V _ _ π hπ hπi hocc
    obtain ⟨W, _, _, σ, hσ, hσi, hdim, huniq⟩ := h F m n hm hn V π hπ hπi hocc
    refine ⟨W, inferInstance, inferInstance, σ, hσ, hσi, ?_, ?_⟩
    · rw [(homSwapEquiv (typeIIWeil F m n) σ π).finrank_eq]
      exact hdim
    · rintro W' _ _ σ' hσ' hσ'i ⟨f, hf⟩
      exact huniq W' σ' hσ' hσ'i ⟨homSwapEquiv (typeIIWeil F m n) σ' π f,
        (LinearEquiv.map_ne_zero_iff _).2 hf⟩
  · intro h F _ _ _ _ m n hm hn V _ _ π hπ hπi hocc
    obtain ⟨W, _, _, σ, hσ, hσi, hdim, huniq⟩ := h F m n hm hn V π hπ hπi hocc
    refine ⟨W, inferInstance, inferInstance, σ, hσ, hσi, ?_, ?_⟩
    · rw [← (homSwapEquiv (typeIIWeil F m n) σ π).finrank_eq]
      exact hdim
    · rintro W' _ _ σ' hσ' hσ'i ⟨f, hf⟩
      exact huniq W' σ' hσ' hσ'i ⟨(homSwapEquiv (typeIIWeil F m n) σ' π).symm f,
        (LinearEquiv.map_ne_zero_iff _).2 hf⟩

/-- `HoweDualityTypeIIStatement` for the Weil representation `ω_ψ ∘ s` of the type II splitting
(GKT Proposition 12.21, Proposition 12.35), over nonarchimedean local fields with `⅟2`. -/
theorem thetaMultiplicityOne_typeIISplitting (h : HoweDualityTypeIIStatement)
    (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [Invertible (2 : F)] {ψ : AddChar F ℂ} (hψ : Continuous ψ) (m n : ℕ) (hm : 1 ≤ m)
    (hn : 1 ≤ n) : ThetaMultiplicityOne (swapRep (typeIISplitting hψ m n).weil) := by
  rw [weil_typeIISplitting]
  exact howeDualityTypeIIStatement_iff.1 h F m n hm hn

/-- **Howe duality for the type II pairs `(GL_n(F), GL_m(F))`** (GKT Theorem 18.19, with both parts
of Theorem 13.21, `D = F`), as a `Prop`. Not proved here. -/
def HoweDualityTypeII : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (m n : ℕ), 1 ≤ m → 1 ≤ n → HoweDuality (swapRep (typeIIWeil F m n))

theorem HoweDualityTypeII.statement (h : HoweDualityTypeII) : HoweDualityTypeIIStatement :=
  howeDualityTypeIIStatement_iff.2 fun F _ _ _ _ m n hm hn => (h F m n hm hn).1

end Langlands.Theta
