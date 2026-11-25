/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs

/-!
# Global sections of a pushforward

For a morphism `g : X ⟶ Y` of `k`-schemes and a sheaf of modules `M` on `X`, the global sections
of `g_* M` are the global sections of `M`. Hence `H⁰(Y, g_* M) ≅ H⁰(X, M)` as `k`-vector spaces,
naturally in `M`.

## Main definitions

- `AlgebraicGeometry.Scheme.Modules.H.zeroPushforwardLinearEquiv`: `H⁰(Y, g_* M) ≃ₗ[k] H⁰(X, M)`.
- `AlgebraicGeometry.Scheme.Modules.pushforwardCompCohomologyFunctorZeroIso`: the natural
  isomorphism `H⁰(Y, g_* -) ≅ H⁰(X, -)`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

variable (k : Type u) [Field k] {X Y : Scheme.{u}} [X.Over (Spec (.of k))]
  [Y.Over (Spec (.of k))]

/-- The structure maps `k →+* Γ(Y, ⊤)` and `k →+* Γ(X, ⊤)` of `k`-schemes are compatible with a
morphism `g : X ⟶ Y` of `k`-schemes. -/
lemma Hom.appTop_globalSectionsRingHom (g : X ⟶ Y) [g.IsOver (Spec (.of k))] (c : k) :
    g.appTop (globalSectionsRingHom k (X := Y) c) = globalSectionsRingHom k (X := X) c := by
  rw [globalSectionsRingHom, globalSectionsRingHom,
    ← (Hom.isOver_iff (Spec (.of k))).mp ‹g.IsOver _›, Scheme.Hom.comp_appTop]
  rfl

namespace Modules

/-- `H⁰(Y, g_* M) ≅ H⁰(X, M)`, both being global sections of `M`. -/
noncomputable def H.zeroPushforwardLinearEquiv (g : X ⟶ Y) [g.IsOver (Spec (.of k))]
    (M : X.Modules) : ((pushforward g).obj M).H 0 ≃ₗ[k] M.H 0 :=
  ((H.zeroLinearEquiv ((pushforward g).obj M)).toAddEquiv.trans
    (H.zeroLinearEquiv M).symm.toAddEquiv).toLinearEquiv fun c x ↦ by
    let s : Γ(M, ⊤) := H.zeroLinearEquiv ((pushforward g).obj M) x
    have h₁ : H.zeroLinearEquiv ((pushforward g).obj M) (c • x) =
        g.appTop (globalSectionsRingHom k (X := Y) c) • s :=
      (H.zeroLinearEquiv ((pushforward g).obj M)).map_smul (globalSectionsRingHom k c) x
    have h₂ : (H.zeroLinearEquiv M).symm (globalSectionsRingHom k (X := X) c • s) =
        c • (H.zeroLinearEquiv M).symm s :=
      (H.zeroLinearEquiv M).symm.map_smul _ _
    refine (congrArg (H.zeroLinearEquiv M).symm h₁).trans ?_
    rw [Hom.appTop_globalSectionsRingHom]
    exact h₂

omit [X.Over (Spec (.of k))] in
/-- The identification `H⁰(X, M) ≅ Γ(X, M)` is natural in `M`. -/
lemma H.zeroLinearEquiv_map {M N : X.Modules} (φ : M ⟶ N) (x : M.H 0) :
    H.zeroLinearEquiv N (H.map φ 0 x) = φ.app ⊤ (H.zeroLinearEquiv M x) :=
  (Sheaf.H.equiv₀_naturality (hT := isTerminalTop)
    ((SheafOfModules.toSheaf X.ringCatSheaf).map φ) x).symm

/-- **Global sections of a pushforward.** `H⁰(Y, g_* M) ≅ H⁰(X, M)`, naturally in `M`, for a
morphism `g : X ⟶ Y` of `k`-schemes: both are the global sections of `M`. -/
noncomputable def pushforwardCompCohomologyFunctorZeroIso (g : X ⟶ Y) [g.IsOver (Spec (.of k))] :
    pushforward g ⋙ cohomologyFunctor k 0 ≅ cohomologyFunctor k 0 :=
  NatIso.ofComponents (fun M ↦ (H.zeroPushforwardLinearEquiv k g M).toModuleIso) fun {M N} φ ↦ by
    ext x
    refine (H.zeroLinearEquiv N).injective ?_
    change H.zeroLinearEquiv N ((H.zeroLinearEquiv N).symm
      (H.zeroLinearEquiv ((pushforward g).obj N) (H.map ((pushforward g).map φ) 0 x))) =
      H.zeroLinearEquiv N (H.map φ 0 ((H.zeroLinearEquiv M).symm
        (H.zeroLinearEquiv ((pushforward g).obj M) x)))
    rw [H.zeroLinearEquiv_map, H.zeroLinearEquiv_map, LinearEquiv.apply_symm_apply,
      LinearEquiv.apply_symm_apply]
    rfl

end Modules

end AlgebraicGeometry.Scheme
