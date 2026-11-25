/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import WeilConjectures.AlgebraicGeometry.AffineLocalAcyclicOpenRestriction
import WeilConjectures.AlgebraicGeometry.EtaleMayerVietorisModuleVanishing
import WeilConjectures.AlgebraicGeometry.EtalePullbackForgetModules

/-! # Finite affine cover bound from local acyclicity

Source: Stacks Project, Tag 0A51, Mayer-Vietoris induction.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme Etale

/-- Local acyclicity on the inverse images of affine opens gives a finite-cover
cohomological bound. No injectivity or torsion assumption is needed for this step.

Source: Stacks Project, Tag 0A51, final paragraph of the proof, with the affine
vanishing used there made an explicit hypothesis.
(blueprint: lem-weil-pbc-finite-affine-cover-restriction-bound)

Proof: induct on n, simultaneously for all schemes and sheaves satisfying hlocal.
For n = 0 the sole affine open is the whole scheme, so hlocal gives the result
through the pullback and inverse-image identity isomorphisms. For n+1, write the
cover as one affine open U and the union V of the remaining n+1 affine opens.
Since X is separated over an affine scheme, intersections of affine opens in X
are affine. Hence U ∩ V has a cover by n+1 affine opens. The hypothesis hlocal
is inherited on both V and U ∩ V: their affine opens are affine opens in X, and
composition and pullback comparisons identify the two restrictions. Apply the
induction hypothesis to these two covers. The restriction on U has no positive
cohomology by hlocal. Pulling back the cover along i gives a two-open cover of Z;
Mayer-Vietoris in degree q has outer terms the degree q-1 group on the inverse
image of U ∩ V and the degree q groups on those of U and V. If q > n+1 all
three groups vanish by the preceding bounds, so exactness kills the middle group.
The inverse-image composition and coefficient-forgetting isomorphisms identify
these groups with the expressions displayed here. This argument also works for
empty opens, repeated members of the cover, and an arbitrary morphism i. -/
theorem Etale.subsingleton_H_of_affine_local_acyclic
    (Λ : Type (u + 1)) [CommRing Λ] {A : Type u} [CommRing A]
    {X Z : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsSeparated f] (i : Z ⟶ X)
    (J : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hlocal : ∀ (W : X.Opens), IsAffineOpen W → ∀ (q : ℕ), 0 < q →
      Subsingleton (Sheaf.H
        ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
          ((pullback.fst W.ι i)^*[ModuleCat.{u + 1} Λ].obj
            ((W.ι)^*[ModuleCat.{u + 1} Λ].obj J))) q))
    (n : ℕ) (U : Fin (n + 1) → X.Opens) (hU : ∀ j, IsAffineOpen (U j))
    (hcov : ⨆ j, U j = ⊤) (q : ℕ) (hq : n < q) :
    Subsingleton (Sheaf.H
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
        ((i)^*[ModuleCat.{u + 1} Λ].obj J)) q) := by
  revert U hU hcov q hq
  revert X Z
  induction n with
  | zero =>
      intro X Z f hf i J hlocal U hU hcov q hq
      have htop : U 0 = ⊤ := by simpa using hcov
      have hX : IsAffineOpen (⊤ : X.Opens) := htop ▸ hU 0
      let W : X.Opens := ⊤
      let p := pullback.snd W.ι i
      have : IsIso W.ι := by dsimp [W]; rw [← Scheme.topIso_hom]; infer_instance
      have : IsIso p := by dsimp [p]; infer_instance
      let G := ((i)^*[ModuleCat.{u + 1} Λ]).obj J
      let B := (sheafCompose Z.smallEtaleTopology
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj G
      have hs := hlocal W hX q hq
      let e := ((Etale.upperStarComp (ModuleCat.{u + 1} Λ)
          (pullback.fst W.ι i) W.ι).app J).symm ≪≫
        (eqToIso (congrArg (fun k ↦ ((k)^*[ModuleCat.{u + 1} Λ]).obj J)
          (pullback.condition (f := W.ι) (g := i)))) ≪≫
        (Etale.upperStarComp (ModuleCat.{u + 1} Λ) p i).app J
      obtain ⟨ef⟩ := Etale.pullback_forget_modules_iso Λ p G
      let ea := (sheafCompose _
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).mapIso e ≪≫ ef
      have : Subsingleton (Sheaf.H (((p)^*[AddCommGrpCat.{u + 1}]).obj B) q) := by
        refine ⟨fun a b ↦ ?_⟩
        have hab := hs.elim (Sheaf.H.map ea.inv q a) (Sheaf.H.map ea.inv q b)
        have hab' := congrArg (Sheaf.H.map ea.hom q) hab
        simpa only [← Sheaf.H.map_comp_apply, Iso.inv_hom_id, Sheaf.H.map_id_apply] using hab'
      exact (Etale.cohomologyMap_bijective p B q).injective.subsingleton
  | succ n ih =>
      intro X Z f hf i J hlocal U hU hcov q hq
      let W : X.Opens := U 0
      let V : X.Opens := ⨆ j : Fin (n + 1), U j.succ
      have hWV : W ⊔ V = ⊤ := by
        rw [← hcov]
        apply le_antisymm
        · exact sup_le (le_iSup U 0) (iSup_le fun j ↦ le_iSup U j.succ)
        · refine iSup_le fun j ↦ ?_
          refine Fin.cases ?_ (fun k ↦ ?_) j
          · exact le_sup_left
          · exact (le_iSup (fun k : Fin (n + 1) ↦ U k.succ) k).trans le_sup_right
      have hVmem (j : Fin (n + 1)) : U j.succ ≤ V :=
        le_iSup (fun k : Fin (n + 1) ↦ U k.succ) j
      let CV : Fin (n + 1) → V.toScheme.Opens := fun j ↦ V.ι ⁻¹ᵁ U j.succ
      have hCV (j) : IsAffineOpen (CV j) :=
        (hU j.succ).preimage_of_isOpenImmersion V.ι (by simpa using hVmem j)
      have hCVcov : ⨆ j, CV j = ⊤ := by
        change ⨆ j : Fin (n + 1), V.ι ⁻¹ᵁ U j.succ = ⊤
        rw [← Scheme.Hom.preimage_iSup]
        exact V.ι_preimage_self
      have hV := ih (V.ι ≫ f) (pullback.fst V.ι i)
        (((V.ι)^*[ModuleCat.{u + 1} Λ]).obj J)
        (Etale.affine_local_acyclic_open_restriction Λ i J hlocal V)
        CV hCV hCVcov q (by omega)
      let I : X.Opens := W ⊓ V
      let CI : Fin (n + 1) → I.toScheme.Opens := fun j ↦ I.ι ⁻¹ᵁ (W ⊓ U j.succ)
      have hCImem (j : Fin (n + 1)) : W ⊓ U j.succ ≤ I :=
        inf_le_inf_left W (hVmem j)
      have hCI (j) : IsAffineOpen (CI j) := by
        have hWU : IsAffineOpen (W ⊓ U j.succ) :=
          isAffineHom_diagonal_iff.mp (inferInstance : IsAffineHom (pullback.diagonal f))
            ⊤ (isAffineOpen_top _) W (by simp) (U j.succ) (by simp) (hU 0) (hU j.succ)
        exact hWU.preimage_of_isOpenImmersion I.ι (by simpa using hCImem j)
      have hCIcov : ⨆ j, CI j = ⊤ := by
        change ⨆ j : Fin (n + 1), I.ι ⁻¹ᵁ (W ⊓ U j.succ) = ⊤
        rw [← Scheme.Hom.preimage_iSup, ← inf_iSup_eq]
        exact I.ι_preimage_self
      obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q ≠ 0)
      have hI := ih (I.ι ≫ f) (pullback.fst I.ι i)
        (((I.ι)^*[ModuleCat.{u + 1} Λ]).obj J)
        (Etale.affine_local_acyclic_open_restriction Λ i J hlocal I)
        CI hCI hCIcov r (by omega)
      exact Etale.subsingleton_H_of_two_open_pullback_cover Λ i J W V hWV r
        (hlocal W (hU 0) (r + 1) (by omega)) hV hI


end AlgebraicGeometry
