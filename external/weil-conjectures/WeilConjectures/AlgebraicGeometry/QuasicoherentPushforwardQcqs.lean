/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
import WeilConjectures.AlgebraicGeometry.Modules.QcqsSections

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel

/-!
# Quasi-coherence of pushforward along a qcqs morphism

Source: Stacks Project, Schemes, Lemma 26.24.1, Tag 01LC
(blueprint: pqf-lem-pushforward-qcoh).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

set_option autoImplicit false

private lemma section_extension_of_basicOpen_eq
    {X : Scheme.{u}} (F : X.Modules) [F.IsQuasicoherent]
    {W O : X.Opens} (hW : IsCompact (W : Set X)) (hqs : IsQuasiSeparated (W : Set X))
    (a : Γ(X, W)) (hO : O = X.basicOpen a) (hle : O ≤ W) (s : Γ(F, O)) :
    ∃ (n : ℕ) (t : Γ(F, W)), F.presheaf.map (homOfLE hle).op t =
      X.presheaf.map (homOfLE hle).op a ^ n • s := by
  subst O
  exact exists_map_eq_pow_smul_of_isCompact_of_isQuasiSeparated F hW hqs a s

private lemma section_torsion_of_basicOpen_eq
    {X : Scheme.{u}} (F : X.Modules) [F.IsQuasicoherent]
    {W O : X.Opens} (hW : IsCompact (W : Set X)) (a : Γ(X, W))
    (hO : O = X.basicOpen a) (hle : O ≤ W) (t : Γ(F, W))
    (ht : F.presheaf.map (homOfLE hle).op t = 0) : ∃ n : ℕ, a ^ n • t = 0 := by
  subst O
  exact exists_pow_smul_eq_zero_of_isCompact F hW a t ht

/-- Pushforward along a quasi-compact, quasi-separated morphism preserves quasi-coherence.
Source: Stacks Project, Schemes, Lemma 26.24.1, Tag 01LC
(blueprint: pqf-lem-pushforward-qcoh).

Proof:
1. Work over an affine open `S₀ = Spec A` and set `X₀ = f⁻¹(S₀)`. Quasi-compactness
   (`definition-ind-etale-pro-etale-weakly--3`) supplies a finite affine cover `Uᵢ = Spec Bᵢ` of
   `X₀`. Quasi-coherence (`pqf-def-coherent`) identifies the restrictions with associated modules
   `Mᵢ`. Quasi-separatedness makes each overlap quasi-compact, by the relative diagonal,
   so choose finite covers of the overlaps by principal opens `Wᵢⱼₖ = D(gᵢⱼₖ)` in `Uᵢ`.
   Their section modules are the localizations `Nᵢⱼₖ = (Mᵢ)_{gᵢⱼₖ}`, using
   `pqf-lem-associated-sections-localize` and restriction of associated sheaves.
2. Sheaf gluing identifies sections on `X₀` with the kernel of the difference of
   restrictions from the finite product of the `Mᵢ` to the finite product of the `Nᵢⱼₖ`.
3. Pull these covers back to each principal open `D(a)` in `S₀`. The section-localization
   lemma (`pqf-lem-associated-sections-localize`) identifies the new two terms and map with
   localization over `A` of the old ones. Localization is exact and commutes with finite
   products, giving sections over `f⁻¹(D(a))` as sections over `X₀` localized at `a`.
4. These identifications commute with further localization because the maps are
   restrictions. Thus on the principal-open basis of `S₀` the pushforward is the sheaf
   associated to its module of sections on `X₀`, hence is quasi-coherent
   (`pqf-def-coherent`). Varying `S₀` proves the result. -/
theorem isQuasicoherent_pushforward_of_quasiCompact_quasiSeparated
    {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    (F : X.Modules) [F.IsQuasicoherent] :
    ((pushforward f).obj F).IsQuasicoherent := by
  refine isQuasicoherent_of_forall_isAffineOpen _ (fun W hW a s ↦ ?_)
    (fun W hW a t ht ↦ ?_)
  · obtain ⟨n, t, ht⟩ := section_extension_of_basicOpen_eq F
      (f.isCompact_preimage hW.isCompact)
      (f.isQuasiSeparated_preimage hW.isQuasiSeparated) (f.app W a)
      (f.preimage_basicOpen a) (f.preimage_mono (S.basicOpen_le a)) s
    refine ⟨n, t, ht.trans ?_⟩
    have he : f.app (S.basicOpen a) (S.presheaf.map (homOfLE (S.basicOpen_le a)).op a) =
        X.presheaf.map (homOfLE (f.preimage_mono (S.basicOpen_le a))).op (f.app W a) := by
      rw [← ConcreteCategory.comp_apply, f.naturality]
      rfl
    rw [← he, ← map_pow]
    rfl
  · obtain ⟨n, hn⟩ := section_torsion_of_basicOpen_eq F
      (f.isCompact_preimage hW.isCompact) (f.app W a)
      (f.preimage_basicOpen a) (f.preimage_mono (S.basicOpen_le a)) t ht
    rw [← map_pow] at hn
    exact ⟨n, hn⟩

end AlgebraicGeometry.Scheme.Modules
