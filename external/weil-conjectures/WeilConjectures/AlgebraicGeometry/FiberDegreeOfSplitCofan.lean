/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree

/-!
# Fibre degree of a finite coproduct of copies

Source: Stacks Project, Tag 03SH (section-trace-method), paragraph after
Definition 03SE: a split finite étale map has degree equal to its number of sheets.
(blueprint: lem-weil-pbc-fiber-degree-split-cofan).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The fibre degree of a finite coproduct of copies of the base counts its summands.
Source: Stacks Project, Tag 03SH (section-trace-method), after Definition 03SE.
(blueprint: lem-weil-pbc-fiber-degree-split-cofan).

Proof:
1. The cofan identifies `Z` with the coproduct of the `D j`. Under each isomorphism
   `D j → U` its structure map is the identity of `U`. Thus this is an isomorphism
   over `U` from `Z` to the coproduct of `J` copies of `U`.
2. Pull back along `Spec κ(x) → U`. Pullback preserves scheme coproducts, so the
   fibre is a coproduct of `J` copies of `Spec κ(x)`, compatibly with its structure map.
3. The global sections of this finite coproduct form the product algebra
   `∏ j : J, κ(x)`. Its dimension over `κ(x)` is the sum of `J` copies of one,
   namely `Nat.card J`. By the definition of fibre degree this is the result.
   For `J` empty the fibre is empty and the zero algebra has dimension zero. -/
theorem Scheme.Hom.fiberDegree_eq_nat_card_of_split_cofan
    {Z U : Scheme.{u}} (p : Z ⟶ U) [IsAffineHom p]
    {J : Type u} [Finite J] (D : J → Scheme.{u}) (i : ∀ j, D j ⟶ Z)
    (hc : Nonempty (IsColimit (Cofan.mk Z i)))
    (hp : ∀ j, IsIso (i j ≫ p)) (x : U) :
    p.fiberDegree x = Nat.card J := by
  classical
  let : Fintype J := Fintype.ofFinite J
  let (j : J) : IsIso (i j ≫ p) := hp j
  let K := U.residueField x
  let q := U.fromSpecResidueField x
  let s : ∀ j, Spec K ⟶ D j := fun j ↦ q ≫ inv (i j ≫ p)
  have hs (j : J) : IsPullback (s j) (𝟙 (Spec K)) (i j ≫ p) q :=
    IsPullback.of_vert_isIso ⟨by simp [s]⟩
  let a : J → (Spec K ⟶ p.fiber x) := fun j ↦
    pullback.lift (s j ≫ i j) (𝟙 _) (by simp [s, q])
  have ha (j : J) : a j ≫ p.fiberToSpecResidueField x = 𝟙 _ := by
    exact pullback.lift_snd _ _ _
  have hc' : Nonempty (IsColimit (Cofan.mk (p.fiber x) a)) := by
    have hu := FinitaryPreExtensive.isUniversal_finiteCoproducts hc.some
    exact hu.nonempty_isColimit_of_isPullback_right (fun j ↦ i j ≫ p) p q
      s (fun _ ↦ 𝟙 _) hs (.of_hasPullback p q) _ (Iso.refl _)
      (fun _ ↦ rfl) (fun j ↦ by exact pullback.lift_fst _ _ _) ha
  have : IsIso (Sigma.desc a) :=
    (Cofan.nonempty_isColimit_iff_isIso_sigmaDesc _).mp hc'
  let r := Spec.map (CommRingCat.ofHom (algebraMap K (J → K)))
  let e : p.fiber x ≅ Spec (.of (J → K)) :=
    (asIso (Sigma.desc a)).symm ≪≫ asIso (sigmaSpec fun _ : J ↦ K)
  have he : e.hom ≫ r = p.fiberToSpecResidueField x := by
    apply (cancel_epi (Sigma.desc a)).mp
    dsimp [e, r]
    simp only [Category.assoc, IsIso.hom_inv_id_assoc]
    rw [sigmaSpec_comp_Spec_map_algebraMap]
    apply Sigma.hom_ext
    intro j
    rw [Sigma.ι_comp_desc]
    change 𝟙 (Spec K) = Sigma.ι (fun _ : J ↦ Spec K) j ≫
      Sigma.desc a ≫ p.fiberToSpecResidueField x
    rw [Sigma.ι_comp_desc_assoc]
    exact (ha j).symm
  change (p.fiberToSpecResidueField x).finrankΓ = Nat.card J
  rw [Scheme.Hom.finrankΓ_eq_of_iso _ r e (Iso.refl _) (by simpa using he)]
  rw [Scheme.Hom.finrankΓ_SpecMap]
  simp [Nat.card_eq_fintype_card]

end AlgebraicGeometry
