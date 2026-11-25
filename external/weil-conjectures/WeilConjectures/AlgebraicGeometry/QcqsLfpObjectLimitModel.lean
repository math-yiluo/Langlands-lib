/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-!
# Qcqs locally finitely presented objects over affine-transition limits

Source: Stacks Project, `limits.tex`, Tag 0EY1, `lemma-descend-finite-presentation-variant`,
essential surjectivity (lines 2722--2810); the category consists of qcqs source schemes
with locally finitely presented structure morphisms over arbitrary bases.
(blueprint: lem-sf-qcqs-lfp-object-limit-model)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- A qcqs scheme locally of finite presentation over a limit with affine transitions
has a model at one stage, without hypotheses on the stages or on the limit.

Source: Stacks Project, `limits.tex`, Tag 0EY1, `lemma-descend-finite-presentation-variant`,
essential surjectivity (lines 2722--2810).
(blueprint: lem-sf-qcqs-lfp-object-limit-model)

Proof (node steps 1--10):
1. Fix `i₀`.  Choose a finite affine open cover `X = ⋃ U_a` with `U_a` mapping into affine
   opens `W_{a,i₀} ⊆ S_{i₀}`; by the affine-transition limit theorem
   (`lem-weil-pbc-limit-affine-transition`) `W_a = lim_j W_{a,j}` with all terms affine, and
   `U_a → W_a` is of finite presentation (Tags 01TQ, 01KO).  If `X` is empty take no charts.
2. Finite-presentation descent (Tag 01ZM) over the affine systems `(W_{a,j})` gives models
   `U_{a,i} → W_{a,i} ⊆ S_i`, affine after increasing `i` (Tag 01Z6), with isomorphisms
   `e_a : U_{a,i} ×_{S_i} S ≅ U_a` over `S`; no hypothesis on a whole stage is used.
3. Descend the quasi-compact overlaps `U_a ∩ U_b` to quasi-compact opens `O_{ab,i} ⊆ U_{a,i}`
   (Tag 01Z4), with `O_{aa,i} = U_{a,i}`; their systems are qcqs with affine transitions.
4. The maps `O_{ab,i} → S_i` and `U_{c,i} → S_i` are locally of finite presentation (Tag 01TR,
   open immersions), hence locally of finite type (Tag 01TQ).
5. Tag 01ZC over the fixed base `S_i` descends `e_b⁻¹ ∘ e_a` on overlaps to `S_i`-maps
   `φ_{ab,i} : O_{ab,i} → O_{ba,i}` via the fibre-product universal property; `φ_{aa,i} = id`.
6. Eventual equality of maps into a locally finite type target gives `φ_{ba} ∘ φ_{ab} = id`.
7. Tag 01Z4(2) gives the gluing domain equality `φ_{ab}⁻¹(O_{ba} ∩ O_{bc}) = O_{ab} ∩ O_{ac}`.
8. Eventual equality into `U_{c,i}` gives the cocycle `φ_{bc} ∘ φ_{ab} = φ_{ac}` on its domain.
9. Glue (Schemes 01JA/01JC) to `X_i` with `f_i : X_i → S_i`; `X_i` is quasi-compact (finitely
   many affine charts) and quasi-separated (Tag 01KO, quasi-compact overlaps); `f_i` is locally
   of finite presentation chartwise.
10. The `e_a` agree on the overlaps `O_{ab,i} ×_{S_i} S` and glue, with their inverses, to an
    isomorphism `X ≅ X_i ×_{S_i} S` over `S`.  No quasi-compactness or quasi-separatedness of
    any `S_i` or of `S` is used.
-/
theorem exists_qcqs_lfp_object_limit_model
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ {i j : Iᵒᵖ} (g : i ⟶ j), IsAffineHom (D.map g)]
    (c : Cone D) (hc : IsLimit c)
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (f : X ⟶ c.pt) [LocallyOfFinitePresentation f] :
    ∃ (i : I) (X_i : Scheme.{u}) (f_i : X_i ⟶ D.obj (op i)),
      CompactSpace X_i ∧ QuasiSeparatedSpace X_i ∧
        LocallyOfFinitePresentation f_i ∧
        ∃ (e : X ≅ pullback (C := Scheme.{u}) f_i (c.π.app (op i))),
          e.hom ≫ pullback.snd f_i (c.π.app (op i)) = f := by
  classical
  let i0 : I := Classical.choice (inferInstance : Nonempty I)
  let i₀ : Iᵒᵖ := op i0
  obtain ⟨Us, hUsB, hUsfin, hUs⟩ :=
    (isBasis_affineOpens_le_preimage (f ≫ c.π.app i₀)).exists_finite_of_isCompact
      (U := ⊤) (by simpa using isCompact_univ)
  have H := descendsToStage_finsetSup (D := D) hc (i₀ := i₀) f hUsfin.toFinset
    (fun W hW ↦ hUsB (hUsfin.mem_toFinset.mp hW))
  rw [Finset.sup_id_eq_sSup, hUsfin.coe_toFinset, ← hUs] at H
  replace H := DescendsToStage.comp_iso (D := D) (c := c) X.topIso.symm H
  rw [Iso.symm_hom, ← Category.assoc, Scheme.toIso_inv_ι, Category.id_comp] at H
  obtain ⟨i, X_i, f_i, h, hf_i, hcompact, hqs, hsq⟩ := H
  refine ⟨i.unop, X_i, f_i, hcompact, hqs, hf_i, hsq.isoPullback, ?_⟩
  exact IsPullback.isoPullback_hom_snd hsq

end AlgebraicGeometry
