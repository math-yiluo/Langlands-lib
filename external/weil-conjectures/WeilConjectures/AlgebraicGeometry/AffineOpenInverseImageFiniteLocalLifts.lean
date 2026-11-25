/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Affine

import WeilConjectures.AlgebraicGeometry.EtaleAbelianLocalUnitRepresentatives
import WeilConjectures.AlgebraicGeometry.AffineOpenRepresentingCoverDescent

/-! # Finite local lifts at an affine open stage -/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace

/-- A terminal inverse-image section has finitely many affine local lifts at one stage.
Source: Stacks Project, Tags 09XN (local inverse-image sections), 0EYL (descent of
objects, arrows and finite covers), and 03Q6, proof steps (1)--(3).
(blueprint: lem-weil-pbc-affine-open-inverse-image-finite-local-lifts).

Proof: Apply etaleAbelian_local_unit_representatives to t, before choosing
any finite stage cover. This gives an etale cover Z_i of the limit, base
objects W_i, arrows a_i to their pullbacks, and sections s_i representing t
locally by the supplied unit. Apply affineOpen_representing_cover_descent to
this geometric data. It refines the cover, selects a finite family, and
provides one stage j, affine models V_b covering D(j), maps w_b to W_{r(b)},
and arrows e_b from their pullbacks to Z_{r(b)}. These satisfy
p^*(w_b) = e_b followed by a_{r(b)}, and e_b followed by z_{r(b)} covers the
terminal object. Set the required sections to F(w_b)(s_{r(b)}) and pi_b to
e_b followed by z_{r(b)}. Naturality of hH's unit identifies the unit image
of the restricted section with restriction along p^*(w_b). The geometric
factorization equation, the local representative equation, and functoriality
then prove each required identity. This calculation uses the specified
adjunction throughout and needs no additional localization comparison.
Empty covers are permitted in both geometric steps; the final pointwise
calculation is vacuous for an empty index. No overlap agreement is asserted. -/
theorem affineOpenSections_inverse_image_finite_local_lifts
    {X : Scheme.{u + 1}} {J : Type (u + 1)} [SmallCategory J] [IsCofiltered J]
    (D : J ⥤ X.Etale)
    [∀ j, IsAffine (D.obj j).left] [∀ j, IsOpenImmersion (D.obj j).hom]
    (c : Cone (D ⋙ Scheme.Etale.forget X ⋙ Over.forget X))
    (p : c.pt ⟶ X) (hp : ∀ j, c.π.app j ≫ (D.obj j).hom = p)
    (hc : IsLimit c)
    (H : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤
      Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hH : H ⊣ p.Etale.sheafPushforwardContinuous
      AddCommGrpCat.{u + 1} X.smallEtaleTopology c.pt.smallEtaleTopology)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (t : (H.obj F).obj.obj (op (Scheme.Etale.mk (𝟙 c.pt)))) :
    ∃ (j : J) (B : Type (u + 1)) (_ : Finite B)
      (V : B → X.Etale) (v : ∀ b, V b ⟶ D.obj j)
      (s : ∀ b, F.obj.obj (op (V b)))
      (π : ∀ b, p.Etale.obj (V b) ⟶ Scheme.Etale.mk (𝟙 c.pt)),
      (∀ b, IsAffine (V b).left) ∧
      Sieve.ofArrows V v ∈ X.smallEtaleTopology (D.obj j) ∧
      Sieve.ofArrows (fun b ↦ p.Etale.obj (V b)) π ∈
        c.pt.smallEtaleTopology (Scheme.Etale.mk (𝟙 c.pt)) ∧
      ∀ b, (H.obj F).obj.map (π b).op t =
        (hH.unit.app F).hom.app (op (V b)) (s b) := by
  obtain ⟨I, Z, z, W, a, s, hz, hs⟩ :=
    etaleAbelian_local_unit_representatives p H hH F t
  obtain ⟨j, B, hB, r, V, v, w, e, hV, hv, hπ, hw⟩ :=
    affineOpen_representing_cover_descent D c p hp hc I Z z W a hz
  refine ⟨j, B, hB, V, v, (fun b ↦ F.obj.map (w b).op (s (r b))),
    (fun b ↦ e b ≫ z (r b)), hV, hv, hπ, ?_⟩
  intro b
  have hu := (hH.unit.app F).hom.naturality_apply (w b).op (s (r b))
  change (hH.unit.app F).hom.app (op (V b)) (F.obj.map (w b).op (s (r b))) =
    (H.obj F).obj.map (p.Etale.map (w b)).op
      ((hH.unit.app F).hom.app (op (W (r b))) (s (r b))) at hu
  rw [hu, hw b]
  rw [op_comp, Functor.map_comp_apply, op_comp, Functor.map_comp_apply, hs (r b)]

