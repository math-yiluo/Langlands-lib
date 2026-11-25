/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.CategoryTheory.RepleteSheafTopos
import WeilConjectures.AlgebraicGeometry.ProEtale.RepleteOnContractible
import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Finite

/-!
# Repleteness of the pro-étale topos

Source: blueprint `proposition-repleteness-pro-etale-topos--1` (chap-The-pro-etale-site,
proposition-repleteness-pro-etale-topos); Bhatt–Scholze, *The pro-étale topology*, Proposition
4.2.8.
-/

@[expose] public section

universe u w

namespace AlgebraicGeometry.Scheme

/-- **Repleteness of the pro-étale topos** (blueprint: proposition-repleteness-pro-etale-topos--1;
Bhatt–Scholze, Proposition 4.2.8). For every scheme, the topos of set-valued sheaves on its
small pro-étale site is replete: inverse sequences with epimorphic transition maps have
epimorphic limit projections at every natural-number index.

Proof:
1. Fix an inverse sequence `F` with epimorphic adjacent maps and an index `m`.
   By `definition-repleteness--1` and the local-surjectivity criterion
   `proposition-repleteness-pro-etale-topos--1`, it suffices to lift each
   section `y` of `F_m` over an arbitrary site object `U` after a covering of `U`.
2. By `ProEt.exists_isWContractibleRing_cover`, cover `U` by affines `W_i ≅ Spec D_i` with
   each `D_i` w-contractible; `isWeaklyContractible_of_iso` makes each `W_i` weakly
   contractible. This applies to arbitrary `U`, without quasi-compactness assumptions.
3. Apply `proposition-repleteness-pro-etale-topos` to the original sequence and each `W_i`.
   The map on sections of the limit projection at `m` is surjective there, so the
   restriction of `y` lifts to a section of the limit over `W_i`.
4. These separate lifts make the projection locally surjective, hence epimorphic by
   `proposition-repleteness-pro-etale-topos--1`. No compatibility on overlaps
   is required. Since the sequence and `m` were arbitrary, the topos is replete.
-/
theorem isReplete_proEtale (X : Scheme.{u}) :
    CategoryTheory.GrothendieckTopology.IsReplete.{u + 1, u, w} (ProEt.topology X) := by
  intro F hF m
  apply (CategoryTheory.Sheaf.isLocallySurjective_iff_epi _).1
  constructor
  intro U y
  obtain ⟨I, W, f, hW, hcov⟩ := ProEt.exists_isWContractibleRing_cover U
  apply (ProEt.topology X).superset_covering _ hcov
  rintro V g ⟨_, a, _, ⟨i⟩, rfl⟩
  obtain ⟨D, hD, ⟨e⟩⟩ := hW i
  have : IsWContractibleRing D := hD
  have hw : (ProEt.topology X).IsWeaklyContractible.{max (u + 1) w} (W i) :=
    ProEt.isWeaklyContractible_of_iso e
  exact (CategoryTheory.Presheaf.imageSieve _ y).downward_closed
    ((proetale_surjective_sections_of_epi_tower X F hF (W i) hw).2 m _) a

end AlgebraicGeometry.Scheme
