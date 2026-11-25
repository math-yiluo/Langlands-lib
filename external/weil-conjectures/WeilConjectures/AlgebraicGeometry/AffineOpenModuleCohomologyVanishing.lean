/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.AlgebraicGeometry.PQFCohomology
public import WeilConjectures.Topology.OpenModuleCohomology
public import Mathlib.AlgebraicGeometry.AffineScheme
import WeilConjectures.AlgebraicGeometry.Cohomology.Affine.Cech
import WeilConjectures.AlgebraicGeometry.OpenModuleCohomologyComparison

/-! # Vanishing of higher module cohomology on affine opens

Source: Stacks Project, Cohomology of Schemes, Lemma 30.2.2, Tag 01XB
(blueprint: pqf-lem-affine-vanishing).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A quasi-coherent module has zero positive-degree cohomology on every affine open.
Source: Stacks Project, Cohomology of Schemes, Lemma 30.2.2, Tag 01XB
(blueprint: pqf-lem-affine-vanishing).

Proof:
1. Regard the affine open U as its induced open subscheme. Its structure sheaf is the
restriction of the structure sheaf of X, and F restricted to U remains quasi-coherent.
The hypothesis IsAffineOpen U says precisely that this induced scheme is affine.
2. Apply affine-scheme vanishing (pqf-lem-affine-vanishing) to U and the restricted
module, obtaining zero cohomology in every positive degree. The comparison between
abelian-sheaf cohomology in that input and module cohomology uses the acyclicity of
injective O_U-modules (Stacks Tag 03FD).
3. Cohomology on U of the restricted module is the displayed openModuleCohomology:
restriction of injective module resolutions to an open remains injective (Tag 01E1).
Thus the vanishing is exactly H^p(U,F) = 0 for each p > 0. -/
theorem subsingleton_openModuleCohomology_of_isAffineOpen (X : Scheme.{u})
    (F : X.Modules) [F.IsQuasicoherent] (U : X.Opens) (hU : IsAffineOpen U)
    (p : ℕ) (hp : 0 < p) :
    Subsingleton ((RingedSpace.openModuleCohomology X.toRingedSpace p U).obj F) := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hp)
  let : IsAffine U.toScheme := hU
  let G := (Scheme.Modules.restrictFunctor U.ι).obj F
  have : Subsingleton (G.H (q + 1)) :=
    Scheme.Modules.subsingleton_H_succ_of_isAffine G q
  obtain ⟨e⟩ := nonempty_openModuleCohomology_addEquiv_restrict_H X F U (q + 1)
  exact ⟨fun x y ↦ e.injective (Subsingleton.elim (e x) (e y))⟩

end AlgebraicGeometry
