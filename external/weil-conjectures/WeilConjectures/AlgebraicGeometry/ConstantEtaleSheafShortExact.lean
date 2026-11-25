/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver

/-!
# Short exact sequences of finite constant etale sheaves

Source: Stacks Project, Etale Cohomology, Tag 03RX (3), via Modules on Sites,
Tag 093U, extension argument; Tag 03EI, exactness of module sheafification
(blueprint: lem-constructible-constant-exact).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- An exact sequence `0 → K → L → N → 0` of finite left modules over a finite ring
induces an exact sequence of constant sheaves on the small etale site.
Source: Stacks Project, Tags 03RX (3), 093U (extension argument), and 03EI
(blueprint: lem-constructible-constant-exact).

Proof:
1. By `def-weil-pbc-constant-sheaf` and `def-weil-pbc-etale-site`, the constant sheaves
and their maps are the sheafifications of the constant presheaves and their maps.
2. Evaluation at every etale object gives the original short exact sequence of modules.
Kernels and cokernels of module presheaves are computed sectionwise, so this presheaf
sequence is short exact (`lem-weil-pbc-site-r-module-presheaf-sheafification-exact`,
clause (1), Stacks Tag 03CS).
3. Module sheafification preserves exactness (the same node, clause (2), Stacks Tag 03EI).
Thus its image is the required short exact sequence of constant sheaves. -/
theorem constantEtaleSheaf_shortExact (X : Scheme.{u}) (Λ : Type (u + 1)) [Ring Λ] [Finite Λ]
    (S : ShortComplex (ModuleCat.{u + 1} Λ)) [Finite S.X₁] [Finite S.X₂] [Finite S.X₃]
    (hS : S.ShortExact) :
    (S.map (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))).ShortExact := by
  exact hS.map_of_exact (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))

end AlgebraicGeometry.Scheme
