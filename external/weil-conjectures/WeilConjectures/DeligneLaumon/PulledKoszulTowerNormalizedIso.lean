/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.PulledKoszulTowerModel.PulledKoszulTowerNormalization
import WeilConjectures.DeligneLaumon.BalancedFiniteTower.BalancedFiniteTowerScalarComparison
import WeilConjectures.DeligneLaumon.BalancedFiniteTower.BalancedFiniteTowerQuotientComparison
import WeilConjectures.DeligneLaumon.BalancedFiniteTower.BalancedFiniteTowerKoszulAugmentation

/-! # Normalized ordinary pullback of the principal Koszul tower

Source: Stacks Project, sites-modules.tex, Tag 03EL, and sites-cohomology.tex,
Tag 07A4; the scalar and adjacent-transition calculation of steps 2--4 of
lem-a1-pulled-koszul-tower-chain-comparison.
(blueprint: lem-a1-pulled-koszul-tower-normalized-iso).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open WeilConjectures.CompletedTowerIndependent
open WeilConjectures.PrincipalKoszulStrictReplacement
open WeilConjectures.PulledKoszulTowerModel

namespace WeilConjectures

end WeilConjectures
