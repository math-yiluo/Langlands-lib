/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.Sites.Torsor
/-! # The universal property of binary contracted products of torsors
Source: Stacks Project, Tag 03AJ.
(blueprint: lem-pur-binary-torsor-quotient-universal). -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory.Sheaf.Torsor
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {G : Sheaf J AddCommGrpCat.{w}}
end CategoryTheory.Sheaf.Torsor
