/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Fpqc

/-! # The structure sheaf on the small pro-etale site

Source: Stacks Project, Tags 03O3 and 098K
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Global sections, restricted to weakly etale schemes over `S`, with pullback of functions.
Source: Stacks Project, Tags 03O3 and 098K
(auxiliary; not a blueprint node). -/
def proEtaleStructurePresheaf (S : Scheme.{u}) : S.ProEtᵒᵖ ⥤ CommRingCat.{u} :=
  (ProEt.forget S ⋙ Over.forget S).op ⋙ Scheme.Γ

/-- Global sections form a sheaf for pro-etale coverings.
Source: Stacks Project, Tag 03O3 (auxiliary; not a blueprint node).
Proof: the underlying set presheaf is represented on schemes by the affine line over `Z`.
Representable functors satisfy fpqc descent. Restrict this descent to the small pro-etale
site, whose coverings are fpqc coverings. The forgetful functor from commutative rings
creates limits and reflects isomorphisms, so set-valued descent gives ring-valued descent. -/
theorem proEtaleStructurePresheaf_isSheaf (S : Scheme.{u}) :
    Presheaf.IsSheaf (ProEt.topology S) (proEtaleStructurePresheaf S) := by
  exact Functor.op_comp_isSheaf_of_isSheaf _ _ proetaleTopology _
    (isSheaf_Γ proetaleTopology)

/-- The pro-etale structure sheaf, with sections `Γ(U, O_U)` and the usual restriction maps.
Source: Stacks Project, Tags 03O3 and 098K
(auxiliary; not a blueprint node). -/
def proEtaleStructureSheaf (S : Scheme.{u}) : Sheaf (ProEt.topology S) CommRingCat.{u} :=
  ⟨proEtaleStructurePresheaf S, proEtaleStructurePresheaf_isSheaf S⟩

end AlgebraicGeometry.Scheme
