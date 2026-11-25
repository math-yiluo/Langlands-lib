/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.TangentSpace
public import WeilConjectures.AlgebraicGeometry.Modules.HomObjSections

/-!
# The Lie algebra of a group scheme

The Lie algebra sheaf `ω_{G/S}^∨` of a group scheme `G` over `S` and its module of global sections
`AlgebraicGeometry.GrpObj.Lie`, the relative tangent vectors at the identity.
-/

@[expose] public section

universe u

open CategoryTheory TrivSqZeroExt
open scoped MonObj

namespace AlgebraicGeometry

/-! ### The Lie algebra sheaf and the Lie algebra over a general base -/

namespace GrpObj

variable {S : Scheme.{u}} (G : Over S) [GrpObj G]

/-- The identity section `e : S ⟶ G` of a group scheme `G` over `S`: the unit `η : 𝟙 ⟶ G` of the
group object, as a morphism of schemes. -/
noncomputable def unitSection : S ⟶ G.left :=
  η[G].left

/-- The identity section is a section of the structure morphism. -/
theorem unitSection_comp_hom : unitSection G ≫ G.hom = 𝟙 S :=
  Over.w η[G]

/-- The `𝒪_S`-module `ω_{G/S} = e^*Ω¹_{G/S}`: the cotangent sheaf of `G/S` pulled back along the
identity section. For smooth `G` it is locally free, and `Lie(G/S)` is its dual.
(blueprint: `def-wf-lie-algebra-derivation`) -/
noncomputable def omega : S.Modules :=
  (Scheme.Modules.pullback (unitSection G)).obj G.hom.cotangentSheaf

/-- The Lie algebra sheaf `Lie(G/S) = ℋom_{𝒪_S}(ω_{G/S}, 𝒪_S)` of a group scheme `G` over `S`: the
sheaf of relative tangent vectors along the identity section. (blueprint:
`def-wf-lie-algebra-derivation`) -/
noncomputable def lieAlgebraSheaf : S.Modules :=
  Scheme.Modules.dual (omega G)

theorem lieAlgebraSheaf_eq_tangentSheafAlong :
    lieAlgebraSheaf G = G.hom.tangentSheafAlong (unitSection G) :=
  rfl

/-- For a smooth group scheme, the Lie algebra sheaf is the pullback `e^*T_{G/S}` of the tangent
sheaf along the identity section. -/
theorem lieAlgebraSheaf_iso_pullback_tangentSheaf [Smooth G.hom] :
    Nonempty (lieAlgebraSheaf G ≅
      (Scheme.Modules.pullback (unitSection G)).obj G.hom.tangentSheaf) :=
  G.hom.tangentSheafAlong_iso_pullback_tangentSheaf (unitSection G) (unitSection_comp_hom G)

/-- The Lie algebra `Lie(G) = Hom_{𝒪_S}(ω_{G/S}, 𝒪_S)` of a group scheme `G` over `S`: the global
sections of the Lie algebra sheaf, the module of relative tangent vectors at the identity. Its Lie
bracket is constructed in `WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Bracket`.
(blueprint: `def-wf-lie-algebra-derivation`) -/
def Lie : Type u :=
  omega G ⟶ Scheme.Modules.unitModule S

noncomputable instance : AddCommGroup (Lie G) :=
  inferInstanceAs (AddCommGroup (omega G ⟶ Scheme.Modules.unitModule S))

noncomputable instance : Module Γ(S, ⊤) (Lie G) :=
  inferInstanceAs (Module Γ(S, ⊤) (omega G ⟶ Scheme.Modules.unitModule S))

/-- The Lie algebra is the module of global sections of the Lie algebra sheaf. -/
theorem nonempty_lie_equiv_sections : Nonempty (Lie G ≃+ Γ(lieAlgebraSheaf G, ⊤)) :=
  ⟨(Scheme.Modules.ΓHomObjAddEquiv _ _).symm⟩

end GrpObj

end AlgebraicGeometry
