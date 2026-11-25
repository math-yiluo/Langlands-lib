/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SelfTorAffineSection
public import WeilConjectures.AlgebraicGeometry.Modules.ExteriorPower
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.SelfTorConormalWedgeChartSectionEquiv
import WeilConjectures.AlgebraicGeometry.SelfTorConormalWedgeChartFromSections

/-! # Affine conormal exterior coordinates preserving ideal wedges

Source: Stacks Project, Tags 01R3 and 0096.
(blueprint: new-t2-self-tor-conormal-wedge-chart). -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry

/-- On one affine chart the exterior conormal coordinate sends the wedge of the
pullback-unit images of ideal sections to the associated algebraic conormal wedge.
This statement involves no derived category or Tor module.
Source: Stacks Project, Tag 01R3 (conormal classes), Tag 0096 (pullback unit).
(blueprint: new-t2-self-tor-conormal-wedge-chart).

Proof: The closed inverse-image chart of U is affine with coordinate ring A/I,
where A = Gamma(Y,U) and I = i.ker.ideal U. Apply affine_conormal_sections in identity
ring coordinates; it makes the pulled-back ideal quasi-coherent and sends the class of
an ideal section to its pullback-unit image. The pulled-back kernel and the associated cotangent
module are quasi-coherent on this affine chart, so their section equivalence gives
a sheaf isomorphism. The map A to the closed chart section ring is onto with kernel I.
Thus A-linearity of the conormal equivalence is also A/I-linearity after the quotient
ring identification. Take the nth exterior power over A/I. Associated-sheaf formation
commutes with exterior powers: check the universal alternating map on basic opens,
where both constructions are localization of the same exterior module. Restriction
commutes with exterior sheaves by exteriorSheaf_restrict_iso. Composing these
identifications gives s, oriented from the exterior sheaf to the affine model.
The conormal unit equation and the characterizing alternating maps give exactly the
asserted equality on each tuple. The affine model section in the conclusion is
constructed by the tilde unit and tensor-pullback unit, so it is the same constant
wedge, not a chosen section. For n=0 both sides are the quotient unit. The empty
chart and zero quotient have zero section modules; the zero ideal is allowed.
No finite generation or regularity is used. -/
theorem exists_selfTor_conormal_wedge_chart
    {Z Y : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]
    (n : ℕ) (U : Y.affineOpens) :
    let N := (Scheme.Modules.tensorPullback i).obj i.ker.toModules
    let E := Scheme.Modules.exteriorPower N n
    let M := conormalExteriorModule (Γ(Y, U.1) : Type u) (i.ker.ideal U) n
    let T := tilde.functor Γ(Y, U.1) ⋙ Scheme.Modules.restrictFunctor U.2.isoSpec.hom ⋙
      Scheme.Modules.pushforward U.1.ι ⋙ Scheme.Modules.tensorPullback i
    ∃ s : E.over (i ⁻¹ᵁ U.1) ≅ (T.obj M).over (i ⁻¹ᵁ U.1),
      ∀ b : Fin n → i.ker.toModules.val.obj (op U.1),
        s.hom.val.app (op (Over.mk (𝟙 (i ⁻¹ᵁ U.1))))
            (Scheme.Modules.wedge (M := N) (r := n) (U := (i ⁻¹ᵁ U.1))
              (fun j ↦ ((Classical.choose
                (Scheme.Modules.exists_tensorPullbackAdjunction i)).unit.app
                  i.ker.toModules).val.app (op U.1) (b j))) =
          selfTorAffineSection i U M (selfTorIdealWedge i U n b) := by
  obtain ⟨e, he⟩ := exists_selfTor_conormal_wedge_chart_section_equiv i n U
  obtain ⟨s, hs⟩ := exists_selfTor_conormal_wedge_chart_from_sections i n U e
  refine ⟨s, ?_⟩
  intro b
  rw [hs]
  exact he b

end AlgebraicGeometry
