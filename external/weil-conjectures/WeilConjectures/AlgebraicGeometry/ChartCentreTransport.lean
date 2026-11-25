/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ConormalGradedAlgebra.ConormalAlgebraFlatBaseChange
public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalRegularPureCodimension
public import WeilConjectures.AlgebraicGeometry.Purity.PurityNormalProjection
public import WeilConjectures.AlgebraicGeometry.RelativeTangentBundle.RelativeTangentBundle
public import WeilConjectures.AlgebraicGeometry.ChartNormalDifferential.ChartNormalDifferential
public import WeilConjectures.AlgebraicGeometry.DiagonalConormalDifferentials
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import WeilConjectures.AlgebraicGeometry.ChartNormalDifferential.ChartNormalDifferential

/-!
# Centred diagonal neighbourhood and its differential under an étale source map

Source: current blueprint, `sk-prop-sp-orientation-charts.proof.md`, Steps 1--2:
remove the off-diagonal components, form the Cartesian centre squares, apply the
canonical flat conormal graded comparison, and identify its normal map with the
differential (Stacks Tags 02GE, 0473 and 0635).
(blueprint: lem-sp-chart-centre-transport)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ChartNormalDifferential

attribute [local irreducible] Scheme.Modules.tensorPullback
  ConormalGradedAlgebra.presentation PurityNormalBundle.normalCone
  RelativeTangentBundle.scheme PurityNormalBundle.projection
  RelativeTangentBundle.projection PurityNormalBundle.zeroSection
  RelativeTangentBundle.zeroSection Scheme.Hom.relativeDifferentials

namespace AlgebraicGeometry

/-- The canonical centred-neighbourhood transport, including its graded and tangent maps.
Source: current blueprint, `sk-prop-sp-orientation-charts.proof.md`, Steps 1--2;
Stacks Tags 02GE, 0473, 0635 and 08S2
(blueprint: lem-sp-chart-centre-transport).

Proof: Since the structural morphisms are separated, so are g, h and uV.
The etale diagonal of uV is open and closed in F = V ×_X V, while
F is closed in V ×_Y V by base change of the separated diagonal of g.
Thus the complement of F minus its diagonal is the specified open O and contains
the whole diagonal. Computing the fibre products gives the two centre squares
and the base-change square for (W0,s). The restrictions of b and a are separated
etale morphisms, since they are base changes and composites of uV.
Flat conormal base change now gives the unique graded map, an isomorphism in every
degree, with local formula [c] tensor r maps to [q-sharp(c) r]. Its degree zero is
the scalar map and its degree one is the canonical conormal map. Relative Spec
gives its Cartesian normal map and preserves the augmentation zero sections.
For a smooth diagonal, the symmetric-algebra identification of the normal cone
with the tangent bundle sends da to the second-factor-minus-first-factor class.
Pulling that class back along (uV,uV) sends it to the same difference for uV-sharp(a).
The universal property of differentials and the symmetric algebra therefore
identifies this specific normal map with duV; etaleness makes its tangent square
Cartesian. At d=0 the diagonal component is clopen and the graded algebra has
only degree zero. The same constructions and equations apply to the empty source. -/
theorem chart_centre_transport (k : Type u) [Field k]
    {X Y V : Scheme.{u}}
    (aX : X ⟶ Spec (CommRingCat.of k))
    (aY : Y ⟶ Spec (CommRingCat.of k))
    (aV : V ⟶ Spec (CommRingCat.of k))
    [IsSeparated aX] [IsSeparated aY] [IsSeparated aV]
    [LocallyOfFiniteType aX] [LocallyOfFiniteType aY] [LocallyOfFiniteType aV]
    [QuasiCompact aX] [QuasiCompact aY] [QuasiCompact aV]
    (g : X ⟶ Y) (d : ℕ) [SmoothOfRelativeDimension d g]
    (hgk : g ≫ aY = aX)
    (uV : V ⟶ X) [Etale uV]
    (huVk : uV ≫ aX = aV)
    (h : V ⟶ Y) (hh : h = uV ≫ g) :
    ∃ (a : pullback h g ⟶ pullback.diagonalObj g)
      (ha : a = pullback.map h g g g uV (𝟙 X) (𝟙 Y) (by simp [hh]) (by simp))
      (b : pullback.diagonalObj h ⟶ pullback h g)
      (hb : b = pullback.map h h h g (𝟙 V) uV (𝟙 Y) (by simp) (by simp [hh]))
      (s : V ⟶ pullback h g)
      (hs : s = pullback.lift (𝟙 V) uV (by simp [hh])),
      IsPullback a (pullback.fst h g) (pullback.fst g g) uV ∧
      IsPullback s uV a (pullback.diagonal g) ∧
      ∃ (O : (pullback.diagonalObj h).Opens) (iO : V ⟶ O.toScheme)
          (hIO : IsClosedImmersion iO)
          (hdiag : iO ≫ O.ι = pullback.diagonal h),
        O.1 =
          (Set.range (pullback.map uV uV h h (𝟙 V) (𝟙 V) g
            (by simp [hh]) (by simp [hh])) \ Set.range (pullback.diagonal h))ᶜ ∧
        Set.range (pullback.diagonal h) ⊆ O.1 ∧
        IsClosedImmersion
          (pullback.map uV uV h h (𝟙 V) (𝟙 V) g (by simp [hh]) (by simp [hh])) ∧
        IsOpenImmersion (pullback.diagonal uV) ∧
        IsClosedImmersion (pullback.diagonal uV) ∧
        IsPullback iO (𝟙 V) (O.ι ≫ b) s ∧
        IsPullback iO uV (O.ι ≫ b ≫ a) (pullback.diagonal g) ∧
        Etale (O.ι ≫ b) ∧ IsSeparated (O.ι ≫ b) ∧
        Etale (O.ι ≫ b ≫ a) ∧ IsSeparated (O.ι ≫ b ≫ a) ∧
        ∃ (hg : IsSeparated g),
          letI : IsSeparated g := hg
          letI : IsClosedImmersion (pullback.diagonal g) := inferInstance
          letI : IsClosedImmersion iO := hIO
          letI : Smooth g := SmoothOfRelativeDimension.smooth d g
          letI : Smooth (uV ≫ g) := inferInstance
          let Ag := ConormalGradedAlgebra.presentation (pullback.diagonal g)
          let Ah := ConormalGradedAlgebra.presentation iO
          ∃ (hcomp : iO ≫ O.ι ≫ b ≫ a = uV ≫ pullback.diagonal g)
            (c : (Scheme.Modules.tensorPullback uV).obj Ag.algebra.toModule ≅
              Ah.algebra.toModule),
            ConormalGradedAlgebra.IsBaseChangeMap iO (pullback.diagonal g)
              (O.ι ≫ b ≫ a) uV hcomp Ah Ag c.hom ∧
            ∃ (ωV : (uV ≫ g).relativeDifferentials ≅ ConormalGradedAlgebra.piece iO 1)
              (ωX : g.relativeDifferentials ≅
                ConormalGradedAlgebra.piece (pullback.diagonal g) 1)
              (tV : PurityNormalBundle.normalCone iO ≅
                RelativeTangentBundle.scheme (uV ≫ g))
              (tX : PurityNormalBundle.normalCone (pullback.diagonal g) ≅
                RelativeTangentBundle.scheme g)
              (ν : PurityNormalBundle.normalCone iO ⟶
                PurityNormalBundle.normalCone (pullback.diagonal g))
              (du : RelativeTangentBundle.scheme (uV ≫ g) ⟶
                RelativeTangentBundle.scheme g),
              IsDifferenceIdentification (uV ≫ g) iO
                (O.ι ≫ pullback.fst h h) (O.ι ≫ pullback.snd h h) ωV ∧
              IsDifferenceIdentification g (pullback.diagonal g)
                (pullback.fst g g) (pullback.snd g g) ωX ∧
              IsNormalTangentIdentification (uV ≫ g) iO ωV tV ∧
              IsNormalTangentIdentification g (pullback.diagonal g) ωX tX ∧
              IsSpecMap uV Ah.algebra Ag.algebra
                (PurityNormalBundle.projection iO)
                (PurityNormalBundle.projection (pullback.diagonal g))
                (normalAlgebraIso iO) (normalAlgebraIso (pullback.diagonal g)) ν
                (pullbackSection uV Ah.algebra.toModule Ag.algebra.toModule c.hom) ∧
              IsPullback ν (PurityNormalBundle.projection iO)
                (PurityNormalBundle.projection (pullback.diagonal g)) uV ∧
              PurityNormalBundle.zeroSection iO ≫ ν =
                uV ≫ PurityNormalBundle.zeroSection (pullback.diagonal g) ∧
              IsDifferential g uV du ∧
              IsPullback du (RelativeTangentBundle.projection (uV ≫ g))
                (RelativeTangentBundle.projection g) uV ∧
              RelativeTangentBundle.zeroSection (uV ≫ g) ≫ du =
                uV ≫ RelativeTangentBundle.zeroSection g ∧
              ν ≫ tX.hom = tV.hom ≫ du := by
  sorry

end AlgebraicGeometry
