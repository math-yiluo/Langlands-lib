/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DivisorModule
public import WeilConjectures.AlgebraicGeometry.Curve.Compactification
import WeilConjectures.AlgebraicGeometry.AffineUnitDivisorBaseChangeCore
import WeilConjectures.AlgebraicGeometry.AffineBoundaryUnitDivisorDescent
import WeilConjectures.AlgebraicGeometry.BaseChangeCurve

/-!
# Boundary principal divisors and algebraically closed base change

Source: blueprint sec-curve-estimates/sbc-thm-algebraically-closed-invariance,
  affine-case proof, unit quotient paragraph (blueprint: lem-sc-affine-unit-divisor-base-change).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- **Boundary principal divisors are unchanged by algebraically closed base change.**
Let `k ⊆ k'` be algebraically closed, `C` a smooth affine connected curve over `k` with a
smooth proper connected compactification `c : C ↪ X = c.Z`, boundary
`S = {P ∈ X closed, P ∉ C}`, and `X' = X ×_k k'` the compactification `c.baseChange` of
`C' = C ×_k k'`, with boundary `S'`. Then:
* every `P ∈ S` has exactly one point `e P ∈ S'` above it and no other point of `X'` lies over
  `P`, giving a bijection `e : S ≃ S'`, hence `ι = Finsupp.domCongr e`;
* for every unit `u` of `𝒪_C(C)` with pullback `u'` along `C' ⟶ C`, the boundary part of
  `div(u')` on `X'` is `ι` of the boundary part of `div(u)` on `X` (units are viewed in the
  function fields through the restriction maps `φ`, `φ'`, tied to the germs at the points of
  `C`, `C'`);
* `ι` maps the set of boundary divisors of units on `C` onto that on `C'`.

Proof: smooth connected curves and their base changes are integral and Noetherian.
The geometric setup and forward order comparison are
`affine_unit_divisor_base_change_core`: restriction to the generic point gives the
compatible maps, rational boundary points have unique fibres, and local DVR base change
preserves orders. Explicit pullback of a unit witnesses the forward inclusion of ranges.
`affine_boundary_unit_divisor_descent` gives the reverse inclusion: a transported boundary
divisor is principal after extension, its degree-zero Picard class vanishes by injectivity
of the Jacobian point comparison, and the divisor exact sequence supplies a unit before
extension. Set antisymmetry gives equality. The two cited intermediate geometric statements
remain open; this is a decomposition of the blueprint argument.

Source: blueprint sec-curve-estimates/sbc-thm-algebraically-closed-invariance,
  affine-case proof, unit quotient paragraph (blueprint: lem-sc-affine-unit-divisor-base-change). -/
theorem affine_unit_divisor_base_change
    (k k' : Type u) [Field k] [IsAlgClosed k] [Field k'] [IsAlgClosed k'] [Algebra k k']
    (C : Scheme.{u}) (f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f] [IsAffine C]
    (c : Compactification f) [IsConnectedCurve c.g] [Smooth c.g] :
    ∃ (_ : IsIntegral c.Z) (_ : IsNoetherian c.Z)
      (_ : IsIntegral (c.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k k')))).Z)
      (_ : IsNoetherian (c.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k k')))).Z),
    ∃ (φ : Γ(C, ⊤) →+* c.Z.functionField)
      (φ' : Γ(CategoryTheory.Limits.pullback f
          (Spec.map (CommRingCat.ofHom (algebraMap k k'))), ⊤) →+*
        (c.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k k')))).Z.functionField),
      (∀ (x : C) (s : Γ(C, ⊤)) (y : c.Z.presheaf.stalk (c.i.base x)),
        c.i.stalkMap x y = C.presheaf.germ ⊤ x trivial s →
          φ s = algebraMap (c.Z.presheaf.stalk (c.i.base x)) c.Z.functionField y) ∧
      (∀ (x : (CategoryTheory.Limits.pullback f (Spec.map (CommRingCat.ofHom (algebraMap k k'))) :
          Scheme.{u}))
        (s : Γ(CategoryTheory.Limits.pullback f
          (Spec.map (CommRingCat.ofHom (algebraMap k k'))), ⊤))
        (y : (c.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k k')))).Z.presheaf.stalk
          ((c.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k k')))).i.base x)),
        (c.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k k')))).i.stalkMap x y =
            (CategoryTheory.Limits.pullback f
              (Spec.map (CommRingCat.ofHom (algebraMap k k')))).presheaf.germ
              ⊤ x trivial s →
          φ' s = algebraMap
            ((c.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k k')))).Z.presheaf.stalk
              ((c.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k k')))).i.base x))
            (c.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k k')))).Z.functionField
            y) ∧
    ∃ e : {P : closedPoints c.Z // P.val ∉ Set.range c.i.base} ≃
        {P : closedPoints (c.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k k')))).Z //
          P.val ∉
            Set.range (c.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k k')))).i.base},
      (∀ P : {P : closedPoints c.Z // P.val ∉ Set.range c.i.base},
        (CategoryTheory.Limits.pullback.fst c.g
            (Spec.map (CommRingCat.ofHom (algebraMap k k')))).base
            (e P).val.val = P.val.val ∧
          ∀ Q : (c.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k k')))).Z,
            (CategoryTheory.Limits.pullback.fst c.g
                (Spec.map (CommRingCat.ofHom (algebraMap k k')))).base Q =
              P.val.val → Q = (e P).val.val) ∧
      (∀ u : Γ(C, ⊤)ˣ,
        Finsupp.subtypeDomain
            (fun P : closedPoints (c.baseChange
                (Spec.map (CommRingCat.ofHom (algebraMap k k')))).Z ↦
              P.val ∉
                Set.range (c.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k k')))).i.base)
            ((c.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k k')))).Z.div
              (Additive.ofMul (Units.map φ'.toMonoidHom
                (Units.map (CategoryTheory.Limits.pullback.fst f
                  (Spec.map (CommRingCat.ofHom (algebraMap k k')))).appTop.hom.toMonoidHom
                  u)))) =
          Finsupp.domCongr e
            (Finsupp.subtypeDomain (fun P : closedPoints c.Z ↦ P.val ∉ Set.range c.i.base)
              (c.Z.div (Additive.ofMul (Units.map φ.toMonoidHom u))))) ∧
      Finsupp.domCongr e ''
          Set.range (fun u : Γ(C, ⊤)ˣ ↦
            Finsupp.subtypeDomain (fun P : closedPoints c.Z ↦ P.val ∉ Set.range c.i.base)
              (c.Z.div (Additive.ofMul (Units.map φ.toMonoidHom u)))) =
        Set.range (fun u' : Γ(CategoryTheory.Limits.pullback f
            (Spec.map (CommRingCat.ofHom (algebraMap k k'))), ⊤)ˣ ↦
          Finsupp.subtypeDomain
            (fun P : closedPoints (c.baseChange
                (Spec.map (CommRingCat.ofHom (algebraMap k k')))).Z ↦
              P.val ∉
                Set.range (c.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k k')))).i.base)
            ((c.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k k')))).Z.div
              (Additive.ofMul (Units.map φ'.toMonoidHom u')))) := by
  classical
  let t := Spec.map (CommRingCat.ofHom (algebraMap k k'))
  let f' := CategoryTheory.Limits.pullback.snd f t
  let c' := c.baseChange t
  let : IsConnectedCurve f' := (baseChange_curve (k' := k') f).2.2.2.2.2 inferInstance
  let : Smooth f' := (baseChange_curve (k' := k') f).2.2.1 inferInstance
  let : IsConnectedCurve c'.g := (baseChange_curve (k' := k') c.g).2.2.2.2.2 inferInstance
  let : Smooth c'.g := (baseChange_curve (k' := k') c.g).2.2.1 inferInstance
  let : ConnectedSpace c.Z := IsConnectedCurve.connectedSpace (f := c.g)
  let : ConnectedSpace c'.Z := IsConnectedCurve.connectedSpace (f := c'.g)
  let : IsNoetherian c.Z := isNoetherian_of_locallyOfFiniteType c.g
  let : IsRegular c.Z := IsRegular.of_smooth c.g
  let : IsIntegral c.Z := IsRegular.isIntegral c.Z
  let : IsNoetherian c'.Z := isNoetherian_of_locallyOfFiniteType c'.g
  let : IsRegular c'.Z := IsRegular.of_smooth c'.g
  let : IsIntegral c'.Z := IsRegular.isIntegral c'.Z
  obtain ⟨φ, φ', hφ, hφ', e, he, hord⟩ :=
    affine_unit_divisor_base_change_core k k' C f c
  refine ⟨inferInstance, inferInstance, inferInstance, inferInstance,
    φ, φ', hφ, hφ', e, he, hord, ?_⟩
  apply Set.Subset.antisymm
  · rintro D ⟨E, ⟨u, rfl⟩, rfl⟩
    exact ⟨Units.map (pullback.fst f t).appTop.hom.toMonoidHom u, hord u⟩
  · exact affine_boundary_unit_divisor_descent k k' C f c φ φ' e ⟨hφ, hφ'⟩ he

end AlgebraicGeometry
