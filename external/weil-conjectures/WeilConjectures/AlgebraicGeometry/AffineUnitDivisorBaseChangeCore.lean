/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve.Divisor
public import WeilConjectures.AlgebraicGeometry.Curve.Compactification
import WeilConjectures.AlgebraicGeometry.LocalDvrBaseChange
import Mathlib.AlgebraicGeometry.AlgClosed.Basic

/-! # Boundary geometry and forward comparison of unit divisors

Source: blueprint proposition-cohomology-smooth-affine-curve, affine unit quotient paragraph.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- Restriction through a nonempty open immersion, compatible with every stalk germ. -/
private theorem exists_open_restriction
    (C X : Scheme.{u}) [Nonempty C] [IsIntegral X]
    (i : C ⟶ X) [IsOpenImmersion i] :
    ∃ φ : Γ(C, ⊤) →+* X.functionField,
      ∀ (x : C) (s : Γ(C, ⊤)) (y : X.presheaf.stalk (i.base x)),
        i.stalkMap x y = C.presheaf.germ ⊤ x trivial s →
          φ s = algebraMap (X.presheaf.stalk (i.base x)) X.functionField y := by
  classical
  obtain ⟨x₀⟩ := ‹Nonempty C›
  let V : X.Opens := i ''ᵁ ⊤
  have : Nonempty V := ⟨⟨i x₀, x₀, trivial, rfl⟩⟩
  let φ : Γ(C, ⊤) →+* X.functionField :=
    ((i.appIso ⊤).inv ≫ X.germToFunctionField V).hom
  refine ⟨φ, ?_⟩
  intro x s y hy
  let z := X.presheaf.germ V (i x) ⟨x, trivial, rfl⟩ ((i.appIso ⊤).inv s)
  have hz : i.stalkMap x z = C.presheaf.germ ⊤ x trivial s := by
    dsimp [z, V]
    erw [Scheme.Hom.germ_stalkMap_apply, ← CommRingCat.comp_apply (i.appIso ⊤).inv,
      Scheme.Hom.appIso_inv_app, TopCat.Presheaf.germ_res_apply]
  have hzy : z = y := (ConcreteCategory.bijective_of_isIso (i.stalkMap x)).1
    (hz.trans hy.symm)
  rw [← hzy]
  exact (Scheme.algebraMap_germ_eq_germToFunctionField (X := X) (U := V)
    (x := i x) (show i x ∈ V from ⟨x, trivial, rfl⟩) _).symm

/-- A fraction-field map specified on one stalk agrees with pullback on open sections. -/
private theorem rational_pullback_germ
    (X Y : Scheme.{u}) [IsIntegral X] [IsIntegral Y]
    (π : Y ⟶ X) [IsDominant π] (P : Y)
    (ρ : X.functionField →+* Y.functionField)
    (hρ : ∀ r : X.presheaf.stalk (π P),
      ρ (algebraMap _ X.functionField r) =
        algebraMap _ Y.functionField (π.stalkMap P r))
    (U : X.Opens) [Nonempty U] [Nonempty (π ⁻¹ᵁ U)] (s : Γ(X, U)) :
    ρ (X.germToFunctionField U s) =
      Y.germToFunctionField (π ⁻¹ᵁ U) (π.app U s) := by
  classical
  have hη : π (genericPoint Y) = genericPoint X := by
    apply ((genericPoint_spec X).eq _).symm
    convert! (genericPoint_spec Y).image π.continuous
    rw [Set.image_univ, π.denseRange.closure_range]
  let ψ : X.functionField →+* Y.functionField :=
    (X.presheaf.stalkSpecializes (Inseparable.of_eq hη).specializes ≫
      π.stalkMap (genericPoint Y)).hom
  have hψ (r : X.presheaf.stalk (π P)) :
      ψ (algebraMap _ X.functionField r) =
        algebraMap _ Y.functionField (π.stalkMap P r) := by
    change (X.presheaf.stalkSpecializes _ ≫ π.stalkMap _) (X.presheaf.stalkSpecializes _ r) =
      Y.presheaf.stalkSpecializes _ (π.stalkMap P r)
    rw [← CommRingCat.comp_apply, ← Category.assoc, TopCat.Presheaf.stalkSpecializes_comp]
    exact π.stalkSpecializes_stalkMap_apply _ P (genericPoint_specializes P) r
  have hρψ : ρ = ψ := IsFractionRing.ringHom_ext (fun r ↦ (hρ r).trans (hψ r).symm)
  rw [hρψ]
  change π.stalkMap _ (X.presheaf.stalkSpecializes _ (X.presheaf.germ U _ _ s)) = _
  change (X.presheaf.germ U _ _ ≫ X.presheaf.stalkSpecializes _ ≫
    π.stalkMap (genericPoint Y)) s = _
  rw [← Category.assoc, TopCat.Presheaf.germ_stalkSpecializes]
  exact π.germ_stalkMap_apply U (genericPoint Y) _ s

/-- Germ-compatible restrictions commute with a dominant morphism in an open square. -/
private theorem open_restriction_natural
    (C C' X Y : Scheme.{u}) [Nonempty C'] [IsIntegral X] [IsIntegral Y]
    (i : C ⟶ X) (i' : C' ⟶ Y) [IsOpenImmersion i] [IsOpenImmersion i']
    (p : C' ⟶ C) (π : Y ⟶ X) [IsDominant π] (hsq : i' ≫ π = p ≫ i)
    (φ : Γ(C, ⊤) →+* X.functionField)
    (φ' : Γ(C', ⊤) →+* Y.functionField)
    (hφ : ∀ (x : C) (s : Γ(C, ⊤)) (y : X.presheaf.stalk (i x)),
      i.stalkMap x y = C.presheaf.germ ⊤ x trivial s →
        φ s = algebraMap _ X.functionField y)
    (hφ' : ∀ (x : C') (s : Γ(C', ⊤)) (y : Y.presheaf.stalk (i' x)),
      i'.stalkMap x y = C'.presheaf.germ ⊤ x trivial s →
        φ' s = algebraMap _ Y.functionField y)
    (P : Y) (ρ : X.functionField →+* Y.functionField)
    (hρ : ∀ r : X.presheaf.stalk (π P),
      ρ (algebraMap _ X.functionField r) =
        algebraMap _ Y.functionField (π.stalkMap P r)) (s : Γ(C, ⊤)) :
    φ' (p.appTop s) = ρ (φ s) := by
  classical
  obtain ⟨x'⟩ := ‹Nonempty C'›
  let V : X.Opens := i ''ᵁ ⊤
  have hx : π (i' x') = i (p x') := by
    simpa only [Scheme.Hom.comp_apply] using congrArg (fun g : C' ⟶ X ↦ g x') hsq
  have hxV : π (i' x') ∈ V := by rw [hx]; exact ⟨p x', trivial, rfl⟩
  have : Nonempty V := ⟨⟨π (i' x'), hxV⟩⟩
  have : Nonempty (π ⁻¹ᵁ V) := ⟨⟨i' x', hxV⟩⟩
  let t := (i.appIso ⊤).inv s
  have ht : φ s = X.germToFunctionField V t := by
    let z := X.presheaf.germ V (i (p x')) ⟨p x', trivial, rfl⟩ t
    have hz : i.stalkMap (p x') z = C.presheaf.germ ⊤ (p x') trivial s := by
      dsimp [z, t, V]
      erw [Scheme.Hom.germ_stalkMap_apply, ← CommRingCat.comp_apply (i.appIso ⊤).inv,
        Scheme.Hom.appIso_inv_app, TopCat.Presheaf.germ_res_apply]
    rw [hφ (p x') s z hz]
    exact Scheme.algebraMap_germ_eq_germToFunctionField X
      (show i (p x') ∈ V from ⟨p x', trivial, rfl⟩) t
  have hV : (⊤ : C'.Opens) ≤ i' ⁻¹ᵁ (π ⁻¹ᵁ V) := by
    intro x _
    have hx : π (i' x) = i (p x) := by
      simpa only [Scheme.Hom.comp_apply] using congrArg (fun g : C' ⟶ X ↦ g x) hsq
    change π (i' x) ∈ V
    rw [hx]
    exact ⟨p x, trivial, rfl⟩
  have hiV : (⊤ : C.Opens) ≤ i ⁻¹ᵁ V := by
    intro x _
    exact ⟨x, trivial, rfl⟩
  have happ : (i.appIso ⊤).inv ≫ π.app V ≫ i'.appLE (π ⁻¹ᵁ V) ⊤ hV =
      p.appTop := by
    rw [← Scheme.Hom.comp_appLE]
    simp only [hsq]
    rw [← Scheme.Hom.appLE_comp_appLE p i V ⊤ ⊤ hiV (by simp)]
    rw [← Category.assoc, Scheme.Hom.appIso_inv_appLE]
    simp only [homOfLE_refl, op_id, CategoryTheory.Functor.map_id, Category.id_comp]
    simp [Scheme.Hom.appLE, Scheme.Hom.appTop]
  let z := Y.presheaf.germ (π ⁻¹ᵁ V) (i' x') hxV (π.app V t)
  have hz : i'.stalkMap x' z = C'.presheaf.germ ⊤ x' trivial (p.appTop s) := by
    dsimp [z]
    rw [Scheme.Hom.germ_stalkMap_apply]
    rw [← TopCat.Presheaf.germ_res_apply C'.presheaf (homOfLE hV) x' trivial]
    change C'.presheaf.germ ⊤ x' trivial
      (((i.appIso ⊤).inv ≫ π.app V ≫ i'.appLE (π ⁻¹ᵁ V) ⊤ hV) s) = _
    rw [happ]
  rw [hφ' x' _ z hz, ht, rational_pullback_germ X Y π P ρ hρ V t]
  exact Scheme.algebraMap_germ_eq_germToFunctionField Y hxV _

/-- Boundary geometry, compatible rational maps, and preservation of unit orders.
Source: blueprint proposition-cohomology-smooth-affine-curve, affine unit quotient paragraph.
(blueprint: lem-sc-affine-unit-divisor-base-change-core).

Proof: put V = c.i(C), a nonempty open in the integral compactification X. Define the
restriction map as the inverse of c.i.appIso at the top open, followed by
X.germToFunctionField V; do the same on X'. Naturality of germs and
Scheme.algebraMap_germ_eq_germToFunctionField prove the stated compatibility. Conversely,
compatibility determines each map by evaluating at any point of the nonempty open.
The complement of V is a finite set of closed points: X is a Noetherian integral curve and
V is nonempty. Each boundary point is k-rational by algebraic closedness and finite type.
Scheme.local_dvr_base_change constructs its unique rational closed point above it. The
cartesian open-immersion square says that the complement of V' is the inverse image of
the complement of V. Hence the unique-fibre assignment is a bijection of the boundaries.
At corresponding points, Scheme.local_dvr_base_change also constructs the rational
pullback from the stalk map and proves equality of normalized orders. The two restriction
maps commute with this rational pullback: compare their germs on the common nonempty open
and specialize to the generic points. Thus the order comparison applies to the pulled-back
unit. Use Scheme.div_apply and equality coefficient by coefficient to obtain the Finsupp
equality. The empty boundary case gives the empty equivalence and zero divisors. -/
theorem affine_unit_divisor_base_change_core
    (k k' : Type u) [Field k] [IsAlgClosed k] [Field k'] [IsAlgClosed k'] [Algebra k k']
    (C : Scheme.{u}) (f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f] [IsAffine C]
    (c : Compactification f) [IsConnectedCurve c.g] [Smooth c.g]
    [IsIntegral c.Z] [IsNoetherian c.Z]
    [IsIntegral (c.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k k')))).Z]
    [IsNoetherian (c.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k k')))).Z] :
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
              (c.Z.div (Additive.ofMul (Units.map φ.toMonoidHom u))))) := by
  classical
  let b := Spec.map (CommRingCat.ofHom (algebraMap k k'))
  let c' := c.baseChange b
  let π := pullback.fst c.g b
  have : Surjective b := ⟨fun x ↦ ⟨default, Subsingleton.elim _ _⟩⟩
  have : IsDominant π := inferInstance
  have := c.isOpenImmersion
  have := c.isProper
  have := c'.isOpenImmersion
  have : Nonempty C := IsConnectedCurve.nonempty f
  obtain ⟨x⟩ := ‹Nonempty C›
  obtain ⟨x', -⟩ := (pullback.fst f b).surjective x
  have : Nonempty (pullback f b : Scheme.{u}) := ⟨x'⟩
  obtain ⟨φ, hφ⟩ := exists_open_restriction C c.Z c.i
  obtain ⟨φ', hφ'⟩ := exists_open_restriction (pullback f b) c'.Z c'.i
  refine ⟨φ, φ', hφ, hφ', ?_⟩
  have hclosed (P : c.Z) (hP : P ∉ Set.range c.i.base) : IsClosed ({P} : Set c.Z) :=
    c.i.isOpenEmbedding.isOpen_range.isClosed_singleton_of_mem_compl
      (IsConnectedCurve.krullDim_eq_one (f := c.g)).le
      (Set.range_nonempty c.i.base) hP
  have hrange : Set.range c'.i.base = π.base ⁻¹' Set.range c.i.base :=
    Scheme.range_snd_of_isPullback
      (c.isPullback_i_ofIsPullback (IsPullback.of_hasPullback f b))
  let B := {P : closedPoints c.Z // P.val ∉ Set.range c.i.base}
  let B' := {Q : closedPoints c'.Z // Q.val ∉ Set.range c'.i.base}
  have hnot (Q : B') : π.base Q.val.val ∉ Set.range c.i.base := by
    intro h
    exact Q.property
      ((congrArg (fun S : Set c'.Z ↦ Q.val.val ∈ S) hrange).mpr h)
  let back : B' → B := fun Q ↦ ⟨⟨π.base Q.val.val, hclosed _ (hnot Q)⟩, hnot Q⟩
  have hlift (P : closedPoints c.Z) :
      ∃ Q : closedPoints c'.Z, π.base Q.val = P.val := by
    let p : c.g.fieldPoints k := ⟨pointOfClosedPoint c.g P.val P.property, by
      simp [pointOfClosedPoint_comp]⟩
    let q := c.g.baseChangeFieldPoint k' p
    have hq : IsClosed ({q.val.base default} : Set c'.Z) := by
      have : Set.range q.val.base = {q.val.base default} :=
        Set.range_eq_singleton_iff.mpr fun a ↦ congrArg q.val.base (Subsingleton.elim a default)
      rw [← this]
      exact q.val.isClosedEmbedding.isClosed_range
    refine ⟨⟨q.val.base default, hq⟩, ?_⟩
    change π.base (q.val.base default) = P.val
    change ((c.g.baseChangeFieldPoint k' p).val ≫ π).base default = P.val
    rw [Scheme.Hom.baseChangeFieldPoint, pullback.lift_fst, Scheme.Hom.comp_apply]
    exact pointOfClosedPoint_apply c.g P.val P.property _
  have hunique (P : closedPoints c.Z) (Q R : c'.Z)
      (hQ : π.base Q = P.val) (hR : π.base R = P.val) : Q = R := by
    let p : c.g.fieldPoints k := ⟨pointOfClosedPoint c.g P.val P.property, by
      simp [pointOfClosedPoint_comp]⟩
    have hQ' : π.base Q = p.val.base default :=
      hQ.trans (pointOfClosedPoint_apply c.g P.val P.property default).symm
    have hR' : π.base R = p.val.base default :=
      hR.trans (pointOfClosedPoint_apply c.g P.val P.property default).symm
    exact (c.g.baseChangeFieldPoint_eq_of_fst_eq k' p hQ').symm.trans
      (c.g.baseChangeFieldPoint_eq_of_fst_eq k' p hR')
  have hbij : Function.Bijective back := by
    constructor
    · intro Q R h
      apply Subtype.ext
      apply Subtype.ext
      exact hunique (back Q).val Q.val.val R.val.val rfl
        (congrArg (fun P : B ↦ P.val.val) h).symm
    · intro P
      obtain ⟨Q, hQ⟩ := hlift P.val
      have hQnot : Q.val ∉ Set.range c'.i.base := by
        rw [hrange]
        change π.base Q.val ∉ Set.range c.i.base
        simpa [hQ] using P.property
      refine ⟨⟨Q, hQnot⟩, ?_⟩
      apply Subtype.ext
      exact Subtype.ext hQ
  let e : B ≃ B' := (Equiv.ofBijective back hbij).symm
  have he (P : B) : π.base (e P).val.val = P.val.val :=
    congrArg (fun P : B ↦ P.val.val) ((Equiv.ofBijective back hbij).apply_symm_apply P)
  refine ⟨e, fun P ↦ ⟨he P, fun Q hQ ↦ hunique P.val Q (e P).val.val hQ (he P)⟩, ?_⟩
  intro a
  apply Finsupp.ext
  intro Q
  have hpoint := he (e.symm Q)
  simp only [e.apply_symm_apply] at hpoint
  obtain ⟨_, _, _, _, P', _, huniq, _, _, ρ, hρ, hord⟩ :=
    Scheme.local_dvr_base_change k k' c.Z c.g (e.symm Q).val.val (e.symm Q).val.property
  have hP'Q : P' = Q.val.val := (huniq Q.val.val hpoint).symm
  subst P'
  have hcompat := open_restriction_natural C (pullback f b) c.Z c'.Z c.i c'.i
    (pullback.fst f b) π (c.baseChange_i_fst b) φ φ' hφ hφ' Q.val.val ρ hρ
    (a : Γ(C, ⊤))
  simp only [Finsupp.subtypeDomain_apply, Finsupp.domCongr_apply,
    Finsupp.equivMapDomain_apply, Scheme.div_apply]
  change c'.Z.ord (φ' ((pullback.fst f b).appTop (a : Γ(C, ⊤)))) Q.val.val =
    c.Z.ord (φ (a : Γ(C, ⊤))) (e.symm Q).val.val
  rw [hcompat]
  exact hord (Units.map φ.toMonoidHom a)

end AlgebraicGeometry
