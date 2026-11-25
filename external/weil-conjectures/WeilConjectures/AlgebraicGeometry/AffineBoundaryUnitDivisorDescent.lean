/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve.Divisor
public import WeilConjectures.AlgebraicGeometry.Curve.Compactification
import WeilConjectures.AlgebraicGeometry.BoundaryDivisorPicKernel
import WeilConjectures.AlgebraicGeometry.Picard.Degree
import WeilConjectures.AlgebraicGeometry.BaseChangeCurve
import WeilConjectures.AlgebraicGeometry.Curve.PicZeroTorsionBaseChange

/-! # Descent of principal boundary divisors

Source: blueprint proposition-cohomology-smooth-affine-curve, affine unit quotient paragraph.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- Every boundary divisor of a unit after extension descends to a boundary divisor of a unit.
Source: blueprint proposition-cohomology-smooth-affine-curve, affine unit quotient paragraph.
(blueprint: lem-sc-affine-boundary-unit-divisor-descent).

Proof: on each curve, boundary_divisor_pic_kernel identifies the boundary divisors of
units with the kernel of the point-ideal divisor-to-Picard homomorphism, after extending
coefficients by zero. Degree of an invertible module is preserved under field extension,
so a Picard class that becomes trivial has degree zero. Restrict Picard pullback to the
kernels of the two degree homomorphisms and apply picZero_torsion_base_change at n = 1
for injectivity; hence the original Picard class is trivial as well.
For each supplied boundary point, construct its rational point morphism and its scalar
extension. The fibre condition he identifies that extension with e(P). The resulting
cartesian square identifies the pullback of the point ideal with the ideal of e(P).
Pullback commutes with its dual, giving equality of the point classes. Induction on a
finitely supported boundary divisor proves compatibility of divisor-to-Picard with
Finsupp.domCongr e. Given a boundary divisor after extension, transport it back using
e.symm. Its class becomes trivial, hence is trivial by Picard injectivity. Apply the
kernel characterization on the original curve and transport forward again. This covers
empty and singleton boundaries without choosing a boundary base point. -/
theorem affine_boundary_unit_divisor_descent
    (k k' : Type u) [Field k] [IsAlgClosed k] [Field k'] [IsAlgClosed k'] [Algebra k k']
    (C : Scheme.{u}) (f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f] [IsAffine C]
    (c : Compactification f) [IsConnectedCurve c.g] [Smooth c.g]
    [IsIntegral c.Z] [IsNoetherian c.Z]
    [IsIntegral (c.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k k')))).Z]
    [IsNoetherian (c.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k k')))).Z] 
    (φ : Γ(C, ⊤) →+* c.Z.functionField)
      (φ' : Γ(CategoryTheory.Limits.pullback f
          (Spec.map (CommRingCat.ofHom (algebraMap k k'))), ⊤) →+*
        (c.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k k')))).Z.functionField)
    (e : {P : closedPoints c.Z // P.val ∉ Set.range c.i.base} ≃
        {P : closedPoints (c.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k k')))).Z //
          P.val ∉
            Set.range (c.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k k')))).i.base})
    (hφ : (∀ (x : C) (s : Γ(C, ⊤)) (y : c.Z.presheaf.stalk (c.i.base x)),
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
            y))
    (he : (∀ P : {P : closedPoints c.Z // P.val ∉ Set.range c.i.base},
        (CategoryTheory.Limits.pullback.fst c.g
            (Spec.map (CommRingCat.ofHom (algebraMap k k')))).base
            (e P).val.val = P.val.val ∧
          ∀ Q : (c.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k k')))).Z,
            (CategoryTheory.Limits.pullback.fst c.g
                (Spec.map (CommRingCat.ofHom (algebraMap k k')))).base Q =
              P.val.val → Q = (e P).val.val)) :
    Set.range (fun u' : Γ(CategoryTheory.Limits.pullback f
            (Spec.map (CommRingCat.ofHom (algebraMap k k'))), ⊤)ˣ ↦
          Finsupp.subtypeDomain
            (fun P : closedPoints (c.baseChange
                (Spec.map (CommRingCat.ofHom (algebraMap k k')))).Z ↦
              P.val ∉
                Set.range (c.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k k')))).i.base)
            ((c.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k k')))).Z.div
              (Additive.ofMul (Units.map φ'.toMonoidHom u')))) ⊆
      Finsupp.domCongr e ''
          Set.range (fun u : Γ(C, ⊤)ˣ ↦
            Finsupp.subtypeDomain (fun P : closedPoints c.Z ↦ P.val ∉ Set.range c.i.base)
              (c.Z.div (Additive.ofMul (Units.map φ.toMonoidHom u)))) := by
  classical
  let b := Spec.map (CommRingCat.ofHom (algebraMap k k'))
  let c' := c.baseChange b
  let π := pullback.fst c.g b
  let C' := pullback f b
  let f' : C' ⟶ Spec (.of k') := pullback.snd f b
  have : IsConnectedCurve f' := (baseChange_curve f).2.2.2.2.2 inferInstance
  have : Smooth f' := inferInstanceAs (Smooth (pullback.snd f b))
  have : IsConnectedCurve c'.g := (baseChange_curve c.g).2.2.2.2.2 inferInstance
  have : Smooth c'.g := inferInstanceAs (Smooth (pullback.snd c.g b))
  have : SmoothOfRelativeDimension 1 c.g :=
    (smoothOfRelativeDimension_iff_topologicalKrullDim_eq c.g 1).mpr
      (IsConnectedCurve.krullDim_eq_one (f := c.g))
  have : SmoothOfRelativeDimension 1 c'.g :=
    (smoothOfRelativeDimension_iff_topologicalKrullDim_eq c'.g 1).mpr
      (IsConnectedCurve.krullDim_eq_one (f := c'.g))
  let : c.Z.Over (Spec (.of k)) := ⟨c.g⟩
  let : c'.Z.Over (Spec (.of k')) := ⟨c'.g⟩
  have : SmoothOfRelativeDimension 1 (c.Z ↘ Spec (.of k)) := ‹_›
  have : SmoothOfRelativeDimension 1 (c'.Z ↘ Spec (.of k')) := ‹_›
  have : LocallyOfFiniteType (c.Z ↘ Spec (.of k)) := inferInstanceAs (LocallyOfFiniteType c.g)
  have : LocallyOfFiniteType (c'.Z ↘ Spec (.of k')) := inferInstanceAs (LocallyOfFiniteType c'.g)
  have := c.isProper
  have := c'.isProper
  have : IsProper (c.Z ↘ Spec (.of k)) := c.isProper
  have : IsProper (c'.Z ↘ Spec (.of k')) := c'.isProper
  let B := {P : closedPoints c.Z // P.val ∉ Set.range c.i.base}
  let B' := {P : closedPoints c'.Z // P.val ∉ Set.range c'.i.base}
  let p := Scheme.Pic.mapHom π
  -- Picard pullback is injective: degree is preserved and Pic⁰ pullback is injective.
  have hdegree (L : c.Z.Pic) : c'.g.picDegree (p L) = c.g.picDegree L := by
    let : (pullback c.g b).Over (Spec (.of k')) := ⟨pullback.snd c.g b⟩
    let M := (fromSkeleton c.Z.Modules).obj L.val
    have : SheafOfModules.IsInvertible.{u, u, u} M := L.isInvertible
    have : Scheme.Modules.IsInvertible M := Scheme.Modules.IsInvertible.of_sheafOfModules M
    change Scheme.Modules.degree k'
      ((fromSkeleton c'.Z.Modules).obj (toSkeleton
        ((Scheme.Modules.pullback π).obj M))) = Scheme.Modules.degree k M
    rw [Scheme.Modules.degree_congr k' (fromSkeletonToSkeletonIso _)]
    exact Scheme.Modules.degree_pullback_of_isPullback b π
      (IsPullback.of_hasPullback c.g b) M
  let d := Scheme.picDegreeHom k c.Z
  let d' := Scheme.picDegreeHom k' c'.Z
  have hd (L : c.Z.Pic) : d' (p L) = d L := congrArg Multiplicative.ofAdd (hdegree L)
  let G := d.ker
  let G' := d'.ker
  let j : G →* G' := {
    toFun L := ⟨p L.val, by
      change d' (p L.val) = 1
      rw [hd]
      exact L.property⟩
    map_one' := Subtype.ext (map_one p)
    map_mul' L M := Subtype.ext (map_mul p L.val M.val) }
  have hj : Function.Injective j :=
    (picZero_torsion_base_change c.g G Scheme.coe_ker_picDegreeHom G'
      Scheme.coe_ker_picDegreeHom j (fun _ ↦ rfl) 1 (by simp)).1
  have hker (L : c.Z.Pic) (hL : p L = 1) : L = 1 := by
    have hmem : L ∈ G := by
      change d L = 1
      rw [← hd, hL, map_one]
    have hsub : j ⟨L, hmem⟩ = j 1 := by
      apply Subtype.ext
      change p L = p 1
      rw [hL, map_one]
    exact congrArg (fun x : G ↦ x.val) (hj hsub)
  -- The supplied fibre condition identifies pullback of each boundary point ideal.
  have hpoint (P : B) : p (Scheme.Pic.ofClosedPoint k P.val) =
      Scheme.Pic.ofClosedPoint k' (e P).val := by
    let x : c.g.fieldPoints k := ⟨pointOfClosedPoint c.g P.val.val P.val.property, by
      simp [pointOfClosedPoint_comp]⟩
    let y := c.g.baseChangeFieldPoint k' x
    have hyP : y.val.base default = (e P).val.val := by
      apply c.g.baseChangeFieldPoint_eq_of_fst_eq k' x
      exact (he P).1.trans
        (pointOfClosedPoint_apply c.g P.val.val P.val.property default).symm
    have hx : x.val ≫ c.g = 𝟙 _ :=
      pointOfClosedPoint_comp c.g P.val.val P.val.property
    have hyx : y.val ≫ π = b ≫ x.val := pullback.lift_fst _ _ _
    have hyg : y.val ≫ c'.g = 𝟙 _ := pullback.lift_snd _ _ _
    have hsquare : IsPullback b y.val x.val π := by
      apply IsPullback.of_bot (v₂₁ := c'.g) (v₂₂ := c.g) _ hyx.symm
        (IsPullback.of_hasPullback c.g b)
      rw [hx, hyg]
      exact IsPullback.of_id_snd
    let I := Scheme.IdealSheafData.vanishingIdeal ⟨{P.val.val}, P.val.property⟩
    let J := Scheme.IdealSheafData.vanishingIdeal ⟨{(e P).val.val}, (e P).val.property⟩
    have hxker : x.val.ker = I := Scheme.ker_pointOfClosedPoint P.val
    have hyker : y.val.ker = J := by
      rw [← Scheme.IdealSheafData.map_bot, ← Scheme.nilradical_eq_bot,
        ← Scheme.IdealSheafData.vanishingIdeal_top,
        Scheme.IdealSheafData.map_vanishingIdeal]
      apply congrArg Scheme.IdealSheafData.vanishingIdeal
      apply SetLike.coe_injective
      change closure (y.val.base '' Set.univ) = {(e P).val.val}
      rw [Set.image_univ, Set.range_eq_singleton_iff.mpr
        (fun a ↦ (congrArg y.val.base (Subsingleton.elim a default)).trans hyP),
        (e P).val.property.closure_eq]
    have hcomap : I.comap π = J := by
      rw [← hxker, ← x.val.ker_of_isPullback π hsquare, hyker]
    have hI : I.IsInvertible :=
      isInvertible_vanishingIdeal_of_smoothOfRelativeDimension_one c.g P.val.property
    have hJ : J.IsInvertible :=
      isInvertible_vanishingIdeal_of_smoothOfRelativeDimension_one c'.g (e P).val.property
    have hI' : (I.comap π).IsInvertible := by rw [hcomap]; exact hJ
    have : (Scheme.Modules.dual I.toModules).IsInvertible := hI.isInvertible_dual_toModules
    have : (Scheme.Modules.dual J.toModules).IsInvertible := hJ.isInvertible_dual_toModules
    obtain ⟨t⟩ := hI.nonempty_pullback_dual_toModules_iso π hI'
    have t' : Scheme.Modules.dual (I.comap π).toModules ≅ Scheme.Modules.dual J.toModules :=
      eqToIso (congrArg (fun K ↦ Scheme.Modules.dual K.toModules) hcomap)
    change Scheme.Pic.mapHom π (Scheme.Pic.ofIsInvertible (Scheme.Modules.dual I.toModules)) =
      Scheme.Pic.ofIsInvertible (Scheme.Modules.dual J.toModules)
    apply Scheme.Pic.eq_iff_nonempty_iso.2
    exact ⟨fromSkeletonToSkeletonIso _ ≪≫
      (Scheme.Modules.pullback π).mapIso
        (Scheme.Pic.ofIsInvertibleIso (Scheme.Modules.dual I.toModules)) ≪≫ t ≪≫ t' ≪≫
      (Scheme.Pic.ofIsInvertibleIso (Scheme.Modules.dual J.toModules)).symm⟩
  let t := Scheme.Divisor.toPic k c.Z
  let t' := Scheme.Divisor.toPic k' c'.Z
  have htransport (D : B →₀ ℤ) :
      p (t (Finsupp.embDomain (.subtype _) D)).toMul =
        (t' (Finsupp.embDomain (.subtype _) (Finsupp.domCongr e D))).toMul := by
    induction D using Finsupp.induction with
    | zero => simp
    | single_add P n D _ _ ih =>
      simp only [Finsupp.embDomain_add, map_add, toMul_add, map_mul]
      rw [ih]
      congr 1
      change p (t (Finsupp.embDomain (.subtype _) (Finsupp.single P n))).toMul =
        (t' (Finsupp.embDomain (.subtype _)
          (Finsupp.equivMapDomain e (Finsupp.single P n)))).toMul
      simp only [t, t', Finsupp.embDomain_single, Finsupp.equivMapDomain_single,
        Scheme.Divisor.toPic_single, toMul_zsmul, toMul_ofMul, map_zpow]
      exact congrArg (fun L ↦ L ^ n) (hpoint P)
  have hK := boundary_divisor_pic_kernel k C f c φ hφ.1
  have hK' := boundary_divisor_pic_kernel k' C' f' c' φ' hφ.2
  rintro D hD
  let E : B →₀ ℤ := Finsupp.domCongr e.symm D
  have hE : Finsupp.domCongr e E = D := (Finsupp.domCongr e).apply_symm_apply D
  have hzero : (t' (Finsupp.embDomain (.subtype _) D)).toMul = 1 := by
    rw [hK'] at hD
    exact hD
  have hbefore : (t (Finsupp.embDomain (.subtype _) E)).toMul = 1 := by
    apply hker
    rw [htransport, hE, hzero]
  refine ⟨E, ?_, hE⟩
  rw [hK]
  exact hbefore

end AlgebraicGeometry
