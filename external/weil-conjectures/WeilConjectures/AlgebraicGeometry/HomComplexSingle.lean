/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.HomComplex
public import WeilConjectures.AlgebraicGeometry.DerivedCategory
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHomFree

/-!
# Internal Hom complexes from a sheaf in degree zero

Source: Stacks Project, sites-cohomology.tex, Section 0A8X, the Hom-complex formula.
(blueprint: lem-sc-hom-complex-single).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

/-- Postcomposition of localized linear maps is additive.
Source: Stacks Project, sites-cohomology.tex, Section 0A8X.
(blueprint: lem-sc-hom-complex-single). -/
instance sheafHomFunctor_additive (Y : Scheme.{u})
    (P : SheafOfModules.{u} (moduleRings Y.toRingedSpace)) :
    ((SheafOfModules.homFunctor Y.toRingedSpace.sheaf).obj (op P)).Additive where
  map_add := by
    intro K L f g
    apply SheafOfModules.hom_ext
    ext X φ
    rfl

private noncomputable def soleFactorIso {B : Type u} [Category B] [HasZeroMorphisms B]
    {f : ℤ → B} (c : Fan f) (hc : IsLimit c) (i : ℤ)
    (hz : ∀ j, j ≠ i → IsZero (f j)) : c.pt ≅ f i where
  hom := c.proj i
  inv := hc.lift (Fan.mk (f i) (fun j ↦ if h : j = i then eqToHom (congrArg f h.symm) else 0))
  hom_inv_id := by
    apply hc.hom_ext
    rintro ⟨j⟩
    rw [Category.assoc, hc.fac]
    by_cases h : j = i
    · subst j
      simp
      rfl
    · exact (hz j h).eq_of_tgt _ _
  inv_hom_id := by
    change hc.lift (Fan.mk (f i)
      (fun j ↦ if h : j = i then eqToHom (congrArg f h.symm) else 0)) ≫
      c.π.app (Discrete.mk i) = 𝟙 (f i)
    rw [hc.fac]
    simp

set_option backward.isDefEq.respectTransparency false in
/-- Hom from a sheaf placed in degree zero is isomorphic to the complex obtained by
applying ordinary internal sheaf Hom degreewise. No exactness or local freeness
assumption is needed, and the coefficient complex can be unbounded.

Source: Stacks Project, sites-cohomology.tex, Section 0A8X, the product and
map formulas defining the Hom complex.
(blueprint: lem-sc-hom-complex-single).

Proof:
1. In degree `n`, the product defining the Hom complex from `P[0]` has factors
   `Hom(P[0]^p,K^(p+n))`. For `p ≠ 0` its source is zero, so the factor is
   zero: on each localized site there is exactly one linear map from zero.
   The factor `p = 0` is `Hom(P,K^n)`, using the single-complex identification
   `P[0]^0 ≅ P` and `0+n=n`.
2. Project to this sole surviving factor. The inverse is the product lift with
   that component the inverse identification and every other component zero.
   The product uniqueness principle proves both inverse identities, including
   when `P` or `K^n` is zero and on the empty scheme.
3. The Hom-complex differential is `d_K f - (-1)^n f d_P`. Since the single
   complex has zero differential, the second term is zero and projection
   intertwines the first term with postcomposition by `d_K`. These degreewise
   isomorphisms and their inverses therefore form chain maps.
4. Postcomposition is additive on localized linear maps, as established by the
   instance above. This supplies the additive structure used to apply sheaf
   Hom degreewise. No exactness of infinite products is used: only one factor
   survives in each degree. -/
theorem homComplex_single_iso
    (Y : Scheme.{u})
    (P : SheafOfModules.{u} (moduleRings Y.toRingedSpace))
    (K : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ) :
    Nonempty
      (homComplex (R := Y.toRingedSpace.sheaf)
        ((CochainComplex.singleFunctor
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj P) K ≅
        (((SheafOfModules.homFunctor Y.toRingedSpace.sheaf).obj (op P)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K) := by
  classical
  let hs := Classical.choose_spec
    (homComplex_exists (C := Opens Y) (J := Opens.grothendieckTopology Y)
      (R := Y.toRingedSpace.sheaf))
  let π := Classical.choose hs
  have hh := Classical.choose_spec hs
  let A := SheafOfModules.{u} (moduleRings Y.toRingedSpace)
  let Pc := (CochainComplex.singleFunctor A 0).obj P
  let T := (SheafOfModules.homFunctor Y.toRingedSpace.sheaf).obj (op P)
  let proj (K : CochainComplex A ℤ) (n : ℤ) := π Pc K n 0 n (zero_add n)
  have hz (K : CochainComplex A ℤ) (n p : ℤ) (hp : p ≠ 0) :
      IsZero (SheafOfModules.homObj (R := Y.sheaf) (Pc.X p) (K.X (p+n))) := by
    let F := (SheafOfModules.homFunctor Y.sheaf).flip.obj (K.X (p+n))
    exact F.map_isZero
      (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 P p hp).op
  have hpi (K : CochainComplex A ℤ) (n q : ℤ) (hq : 0+n=q) :
      IsIso (π Pc K n 0 q hq) := by
    subst q
    let c := Fan.mk ((homComplex (R := Y.sheaf) Pc K).X n)
      (fun p : ℤ ↦ π Pc K n p (p+n) rfl)
    let hc : IsLimit c := (hh.1 Pc K n).some
    have he := (soleFactorIso c hc 0 (hz K n)).isIso_hom
    change IsIso (π Pc K n 0 (0+n) rfl) at he
    exact he
  have hp (K : CochainComplex A ℤ) (n : ℤ) : IsIso (proj K n) :=
    hpi K n n (zero_add n)
  let e (K : CochainComplex A ℤ) (n : ℤ) := asIso (proj K n)
  let ec (K : CochainComplex A ℤ) : homComplex (R := Y.sheaf) Pc K ≅
      (T.mapHomologicalComplex (ComplexShape.up ℤ)).obj K :=
    HomologicalComplex.Hom.isoOfComponents (e K) (by
      intro n m hnm
      symm
      change (homComplex (R := Y.sheaf) Pc K).d n m ≫ proj K m =
        proj K n ≫ T.map (K.d n m)
      have hd := hh.2.1 Pc K n m 0 m n 1 hnm (zero_add m) (zero_add n)
        ((add_comm 1 n).trans hnm)
      have hzero : SheafOfModules.homObjMap (R := Y.sheaf)
          (Pc.d 0 1) (𝟙 (K.X m)) = 0 := by
        change ((SheafOfModules.homFunctor Y.sheaf).flip.obj (K.X m)).map
          (Pc.d 0 1).op = 0
        rw [show Pc.d 0 1 = 0 from rfl, op_zero]
        exact Functor.map_zero
          ((SheafOfModules.homFunctor Y.sheaf).flip.obj (K.X m)) _ _
      simp only [hzero, comp_zero, smul_zero, sub_zero] at hd
      exact hd)
  exact ⟨ec K⟩

end AlgebraicGeometry
