/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.HomComplexProjections
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.HomotopyCofiber
import Mathlib.Tactic.Abel

/-! # Differential compatibility of the internal Hom mapping-cone comparison

Source: Stacks Project, sites-cohomology.tex, Section 0A8X, the displayed Hom
differential, and Section 08J7, the proof of Lemma 21.35.4.
(blueprint: lem-sc-hom-complex-mapping-cone-differential).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

private lemma homObjMap_add_right
    {C : Type v} [SmallCategory C] {J : GrothendieckTopology C}
    {R : Sheaf J CommRingCat.{max u v}}
    {A A' B B' : SheafOfModules.{max u v}
      ((sheafCompose J (forget₂ CommRingCat RingCat.{max u v})).obj R)}
    (f : A' ⟶ A) (g h : B ⟶ B') :
    SheafOfModules.homObjMap (R := R) f (g + h) =
      SheafOfModules.homObjMap f g + SheafOfModules.homObjMap f h := by
  apply SheafOfModules.hom_ext
  ext X φ
  rfl

private lemma homObjMap_neg_right
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {R : Sheaf J CommRingCat.{u}}
    {A A' B B' : SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)}
    (f : A' ⟶ A) (g : B ⟶ B') :
    SheafOfModules.homObjMap (R := R) f (-g) =
      -SheafOfModules.homObjMap f g := by
  apply SheafOfModules.hom_ext
  ext X φ
  rfl

private lemma homObjMap_comp_id_right
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {R : Sheaf J CommRingCat.{u}}
    {A A' B B' : SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)}
    (f : A' ⟶ A) (g : B ⟶ B') :
    SheafOfModules.homObjMap (R := R) f (g ≫ 𝟙 B') =
      SheafOfModules.homObjMap f g := by
  rw [Category.comp_id]

private lemma cone_sum_identity {A : Type*} [AddCommGroup A] (a b c x y : A) :
    -a + b + c - (x + y) = -(a - -x) + (b + (c - y)) := by
  abel

-- Elaborating the dependent projection formulas unfolds the chosen Hom-complex objects.
-- Inferring the additive Hom types unfolds the chosen Hom-complex product objects.
set_option backward.isDefEq.respectTransparency true in
/-- A degreewise cone comparison with the specified product components is a chain map.
This assertion constructs no degreewise isomorphism.

Source: Stacks Project, sites-cohomology.tex, Section 0A8X, the displayed Hom
differential, and Section 08J7, the proof of Lemma 21.35.4.
(blueprint: lem-sc-hom-complex-mapping-cone-differential).

Proof: fix adjacent degrees `n` and `m = n+1`. Postcompose the proposed equality
with each product projection in degree `m`. The projections are jointly monic.
By the assumed component equation, this becomes an equality into the internal Hom
from `E^p` to `G^(p+m+1) ⊞ I^(p+m)`. Postcompose further with internal Hom of
the two cone projections. These are jointly monic: internal Hom preserves this
binary product, as is checked sectionwise on local linear maps. The first projection
of the degreewise comparison is the first cone projection followed by the degree
`n+1` Hom-product projection; the second is the second cone projection followed
by the degree `n` Hom-product projection. Expand the Hom differentials using
`homComplex_projections_exists`, and the cone differential using its two projection
formulas. The first component on either side is
`-d_G a + (-1)^(n+1) a d_E`; the second is
`f a + d_I b - (-1)^n b d_E`. The two expressions agree by
`(-1)^(n+1) = -(-1)^n` and associativity of local linear-map composition.
Composition distributes over addition, subtraction and the sign scalar.
Hence equality holds after both cone projections and all product projections,
which proves the chain-map equation. The argument applies to zero objects,
zero maps, empty sites and unbounded complexes, and requires no exactness of
infinite products. -/
theorem homComplex_mappingCone_differential
    {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{u})
    (E G I : CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ)
    (f : G ⟶ I) :
    let π := Classical.choose
      (homComplex_projections_exists.{u, u, u, u} (C := C) (J := J) (R := R))
    let hf := ((homComplexFunctor (R := R)).obj (op E)).map f
    let K := HomologicalComplex.homotopyCofiber hf
    let cf := HomologicalComplex.homotopyCofiber f
    let H := ((homComplexFunctor (R := R)).obj (op E)).obj cf
    ∀ (e : ∀ n : ℤ, K.X n ≅ H.X n),
      (∀ n p : ℤ, (e n).hom ≫ π E cf n p (p + n) rfl =
        (show K.X n ⟶ SheafOfModules.homObj (R := R) (E.X p) (cf.X (p + n)) from
        HomologicalComplex.homotopyCofiber.fstX hf n (n + 1) rfl ≫
          π E G (n + 1) p (p + (n + 1)) rfl ≫
          SheafOfModules.homObjMap (R := R) (𝟙 (E.X p))
            (HomologicalComplex.homotopyCofiber.inlX f (p + (n + 1)) (p + n)
              (by change (p + n) + 1 = p + (n + 1); omega)) +
        HomologicalComplex.homotopyCofiber.sndX hf n ≫ π E I n p (p + n) rfl ≫
          SheafOfModules.homObjMap (R := R) (𝟙 (E.X p))
            (HomologicalComplex.homotopyCofiber.inrX f (p + n)))) →
      ∀ n m : ℤ, n + 1 = m →
        (e n).hom ≫ H.d n m = K.d n m ≫ (e m).hom := by
  classical
  intro π hf K cf H e he n m hnm
  subst m
  have hπ := Classical.choose_spec
    (homComplex_projections_exists.{u, u, u, u} (C := C) (J := J) (R := R))
  let F := (homComplexFunctor (R := R)).obj (op E)
  let proj (T : CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ) (k p : ℤ) :=
    π E T k p (p + k) rfl
  have hd (T : CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ)
      (k p q p' : ℤ) (hq : p + (k + 1) = q) (hp' : p' + k = q) :
      (F.obj T).d k (k + 1) ≫ π E T (k + 1) p q hq =
        proj T k p ≫ SheafOfModules.homObjMap (R := R) (𝟙 (E.X p))
          (T.d (p + k) q) -
        k.negOnePow • (π E T k p' q hp' ≫
          SheafOfModules.homObjMap (R := R) (E.d p p') (𝟙 (T.X q))) := by
    exact hπ.2.1 E T k (k + 1) p q (p + k) p' rfl hq rfl hp'
  have hm (k p : ℤ) : (hf.f k) ≫ proj I k p =
      proj G k p ≫ SheafOfModules.homObjMap (R := R) (𝟙 (E.X p)) (f.f (p + k)) := by
    simpa only [op_id, Functor.map_id, NatTrans.id_app, Category.id_comp,
      HomologicalComplex.id_f] using hπ.2.2 E E G I (𝟙 E) f k p (p + k) rfl
  have hc (k p q q' : ℤ) (hq : p + k = q) (hq' : p + (k + 1) = q') :
      (e k).hom ≫ π E cf k p q hq =
        HomologicalComplex.homotopyCofiber.fstX hf k (k + 1) rfl ≫
          π E G (k + 1) p q' hq' ≫
          SheafOfModules.homObjMap (R := R) (𝟙 (E.X p))
            (HomologicalComplex.homotopyCofiber.inlX f q' q (by
              change q + 1 = q'; omega)) +
        HomologicalComplex.homotopyCofiber.sndX hf k ≫ π E I k p q hq ≫
          SheafOfModules.homObjMap (R := R) (𝟙 (E.X p))
            (HomologicalComplex.homotopyCofiber.inrX f q) := by
    subst q q'
    exact he k p
  apply Fan.IsLimit.hom_ext (Classical.choice (hπ.1 E cf (n + 1)))
  intro p
  change ((e n).hom ≫ H.d n (n + 1)) ≫ proj cf (n + 1) p =
    (K.d n (n + 1) ≫ (e (n + 1)).hom) ≫ proj cf (n + 1) p
  rw [Category.assoc, hd cf n p (p + (n + 1)) (p + 1) rfl (by omega),
    Preadditive.comp_sub, Linear.comp_units_smul]
  simp only [← Category.assoc]
  dsimp only [proj]
  simp only [hc n p (p + n) (p + (n + 1)) rfl rfl,
    hc n (p + 1) (p + (n + 1)) (p + ((n + 1) + 1)) (by omega) (by omega)]
  simp only [Category.assoc]
  simp only [hc (n + 1) p (p + (n + 1)) (p + ((n + 1) + 1)) rfl rfl,
    Preadditive.comp_add]
  simp only [Preadditive.add_comp, Category.assoc,
    SheafOfModules.homObjMap_comp_homObjMap, Category.comp_id]
  dsimp only [cf, K, HomologicalComplex.homotopyCofiber_d]
  simp only [HomologicalComplex.homotopyCofiber.inlX_d f (p + n)
      (p + (n + 1)) (p + ((n + 1) + 1)) (by change (p + n) + 1 = _; omega)
      (by change (p + (n + 1)) + 1 = _; omega),
    HomologicalComplex.homotopyCofiber.inrX_d,
    HomologicalComplex.homotopyCofiber.d_fstX_assoc hf n (n + 1) ((n + 1) + 1) rfl rfl,
    HomologicalComplex.homotopyCofiber.d_sndX_assoc hf n (n + 1) rfl,
    homObjMap_add_right (R := R), homObjMap_neg_right, Preadditive.comp_add,
    Preadditive.add_comp, Preadditive.neg_comp, Preadditive.comp_neg]
  dsimp only [proj] at hd hm
  have hg := congrArg (fun t ↦ t ≫ SheafOfModules.homObjMap (R := R) (𝟙 (E.X p))
    (HomologicalComplex.homotopyCofiber.inlX f (p + ((n + 1) + 1))
      (p + (n + 1)) (by change (p + (n + 1)) + 1 = _; omega)))
    (hd G (n + 1) p (p + ((n + 1) + 1)) (p + 1) rfl (by omega))
  have hi := congrArg (fun t ↦ t ≫ SheafOfModules.homObjMap (R := R) (𝟙 (E.X p))
    (HomologicalComplex.homotopyCofiber.inrX f (p + (n + 1))))
    (hd I n p (p + (n + 1)) (p + 1) rfl (by omega))
  have hmf := congrArg (fun t ↦ t ≫ SheafOfModules.homObjMap (R := R) (𝟙 (E.X p))
    (HomologicalComplex.homotopyCofiber.inrX f (p + (n + 1)))) (hm (n + 1) p)
  simp only [Preadditive.sub_comp, Linear.units_smul_comp, Category.assoc,
    SheafOfModules.homObjMap_comp_homObjMap, Category.id_comp] at hg hi hmf
  dsimp only [F] at hg hi
  simp only [Category.assoc, hg, hi, hmf, Preadditive.comp_sub,
    Linear.comp_units_smul, Preadditive.comp_neg,
    Int.negOnePow_succ, Units.neg_smul, smul_add]
  simp only [homObjMap_comp_id_right]
  exact cone_sum_identity _ _ _ _ _

end CategoryTheory
