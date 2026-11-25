/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve.EtaleAdditiveCechNormalization

/-! # Coefficient augmentation preserves closed elements
Source: Stacks Project, Tag 01EQ, Lemma 20.11.2. -/

@[expose] public section



universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry.Scheme.Modules
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The horizontal part of the total differential kills the coefficient augmentation.
Source: Stacks Project, Tag 01EQ, Lemma 20.11.2, augmentation beta.
(blueprint: lem-pbc-etale-additive-cech-beta-closed)

Proof: Test the horizontal differential on each tuple projection. Its alternating
sum restricts each face coordinate. Naturality of restrictFunctorΓ.inv identifies
restriction of a structural section with the section on the smaller open subscheme.
Naturality of I.ι.f 0 moves that restriction past the resolution augmentation.
Additivity distributes the augmentation and universe lift across the finite
alternating sum. Thus the horizontal differential equals the coefficient map
applied to the differential of the included cycle, which is zero by iCycles_d.
The total inclusion preserves zero. No covering condition is used; empty products
and repeated or empty intersections obey the same naturality calculation. -/
private theorem etaleAdditiveCech_beta_horizontal
    {X : Scheme.{u}} {ι : Type u} [Finite ι] (U : ι → X.Opens)
    (I : InjectiveResolution X.etaleAdditiveSheaf) (n : ℕ)
    (z : (cechOver X.toSpecΓ U (SheafOfModules.unit X.ringCatSheaf)).cycles n) :
    (etaleOpenCechResolutionDoubleComplex X (additiveCechOpenInclusion X) U I).D₁
      (.up ℕ) n (n + 1) (additiveCechBeta U I n
        ((cechOver X.toSpecΓ U
          (SheafOfModules.unit X.ringCatSheaf)).iCycles n z)) = 0 := by
  let P := presheafOver X.toSpecΓ (SheafOfModules.unit X.ringCatSheaf)
  let C := (cechComplexFunctor U).obj P
  let Q := X.presheaf ⋙ etaleAdditiveCoefficients
  let H := (cechComplexFunctor U).obj Q
  let J := (cechComplexFunctor U).obj
    ((additiveCechOpenInclusion X).op ⋙ (I.cocomplex.X 0).obj)
  let τ : Q ⟶ (additiveCechOpenInclusion X).op ⋙ (I.cocomplex.X 0).obj :=
    Functor.whiskerRight X.restrictFunctorΓ.inv etaleAdditiveCoefficients ≫
      Functor.whiskerLeft (additiveCechOpenInclusion X).op (I.ι.f 0).hom
  let j (k : ℕ) : AddCommGrpCat.of (ULift.{u + 1} (C.X k)) ⟶ H.X k :=
    Limits.Pi.lift fun y : Fin (k + 1) → ι ↦ AddCommGrpCat.ofHom
      { toFun := fun a ↦ ULift.up (TopCat.Presheaf.cechComplexFunctorπ U P k y a.down)
        map_zero' := by apply ULift.ext; exact map_zero _
        map_add' := by intro a b; apply ULift.ext; exact map_add _ _ _ }
  have hj (k : ℕ) (a : C.X k) (y : Fin (k + 1) → ι) :
      TopCat.Presheaf.cechComplexFunctorπ U Q k y ((j k).hom (ULift.up a)) =
        ULift.up (TopCat.Presheaf.cechComplexFunctorπ U P k y a) := by
    change ((j k ≫ TopCat.Presheaf.cechComplexFunctorπ U Q k y).hom) (ULift.up a) = _
    rw [show j k ≫ TopCat.Presheaf.cechComplexFunctorπ U Q k y = _ from
      Limits.Pi.lift_comp_π _ y]
    rfl
  have hc (k : ℕ) (a : C.X k) :
      (H.d k (k + 1)).hom ((j k).hom (ULift.up a)) =
        (j (k + 1)).hom (ULift.up (C.d k (k + 1) a)) := by
    have hcoord (y : Fin (k + 2) → ι) :
        TopCat.Presheaf.cechComplexFunctorπ U Q (k + 1) y
          ((H.d k (k + 1)).hom ((j k).hom (ULift.up a))) =
        TopCat.Presheaf.cechComplexFunctorπ U Q (k + 1) y
          ((j (k + 1)).hom (ULift.up (C.d k (k + 1) a))) := by
      rw [hj]
      rw [← ConcreteCategory.comp_apply, TopCat.Presheaf.cechComplexFunctor_d_π]
      rw [AddCommGrpCat.sum_apply]
      change (∑ i : Fin (k + 2), (( (-1 : ℤ) ^ (i : ℕ) •
        (TopCat.Presheaf.cechComplexFunctorπ U Q k (y ∘ i.succAbove) ≫
          Q.map (Limits.Pi.lift fun l ↦ Limits.Pi.π (fun l ↦ U (y l)) (i.succAbove l)).op)).hom)
            ((j k).hom (ULift.up a))) = _
      simp only [AddCommGrpCat.hom_zsmul, AddMonoidHom.smul_apply,
        AddCommGrpCat.hom_comp, AddMonoidHom.comp_apply]
      change (∑ i : Fin (k + 2), (-1 : ℤ) ^ (i : ℕ) •
        Q.map (Limits.Pi.lift fun l ↦ Limits.Pi.π (fun l ↦ U (y l)) (i.succAbove l)).op
          (TopCat.Presheaf.cechComplexFunctorπ U Q k (y ∘ i.succAbove)
            ((j k).hom (ULift.up a)))) = _
      rw [show TopCat.Presheaf.cechComplexFunctorπ U P (k + 1) y
          (C.d k (k + 1) a) = _ from
        TopCat.Presheaf.cechComplexFunctorπ_d_apply U P k y a]
      simp only [hj]
      change (∑ i : Fin (k + 2), (-1 : ℤ) ^ (i : ℕ) • ULift.up
        (P.map (Limits.Pi.lift fun l ↦ Limits.Pi.π (fun l ↦ U (y l)) (i.succAbove l)).op
          (TopCat.Presheaf.cechComplexFunctorπ U P k (y ∘ i.succAbove) a))) = _
      apply ULift.ext
      change (AddEquiv.ulift (∑ i : Fin (k + 2), (-1 : ℤ) ^ (i : ℕ) • ULift.up
        (P.map (Limits.Pi.lift fun l ↦ Limits.Pi.π (fun l ↦ U (y l)) (i.succAbove l)).op
          (TopCat.Presheaf.cechComplexFunctorπ U P k (y ∘ i.succAbove) a)))) = _
      rw [map_sum]
      simp only [map_zsmul]
      rfl
    apply Limits.Concrete.limit_ext (Discrete.functor
      (fun y : Fin (k + 2) → ι ↦ Q.obj (op (∏ᶜ fun l ↦ U (y l)))))
    intro y
    exact hcoord y.as
  let f := (cechComplexFunctor U).map τ
  let b : AddCommGrpCat.of
      (ULift.{u + 1} ((cechOver X.toSpecΓ U (SheafOfModules.unit X.ringCatSheaf)).X n)) ⟶
      ((cechComplexFunctor U).obj
        ((additiveCechOpenInclusion X).op ⋙ (I.cocomplex.X 0).obj)).X n :=
    Limits.Pi.lift (fun y : Fin (n + 1) → ι ↦ AddCommGrpCat.ofHom
      { toFun := fun x ↦ (I.ι.f 0).hom.app
          (op ((additiveCechOpenInclusion X).obj (∏ᶜ fun l ↦ U (y l))))
          (ULift.up ((X.restrictFunctorΓ.inv.app (op (∏ᶜ fun l ↦ U (y l)))).hom
            (TopCat.Presheaf.cechComplexFunctorπ U
              (presheafOver X.toSpecΓ (SheafOfModules.unit X.ringCatSheaf)) n y x.down)))
        map_zero' := by
          simp only [ULift.zero_down, map_zero]
          change ((I.ι.f 0).hom.app _) 0 = 0
          exact map_zero _
        map_add' := by
          intro x y
          simp only [ULift.add_down, map_add]
          change ((I.ι.f 0).hom.app _) (_ + _) = _
          exact map_add _ _ _ })
  have hb : b = j n ≫ f.f n := by
    apply Limits.Pi.hom_ext
    intro y
    change b ≫ TopCat.Presheaf.cechComplexFunctorπ U _ n y =
      j n ≫ f.f n ≫ TopCat.Presheaf.cechComplexFunctorπ U _ n y
    rw [TopCat.Presheaf.cechComplexFunctor_map_f_π]
    rw [show b ≫ TopCat.Presheaf.cechComplexFunctorπ U _ n y = _ from
      Limits.Pi.lift_comp_π _ y, ← Category.assoc]
    change _ = (j n ≫ TopCat.Presheaf.cechComplexFunctorπ U Q n y) ≫ τ.app _
    rw [show j n ≫ TopCat.Presheaf.cechComplexFunctorπ U Q n y = _ from
      Limits.Pi.lift_comp_π _ y]
    apply AddCommGrpCat.ext
    intro a
    rfl
  let x := C.iCycles n z
  have hx : C.d n (n + 1) x = 0 := ConcreteCategory.congr_hom (C.iCycles_d n (n + 1)) z
  have hz : (H.d n (n + 1)).hom ((j n).hom (ULift.up x)) = 0 := by
    rw [hc, hx]
    exact (j (n + 1)).hom.map_zero
  have hf := congrArg (fun g ↦ g.hom ((j n).hom (ULift.up x))) (f.comm n (n + 1))
  have hbz : (J.d n (n + 1)).hom (b.hom (ULift.up x)) = 0 := by
    rw [hb, AddCommGrpCat.hom_comp, AddMonoidHom.comp_apply]
    change (J.d n (n + 1)).hom ((f.f n).hom ((j n).hom (ULift.up x))) =
      (f.f (n + 1)).hom ((H.d n (n + 1)).hom ((j n).hom (ULift.up x))) at hf
    rw [hz, map_zero] at hf
    exact hf
  let K := etaleOpenCechResolutionDoubleComplex X (additiveCechOpenInclusion X) U I
  have hd := congrArg (fun g ↦ g.hom (b.hom (ULift.up x)))
    (K.ι_D₁ (.up ℕ) n (n + 1) n 0 (by simp))
  rw [HomologicalComplex₂.d₁_eq K (.up ℕ) (i₁' := n + 1) (by simp)
    0 (n + 1) (by simp)] at hd
  change ((K.d n (n + 1)).f 0).hom (b.hom (ULift.up x)) = 0 at hbz
  change (K.D₁ (.up ℕ) n (n + 1)).hom
    ((K.ιTotal (.up ℕ) n 0 n (by simp)).hom (b.hom (ULift.up x))) = 0
  have hs : ComplexShape.ε₁ (.up ℕ) (.up ℕ) (.up ℕ) (n, 0) = 1 := rfl
  rw [hs, one_smul] at hd
  simp only [AddCommGrpCat.hom_comp, AddMonoidHom.comp_apply, hbz, map_zero] at hd
  exact hd


/-- The vertical part of the total differential kills the coefficient augmentation.
Source: Stacks Project, Tag 01EQ, Lemma 20.11.2, augmentation beta.
(blueprint: lem-pbc-etale-additive-cech-beta-closed)

Proof: Use ι_D₂ and d₂_eq to express the composite with the vertical total
differential as the signed inclusion of the resolution differential. Test the
Čech product on tuple projections. Its coordinate is the structural section,
lifted by ULift, mapped first by I.ι.f 0 and then by I.cocomplex.d 0 1.
The composite is zero by I.ι_f_zero_comp_complex_d, evaluated at the open
subscheme. Every projection is zero, so product extensionality gives zero.
The signed total inclusion sends zero to zero. This holds for arbitrary cochains,
including degree zero, empty index families, and empty or repeated intersections. -/
private theorem etaleAdditiveCech_beta_vertical
    {X : Scheme.{u}} {ι : Type u} [Finite ι] (U : ι → X.Opens)
    (I : InjectiveResolution X.etaleAdditiveSheaf) (n : ℕ)
    (x : (cechOver X.toSpecΓ U (SheafOfModules.unit X.ringCatSheaf)).X n) :
    (etaleOpenCechResolutionDoubleComplex X (additiveCechOpenInclusion X) U I).D₂
      (.up ℕ) n (n + 1) (additiveCechBeta U I n
        x) = 0 := by
  let K := etaleOpenCechResolutionDoubleComplex X (additiveCechOpenInclusion X) U I
  let b : AddCommGrpCat.of
      (ULift.{u + 1} ((cechOver X.toSpecΓ U (SheafOfModules.unit X.ringCatSheaf)).X n)) ⟶
      (K.X n).X 0 :=
    Limits.Pi.lift (fun y : Fin (n + 1) → ι ↦ AddCommGrpCat.ofHom
      { toFun := fun x ↦ (I.ι.f 0).hom.app
          (op ((additiveCechOpenInclusion X).obj (∏ᶜ fun l ↦ U (y l))))
          (ULift.up ((X.restrictFunctorΓ.inv.app (op (∏ᶜ fun l ↦ U (y l)))).hom
            (TopCat.Presheaf.cechComplexFunctorπ U
              (presheafOver X.toSpecΓ (SheafOfModules.unit X.ringCatSheaf)) n y x.down)))
        map_zero' := by
          simp only [ULift.zero_down, map_zero]
          change ((I.ι.f 0).hom.app _) 0 = 0
          exact map_zero _
        map_add' := by
          intro x y
          simp only [ULift.add_down, map_add]
          change ((I.ι.f 0).hom.app _) (_ + _) = _
          exact map_add _ _ _ })
  have hb : b ≫ (K.X n).d 0 1 = 0 := by
    apply Limits.Pi.hom_ext
    intro y
    change b ≫ Limits.Pi.map (fun y : Fin (n + 1) → ι ↦
      (I.cocomplex.d 0 1).hom.app
        (op ((additiveCechOpenInclusion X).obj (∏ᶜ fun l ↦ U (y l))))) ≫
          Limits.Pi.π _ y = _
    rw [Limits.Pi.map_π, ← Category.assoc]
    dsimp only [b]
    rw [Limits.Pi.lift_comp_π, Limits.zero_comp]
    apply AddCommGrpCat.ext
    intro a
    let W := op ((additiveCechOpenInclusion X).obj (∏ᶜ fun l ↦ U (y l)))
    have hi : (I.ι.f 0).hom.app W ≫ (I.cocomplex.d 0 1).hom.app W = 0 :=
      congrArg (fun f ↦ f.hom.app W) I.ι_f_zero_comp_complex_d
    change (((I.ι.f 0).hom.app W ≫ (I.cocomplex.d 0 1).hom.app W).hom)
      (ULift.up ((X.restrictFunctorΓ.inv.app (op (∏ᶜ fun l ↦ U (y l)))).hom
        (TopCat.Presheaf.cechComplexFunctorπ U
          (presheafOver X.toSpecΓ (SheafOfModules.unit X.ringCatSheaf)) n y
          a.down))) = 0
    rw [hi]
    rfl
  have ht : b ≫ K.ιTotal (.up ℕ) n 0 n (by simp) ≫ K.D₂ (.up ℕ) n (n + 1) = 0 := by
    rw [HomologicalComplex₂.ι_D₂,
      HomologicalComplex₂.d₂_eq K (.up ℕ) n (i₂' := 1) (by simp) (n + 1) (by simp)]
    rw [Linear.comp_units_smul, ← Category.assoc, hb, Limits.zero_comp, smul_zero]
  change ((b ≫ K.ιTotal (.up ℕ) n 0 n (by simp) ≫ K.D₂ (.up ℕ) n (n + 1)).hom)
    (ULift.up x) = 0
  rw [ht]
  rfl



/-- The coefficient augmentation sends cycles to elements killed by the total differential.
Source: Stacks Project, Tag 01EQ, Lemma 20.11.2, augmentation beta.
(blueprint: lem-pbc-etale-additive-cech-beta-closed)

Proof: Identify the unit module on each finite open intersection with its additive
structural sections using restrictFunctorGamma and lift by ULift. Naturality of
this identification and of the resolution augmentation identifies the horizontal
differential of beta(z) with beta of the coefficient differential of z, hence zero.
The vertical differential is zero because the resolution augmentation is killed
by its first differential. The total differential is the sum of these two
components, with the standard sign on the vertical component, so it vanishes.
The argument applies in degree zero and to empty or repeated intersections; it
does not require a covering or an affine acyclicity hypothesis. -/
theorem etaleAdditiveCech_beta_closed
    {X : Scheme.{u}} {ι : Type u} [Finite ι] (U : ι → X.Opens)
    (I : InjectiveResolution X.etaleAdditiveSheaf) (n : ℕ)
    (z : (cechOver X.toSpecΓ U (SheafOfModules.unit X.ringCatSheaf)).cycles n) :
    (additiveCechTotal U I).d n (n + 1)
      (additiveCechBeta U I n
        ((cechOver X.toSpecΓ U
          (SheafOfModules.unit X.ringCatSheaf)).iCycles n z)) = 0 := by
  let K := etaleOpenCechResolutionDoubleComplex X (additiveCechOpenInclusion X) U I
  let x := (cechOver X.toSpecΓ U (SheafOfModules.unit X.ringCatSheaf)).iCycles n z
  change ((K.D₁ (.up ℕ) n (n + 1) + K.D₂ (.up ℕ) n (n + 1)).hom)
    (additiveCechBeta U I n x) = 0
  rw [AddCommGrpCat.hom_add, AddMonoidHom.add_apply]
  exact (congrArg₂ (· + ·) (etaleAdditiveCech_beta_horizontal U I n z)
    (etaleAdditiveCech_beta_vertical U I n x)).trans (zero_add 0)

end AlgebraicGeometry.Scheme.Modules
