/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.HomComplex
public import Mathlib.Algebra.Homology.TotalComplex
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.Algebra.Homology.HomComplexProjections

/-! # Comparison of the Hom complex with an opposite total complex

Source: Stacks Project, sites-cohomology.tex, Section 0A8X, product Hom differential;
cohomology.tex, Tags 0GM7 and 0GM8, finite-diagonal Hom calculation.
(blueprint: lem-sc-hom-complex-dual-total-comparison) -/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace CochainComplex

private lemma homComplex_dual_total_degree_isos
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {R : Sheaf J CommRingCat.{w}}
    (E A : CochainComplex (SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) ℤ)
    (K : HomologicalComplex₂ (SheafOfModules.{max u v w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R))ᵒᵖ
        (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [K.HasTotal (ComplexShape.up ℤ)]
    (e : ∀ p q : ℤ, (K.X p).X q ≅ op (SheafOfModules.homObj (E.X p) (A.X (-q))))
    (π : ∀ n p q : ℤ, p + n = q →
      ((CategoryTheory.homComplex E A).X n ⟶ SheafOfModules.homObj (E.X p) (A.X q)))
    (hπ : ∀ n : ℤ, Nonempty (IsLimit (Fan.mk ((CategoryTheory.homComplex E A).X n)
      (fun p : ℤ ↦ π n p (p + n) rfl)))) :
    ∃ φ : ∀ n : ℤ, (CategoryTheory.homComplex E A).X n ≅
        unop ((K.total (ComplexShape.up ℤ)).X (-n)),
      ∀ n p q : ℤ, ∀ h : p + q = -n,
        (φ n).hom ≫ (K.ιTotal (ComplexShape.up ℤ) p q (-n) h).unop =
          (p * n + p * (p + 1) / 2).negOnePow •
            (π n p (-q) (by omega) ≫ (e p q).hom.unop) := by
  classical
  let H := CategoryTheory.homComplex E A
  let σ (n p : ℤ) := (p * n + p * (p + 1) / 2).negOnePow
  let f (n : ℤ) : H.X n ⟶ unop ((K.total (ComplexShape.up ℤ)).X (-n)) :=
    (K.totalDesc (fun p q h ↦ (e p q).hom ≫
      (σ n p • π n p (-q) (by change p + q = -n at h; omega)).op)).unop
  have hf (n p q : ℤ) (h : p + q = -n) :
      f n ≫ (K.ιTotal (ComplexShape.up ℤ) p q (-n) h).unop =
        σ n p • (π n p (-q) (by omega) ≫ (e p q).hom.unop) := by
    dsimp only [f]
    rw [← unop_comp, K.ι_totalDesc]
    simp [Units.smul_def]
  let g (n : ℤ) : unop ((K.total (ComplexShape.up ℤ)).X (-n)) ⟶ H.X n :=
    Fan.IsLimit.lift (hπ n).some (fun p ↦ σ n p •
      ((K.ιTotal (ComplexShape.up ℤ) p (-(p + n)) (-n) (by change _ + _ = _; omega)).unop ≫
        (by simpa only [neg_neg] using (e p (-(p + n))).inv.unop)))
  have hg (n p q : ℤ) (h : p + n = q) :
      g n ≫ π n p q h = σ n p •
        ((K.ιTotal (ComplexShape.up ℤ) p (-q) (-n) (by change _ + _ = _; omega)).unop ≫
          (by simpa only [neg_neg] using (e p (-q)).inv.unop)) := by
    subst q
    exact Fan.IsLimit.fac (hπ n).some _ p
  have hfg (n : ℤ) : f n ≫ g n = 𝟙 _ := by
    apply Fan.IsLimit.hom_ext (hπ n).some
    intro p
    change (f n ≫ g n) ≫ π n p (p + n) rfl = π n p (p + n) rfl
    rw [Category.assoc, hg n p (p + n) rfl]
    simp only [Linear.comp_units_smul, ← Category.assoc, hf, Linear.units_smul_comp,
      smul_smul, Int.units_mul_self, one_smul]
    simp only [Category.assoc]
    simp only [eq_mp_eq_cast, neg_add_rev, neg_neg, congrArg_cast_hom_right, cancelIso]
    have hcast (q : ℤ) (h : p + n = q) :
        π n p q h ≫ eqToHom (by rw [← h]) = π n p (p + n) rfl := by
      subst q
      simp
    exact hcast _ _
  have hgf (n : ℤ) : g n ≫ f n = 𝟙 _ := by
    apply Quiver.Hom.op_inj
    apply HomologicalComplex₂.total.hom_ext
    intro p q h
    change p + q = -n at h
    have hq : p + n = -q := by omega
    simp only [op_comp, op_id]
    apply Quiver.Hom.unop_inj
    simp only [unop_comp, Quiver.Hom.unop_op, Category.comp_id, hf,
      Linear.comp_units_smul, ← Category.assoc, hg n p (-q) hq,
      Linear.units_smul_comp, smul_smul, Int.units_mul_self, one_smul]
    simp only [eq_mp_eq_cast, neg_neg, congrArg_cast_hom_right, Category.assoc, op_unop]
    have hcancel (q q' : ℤ) (hqq : q = q') (hi : p + q = -n) :
        (K.ιTotal (ComplexShape.up ℤ) p q (-n) hi).unop ≫ (e p q).inv.unop ≫
          eqToHom (by rw [hqq]) ≫ (e p q').hom.unop =
            (K.ιTotal (ComplexShape.up ℤ) p q' (-n) (by change p + q' = -n; omega)).unop := by
      subst q'
      simp [← unop_comp]
    exact hcancel _ _ (neg_neg q) _
  exact ⟨fun n ↦ ⟨f n, g n, hfg n, hgf n⟩, hf⟩

private lemma triangle_succ (p : ℤ) :
    (p + 1) * (p + 1 + 1) / 2 = p * (p + 1) / 2 + p + 1 := by
  have h : (p + 1) * (p + 1 + 1) = p * (p + 1) + 2 * p + 2 := by ring
  omega

private lemma sign_vertical (i p : ℤ) :
    p.negOnePow * (p * i + p * (p + 1) / 2).negOnePow =
      (p * (i + 1) + p * (p + 1) / 2).negOnePow := by
  rw [← Int.negOnePow_add]
  congr 1
  ring

private lemma sign_horizontal (i p : ℤ) :
    ((p + 1) * i + (p + 1) * (p + 1 + 1) / 2).negOnePow =
      -((p * (i + 1) + p * (p + 1) / 2).negOnePow * i.negOnePow) := by
  rw [triangle_succ]
  have h : (p + 1) * i + (p * (p + 1) / 2 + p + 1) =
      (p * (i + 1) + p * (p + 1) / 2) + i + 1 := by ring
  rw [h, Int.negOnePow_succ, Int.negOnePow_add]

private lemma homComplex_dual_total_differential_compatibility
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    {R : Sheaf J CommRingCat.{w}}
    (E A : CochainComplex (SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) ℤ)
    (K : HomologicalComplex₂ (SheafOfModules.{max u v w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R))ᵒᵖ
        (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [K.HasTotal (ComplexShape.up ℤ)]
    (e : ∀ p q : ℤ, (K.X p).X q ≅ op (SheafOfModules.homObj (E.X p) (A.X (-q))))
    (π : ∀ n p q : ℤ, p + n = q →
      ((CategoryTheory.homComplex E A).X n ⟶ SheafOfModules.homObj (E.X p) (A.X q)))
    (hd : ∀ n m p q q' p' (_ : n + 1 = m) (hpq : p + m = q)
      (hq' : p + n = q') (hp' : p' + n = q),
      (CategoryTheory.homComplex E A).d n m ≫ π m p q hpq =
        π n p q' hq' ≫ SheafOfModules.homObjMap (𝟙 _) (A.d q' q) -
          n.negOnePow • (π n p' q hp' ≫ SheafOfModules.homObjMap (E.d p p') (𝟙 _)))
    (h₁ : ∀ p p' q, (K.d p p').f q ≫ (e p' q).hom = (e p q).hom ≫
      (SheafOfModules.homObjMap (E.d p p') (𝟙 _)).op)
    (h₂ : ∀ p q q', (K.X p).d q q' ≫ (e p q').hom = (e p q).hom ≫
      (SheafOfModules.homObjMap (𝟙 _) (A.d (-q') (-q))).op)
    (φ : ∀ n : ℤ, (CategoryTheory.homComplex E A).X n ≅
      unop ((K.total (ComplexShape.up ℤ)).X (-n)))
    (hφ : ∀ n p q : ℤ, ∀ h : p + q = -n,
      (φ n).hom ≫ (K.ιTotal (ComplexShape.up ℤ) p q (-n) h).unop =
        (p * n + p * (p + 1) / 2).negOnePow •
          (π n p (-q) (by omega) ≫ (e p q).hom.unop))
    (i j : ℤ) (hij : i + 1 = j) :
    (φ i).hom ≫ ((K.total (ComplexShape.up ℤ)).d (-j) (-i)).unop =
      (CategoryTheory.homComplex E A).d i j ≫ (φ j).hom := by
  apply Quiver.Hom.op_inj
  apply HomologicalComplex₂.total.hom_ext
  intro p q h
  change p + q = -j at h
  apply Quiver.Hom.unop_inj
  simp only [op_comp, Quiver.Hom.unop_op, unop_comp]
  rw [Category.assoc, ← unop_comp]
  change (φ i).hom ≫
      (K.ιTotal (ComplexShape.up ℤ) p q (-j) h ≫
        ((K.total (ComplexShape.up ℤ)).d (-j) (-i))).unop = _
  have ht : K.ιTotal (ComplexShape.up ℤ) p q (-j) h ≫
      (K.total (ComplexShape.up ℤ)).d (-j) (-i) =
      (K.d p (p + 1)).f q ≫ K.ιTotal (ComplexShape.up ℤ) (p + 1) q (-i)
        (by change _ + _ = _; omega) +
      p.negOnePow • ((K.X p).d q (q + 1) ≫
        K.ιTotal (ComplexShape.up ℤ) p (q + 1) (-i)
          (by change _ + _ = _; omega)) := by
    change K.ιTotal _ _ _ _ _ ≫ (K.D₁ _ _ _ + K.D₂ _ _ _) = _
    rw [Preadditive.comp_add, K.ι_D₁, K.ι_D₂,
      K.d₁_eq (ComplexShape.up ℤ) (i₁ := p) (i₁' := p + 1) (by simp) q (-i)
        (by change _ + _ = _; omega),
      K.d₂_eq (ComplexShape.up ℤ) p (i₂ := q) (i₂' := q + 1) (by simp) (-i)
        (by change _ + _ = _; omega)]
    change (1 : ℤˣ) • _ + p.negOnePow • _ = _
    rw [one_smul]
  rw [ht]
  simp only [unop_add, Units.smul_def, unop_zsmul, unop_comp,
    Preadditive.comp_add, Preadditive.comp_zsmul]
  rw [← Category.assoc, hφ i (p + 1) q (by omega),
    ← Category.assoc, hφ i p (q + 1) (by omega),
    Category.assoc, hφ j p q h, Linear.comp_units_smul,
    ← Category.assoc, hd i j p (-q) (-(q + 1)) (p + 1) hij
      (by omega) (by omega) (by omega)]
  have hh := congrArg Quiver.Hom.unop (h₁ p (p + 1) q)
  have hv := congrArg Quiver.Hom.unop (h₂ p q (q + 1))
  simp only [unop_comp, Quiver.Hom.unop_op] at hh hv
  simp only [Category.assoc, hh, hv, Preadditive.sub_comp, Units.smul_def, smul_sub,
    smul_smul, Preadditive.zsmul_comp]
  subst j
  rw [← Units.val_mul, sign_vertical, sign_horizontal]
  simp only [Units.val_neg, Units.val_mul, neg_smul]
  abel

/-- Identify the short complex of the product Hom complex with the unop short complex
of the total
of its commuting Hom bicomplex in the opposite category, with the second index negated.
This comparison does not assume exact columns or boundedness.

Source: Stacks Project, sites-cohomology.tex, Section 0A8X, product Hom differential;
cohomology.tex, Tags 0GM7 and 0GM8, the Hom calculation.
(blueprint: lem-sc-hom-complex-dual-total-comparison)

Proof: unop the coproduct cocone of the total in degree `-n`. It is a product
cone in module sheaves with factors indexed by `p+q=-n`. Reindex by `p`, so
`q=-p-n`, and use `e` to identify these factors with Hom(E^p,A^(p+n)).
The product universal property in `homComplex_exists` gives an isomorphism
of the degree objects. Multiply the p-th projection in degree n by the unit
`(-1)^(p*n+p*(p+1)/2)`. Its ratio under n increasing by one is `(-1)^p`,
and its ratio between (p+1,n) and (p,n+1) is `(-1)^(n+1)`.
The total differential has horizontal coefficient 1 and vertical coefficient
`(-1)^p`. The two assumed differential formulas therefore identify its unop,
with degrees reversed, with `d_A f - (-1)^n f d_E`. Check these equalities
on every product projection; no finiteness or sectionwise lifting is needed.
The isomorphisms in degrees n-1,n,n+1 give an isomorphism of short complexes
between the Hom short complex at n and the unop of the total short complex
at -n. This is the asserted short-complex isomorphism;
its construction uses only products and the two differential formulas.
Empty or zero products obey the same argument. -/
theorem homComplex_sc_iso_dual_total
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    {R : Sheaf J CommRingCat.{w}}
    (E A : CochainComplex (SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) ℤ)
    (K : HomologicalComplex₂ (SheafOfModules.{max u v w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R))ᵒᵖ
        (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [K.HasTotal (ComplexShape.up ℤ)]
    (e : ∀ p q : ℤ, (K.X p).X q ≅ op (SheafOfModules.homObj (E.X p) (A.X (-q))))
    (h₁ : ∀ p p' q : ℤ,
      (K.d p p').f q ≫ (e p' q).hom = (e p q).hom ≫
        (SheafOfModules.homObjMap (E.d p p') (𝟙 (A.X (-q)))).op)
    (h₂ : ∀ p q q' : ℤ,
      (K.X p).d q q' ≫ (e p q').hom = (e p q).hom ≫
        (SheafOfModules.homObjMap (𝟙 (E.X p)) (A.d (-q') (-q))).op)
    (n : ℤ) :
    Nonempty ((CategoryTheory.homComplex E A).sc n ≅
      ((K.total (ComplexShape.up ℤ)).sc (-n)).unop) := by
  classical
  obtain ⟨π, hπ, hd, _⟩ := CategoryTheory.homComplex_projections_exists
    (C := C) (J := J) (R := R)
  obtain ⟨φ, hφ⟩ := homComplex_dual_total_degree_isos E A K e (π E A) (hπ E A)
  have hcomm (i j : ℤ) (hij : i + 1 = j) :
      (φ i).hom ≫ ((K.total (ComplexShape.up ℤ)).d (-j) (-i)).unop =
        (CategoryTheory.homComplex E A).d i j ≫ (φ j).hom := by
    exact homComplex_dual_total_differential_compatibility E A K e
      (π E A) (hd E A) h₁ h₂ φ hφ i j hij
  let H := CategoryTheory.homComplex E A
  let T := K.total (ComplexShape.up ℤ)
  have ec : H.sc' (n - 1) n (n + 1) ≅ (T.sc' (-(n + 1)) (-n) (-(n - 1))).unop :=
    ShortComplex.isoMk (φ (n - 1)) (φ n) (φ (n + 1))
      (hcomm (n - 1) n (by omega)) (hcomm n (n + 1) rfl)
  let a := H.isoSc' (n - 1) n (n + 1) (by simp) (by simp)
  let b := T.isoSc' (-(n + 1)) (-n) (-(n - 1)) (by simp; omega) (by simp; omega)
  exact ⟨a ≪≫ ec ≪≫ ((ShortComplex.unopFunctor _).mapIso b).unop⟩

end CochainComplex
