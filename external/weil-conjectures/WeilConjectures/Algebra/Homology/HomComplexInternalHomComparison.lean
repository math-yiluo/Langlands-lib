/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.HomComplexComponents
public import WeilConjectures.Algebra.Homology.InternalHom
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
public import WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian

/-!
# Comparison of `homComplex` with the internal hom of cochain complexes

Let `R` be a sheaf of commutative rings on a site `C : Type u` with `Category.{u} C`. Sheaves of
`R`-modules form a monoidal closed category (`SheafOfModules.monoidalCategory R`,
`SheafOfModules.monoidalClosed`), with internal hom `SheafOfModules.homObj`, so that cochain
complexes of `R`-modules have the internal hom complex `CochainComplex.internalHomObj L M`.
Both it and the sheaf Hom complex `homComplex L M` have the products
`∏_{p + n = q} 𝓗om(L^p, M^q)` in degree `n`, but with different sign conventions for the
differential: `d_M f - (-1)^n f d_L` for `homComplex` and `(-1)^p (d_M f - f d_L)` for
`internalHomObj`.

## Main definitions

- `CategoryTheory.homComplexIsoInternalHomObj L M : homComplex L M ≅ internalHomObj L M`: the
  isomorphism which is `(-1)^(p n)` times the identity on the factor `𝓗om(L^p, M^(p+n))` in
  degree `n`.
- `CategoryTheory.homComplexFunctorObjIsoInternalHom L`: the same isomorphism, natural in `M`,
  between `homComplexFunctor.obj (op L)` and `CochainComplex.internalHom L`.

Source: Stacks Project, sites-cohomology.tex, Section 0A8X (blueprint: def-pur-hom-complex).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory MonoidalClosed
open CochainComplex

namespace CategoryTheory

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasSheafify J AddCommGrpCat.{u}]
  {R : Sheaf J CommRingCat.{u}}

set_option hygiene false in
local notation "𝒜" =>
  SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)

attribute [local instance] SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory
  SheafOfModules.monoidalClosed

local instance : MonoidalPreadditive 𝒜 := (SheafOfModules.tensorClosed R).1.some

local instance : HasColimitsOfSize.{0, 0} 𝒜 := hasColimitsOfSizeShrink.{0, 0, u, u} 𝒜

variable (L M : CochainComplex 𝒜 ℤ)

/-- The projection `homComplexπ` of the Hom complex, as a morphism to the internal hom
`(ihom (L.X p)).obj (M.X q) = 𝓗om(L^p, M^q)`. -/
noncomputable abbrev homComplexIhomπ (n p q : ℤ) (h : p + n = q) :
    (homComplex.{u, u, u, u} L M).X n ⟶ (ihom (L.X p)).obj (M.X q) :=
  homComplexπ L M n p q h

lemma homComplex_d_ihomπ (n m p q q' p' : ℤ) (hnm : n + 1 = m) (hpq : p + m = q)
    (hq' : p + n = q') (hp' : p' + n = q) :
    (homComplex.{u, u, u, u} L M).d n m ≫ homComplexIhomπ L M m p q hpq =
      homComplexIhomπ L M n p q' hq' ≫ (ihom (L.X p)).map (M.d q' q) -
        n.negOnePow • (homComplexIhomπ L M n p' q hp' ≫ (pre (L.d p p')).app (M.X q)) := by
  have hpre : (pre (L.d p p')).app (M.X q) =
      SheafOfModules.homObjMap.{u, u, u, u} (L.d p p') (𝟙 (M.X q)) :=
    SheafOfModules.pre_app.{u} _ _
  rw [hpre]
  exact homComplex_d_π L M n m p q q' p' hnm hpq hq' hp'

lemma homComplex_d_ihomπ_of_smul (n p q : ℤ) (h : p + (n + 1) = q) (h₁ : p + 1 + n = q) :
    (homComplex.{u, u, u, u} L M).d n (n + 1) ≫
        ((p * (n + 1)).negOnePow • homComplexIhomπ L M (n + 1) p q h) =
      ((p * (n + 1)).negOnePow : ℤ) • (homComplexIhomπ L M n p (p + n) rfl ≫
        (ihom (L.X p)).map (M.d (p + n) q) -
        (n.negOnePow : ℤ) • (homComplexIhomπ L M n (p + 1) q h₁ ≫
          (pre (L.d p (p + 1))).app (M.X q))) := by
  rw [Units.smul_def, Preadditive.comp_zsmul,
    homComplex_d_ihomπ L M n (n + 1) p q (p + n) (p + 1) rfl h rfl h₁, Units.smul_def]

variable {L M} in
lemma homComplexFunctor_obj_map_f_ihomπ {M' : CochainComplex 𝒜 ℤ} (g : M ⟶ M')
    (n p q : ℤ) (h : p + n = q) :
    (((homComplexFunctor.{u, u, u, u} (C := C) (J := J) (R := R)).obj (op L)).map g).f n ≫
        homComplexIhomπ L M' n p q h =
      homComplexIhomπ L M n p q h ≫ (ihom (L.X p)).map (g.f q) :=
  homComplexFunctor_obj_map_f_π g n p q h

/-- The degree `n` part of `homComplexIsoInternalHomObj`, from `homComplex` to
`internalHomObj`: `(-1)^(p n)` times the identity on the factor `𝓗om(L^p, M^(p+n))`. -/
noncomputable def homComplexToInternalHomObjX (n : ℤ) :
    (homComplex.{u, u, u, u} L M).X n ⟶ (internalHomObj L M).X n :=
  Pi.lift fun T : HomComplex.Triplet n ↦
    (T.p * n).negOnePow • homComplexIhomπ L M n T.p T.q T.hpq

/-- The degree `n` part of `homComplexIsoInternalHomObj`, from `internalHomObj` to
`homComplex`. -/
noncomputable def internalHomObjToHomComplexX (n : ℤ) :
    (internalHomObj L M).X n ⟶ (homComplex.{u, u, u, u} L M).X n :=
  (homComplexIsLimit L M n).lift
    (Fan.mk _ fun p ↦ (p * n).negOnePow • internalHomπ L M n p (p + n) rfl)

@[reassoc]
lemma homComplexToInternalHomObjX_π (n p q : ℤ) (h : p + n = q) :
    homComplexToInternalHomObjX L M n ≫ internalHomπ L M n p q h =
      (p * n).negOnePow • homComplexIhomπ L M n p q h :=
  Pi.lift_comp_π _ _

@[reassoc]
lemma internalHomObjToHomComplexX_π (n p q : ℤ) (h : p + n = q) :
    internalHomObjToHomComplexX L M n ≫ homComplexIhomπ L M n p q h =
      (p * n).negOnePow • internalHomπ L M n p q h := by
  subst h
  exact (homComplexIsLimit L M n).fac _ ⟨p⟩

/-- The degree `n` part of `homComplexIsoInternalHomObj`. -/
noncomputable def homComplexXIsoInternalHomObjX (n : ℤ) :
    (homComplex.{u, u, u, u} L M).X n ≅ (internalHomObj L M).X n where
  hom := homComplexToInternalHomObjX L M n
  inv := internalHomObjToHomComplexX L M n
  hom_inv_id := homComplex_hom_ext.{u, u, u, u} fun p q h ↦ by
    change _ ≫ homComplexIhomπ L M n p q h = 𝟙 _ ≫ homComplexIhomπ L M n p q h
    rw [Category.assoc, internalHomObjToHomComplexX_π, Linear.comp_units_smul,
      homComplexToInternalHomObjX_π, smul_smul, Int.units_mul_self, one_smul, Category.id_comp]
  inv_hom_id := internalHomObj_hom_ext fun p q h ↦ by
    rw [Category.assoc, homComplexToInternalHomObjX_π, Linear.comp_units_smul,
      internalHomObjToHomComplexX_π, smul_smul, Int.units_mul_self, one_smul, Category.id_comp]

lemma homComplexToInternalHomObjX_comm (n m : ℤ) (hnm : n + 1 = m) :
    homComplexToInternalHomObjX L M n ≫ (internalHomObj L M).d n m =
      (homComplex.{u, u, u, u} L M).d n m ≫ homComplexToInternalHomObjX L M m := by
  subst hnm
  refine internalHomObj_hom_ext fun p q h ↦ ?_
  have h₁ : p + 1 + n = q := by omega
  rw [Category.assoc, Category.assoc,
    internalHomObj_d_π L M n (n + 1) p q h (p + n) (p + 1) rfl h₁,
    homComplexToInternalHomObjX_π, homComplex_d_ihomπ_of_smul L M n p q h h₁]
  simp only [Units.smul_def, Preadditive.comp_zsmul, Preadditive.comp_sub,
    homComplexToInternalHomObjX_π_assoc, Preadditive.zsmul_comp]
  rw [show p * (n + 1) = p * n + p by ring, show (p + 1) * n = p * n + n by ring,
    Int.negOnePow_add, Int.negOnePow_add]
  simp only [Units.val_mul, smul_sub, smul_smul, mul_comm, mul_left_comm]

/-- The comparison isomorphism `homComplex L M ≅ internalHomObj L M` between the sheaf Hom
complex and the internal hom complex of the monoidal closed category of sheaves of modules. In
degree `n`, it is `(-1)^(p n)` times the identity on the factor `𝓗om(L^p, M^(p+n))`; the sign
converts the differential `d_M f - (-1)^n f d_L` of `homComplex` into the differential
`(-1)^p (d_M f - f d_L)` of `internalHomObj`. -/
noncomputable def homComplexIsoInternalHomObj : homComplex.{u, u, u, u} L M ≅ internalHomObj L M :=
  HomologicalComplex.Hom.isoOfComponents (homComplexXIsoInternalHomObjX L M)
    (fun n m hnm ↦ homComplexToInternalHomObjX_comm L M n m hnm)

@[reassoc]
lemma homComplexIsoInternalHomObj_hom_f_π (n p q : ℤ) (h : p + n = q) :
    (homComplexIsoInternalHomObj L M).hom.f n ≫ internalHomπ L M n p q h =
      (p * n).negOnePow • homComplexIhomπ L M n p q h :=
  homComplexToInternalHomObjX_π L M n p q h

-- Rewriting with the components of `homComplexIsoInternalHomObj` in the naturality square
-- needs unification up to the universe presentation `max u u u` of `homComplex`.
/-- The comparison isomorphism `homComplexIsoInternalHomObj`, natural in the second variable:
`homComplexFunctor.obj (op L) ≅ CochainComplex.internalHom L`. -/
noncomputable def homComplexFunctorObjIsoInternalHom :
    (homComplexFunctor.{u, u, u, u} (C := C) (J := J) (R := R)).obj (op L) ≅
      CochainComplex.internalHom L :=
  NatIso.ofComponents (fun M ↦ homComplexIsoInternalHomObj L M) fun {M M'} g ↦ by
    beta_reduce
    ext n : 1
    refine internalHomObj_hom_ext fun p q h ↦ ?_
    rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f]
    rw [Category.assoc, Category.assoc]
    rw [CochainComplex.internalHom_map_f_π]
    have e₁ := homComplexIsoInternalHomObj_hom_f_π L M n p q h
    have e₂ := homComplexIsoInternalHomObj_hom_f_π L M' n p q h
    rw [reassoc_of% e₁]
    rw [e₂]
    simp only [Units.smul_def, Preadditive.comp_zsmul, Preadditive.zsmul_comp,
      homComplexFunctor_obj_map_f_ihomπ]

end CategoryTheory
