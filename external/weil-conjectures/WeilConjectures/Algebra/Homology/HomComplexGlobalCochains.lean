/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.HomComplex
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
import WeilConjectures.Algebra.Homology.HomComplexProjections

/-!
# Global sections of the sheaf Hom complex as ordinary cochains

Source: Stacks Project, Cohomology on Sites, Section 21.34, Equation (21.34.0.2)
(Tag 0A8Z), and Lemma 21.34.8 (Tag 0A96).
(blueprint: lem-pur-hom-complex-global-cochains)
-/

@[expose] public section

universe u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive Opposite

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {R : Sheaf J CommRingCat.{max u v}}

set_option hygiene false in
local notation "𝓡" =>
  (sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R
set_option hygiene false in
local notation "Mod" => SheafOfModules.{max u v} 𝓡

private noncomputable def factorEquiv (M N : Mod) :
    (SheafOfModules.unit 𝓡 ⟶ SheafOfModules.homObj (R := R) M N) ≃+ (M ⟶ N) where
  toEquiv := (SheafOfModules.unitHomEquiv _).trans
    (SheafOfModules.homObjSectionsEquiv M N)
  map_add' f g := by rfl

private lemma factorEquiv_comp {M M' N N' : Mod}
    (s : SheafOfModules.unit 𝓡 ⟶ SheafOfModules.homObj (R := R) M N)
    (f : M' ⟶ M) (g : N ⟶ N') :
    factorEquiv M' N' (s ≫ SheafOfModules.homObjMap (R := R) f g) =
      f ≫ factorEquiv M N s ≫ g := by
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Global sections, represented by morphisms from the rank-one free module sheaf,
identify the sheaf Hom complex with the ordinary complex of cochains.
Source: Stacks Project, Cohomology on Sites, Equation (21.34.0.2) (Tag 0A8Z).
(blueprint: lem-pur-hom-complex-global-cochains)

Proof: choose the product projections specified by `homComplex_exists`.
The universal property of each product identifies maps from the rank-one free
module sheaf with families of maps to its internal Hom factors. The equivalence
`SheafOfModules.unitHomEquiv` identifies the latter with global sections, and
`SheafOfModules.homObjSectionsEquiv` identifies those sections with module-sheaf
morphisms. Reindex the family from p to triples (p,q,p+n=q) to obtain ordinary
cochains. All maps preserve addition, so this is an additive equivalence.
Apply the differential projection formula to each component. Postcomposition
with d_B and precomposition with d_A become ordinary composition under the
internal-Hom sections equivalence. The formula is d_B f - (-1)^n f d_A,
precisely the external cochain differential. Equality on every component proves
the asserted compatibility. Products allow unbounded families; no local
acyclicity or boundedness is assumed. For a zero complex all factors vanish;
for zero differentials both differentials vanish. -/
theorem homComplex_global_cochains
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{max u v})
    (A B : CochainComplex (SheafOfModules.{max u v}
      ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)) ℤ) :
    let R₀ := (sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R
    let H := homComplex (R := R) A B
    ∃ e : ∀ n : ℤ, (SheafOfModules.unit R₀ ⟶ H.X n) ≃+
        CochainComplex.HomComplex.Cochain A B n,
      ∀ (i j : ℤ), i + 1 = j → ∀ s : SheafOfModules.unit R₀ ⟶ H.X i,
        e j (s ≫ H.d i j) = CochainComplex.HomComplex.δ i j (e i s) := by
  classical
  dsimp only
  obtain ⟨π, hπ, hd, _⟩ :=
    homComplex_projections_exists.{u, v, max u v, max u v} (J := J) (R := R)
  let e (n : ℤ) : (SheafOfModules.unit 𝓡 ⟶ (homComplex (R := R) A B).X n) ≃+
      CochainComplex.HomComplex.Cochain A B n :=
    { toFun s := CochainComplex.HomComplex.Cochain.mk fun p q hpq ↦
        factorEquiv (A.X p) (B.X q) (s ≫ π A B n p q hpq)
      invFun c := Fan.IsLimit.lift (hπ A B n).some fun p ↦
        (factorEquiv (A.X p) (B.X (p + n))).symm (c.v p (p + n) rfl)
      left_inv s := by
        apply Fan.IsLimit.hom_ext (hπ A B n).some
        intro p
        simpa using Fan.IsLimit.fac (hπ A B n).some (fun p ↦
          s ≫ π A B n p (p + n) rfl) p
      right_inv c := by
        apply CochainComplex.HomComplex.Cochain.ext
        intro p q hpq
        subst q
        change factorEquiv (A.X p) (B.X (p + n))
          (Fan.IsLimit.lift (hπ A B n).some (fun p ↦
            (factorEquiv (A.X p) (B.X (p + n))).symm (c.v p (p + n) rfl)) ≫
            π A B n p (p + n) rfl) = c.v p (p + n) rfl
        have hf := Fan.IsLimit.fac (hπ A B n).some (fun p ↦
          (factorEquiv (A.X p) (B.X (p + n))).symm (c.v p (p + n) rfl)) p
        simp only [fan_mk_proj] at hf
        rw [hf]
        exact AddEquiv.apply_symm_apply _ _
      map_add' s t := by
        apply CochainComplex.HomComplex.Cochain.ext
        intro p q hpq
        simp [add_comp] }
  refine ⟨e, ?_⟩
  intro i j hij s
  apply CochainComplex.HomComplex.Cochain.ext
  intro p q hpq
  rw [CochainComplex.HomComplex.δ_v i j hij _ p q hpq (p + i) (p + 1)
    (by omega) rfl]
  change factorEquiv (A.X p) (B.X q)
      ((s ≫ (homComplex (R := R) A B).d i j) ≫ π A B j p q hpq) = _
  dsimp only [homComplex] at *
  rw [Category.assoc, hd A B i j p q (p + i) (p + 1) hij hpq rfl (by omega)]
  simp only [comp_sub, Units.smul_def, comp_zsmul, ← Category.assoc, map_sub, map_zsmul,
    factorEquiv_comp, Category.id_comp, Category.comp_id]
  subst j
  simp [e, Int.negOnePow_succ, sub_eq_add_neg]

end CategoryTheory
