/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Mathlib.Algebra.Homology.TotalComplex
public import Mathlib.Algebra.Homology.QuasiIso
import WeilConjectures.CategoryTheory.DoubleComplexTotal
import WeilConjectures.FromJoel.Algebra.Homology.BicomplexColumns
import Mathlib.Algebra.Homology.TotalComplexSymmetry
import WeilConjectures.Algebra.Homology.FirstQuadrantTotalExtension

/-! # Comparison for a finite strip of rows

Source: Stacks Project, Homology, Section 12.25, finite filtration argument.
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex₂

-- The usual sign (-1)^(pq) also gives total-complex symmetry over the naturals.
@[instance_reducible]
private def natTotalSymmetry :
    TotalComplexShapeSymmetry (ComplexShape.up ℕ) (ComplexShape.up ℕ) (ComplexShape.up ℕ) where
  symm p q := Nat.add_comm q p
  σ p q := (-1 : ℤˣ) ^ (p * q)
  σ_ε₁ := by
    rintro p _ rfl q
    change (-1 : ℤˣ) ^ (p * q) * 1 =
      (-1 : ℤˣ) ^ q * (-1 : ℤˣ) ^ ((p + 1) * q)
    rw [mul_one, Nat.add_mul, one_mul, pow_add]
    calc
      _ = (-1 : ℤˣ) ^ (p * q) *
          ((-1 : ℤˣ) ^ q * (-1 : ℤˣ) ^ q) := by rw [Int.units_mul_self, mul_one]
      _ = _ := mul_left_comm _ _ _
  σ_ε₂ := by
    rintro p q _ rfl
    change (-1 : ℤˣ) ^ (p * q) * (-1 : ℤˣ) ^ p =
      1 * (-1 : ℤˣ) ^ (p * (q + 1))
    rw [one_mul, Nat.mul_add, Nat.mul_one, pow_add]

private noncomputable abbrev extendBicomplexNat (C : Type u) [Category.{v} C] [Abelian C] :=
  (ComplexShape.embeddingUpNat.extendFunctor C).mapHomologicalComplex (ComplexShape.up ℕ) ⋙
    ComplexShape.embeddingUpNat.extendFunctor (CochainComplex C ℤ)

private theorem extendBicomplexNat_zero {C : Type u} [Category.{v} C] [Abelian C]
    (K : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ)) (p q : ℤ)
    (h : p < 0 ∨ q < 0) : IsZero ((((extendBicomplexNat C).obj K).X p).X q) := by
  rcases h with hp | hq
  · exact (HomologicalComplex.eval _ _ q).map_isZero
      (HomologicalComplex.isZero_extend_X _ ComplexShape.embeddingUpNat p (by
        intro i hi
        change (i : ℤ) = p at hi
        omega))
  · by_cases hp : 0 ≤ p
    · obtain ⟨i, rfl⟩ := Int.eq_ofNat_of_zero_le hp
      let e := HomologicalComplex.extendXIso
        (((ComplexShape.embeddingUpNat.extendFunctor C).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj K)
        ComplexShape.embeddingUpNat (i := i) rfl
      exact IsZero.of_iso (HomologicalComplex.isZero_extend_X (K.X i)
        ComplexShape.embeddingUpNat q (by intro j hj; change (j : ℤ) = q at hj; omega))
        ((HomologicalComplex.eval _ _ q).mapIso e)
    · exact (HomologicalComplex.eval _ _ q).map_isZero
        (HomologicalComplex.isZero_extend_X _ ComplexShape.embeddingUpNat p (by
          intro i hi
          change (i : ℤ) = p at hi
          omega))

private theorem extendBicomplexNat_le {C : Type u} [Category.{v} C] [Abelian C]
    (K : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ)) (N : ℕ)
    (hK : ∀ p q : ℕ, N < p → IsZero ((K.X p).X q)) :
    CochainComplex.IsStrictlyLE ((extendBicomplexNat C).obj K) (N : ℤ) := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro p hp
  obtain ⟨i, rfl⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ p by omega)
  apply IsZero.of_iso _ (HomologicalComplex.extendXIso
    (((ComplexShape.embeddingUpNat.extendFunctor C).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj K)
    ComplexShape.embeddingUpNat (i := i) rfl)
  apply (ComplexShape.embeddingUpNat.extendFunctor C).map_isZero
  rw [IsZero.iff_id_eq_zero]
  ext q
  exact (hK i q (by omega)).eq_of_src _ _

set_option backward.isDefEq.respectTransparency false in
private theorem extendBicomplexNat_column_quasiIso {C : Type u} [Category.{v} C] [Abelian C]
    {K L : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ)} (f : K ⟶ L)
    (hf : ∀ i : ℕ, QuasiIso (f.f i)) (i : ℕ) :
    QuasiIso (((extendBicomplexNat C).map f).f (i : ℤ)) := by
  have : QuasiIso (f.f i) := hf i
  have : QuasiIso (HomologicalComplex.extendMap (f.f i) ComplexShape.embeddingUpNat) :=
    inferInstance
  apply (quasiIso_iff_of_arrow_mk_iso (((extendBicomplexNat C).map f).f (i : ℤ))
    (HomologicalComplex.extendMap (f.f i) ComplexShape.embeddingUpNat) (Arrow.isoMk
    (HomologicalComplex.extendXIso
      (((ComplexShape.embeddingUpNat.extendFunctor C).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj K)
      ComplexShape.embeddingUpNat (i := i) rfl)
    (HomologicalComplex.extendXIso
      (((ComplexShape.embeddingUpNat.extendFunctor C).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj L)
      ComplexShape.embeddingUpNat (i := i) rfl) ?_)).mpr this
  change _ = (HomologicalComplex.extendMap
    (((ComplexShape.embeddingUpNat.extendFunctor C).mapHomologicalComplex
      (ComplexShape.up ℕ)).map f)
    ComplexShape.embeddingUpNat).f (i : ℤ) ≫ _
  rw [HomologicalComplex.extendMap_f
    (((ComplexShape.embeddingUpNat.extendFunctor C).mapHomologicalComplex
      (ComplexShape.up ℕ)).map f)
    ComplexShape.embeddingUpNat (i := i) (i' := (i : ℤ)) (by rfl)]
  simp

set_option backward.isDefEq.respectTransparency false in
/-- Column comparison when only finitely many rows can be nonzero.
Source: Stacks Project, Section 12.25 (Tags 012X and 0133), finite filtration argument.
(blueprint: lem-sc-finite-row-total-column-comparison).

Proof: filter both total complexes by the vertical degree, starting with the largest
possible degree N. The successive subquotients are the horizontal complexes in
vertical degree q, shifted by q, with the total differential's signs. The induced
map on each subquotient is a shift of the corresponding column map of the flipped
bicomplex, hence is a quasi-isomorphism by hf. The filtration starts at zero above
N and ends at the whole total complex at zero. Each filtration short exact sequence
is split on graded objects, because the diagonal is a finite direct sum. Apply the
long exact homology sequence and the five lemma at each successive step, descending
from N to zero. This proves the total map is a quasi-isomorphism. For N=0 there is
one quotient; no assumption about boundedness in the horizontal direction is used. -/
theorem quasiIso_totalMap_of_columns_of_finite_rows
    {C : Type u} [Category.{v} C] [Abelian C]
    {K L : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ)}
    (f : K ⟶ L) (N : ℕ)
    (hK : ∀ p q : ℕ, N < q → IsZero ((K.X p).X q))
    (hL : ∀ p q : ℕ, N < q → IsZero ((L.X p).X q))
    (hf : ∀ q : ℕ, QuasiIso
      (((flipFunctor C (ComplexShape.up ℕ) (ComplexShape.up ℕ)).map f).f q)) :
    QuasiIso (total.map f (ComplexShape.up ℕ)) := by
  let : TotalComplexShapeSymmetry (ComplexShape.up ℕ) (ComplexShape.up ℕ) (ComplexShape.up ℕ) :=
    natTotalSymmetry
  -- Transpose and extend both indices; the finite-column theorem handles the filtration.
  let F := flipFunctor C (ComplexShape.up ℕ) (ComplexShape.up ℕ)
  let g := F.map f
  have hEK : HasTotal ((extendBicomplexNat C).obj (F.obj K)) (ComplexShape.up ℤ) :=
    hasTotal_of_firstQuadrant _ (extendBicomplexNat_zero (F.obj K))
  have hEL : HasTotal ((extendBicomplexNat C).obj (F.obj L)) (ComplexShape.up ℤ) :=
    hasTotal_of_firstQuadrant _ (extendBicomplexNat_zero (F.obj L))
  have : CochainComplex.IsStrictlyGE ((extendBicomplexNat C).obj (F.obj K)) 0 := by
    change CochainComplex.IsStrictlyGE
      ((((ComplexShape.embeddingUpNat.extendFunctor C).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj
        (F.obj K)).extend ComplexShape.embeddingUpNat) 0
    infer_instance
  have : CochainComplex.IsStrictlyGE ((extendBicomplexNat C).obj (F.obj L)) 0 := by
    change CochainComplex.IsStrictlyGE
      ((((ComplexShape.embeddingUpNat.extendFunctor C).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj
        (F.obj L)).extend ComplexShape.embeddingUpNat) 0
    infer_instance
  have : CochainComplex.IsStrictlyLE ((extendBicomplexNat C).obj (F.obj K)) (N : ℤ) :=
    extendBicomplexNat_le (F.obj K) N (fun p q hp ↦ hK q p hp)
  have : CochainComplex.IsStrictlyLE ((extendBicomplexNat C).obj (F.obj L)) (N : ℤ) :=
    extendBicomplexNat_le (F.obj L) N (fun p q hp ↦ hL q p hp)
  have htotal : QuasiIso (total.map ((extendBicomplexNat C).map g) (ComplexShape.up ℤ)) :=
    total.quasiIso_map_of_finitely_many_columns ((extendBicomplexNat C).map g) 0 (N : ℤ) (by
      intro i hi _
      obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le hi
      exact extendBicomplexNat_column_quasiIso g hf q)
  -- Only the reindexing isomorphism remains open, not the comparison argument.
  obtain ⟨e⟩ := totalMap_extend_nat_arrow_iso g
  have hext : QuasiIso (HomologicalComplex.extendMap (total.map g (ComplexShape.up ℕ))
      ComplexShape.embeddingUpNat) := (quasiIso_iff_of_arrow_mk_iso _ _ e).mp htotal
  have hg : QuasiIso (total.map g (ComplexShape.up ℕ)) :=
    (HomologicalComplex.quasiIso_extendMap_iff _ _).mp hext
  apply (quasiIso_iff_of_arrow_mk_iso (total.map g (ComplexShape.up ℕ))
    (total.map f (ComplexShape.up ℕ))
    (Arrow.isoMk (K.totalFlipIso (ComplexShape.up ℕ)) 
      (L.totalFlipIso (ComplexShape.up ℕ)) ?_)).mp hg
  ext n
  apply total.hom_ext
  intro q p hpq
  simp only [HomologicalComplex.comp_f, Arrow.mk_hom]
  dsimp only [F, g, flipFunctor]
  rw [ιTotal_map_assoc, ιTotal_totalFlipIso_f_hom_assoc, ιTotal_totalFlipIso_f_hom]
  simp only [Linear.units_smul_comp, Linear.comp_units_smul]
  rw [ιTotal_map]

end HomologicalComplex₂
