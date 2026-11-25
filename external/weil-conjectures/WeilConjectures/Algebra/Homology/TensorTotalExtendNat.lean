/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.Bifunctor
public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import WeilConjectures.Mathlib.Algebra.Homology.ComplexShapeSigns

/-! # Tensor totalization and extension by zero

Source: Stacks Project, Tag 012Z, the diagonal direct-sum total formula.
(blueprint: lem-sc-tensor-total-extend-nat).
-/

@[expose] public section
universe w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace HomologicalComplex

private noncomputable abbrev intTotal
    {k : Type w} [Field k] (A B : CochainComplex (ModuleCat.{w} k) ℕ)
    := mapBifunctor (A.extend ComplexShape.embeddingUpNat)
  (B.extend ComplexShape.embeddingUpNat) (curriedTensor (ModuleCat.{w} k)) (.up ℤ)

private noncomputable abbrev natTotal
    {k : Type w} [Field k] (A B : CochainComplex (ModuleCat.{w} k) ℕ)
    := mapBifunctor A B (curriedTensor (ModuleCat.{w} k)) (.up ℕ)

private theorem negative_factor
    {k : Type w} [Field k] (A B : CochainComplex (ModuleCat.{w} k) ℕ)
    (p q : ℤ) (h : p < 0 ∨ q < 0) :
    IsZero ((A.extend ComplexShape.embeddingUpNat).X p ⊗
      (B.extend ComplexShape.embeddingUpNat).X q) := by
  rw [IsZero.iff_id_eq_zero, ← id_tensorHom_id]
  rcases h with hp | hq
  · have hz := A.isZero_extend_X ComplexShape.embeddingUpNat p (by
      intro i hi
      change (i : ℤ) = p at hi
      omega)
    rw [hz.eq_of_src (𝟙 _) 0]
    simp
  · have hz := B.isZero_extend_X ComplexShape.embeddingUpNat q (by
      intro i hi
      change (i : ℤ) = q at hi
      omega)
    rw [hz.eq_of_src (𝟙 _) 0]
    simp

private noncomputable def toNatDegree
    {k : Type w} [Field k] (A B : CochainComplex (ModuleCat.{w} k) ℕ) (n : ℕ) :
    (intTotal A B).X (n : ℤ) ⟶ (natTotal A B).X n :=
  mapBifunctorDesc fun p q h ↦
    if hp : 0 ≤ p then
      if hq : 0 ≤ q then
        ((A.extendXIso ComplexShape.embeddingUpNat
            (i := p.toNat) (Int.toNat_of_nonneg hp)).hom ⊗ₘ
          (B.extendXIso ComplexShape.embeddingUpNat
            (i := q.toNat) (Int.toNat_of_nonneg hq)).hom) ≫
          ιMapBifunctor A B (curriedTensor (ModuleCat.{w} k)) (.up ℕ)
            p.toNat q.toNat n (by
              change p + q = (n : ℤ) at h
              change p.toNat + q.toNat = n
              omega)
      else 0
    else 0

private noncomputable def fromNatDegree
    {k : Type w} [Field k] (A B : CochainComplex (ModuleCat.{w} k) ℕ) (n : ℕ) :
    (natTotal A B).X n ⟶ (intTotal A B).X (n : ℤ) :=
  mapBifunctorDesc fun p q h ↦
    ((A.extendXIso ComplexShape.embeddingUpNat (i := p) rfl).inv ⊗ₘ
      (B.extendXIso ComplexShape.embeddingUpNat (i := q) rfl).inv) ≫
      ιMapBifunctor (A.extend ComplexShape.embeddingUpNat)
        (B.extend ComplexShape.embeddingUpNat) (curriedTensor (ModuleCat.{w} k))
          (.up ℤ) (p : ℤ) (q : ℤ) (n : ℤ) (by
            change p + q = n at h
            change (p : ℤ) + (q : ℤ) = (n : ℤ)
            omega)

private theorem to_fromNatDegree
    {k : Type w} [Field k] (A B : CochainComplex (ModuleCat.{w} k) ℕ) (n : ℕ) :
    toNatDegree A B n ≫ fromNatDegree A B n = 𝟙 _ := by
  apply mapBifunctor.hom_ext
  intro p q h
  change p + q = (n : ℤ) at h
  by_cases hp : 0 ≤ p
  · by_cases hq : 0 ≤ q
    · obtain ⟨p, rfl⟩ := Int.eq_ofNat_of_zero_le hp
      obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le hq
      simp [toNatDegree, fromNatDegree, Category.assoc]
    · exact (negative_factor A B p q (Or.inr (by omega))).eq_of_src _ _
  · exact (negative_factor A B p q (Or.inl (by omega))).eq_of_src _ _

private theorem from_toNatDegree
    {k : Type w} [Field k] (A B : CochainComplex (ModuleCat.{w} k) ℕ) (n : ℕ) :
    fromNatDegree A B n ≫ toNatDegree A B n = 𝟙 _ := by
  apply mapBifunctor.hom_ext
  intro p q h
  simp [fromNatDegree, toNatDegree, Category.assoc]

private noncomputable def natDegreeIso
    {k : Type w} [Field k] (A B : CochainComplex (ModuleCat.{w} k) ℕ) (n : ℕ) :
    (intTotal A B).X (n : ℤ) ≅
      ((natTotal A B).extend ComplexShape.embeddingUpNat).X (n : ℤ) :=
  { hom := toNatDegree A B n
    inv := fromNatDegree A B n
    hom_inv_id := to_fromNatDegree A B n
    inv_hom_id := from_toNatDegree A B n } ≪≫
    ((natTotal A B).extendXIso ComplexShape.embeddingUpNat (i := n) rfl).symm

private theorem negative_total
    {k : Type w} [Field k] (A B : CochainComplex (ModuleCat.{w} k) ℕ)
    (n : ℤ) (hn : n < 0) : IsZero ((intTotal A B).X n) := by
  rw [IsZero.iff_id_eq_zero]
  apply mapBifunctor.hom_ext
  intro p q h
  change p + q = n at h
  exact (negative_factor A B p q (by omega)).eq_of_src _ _

private noncomputable def degreeIso
    {k : Type w} [Field k] (A B : CochainComplex (ModuleCat.{w} k) ℕ) (n : ℤ) :
    (intTotal A B).X n ≅ ((natTotal A B).extend ComplexShape.embeddingUpNat).X n :=
  match n with
  | .ofNat n => natDegreeIso A B n
  | .negSucc n => (negative_total A B _ (by omega)).iso
      ((natTotal A B).isZero_extend_X ComplexShape.embeddingUpNat _ (by
        intro i
        change (i : ℤ) ≠ Int.negSucc n
        omega))

private theorem toNatDegree_comm
    {k : Type w} [Field k] (A B : CochainComplex (ModuleCat.{w} k) ℕ) (n : ℕ) :
    toNatDegree A B n ≫ (natTotal A B).d n (n + 1) =
      (intTotal A B).d (n : ℤ) ((n + 1 : ℕ) : ℤ) ≫ toNatDegree A B (n + 1) := by
  set_option backward.isDefEq.respectTransparency false in
    apply mapBifunctor.hom_ext
    intro p q h
    change p + q = (n : ℤ) at h
    by_cases hp : 0 ≤ p
    · by_cases hq : 0 ≤ q
      · obtain ⟨p, rfl⟩ := Int.eq_ofNat_of_zero_le hp
        obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le hq
        have hn : p + q = n := by omega
        subst n
        simp only [mapBifunctor.d_eq, Preadditive.comp_add,
          Preadditive.add_comp, mapBifunctor.ι_D₁_assoc, mapBifunctor.ι_D₂_assoc]
        simp only [curriedTensor_obj_obj, Int.natCast_add, toNatDegree, ComplexShape.π_def,
          ι_mapBifunctorDesc_assoc, Nat.cast_nonneg, ↓reduceDIte, Int.toNat_natCast,
          Category.assoc, mapBifunctor.ι_D₁, mapBifunctor.ι_D₂, Int.cast_ofNat_Int]
        rw [mapBifunctor.d₁_eq A B (curriedTensor (ModuleCat.{w} k)) (.up ℕ)
            (i₁' := p + 1) rfl q _ (by change p + 1 + q = p + q + 1; omega),
          mapBifunctor.d₂_eq A B (curriedTensor (ModuleCat.{w} k)) (.up ℕ)
            p (i₂' := q + 1) rfl _ (by change p + (q + 1) = p + q + 1; omega),
          mapBifunctor.d₁_eq (A.extend ComplexShape.embeddingUpNat)
            (B.extend ComplexShape.embeddingUpNat) (curriedTensor (ModuleCat.{w} k)) (.up ℤ)
            (i₁' := ((p + 1 : ℕ) : ℤ)) (by change (p : ℤ) + 1 = ((p + 1 : ℕ) : ℤ); omega)
            (q : ℤ) _ (by change ((p + 1 : ℕ) : ℤ) + (q : ℤ) = (p : ℤ) + (q : ℤ) + 1; omega),
          mapBifunctor.d₂_eq (A.extend ComplexShape.embeddingUpNat)
            (B.extend ComplexShape.embeddingUpNat) (curriedTensor (ModuleCat.{w} k)) (.up ℤ)
            (p : ℤ) (i₂' := ((q + 1 : ℕ) : ℤ))
            (by change (q : ℤ) + 1 = ((q + 1 : ℕ) : ℤ); omega)
            _ (by change (p : ℤ) + ((q + 1 : ℕ) : ℤ) = (p : ℤ) + (q : ℤ) + 1; omega)]
        simp only [curriedTensor_obj_obj, ComplexShape.ε₁_def, curriedTensor_map_app,
          ← tensorHom_id, one_smul, tensorHom_comp_tensorHom_assoc, Category.comp_id,
          ComplexShape.ε₂_def, ComplexShape.ε_up_ℕ, curriedTensor_obj_map, ← id_tensorHom,
          Linear.comp_units_smul, Int.natCast_add, Int.cast_ofNat_Int, Category.assoc,
          ι_mapBifunctorDesc, Nat.cast_nonneg, ↓reduceDIte, Int.toNat_natCast_add_one,
          Int.toNat_natCast, ComplexShape.ε_up_ℤ, Int.negOnePow, zpow_natCast,
          Linear.units_smul_comp]
        erw [A.extend_d_eq ComplexShape.embeddingUpNat
            (i := p) (j := p + 1) (i' := (p : ℤ)) (j' := (p : ℤ) + 1) rfl
            (by change ((p + 1 : ℕ) : ℤ) = (p : ℤ) + 1; omega),
          B.extend_d_eq ComplexShape.embeddingUpNat
            (i := q) (j := q + 1) (i' := (q : ℤ)) (j' := (q : ℤ) + 1) rfl
            (by change ((q + 1 : ℕ) : ℤ) = (q : ℤ) + 1; omega)]
        simp [show (0 : ℤ) ≤ (p : ℤ) + 1 by omega,
          show (0 : ℤ) ≤ (q : ℤ) + 1 by omega, Category.assoc,
          -tensorHom_id, -id_tensorHom]
      · exact (negative_factor A B p q (Or.inr (by omega))).eq_of_src _ _
    · exact (negative_factor A B p q (Or.inl (by omega))).eq_of_src _ _

private theorem degreeIso_ι
    {k : Type w} [Field k] (A B : CochainComplex (ModuleCat.{w} k) ℕ) (p q : ℕ) :
        ιMapBifunctor (A.extend ComplexShape.embeddingUpNat)
            (B.extend ComplexShape.embeddingUpNat) (curriedTensor (ModuleCat.{w} k))
              (.up ℤ) (p : ℤ) (q : ℤ) ((p + q : ℕ) : ℤ) (by
                change (p : ℤ) + (q : ℤ) = ((p + q : ℕ) : ℤ); omega) ≫
          (degreeIso A B ((p + q : ℕ) : ℤ)).hom ≫
          ((natTotal A B).extendXIso ComplexShape.embeddingUpNat
            (i := p + q) rfl).hom =
        ((A.extendXIso ComplexShape.embeddingUpNat (i := p) rfl).hom ⊗ₘ
          (B.extendXIso ComplexShape.embeddingUpNat (i := q) rfl).hom) ≫
          ιMapBifunctor A B (curriedTensor (ModuleCat.{w} k)) (.up ℕ) p q (p + q) rfl := by
  simp [degreeIso, natDegreeIso, toNatDegree, Category.assoc]

/-- Zero extension commutes with tensor totalization, preserving summand inclusions.
Source: Stacks Project, Tag 012Z, the diagonal direct-sum total formula.
(blueprint: lem-sc-tensor-total-extend-nat).

Proof: In total degree n>=0 only summands with two nonnegative indices survive.
The map sends each integer summand (p,q) to the natural summand (p.toNat,q.toNat)
using the two extendXIso homomorphisms. Its inverse sends each natural summand
back using their inverses. A negative factor is zero, so its tensor summand is
zero and has a unique map. The coproduct universal property defines both maps.
Checking on each coprojection proves that they are inverse. In negative total
degree all summands have a negative factor, and both complexes are zero there.
For consecutive nonnegative degrees check differential compatibility on each
summand: the two tensor differential terms become the same factor differentials
under extend_d_eq, and (-1)^p agrees with the integer sign at the cast of p.
The boundary from -1 to 0 has zero source. All other differentials vanish by
shape. These degree maps define a cochain isomorphism; its construction gives
the displayed summand identity. Degree zero has only the (0,0) summand; zero
factor complexes have only zero summands, so both cases obey the same formula. -/
theorem tensorTotal_extend_nat
    {k : Type w} [Field k] (A B : CochainComplex (ModuleCat.{w} k) ℕ) :
    ∃ s : mapBifunctor (A.extend ComplexShape.embeddingUpNat)
        (B.extend ComplexShape.embeddingUpNat) (curriedTensor (ModuleCat.{w} k))
          (ComplexShape.up ℤ) ≅
      (mapBifunctor A B (curriedTensor (ModuleCat.{w} k))
        (ComplexShape.up ℕ)).extend ComplexShape.embeddingUpNat,
      ∀ p q : ℕ,
        ιMapBifunctor (A.extend ComplexShape.embeddingUpNat)
            (B.extend ComplexShape.embeddingUpNat) (curriedTensor (ModuleCat.{w} k))
              (ComplexShape.up ℤ) (p : ℤ) (q : ℤ) ((p + q : ℕ) : ℤ)
                (by change (p : ℤ) + (q : ℤ) = ((p + q : ℕ) : ℤ); omega) ≫
          s.hom.f ((p + q : ℕ) : ℤ) ≫
          ((mapBifunctor A B (curriedTensor (ModuleCat.{w} k))
            (ComplexShape.up ℕ)).extendXIso ComplexShape.embeddingUpNat
              (i := p + q) rfl).hom =
        ((A.extendXIso ComplexShape.embeddingUpNat (i := p) rfl).hom ⊗ₘ
          (B.extendXIso ComplexShape.embeddingUpNat (i := q) rfl).hom) ≫
          ιMapBifunctor A B (curriedTensor (ModuleCat.{w} k))
            (ComplexShape.up ℕ) p q (p + q) rfl := by
  refine ⟨Hom.isoOfComponents (degreeIso A B) ?_, ?_⟩
  · intro i j hij
    change i + 1 = j at hij
    subst j
    cases i with
    | ofNat n =>
      erw [show Int.ofNat n + 1 = Int.ofNat (n + 1) by
        change (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ)
        omega]
      change (natDegreeIso A B n).hom ≫
          ((natTotal A B).extend ComplexShape.embeddingUpNat).d
            (n : ℤ) ((n + 1 : ℕ) : ℤ) =
        (intTotal A B).d (n : ℤ) ((n + 1 : ℕ) : ℤ) ≫ (natDegreeIso A B (n + 1)).hom
      erw [(natTotal A B).extend_d_eq ComplexShape.embeddingUpNat
        (i := n) (j := n + 1) (i' := (n : ℤ)) (j' := ((n + 1 : ℕ) : ℤ)) rfl rfl]
      simp only [natDegreeIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
        Iso.inv_hom_id_assoc]
      simpa only [Category.assoc] using congrArg
        (fun f ↦ f ≫ ((natTotal A B).extendXIso ComplexShape.embeddingUpNat
          (i := n + 1) rfl).inv) (toNatDegree_comm A B n)
    | negSucc n =>
      exact (negative_total A B _ (by omega)).eq_of_src _ _
  · intro p q
    exact degreeIso_ι A B p q

end HomologicalComplex
