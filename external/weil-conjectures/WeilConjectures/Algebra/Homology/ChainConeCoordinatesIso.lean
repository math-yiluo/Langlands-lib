/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.Linear
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Category.ModuleCat.Biproducts

/-! # Assembling scalar cone coordinates into a complex isomorphism

Source: Stacks Project, More on Algebra, Tags 0628 and 0629, and
Homological Algebra, the definition of a mapping cone.
(blueprint: lem-pc-chain-cone-coordinates-iso).
-/

@[expose] public section

universe u

open CategoryTheory

namespace ChainComplex

private noncomputable def downIso (A : Type u) [CommRing A]
    (L : ChainComplex (ModuleCat.{u} A) ℕ) (n : ℕ) :
    (L.extend ComplexShape.embeddingDownNat).X (-(n : ℤ)) ≅ L.X n :=
  L.extendXIso ComplexShape.embeddingDownNat rfl

private noncomputable def coneNegIso (A : Type u) [CommRing A]
    (K L : ChainComplex (ModuleCat.{u} A) ℕ) (a : A)
    (e : ∀ n : ℕ, K.X (n + 1) ≃ₗ[A] L.X (n + 1) × L.X n) (n : ℕ) :
    (K.extend ComplexShape.embeddingDownNat).X (-((n + 1 : ℕ) : ℤ)) ≅
      (CochainComplex.mappingCone (a • 𝟙 (L.extend ComplexShape.embeddingDownNat))).X
        (-((n + 1 : ℕ) : ℤ)) :=
  downIso A K (n + 1) ≪≫ (e n).toModuleIso ≪≫
    (LinearEquiv.prodComm A (L.X (n + 1)) (L.X n)).toModuleIso ≪≫
    (ModuleCat.biprodIsoProd (L.X n) (L.X (n + 1))).symm ≪≫
    Limits.biprod.mapIso (L.extendXIso ComplexShape.embeddingDownNat
      (show -(n : ℤ) = -((n + 1 : ℕ) : ℤ) + 1 by omega)).symm
      (downIso A L (n + 1)).symm ≪≫
    (HomologicalComplex.homotopyCofiber.XIsoBiprod
      (a • 𝟙 (L.extend ComplexShape.embeddingDownNat))
      (-((n + 1 : ℕ) : ℤ)) (-((n + 1 : ℕ) : ℤ) + 1) rfl).symm

private noncomputable def coneZeroIso (A : Type u) [CommRing A]
    (K L : ChainComplex (ModuleCat.{u} A) ℕ) (a : A)
    (e₀ : K.X 0 ≃ₗ[A] L.X 0) :
    (K.extend ComplexShape.embeddingDownNat).X 0 ≅
      (CochainComplex.mappingCone (a • 𝟙 (L.extend ComplexShape.embeddingDownNat))).X 0 :=
  downIso A K 0 ≪≫ e₀.toModuleIso ≪≫ (downIso A L 0).symm ≪≫
    Limits.isoZeroBiprod (CochainComplex.isZero_of_isStrictlyLE
      (L.extend ComplexShape.embeddingDownNat) 0 1) ≪≫
    (HomologicalComplex.homotopyCofiber.XIsoBiprod
      (a • 𝟙 (L.extend ComplexShape.embeddingDownNat)) 0 1 rfl).symm

private noncomputable def coneCoordinatesIso (A : Type u) [CommRing A]
    (K L : ChainComplex (ModuleCat.{u} A) ℕ) (a : A)
    (e₀ : K.X 0 ≃ₗ[A] L.X 0)
    (e : ∀ n : ℕ, K.X (n + 1) ≃ₗ[A] L.X (n + 1) × L.X n) :
    ∀ i : ℤ, (K.extend ComplexShape.embeddingDownNat).X i ≅
      (CochainComplex.mappingCone (a • 𝟙 (L.extend ComplexShape.embeddingDownNat))).X i
  | .ofNat 0 => coneZeroIso A K L a e₀
  | .ofNat (n + 1) => by
      have hn : (0 : ℤ) < Int.ofNat (n + 1) := by
        change 0 < ((n + 1 : ℕ) : ℤ)
        omega
      exact Limits.IsZero.iso
        (CochainComplex.isZero_of_isStrictlyLE (K.extend ComplexShape.embeddingDownNat) 0 _ hn)
        ((CochainComplex.mappingCone.isZero_X_iff _ _).2
          ⟨CochainComplex.isZero_of_isStrictlyLE
              (L.extend ComplexShape.embeddingDownNat) 0 _ (by omega),
            CochainComplex.isZero_of_isStrictlyLE
              (L.extend ComplexShape.embeddingDownNat) 0 _ hn⟩)
  | .negSucc n => coneNegIso A K L a e n

private lemma coneBiprod_snd (A : Type u) [CommRing A]
    (L : CochainComplex (ModuleCat.{u} A) ℤ) (a : A) (i j : ℤ) (h : i + 1 = j) :
    (HomologicalComplex.homotopyCofiber.XIsoBiprod (a • 𝟙 L) i j h).inv ≫
      (CochainComplex.mappingCone.snd (a • 𝟙 L)).v i i (add_zero i) = Limits.biprod.snd := by
  obtain rfl := (ComplexShape.up ℤ).next_eq' h
  simp [CochainComplex.mappingCone.snd, HomologicalComplex.homotopyCofiber.sndX]

private lemma coneNegIso_fst (A : Type u) [CommRing A]
    (K L : ChainComplex (ModuleCat.{u} A) ℕ) (a : A)
    (e : ∀ n : ℕ, K.X (n + 1) ≃ₗ[A] L.X (n + 1) × L.X n) (n : ℕ) :
    (coneNegIso A K L a e n).hom ≫
      (CochainComplex.mappingCone.fst (a • 𝟙 (L.extend ComplexShape.embeddingDownNat))).1.v
        (-((n + 1 : ℕ) : ℤ)) (-((n + 1 : ℕ) : ℤ) + 1) rfl ≫
      (L.extendXIso ComplexShape.embeddingDownNat
        (show -(n : ℤ) = -((n + 1 : ℕ) : ℤ) + 1 by omega)).hom =
    (downIso A K (n + 1)).hom ≫
      ModuleCat.ofHom ((LinearMap.snd A (L.X (n + 1)) (L.X n)).comp (e n).toLinearMap) := by
  simp [coneNegIso, CochainComplex.mappingCone.fst,
    HomologicalComplex.homotopyCofiber.fstX, Category.assoc]
  rfl

private lemma coneNegIso_snd (A : Type u) [CommRing A]
    (K L : ChainComplex (ModuleCat.{u} A) ℕ) (a : A)
    (e : ∀ n : ℕ, K.X (n + 1) ≃ₗ[A] L.X (n + 1) × L.X n) (n : ℕ) :
    (coneNegIso A K L a e n).hom ≫
      (CochainComplex.mappingCone.snd (a • 𝟙 (L.extend ComplexShape.embeddingDownNat))).v
        (-((n + 1 : ℕ) : ℤ)) (-((n + 1 : ℕ) : ℤ)) (add_zero _) ≫
      (downIso A L (n + 1)).hom =
    (downIso A K (n + 1)).hom ≫
      ModuleCat.ofHom ((LinearMap.fst A (L.X (n + 1)) (L.X n)).comp (e n).toLinearMap) := by
  simp [coneNegIso, Category.assoc, reassoc_of% coneBiprod_snd]
  rfl

private lemma coneNegIso_fst' (A : Type u) [CommRing A]
    (K L : ChainComplex (ModuleCat.{u} A) ℕ) (a : A)
    (e : ∀ n : ℕ, K.X (n + 1) ≃ₗ[A] L.X (n + 1) × L.X n)
    (n : ℕ) (j : ℤ) (h : -((n + 1 : ℕ) : ℤ) + 1 = j) :
    (coneNegIso A K L a e n).hom ≫
      (CochainComplex.mappingCone.fst (a • 𝟙 (L.extend ComplexShape.embeddingDownNat))).1.v
        (-((n + 1 : ℕ) : ℤ)) j h ≫
      (L.extendXIso ComplexShape.embeddingDownNat
        (show -(n : ℤ) = j by omega)).hom =
    (downIso A K (n + 1)).hom ≫
      ModuleCat.ofHom ((LinearMap.snd A (L.X (n + 1)) (L.X n)).comp (e n).toLinearMap) := by
  subst j
  exact coneNegIso_fst A K L a e n

private lemma coneZeroIso_snd (A : Type u) [CommRing A]
    (K L : ChainComplex (ModuleCat.{u} A) ℕ) (a : A)
    (e₀ : K.X 0 ≃ₗ[A] L.X 0) :
    (coneZeroIso A K L a e₀).hom ≫
      (CochainComplex.mappingCone.snd (a • 𝟙 (L.extend ComplexShape.embeddingDownNat))).v
        0 0 (add_zero _) ≫ (downIso A L 0).hom =
    (downIso A K 0).hom ≫ e₀.toModuleIso.hom := by
  simp [coneZeroIso, Category.assoc, CochainComplex.mappingCone.snd]

set_option backward.isDefEq.respectTransparency false in
private lemma coneNegIso_comm (A : Type u) [CommRing A]
    (K L : ChainComplex (ModuleCat.{u} A) ℕ) (a : A)
    (e : ∀ n : ℕ, K.X (n + 1) ≃ₗ[A] L.X (n + 1) × L.X n)
    (hd : ∀ (n : ℕ) (x : K.X (n + 2)), e n (K.d (n + 2) (n + 1) x) =
      (L.d (n + 2) (n + 1) (e (n + 1) x).1 + a • (e (n + 1) x).2,
        -L.d (n + 1) n (e (n + 1) x).2)) (n : ℕ) :
    (coneNegIso A K L a e (n + 1)).hom ≫
      (CochainComplex.mappingCone (a • 𝟙 (L.extend ComplexShape.embeddingDownNat))).d
        (-((n + 2 : ℕ) : ℤ)) (-((n + 1 : ℕ) : ℤ)) =
    (K.extend ComplexShape.embeddingDownNat).d
      (-((n + 2 : ℕ) : ℤ)) (-((n + 1 : ℕ) : ℤ)) ≫
      (coneNegIso A K L a e n).hom := by
  let φ := a • 𝟙 (L.extend ComplexShape.embeddingDownNat)
  apply CochainComplex.mappingCone.ext_to φ (-((n + 1 : ℕ) : ℤ))
    (-((n + 1 : ℕ) : ℤ) + 1) rfl
  · apply (cancel_mono (L.extendXIso ComplexShape.embeddingDownNat
      (show -(n : ℤ) = -((n + 1 : ℕ) : ℤ) + 1 by omega)).hom).1
    simp only [Category.assoc]
    rw [CochainComplex.mappingCone.d_fst_v_assoc φ _ _ _ (by omega) rfl]
    dsimp only [φ]
    rw [L.extend_d_eq ComplexShape.embeddingDownNat (i := n + 1) (j := n)
      (i' := -((n + 1 : ℕ) : ℤ)) (j' := -((n + 1 : ℕ) : ℤ) + 1)
      rfl (by change -(n : ℤ) = -((n + 1 : ℕ) : ℤ) + 1; omega),
      K.extend_d_eq ComplexShape.embeddingDownNat (i := n + 2) (j := n + 1)
        (i' := -((n + 2 : ℕ) : ℤ)) (j' := -((n + 1 : ℕ) : ℤ)) rfl rfl]
    simp only [Category.assoc, Preadditive.neg_comp, Preadditive.comp_neg,
      Iso.inv_hom_id, Category.comp_id]
    simp only [reassoc_of% coneNegIso_fst', coneNegIso_fst]
    simp only [downIso, Iso.inv_hom_id_assoc, ← Preadditive.comp_neg]
    apply (cancel_epi (K.extendXIso ComplexShape.embeddingDownNat
      (show ComplexShape.embeddingDownNat.f (n + 2) = -((n + 2 : ℕ) : ℤ) from rfl)).hom).2
    ext x
    exact (congrArg Prod.snd (hd n x)).symm
  · apply (cancel_mono (downIso A L (n + 1)).hom).1
    simp only [Category.assoc]
    rw [CochainComplex.mappingCone.d_snd_v_assoc φ _ _ (by omega)]
    dsimp only [φ]
    rw [L.extend_d_eq ComplexShape.embeddingDownNat (i := n + 2) (j := n + 1)
      (i' := -((n + 2 : ℕ) : ℤ)) (j' := -((n + 1 : ℕ) : ℤ)) rfl rfl,
      K.extend_d_eq ComplexShape.embeddingDownNat (i := n + 2) (j := n + 1)
        (i' := -((n + 2 : ℕ) : ℤ)) (j' := -((n + 1 : ℕ) : ℤ)) rfl rfl]
    simp only [HomologicalComplex.smul_f_apply, HomologicalComplex.id_f,
      Preadditive.add_comp, Preadditive.comp_add, Category.assoc,
      Linear.comp_smul, Linear.smul_comp, Category.comp_id]
    have hf := coneNegIso_fst' A K L a e (n + 1) (-((n + 1 : ℕ) : ℤ)) (by omega)
    have hs := coneNegIso_snd A K L a e (n + 1)
    have ht := coneNegIso_snd A K L a e n
    dsimp only [downIso] at hf hs ht ⊢
    simp only [Iso.inv_hom_id_assoc, hf, reassoc_of% hs, ht]
    simp only [Iso.inv_hom_id, Category.comp_id]
    simp only [← Linear.comp_smul, ← Preadditive.comp_add]
    apply (cancel_epi (K.extendXIso ComplexShape.embeddingDownNat
      (show ComplexShape.embeddingDownNat.f (n + 2) = -((n + 2 : ℕ) : ℤ) from rfl)).hom).2
    ext x
    change a • (e (n + 1) x).2 + L.d (n + 2) (n + 1) (e (n + 1) x).1 =
      (e n (K.d (n + 2) (n + 1) x)).1
    simpa only [add_comm] using (congrArg Prod.fst (hd n x)).symm

set_option backward.isDefEq.respectTransparency false in
private lemma coneZeroIso_comm (A : Type u) [CommRing A]
    (K L : ChainComplex (ModuleCat.{u} A) ℕ) (a : A)
    (e₀ : K.X 0 ≃ₗ[A] L.X 0)
    (e : ∀ n : ℕ, K.X (n + 1) ≃ₗ[A] L.X (n + 1) × L.X n)
    (h₀ : ∀ x : K.X 1, e₀ (K.d 1 0 x) =
      L.d 1 0 (e 0 x).1 + a • (e 0 x).2) :
    (coneNegIso A K L a e 0).hom ≫
      (CochainComplex.mappingCone (a • 𝟙 (L.extend ComplexShape.embeddingDownNat))).d (-1) 0 =
    (K.extend ComplexShape.embeddingDownNat).d (-1) 0 ≫
      (coneZeroIso A K L a e₀).hom := by
  let φ := a • 𝟙 (L.extend ComplexShape.embeddingDownNat)
  apply CochainComplex.mappingCone.ext_to φ 0 1 rfl
  · exact (CochainComplex.isZero_of_isStrictlyLE
      (L.extend ComplexShape.embeddingDownNat) 0 1).eq_of_tgt _ _
  · apply (cancel_mono (downIso A L 0).hom).1
    simp only [Category.assoc]
    rw [CochainComplex.mappingCone.d_snd_v_assoc φ _ _ (by omega)]
    dsimp only [φ]
    rw [L.extend_d_eq ComplexShape.embeddingDownNat (i := 1) (j := 0)
      (i' := -1) (j' := 0) rfl rfl,
      K.extend_d_eq ComplexShape.embeddingDownNat (i := 1) (j := 0)
        (i' := -1) (j' := 0) rfl rfl]
    simp only [HomologicalComplex.smul_f_apply, HomologicalComplex.id_f,
      Preadditive.add_comp, Preadditive.comp_add, Category.assoc,
      Linear.comp_smul, Linear.smul_comp, Category.comp_id]
    have hf := coneNegIso_fst' A K L a e 0 0 (by omega)
    have hs := coneNegIso_snd A K L a e 0
    have ht := coneZeroIso_snd A K L a e₀
    dsimp only [downIso] at hf hs ht ⊢
    simp only [Int.natCast_one, Nat.reduceAdd] at hf hs ht
    simp only [Iso.inv_hom_id_assoc, hf, reassoc_of% hs, ht]
    simp only [Iso.inv_hom_id, Category.comp_id]
    simp only [← Linear.comp_smul, ← Preadditive.comp_add]
    apply (cancel_epi (K.extendXIso ComplexShape.embeddingDownNat
      (show ComplexShape.embeddingDownNat.f 1 = -1 from rfl)).hom).2
    ext x
    change a • (e 0 x).2 + L.d 1 0 (e 0 x).1 = e₀ (K.d 1 0 x)
    simpa only [add_comm] using (h₀ x).symm

/-- Degreewise scalar-cone coordinates compatible with the differentials assemble
into an isomorphism after extension from homological degree `n` to cochain degree `-n`.
Source: Stacks Project, Tags 0628 and 0629; the matrix of the cone differential.
(blueprint: lem-pc-chain-cone-coordinates-iso).

Proof: In cochain degree `-(n+1)`, use `e n` followed by the exchange of the two
factors to identify `K_(n+1)` with `L_n ⊕ L_(n+1)`. These are the source-shift
and target summands of the mapping cone. In degree zero use `e₀` and the
canonical identification of the cone with `L_0`, since the extended `L` in cochain degree
one is zero. In strictly positive cochain degrees both complexes are zero;
use the unique isomorphism between zero objects. In negative degrees the
higher differential equation gives, in this summand order, the matrix
`(y,x) ↦ (-d y, d x + a • y)`, exactly Mathlib's cone differential. The
separate degree-one equation verifies the differential into cochain degree
zero. The differential out of degree zero is zero on both sides. These checks
show that the degreewise isomorphisms commute with every differential.
Apply `HomologicalComplex.Hom.isoOfComponents`. No regularity or nonzero
hypothesis is used; this includes zero modules, the zero ring, and zero scalars. -/
theorem scalarCone_iso_of_coordinates (A : Type u) [CommRing A]
    (K L : ChainComplex (ModuleCat.{u} A) ℕ) (a : A)
    (e₀ : K.X 0 ≃ₗ[A] L.X 0)
    (e : ∀ n : ℕ, K.X (n + 1) ≃ₗ[A] L.X (n + 1) × L.X n)
    (h₀ : ∀ x : K.X 1, e₀ (K.d 1 0 x) =
      L.d 1 0 (e 0 x).1 + a • (e 0 x).2)
    (hd : ∀ (n : ℕ) (x : K.X (n + 2)), e n (K.d (n + 2) (n + 1) x) =
      (L.d (n + 2) (n + 1) (e (n + 1) x).1 + a • (e (n + 1) x).2,
        -L.d (n + 1) n (e (n + 1) x).2)) :
    Nonempty (K.extend ComplexShape.embeddingDownNat ≅
      CochainComplex.mappingCone
        (a • 𝟙 (L.extend ComplexShape.embeddingDownNat))) := by
  refine ⟨HomologicalComplex.Hom.isoOfComponents (coneCoordinatesIso A K L a e₀ e) ?_⟩
  intro i j hij
  change i + 1 = j at hij
  subst j
  cases i with
  | ofNat n =>
      apply ((CochainComplex.mappingCone.isZero_X_iff _ _).2
        ⟨CochainComplex.isZero_of_isStrictlyLE
            (L.extend ComplexShape.embeddingDownNat) 0 _
            (by change 0 < (n : ℤ) + 1 + 1; omega),
          CochainComplex.isZero_of_isStrictlyLE
            (L.extend ComplexShape.embeddingDownNat) 0 _
            (by change 0 < (n : ℤ) + 1; omega)⟩).eq_of_tgt
  | negSucc n =>
      cases n with
      | zero => exact coneZeroIso_comm A K L a e₀ e h₀
      | succ n =>
          have hi : Int.negSucc (n + 1) + 1 = Int.negSucc n := by omega
          rw [hi]
          exact coneNegIso_comm A K L a e hd n

end ChainComplex
