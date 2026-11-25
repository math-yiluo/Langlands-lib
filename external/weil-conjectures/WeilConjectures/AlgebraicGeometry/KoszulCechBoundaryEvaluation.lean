/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.ModuleHomComplex
public import WeilConjectures.AlgebraicGeometry.PrincipalOpenCechTotal
public import WeilConjectures.AlgebraicGeometry.KoszulOpenSystem
import WeilConjectures.RingTheory.KoszulGeneratorChainMap

/-! # Increasing-wedge Koszul boundary evaluation

Source: Stacks Project, Tags 08D0 and 08D1.
(blueprint: lem-sc-koszul-cech-boundary-evaluation).
-/

@[expose] public section

universe uK

open CategoryTheory

namespace AlgebraicGeometry

variable (A : Type uK) [CommRing A] (r : ℕ) (f : Fin r → A)
variable (F : CochainComplex
  (SheafOfModules.{uK} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ)

private theorem ordered_erase (S : Finset (Fin r)) (k : ℕ) (hS : S.card = k + 1)
    (i : Fin (k + 1)) (hE : (S.erase (S.orderEmbOfFin hS i)).card = k) :
    (fun t ↦ S.orderEmbOfFin hS (i.succAbove t)) =
      (S.erase (S.orderEmbOfFin hS i)).orderEmbOfFin hE := by
  apply Finset.orderEmbOfFin_unique hE
  · intro t
    apply Finset.mem_erase.mpr
    exact ⟨fun h ↦ Fin.succAbove_ne i t ((S.orderEmbOfFin hS).injective h),
      S.orderEmbOfFin_mem hS _⟩
  · exact (S.orderEmbOfFin hS).strictMono.comp (Fin.strictMono_succAbove i)

private theorem ordered_position (S : Finset (Fin r)) (k : ℕ) (hS : S.card = k)
    (i : Fin k) :
    (S.filter (fun j ↦ j < S.orderEmbOfFin hS i)).card = i.val := by
  classical
  have hset : S.filter (fun j ↦ j < S.orderEmbOfFin hS i) =
      (Finset.Iio i).image (S.orderEmbOfFin hS) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_Iio]
    constructor
    · rintro ⟨hj, hlt⟩
      obtain ⟨t, ht⟩ := (S.orderIsoOfFin hS).surjective ⟨j, hj⟩
      have ht' : S.orderEmbOfFin hS t = j := congrArg Subtype.val ht
      exact ⟨t, (S.orderEmbOfFin hS).lt_iff_lt.mp (by simpa [ht'] using hlt), ht'⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨S.orderEmbOfFin_mem hS t, (S.orderEmbOfFin hS).strictMono ht⟩
  rw [hset, Finset.card_image_of_injective _ (S.orderEmbOfFin hS).injective]
  simp

private theorem boundary_sorted (g : Fin r → A) (S : Finset (Fin r))
    (k : ℕ) (hS : S.card = k + 1) :
    ExteriorAlgebra.koszulBoundary A r g k
        (exteriorPower.ιMulti A (k + 1)
          (fun i ↦ Finsupp.single (S.orderEmbOfFin hS i) (1 : A))) =
      ∑ j : S, ((-1 : A) ^ (S.filter (fun t ↦ t < j.val)).card * g j.val) •
        exteriorPower.ιMulti A k
          (fun i ↦ Finsupp.single ((S.erase j.val).orderEmbOfFin
            (show (S.erase j.val).card = k by
              have := Finset.card_erase_add_one j.property
              omega) i) (1 : A)) := by
  classical
  rw [ExteriorAlgebra.boundary_wedge]
  rw [← (S.orderIsoOfFin hS).toEquiv.sum_comp]
  apply Finset.sum_congr rfl
  intro i _
  have hj : ((S.orderIsoOfFin hS).toEquiv i).val = S.orderEmbOfFin hS i := rfl
  simp only [hj, Finsupp.linearCombination_single, one_smul]
  rw [ordered_position r S (k + 1) hS i]
  have hs : (-1 : A) ^ (i.val + 2) = (-1 : A) ^ i.val := by
    rw [pow_add, neg_one_sq, mul_one]
  rw [hs]
  congr 2
  funext t
  dsimp only [Function.comp_apply]
  congr 1
  exact congrFun (ordered_erase r S k hS i _) t

private theorem evaluate_extend_transport
    (K : ChainComplex (ModuleCat.{uK} A) ℕ) (n : ℤ)
    (z : CochainComplex.HomComplex.Cochain
      (K.extend ComplexShape.embeddingDownNat)
      (((affineOpenSections A ⊤).mapHomologicalComplex (ComplexShape.up ℤ)).obj F) n)
    (i : ℕ) (p p' q q' : ℤ)
    (hp : ComplexShape.embeddingDownNat.f i = p)
    (hp' : ComplexShape.embeddingDownNat.f i = p') (hq : q = q')
    (hpq : p + n = q) (hpq' : p' + n = q') (x : K.X i) :
    z.v p' q' hpq' ((K.extendXIso ComplexShape.embeddingDownNat hp').inv x) =
      (affineOpenSections A ⊤).map (eqToHom (congrArg F.X hq))
        (z.v p q hpq ((K.extendXIso ComplexShape.embeddingDownNat hp).inv x)) := by
  have he : p = p' := hp.symm.trans hp'
  cases he
  cases hq
  rw [eqToHom_refl, (affineOpenSections A ⊤).map_id]
  rfl

/-- Evaluation of the negative tail boundary on an increasing wedge, before localization.
Source: Stacks Project, Tags 08D0 and 08D1, the first differential calculation.
(blueprint: lem-sc-koszul-cech-boundary-evaluation)
Proof: since card(J)>1, both tail degrees and every erased subset are supported.
Use extendXIso to transport the differential to minus koszulBoundary. Include the
exterior powers into the exterior algebra and apply the contraction recursion
contractLeft_ι_mul to the increasing product of basis generators. This gives one
summand per deleted generator, with coefficient (-1)^position*f(j)^(e+1).
The increasing enumeration of the erased subset is the original enumeration with
that position removed, so position equals the number of indices smaller than j.
Apply the linear component of z to this finite sum. Its source degree is
1-card(J.erase j)=2-card(J), by card_erase_add_one. The corresponding target
degree equality is principalCech_erase_degree; transporting through z gives the
coefficient eqToHom displayed here. Linearity pulls out the negative and scalars.
There is no division, restriction, Hom differential sign or totalization sign
in this identity. The smallest supported subset has two indices, where the
formula is minus (f(i)^(e+1)*e_j - f(j)^(e+1)*e_i). -/
theorem koszulCechBoundary_evaluation (e : ℕ)
    (B : ∀ J : {J : Finset (Fin r) // J.Nonempty},
      ((koszulOpenTail A r f e).extend ComplexShape.embeddingDownNat).X
        (1 - (J.val.card : ℤ)))
    (hB : ∀ J, B J =
      ((koszulOpenTail A r f e).extendXIso ComplexShape.embeddingDownNat
        (show ComplexShape.embeddingDownNat.f (J.val.card - 1) =
          1 - (J.val.card : ℤ) by
          simp only [ComplexShape.embeddingDownNat_f]
          have h : 0 < J.val.card := Finset.card_pos.mpr J.property
          omega)).inv
        (exteriorPower.ιMulti A (J.val.card - 1 + 1)
          (fun i ↦ Finsupp.single (J.val.orderEmbOfFin
            (show J.val.card = J.val.card - 1 + 1 by
              have h : 0 < J.val.card := Finset.card_pos.mpr J.property
              omega) i) (1 : A)))) (n : ℤ)
    (z : CochainComplex.HomComplex.Cochain
      ((koszulOpenTail A r f e).extend ComplexShape.embeddingDownNat)
      (((affineOpenSections A ⊤).mapHomologicalComplex (ComplexShape.up ℤ)).obj F) n)
    (J : {J : Finset (Fin r) // J.Nonempty}) (hJ : 1 < J.val.card) :
    ((((koszulOpenTail A r f e).extend ComplexShape.embeddingDownNat).d
      (1 - (J.val.card : ℤ)) (2 - (J.val.card : ℤ)) ≫
      z.v (2 - (J.val.card : ℤ)) ((n + 1) + 1 - (J.val.card : ℤ)) (by ring)) (B J)) =
    -(∑ j : J.val, if h : (J.val.erase j.val).Nonempty then
      ((-1 : A) ^ ((J.val.filter (fun i ↦ i < j.val)).card) * f j.val ^ (e + 1)) •
        (affineOpenSections A ⊤).map
          (eqToHom (congrArg F.X
            (principalCech_erase_degree r J.val j.val j.property n)))
          ((z.v (1 - ((J.val.erase j.val).card : ℤ))
            (n + 1 - ((J.val.erase j.val).card : ℤ)) (by ring))
              (B ⟨J.val.erase j.val, h⟩))
      else 0) := by
  classical
  have basis (T : {T : Finset (Fin r) // T.Nonempty}) (l : ℕ)
      (hl : T.val.card - 1 = l)
      (hp : ComplexShape.embeddingDownNat.f l = 1 - (T.val.card : ℤ)) :
      B T = ((koszulOpenTail A r f e).extendXIso
        ComplexShape.embeddingDownNat hp).inv
          (exteriorPower.ιMulti A (l + 1)
            (fun i ↦ Finsupp.single (T.val.orderEmbOfFin (by
              have := Finset.card_pos.mpr T.property
              omega) i) (1 : A))) := by
    subst l
    exact hB T
  let k := J.val.card - 2
  have hcard : J.val.card = k + 2 := by dsimp [k]; omega
  have hsub : J.val.card - 1 = k + 1 := by omega
  have hi : ComplexShape.embeddingDownNat.f (k + 1) =
      1 - (J.val.card : ℤ) := by simp only [ComplexShape.embeddingDownNat_f]; omega
  have hj : ComplexShape.embeddingDownNat.f k =
      2 - (J.val.card : ℤ) := by simp only [ComplexShape.embeddingDownNat_f]; omega
  have hBJ : B J =
      ((koszulOpenTail A r f e).extendXIso ComplexShape.embeddingDownNat hi).inv
        (exteriorPower.ιMulti A (k + 1 + 1)
          (fun i ↦ Finsupp.single (J.val.orderEmbOfFin (by omega) i) (1 : A))) := by
    exact basis J (k + 1) hsub hi
  rw [ModuleCat.comp_apply, hBJ]
  rw [HomologicalComplex.extend_d_eq _ _ hi hj]
  simp only [ModuleCat.comp_apply, Iso.inv_hom_id_apply]
  have hd : (koszulOpenTail A r f e).d (k + 1) k =
      -ModuleCat.ofHom
        (ExteriorAlgebra.koszulBoundary A r (fun i ↦ f i ^ (e + 1)) (k + 1)) := by
    dsimp only [koszulOpenTail]
    rw [ChainComplex.of_d]
  rw [hd]
  change z.v _ _ _ (((koszulOpenTail A r f e).extendXIso
    ComplexShape.embeddingDownNat hj).inv
      (-(ExteriorAlgebra.koszulBoundary A r (fun i ↦ f i ^ (e + 1)) (k + 1)
        (exteriorPower.ιMulti A (k + 1 + 1)
          (fun i ↦ Finsupp.single (J.val.orderEmbOfFin hcard i) (1 : A)))))) = _
  rw [boundary_sorted A r (fun i ↦ f i ^ (e + 1)) J.val (k + 1) hcard]
  simp only [map_neg, map_sum, map_smul]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  have hE : (J.val.erase j.val).card = k + 1 := by
    have := Finset.card_erase_add_one j.property
    omega
  have hne : (J.val.erase j.val).Nonempty := Finset.card_pos.mp (by omega)
  rw [dite_eq_left hne]
  congr 1
  have he : ComplexShape.embeddingDownNat.f k =
      1 - ((J.val.erase j.val).card : ℤ) := by
    simp only [ComplexShape.embeddingDownNat_f]
    omega
  rw [basis ⟨J.val.erase j.val, hne⟩ k (by dsimp; omega) he]
  exact evaluate_extend_transport A F (koszulOpenTail A r f e) n z k
    _ _ _ _ he hj (principalCech_erase_degree r J.val j.val j.property n) _ _ _

end AlgebraicGeometry
