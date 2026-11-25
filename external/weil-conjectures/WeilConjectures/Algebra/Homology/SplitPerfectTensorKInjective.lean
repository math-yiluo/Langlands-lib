/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import Mathlib.CategoryTheory.Monoidal.Rigid.Braided
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalFree
import WeilConjectures.Algebra.Homology.BoundedAboveFlatSheafKFlat
import WeilConjectures.Algebra.Homology.Monoidal.Dual
import WeilConjectures.CategoryTheory.Monoidal.Dualizable
import WeilConjectures.CategoryTheory.Monoidal.Rigid.Flat
import WeilConjectures.FromJoel.Algebra.Homology.HomotopyCategory.Monoidal
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.OfEquivalence

/-!
# Tensoring K-injectives with bounded split-projective complexes

Source: Stacks Project, Cohomology on Sites, Tags 0A96, 06YQ, 0FPR;
Modules on Sites, Tag 0FNY; More on Algebra, Tag 0FNK
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

private lemma isDualizable_finite_power
    {A : Type*} [Category A] [Preadditive A] [MonoidalCategory A]
    [MonoidalPreadditive A] [HasFiniteBiproducts A]
    (U : A) (hU : IsDualizable U) (n : ℕ) :
    IsDualizable (∏ᶜ fun _ : Fin n ↦ U) := by
  let : HasBinaryBiproducts A := HasBinaryBiproducts.of_hasBinaryProducts
  induction n with
  | zero =>
    apply IsZero.isDualizable
    rw [IsZero.iff_id_eq_zero]
    apply Pi.hom_ext
    intro i
    exact Fin.elim0 i
  | succ n hn =>
    let V := ∏ᶜ fun _ : Fin n ↦ U
    let e : U ⊞ V ≅ ∏ᶜ (fun _ : Fin (n + 1) ↦ U) :=
      { hom := Pi.lift (Fin.cases biprod.fst (fun i ↦ biprod.snd ≫ Pi.π _ i))
        inv := biprod.lift (Pi.π _ 0) (Pi.lift fun i : Fin n ↦ Pi.π _ i.succ)
        hom_inv_id := by
          apply biprod.hom_ext
          · simp
          · apply Pi.hom_ext
            intro i
            simp
        inv_hom_id := by
          apply Pi.hom_ext
          intro i
          refine Fin.cases ?_ (fun j ↦ ?_) i
          · simp
          · simp }
    exact (hU.biprod hn).of_iso e

set_option synthInstance.maxSize 2048 in
/-- Tensoring a K-injective complex with a bounded complex of finite-free retracts
preserves K-injectivity. Neither boundedness of `I` nor a zero differential on `P` is required.
Source: Stacks Project, Tags 0A96, 06YQ, 0FPR, 0FNY, 0FNK
(auxiliary; not a blueprint node).

Proof:
1. Finite powers of the tensor unit are dualizable, by induction using the zero object
   and binary biproducts. Dualizability passes to the given retracts, so every term of
   `P` has a right dual.
2. Use the source library's `P.rightDual` and `exactPairingRightDual` to construct a
   dual complex `D` and its evaluation and coevaluation. The boundedness of `P` gives
   bounds `[-b,-a]` for `D`. This construction includes the differential signs.
3. Every term of `D` is dualizable, hence flat. The bounded-above flat criterion
   (`lem-pc-bounded-above-flat-kflat-site`) therefore makes `D` K-flat.
4. The monoidal quotient to the homotopy category preserves the dual pair. Thus
   tensoring on the right with `D` is left adjoint to tensoring on the right with `P`.
   For acyclic `A`, a map `A → I ⊗ P` corresponds to a map `A ⊗ D → I` there.
   The latter is zero because `A ⊗ D` is acyclic and `I` is K-injective. The adjunction
   preserves zero, so the original map is zero in the homotopy category and hence
   admits a null homotopy. -/
theorem isKInjective_mapBifunctor_of_bounded_splitFree
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]
    {R : Sheaf J CommRingCat.{u}}
    (I P : CochainComplex
      (SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ)
    [I.IsKInjective]
    (hbounded : ∃ a b : ℤ, ∀ r : ℤ, r < a ∨ b < r → IsZero (P.X r))
    (hsplit : ∀ r : ℤ, ∃ N : ℕ,
      ∃ i : P.X r ⟶ ∏ᶜ (fun _ : Fin N =>
        SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)),
      ∃ p : (∏ᶜ (fun _ : Fin N =>
        SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)))
          ⟶ P.X r, i ≫ p = 𝟙 (P.X r)) :
    (mapBifunctor I P
      (@MonoidalCategory.curriedTensor _ _ (SheafOfModules.monoidalCategory R))).IsKInjective := by
  classical
  let M := SheafOfModules.{u}
    ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.symmetricCategory R
  let : MonoidalPreadditive M :=
    { whiskerLeft_zero := fun {X Y Z} ↦ (MonoidalCategory.tensorLeft X).map_zero Y Z
      zero_whiskerRight := fun {X Y Z} ↦ (MonoidalCategory.tensorRight X).map_zero Y Z
      whiskerLeft_add := fun {X Y Z} f g ↦ (MonoidalCategory.tensorLeft X).map_add (f := f) (g := g)
      add_whiskerRight := fun {X Y Z} f g ↦
        (MonoidalCategory.tensorRight X).map_add (f := f) (g := g) }
  -- Closedness supplies preservation of coproducts for the total tensor construction.
  let : MonoidalClosed M := SheafOfModules.monoidalClosed.{u} (R := R)
  let : HasFiniteBiproducts M := HasFiniteBiproducts.of_hasFiniteProducts
  have hdual (n : ℤ) : IsDualizable (P.X n) := by
    obtain ⟨N, i, p, hip⟩ := hsplit n
    exact IsDualizable.of_retract ⟨i, p, hip⟩
      (isDualizable_finite_power _ (isDualizable_unit) N)
  let : ∀ n, HasRightDual (P.X n) := fun n ↦ (hdual n).some
  obtain ⟨a, b, hab⟩ := hbounded
  have : P.IsStrictlyGE a := (isStrictlyGE_iff P a).2 (fun n hn ↦ hab n (Or.inl hn))
  have : P.IsStrictlyLE b := (isStrictlyLE_iff P b).2 (fun n hn ↦ hab n (Or.inr hn))
  let D := P.rightDual
  have hDflat (n : ℤ) : SheafOfModules.IsFlat (D.X n) := by
    have hd : IsDualizable (D.X n) :=
      ⟨{ rightDual := P.X (-n)
         exact := BraidedCategory.exactPairing_swap (P.X (-n)) (P.X (-n))ᘁ }⟩
    exact hd.flat.2
  have hD : D.IsKFlatTensor := isKFlat_of_boundedAbove_flat D
    ⟨-a, fun n hn ↦ D.isZero_of_isStrictlyLE (-a) n hn⟩ hDflat
  let := exactPairingRightDual P a b
  let := BraidedCategory.exactPairing_swap P D
  let Q := HomotopyCategory.quotient M (.up ℤ)
  let : ExactPairing (Q.obj D) (Q.obj P) := ExactPairing.map Q D P
  let adj := tensorRightAdjunction (Q.obj D) (Q.obj P)
  have := adj.isLeftAdjoint
  refine ⟨fun {A} f hA ↦ ⟨HomotopyCategory.homotopyOfEq _ _ ?_⟩⟩
  change Q.map f = Q.map 0
  rw [Functor.map_zero]
  apply (adj.homEquiv (Q.obj A) (Q.obj I)).symm.injective
  have hg : (adj.homEquiv (Q.obj A) (Q.obj I)).symm (Q.map f) = 0 := by
    apply IsKInjective.rightOrthogonal I
    exact (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).2 (hD A hA)
  rw [hg]
  symm
  simp only [Adjunction.homEquiv_counit, Functor.map_zero, zero_comp]

end CochainComplex
