import Langlands.Automorphic.TwoBlockConstantTermRadical
import Langlands.Global.ArchimedeanBlockLieInclusions
import Langlands.Global.ArchimedeanComplexifiedPlaces
import Langlands.Algebra.EnvelopingPiCenter
import Langlands.Representation.Archimedean.TwoBlockLeviCenterIdeals

/-! # Cofinite center ideals for adelic two-block constant terms -/

noncomputable section
universe u

open scoped Classical TensorProduct
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic

open NumberField
open Langlands.Algebra
open Langlands.Archimedean Langlands.Archimedean.TwoBlockEnveloping
open Langlands.Global.ArchimedeanGL

attribute [local instance 100] LieRing.ofAssociativeRing

variable (F : Type u) [Field F] [NumberField F]

local notation "M" => fun n : ℕ => Matrix (Fin n) (Fin n) ℂ
local notation "U" => EnvelopingAlgebra F
local notation "Z" => EnvelopingCenter F
local notation "UP" => VermaGL.glU
local notation "ZP" => VermaGL.center
local notation "Place" => Fin (Fintype.card (ComplexifiedPlace F))
local notation "Mixed" => mixedEmbedding.mixedSpace F

private def placeIndex : ComplexifiedPlace F ≃ Place := Fintype.equivFin _

/-- The actual complexified archimedean Lie algebra in its numbered matrix factors. -/
def archimedeanPlaceLieCoordinates (n : ℕ) : ComplexLieAlgebra F n ≃ₗ⁅ℂ⁆ (Place → M n) :=
  (complexLieMatrixCoordinates F n).trans
    (((Matrix.piAlgEquiv ℂ (β := fun _ : ComplexifiedPlace F => ℂ) (n := Fin n)).trans
      (AlgEquiv.piCongrLeft' (R := ℂ) (fun _ : ComplexifiedPlace F => M n)
        (placeIndex F))).toLieEquiv)

theorem archimedeanPlaceLieCoordinates_apply (n : ℕ) (X : ComplexLieAlgebra F n)
    (r : Place) (i j : Fin n) :
    archimedeanPlaceLieCoordinates F n X r i j =
      complexLieMatrixCoordinates F n X i j ((placeIndex F).symm r) :=
  rfl

private def placeLieInclusion (n : ℕ) (r : Place) : M n →ₗ⁅ℂ⁆ ComplexLieAlgebra F n :=
  (archimedeanPlaceLieCoordinates F n).symm.toLieHom.comp
    (LieEnvelopingEquiv.coordinateLieInclusion ℂ (M n) r)

private def placeEnvelopingInclusion (n : ℕ) (r : Place) : UP n →ₐ[ℂ] U n :=
  LieEnvelopingEquiv.map (placeLieInclusion F n r)

private def placeCenterCoordinates (n : ℕ) :
    Z n ≃ₐ[ℂ] (Subalgebra.center ℂ (UniversalEnvelopingAlgebra ℂ (Place → M n))) :=
  LieEnvelopingEquiv.center (LieEnvelopingEquiv.enveloping (archimedeanPlaceLieCoordinates F n))

private def placeCenterInclusion (n : ℕ) (r : Place) : ZP n →ₐ[ℂ] Z n :=
  (placeCenterCoordinates F n).symm.toAlgHom.comp
    (LieEnvelopingEquiv.coordinateCenterInclusion ℂ (M n) r)

private theorem placeCenterInclusion_val (n : ℕ) (r : Place) (z : ZP n) :
    (placeCenterInclusion F n r z).val = placeEnvelopingInclusion F n r z.val := by
  change ((LieEnvelopingEquiv.center
    (LieEnvelopingEquiv.enveloping (archimedeanPlaceLieCoordinates F n))).symm
      (LieEnvelopingEquiv.coordinateCenterInclusion ℂ (M n) r z)).val = _
  have h : ∀ (z' : Subalgebra.center ℂ
      (UniversalEnvelopingAlgebra ℂ (Place → M n))),
      ((placeCenterCoordinates F n).symm z').val =
        (LieEnvelopingEquiv.enveloping (archimedeanPlaceLieCoordinates F n)).symm z'.val := by
    intro z'
    apply (LieEnvelopingEquiv.enveloping (archimedeanPlaceLieCoordinates F n)).injective
    rw [AlgEquiv.apply_symm_apply, ← LieEnvelopingEquiv.center_apply]
    change (placeCenterCoordinates F n ((placeCenterCoordinates F n).symm z')).val = _
    rw [AlgEquiv.apply_symm_apply]
  change ((placeCenterCoordinates F n).symm
    (LieEnvelopingEquiv.coordinateCenterInclusion ℂ (M n) r z)).val = _
  rw [h, LieEnvelopingEquiv.coordinateCenterInclusion_val]
  change ((LieEnvelopingEquiv.map (archimedeanPlaceLieCoordinates F n).symm.toLieHom).comp
    (LieEnvelopingEquiv.map (LieEnvelopingEquiv.coordinateLieInclusion ℂ (M n) r))) z.val = _
  rw [LieEnvelopingEquiv.map_comp]
  rfl

omit [NumberField F] in
private theorem complexifiedPlaceValue_zero (v : ComplexifiedPlace F) :
    complexifiedPlaceValue F 0 v = 0 := by
  rcases v with v | ⟨v, s⟩
  · simp [complexifiedPlaceValue]
  · cases s <;> simp [complexifiedPlaceValue]

variable (a b : ℕ)

local notation "e" => (finSumFinEquiv : Fin a ⊕ Fin b ≃ Fin (a + b))
local notation "h" => (rfl : a + b = a + b)

private theorem firstBlock_at_place (X : ComplexLieAlgebra F a) (r : Place) :
    archimedeanPlaceLieCoordinates F (a + b) (firstBlockComplexLieInclusion F h X) r =
      firstComplexMatrixBlockInclusion a b (archimedeanPlaceLieCoordinates F a X r) := by
  induction X using TensorProduct.inductionOn with
  | tmul c X =>
    ext i j
    obtain ⟨i, rfl⟩ := (e).surjective i
    obtain ⟨j, rfl⟩ := (e).surjective j
    rw [archimedeanPlaceLieCoordinates_apply, firstBlockComplexLieInclusion_tmul,
      complexLieMatrixCoordinates_tmul, firstBlockRealLieInclusion_matrix,
      blockDiagonalMatrixMap_apply]
    change c * complexifiedPlaceValue F
      ((Matrix.fromBlocks (realLieAlgebraToMatrix F a X) 0 0 0) ((e).symm (e i))
        ((e).symm (e j))) ((placeIndex F).symm r) =
      (Matrix.fromBlocks (archimedeanPlaceLieCoordinates F a (c ⊗ₜ[ℝ] X) r) 0 0 0)
        ((e).symm (e i)) ((e).symm (e j))
    simp only [Equiv.symm_apply_apply]
    cases i <;> cases j <;>
      simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
        Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply,
        archimedeanPlaceLieCoordinates_apply, complexLieMatrixCoordinates_tmul,
        complexifiedPlaceValue_zero, mul_zero]
  | add X Y hx hy => simp only [map_add, Pi.add_apply, hx, hy]

private theorem secondBlock_at_place (X : ComplexLieAlgebra F b) (r : Place) :
    archimedeanPlaceLieCoordinates F (a + b) (secondBlockComplexLieInclusion F h X) r =
      secondComplexMatrixBlockInclusion a b (archimedeanPlaceLieCoordinates F b X r) := by
  induction X using TensorProduct.inductionOn with
  | tmul c X =>
    ext i j
    obtain ⟨i, rfl⟩ := (e).surjective i
    obtain ⟨j, rfl⟩ := (e).surjective j
    rw [archimedeanPlaceLieCoordinates_apply, secondBlockComplexLieInclusion_tmul,
      complexLieMatrixCoordinates_tmul, secondBlockRealLieInclusion_matrix,
      blockDiagonalMatrixMap_apply]
    change c * complexifiedPlaceValue F
      ((Matrix.fromBlocks 0 0 0 (realLieAlgebraToMatrix F b X)) ((e).symm (e i))
        ((e).symm (e j))) ((placeIndex F).symm r) =
      (Matrix.fromBlocks 0 0 0 (archimedeanPlaceLieCoordinates F b (c ⊗ₜ[ℝ] X) r))
        ((e).symm (e i)) ((e).symm (e j))
    simp only [Equiv.symm_apply_apply]
    cases i <;> cases j <;>
      simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
        Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply,
        archimedeanPlaceLieCoordinates_apply, complexLieMatrixCoordinates_tmul,
        complexifiedPlaceValue_zero, mul_zero]
  | add X Y hx hy => simp only [map_add, Pi.add_apply, hx, hy]

private theorem firstBlockEnvelopingInclusion_place (r : Place) :
    (firstBlockEnvelopingInclusion F h).comp (placeEnvelopingInclusion F a r) =
      (placeEnvelopingInclusion F (a + b) r).comp (firstComplexMatrixBlockEnveloping a b) := by
  change (LieEnvelopingEquiv.map (firstBlockComplexLieInclusion F h)).comp
      (LieEnvelopingEquiv.map (placeLieInclusion F a r)) =
    (LieEnvelopingEquiv.map (placeLieInclusion F (a + b) r)).comp
      (LieEnvelopingEquiv.map (firstComplexMatrixBlockInclusion a b))
  rw [LieEnvelopingEquiv.map_comp, LieEnvelopingEquiv.map_comp]
  congr 1
  apply LieHom.ext
  intro X
  apply (archimedeanPlaceLieCoordinates F (a + b)).injective
  funext s
  change archimedeanPlaceLieCoordinates F (a + b)
      (firstBlockComplexLieInclusion F h (placeLieInclusion F a r X)) s =
    archimedeanPlaceLieCoordinates F (a + b)
      (placeLieInclusion F (a + b) r (firstComplexMatrixBlockInclusion a b X)) s
  rw [firstBlock_at_place F a b]
  change firstComplexMatrixBlockInclusion a b
      (archimedeanPlaceLieCoordinates F a ((archimedeanPlaceLieCoordinates F a).symm
        (Pi.single r X)) s) =
    archimedeanPlaceLieCoordinates F (a + b) ((archimedeanPlaceLieCoordinates F (a + b)).symm
      (Pi.single r (firstComplexMatrixBlockInclusion a b X))) s
  simp only [LieEquiv.apply_symm_apply]
  by_cases hs : s = r
  · subst s
    simp only [Pi.single_eq_same]
  · simp only [Pi.single_eq_of_ne hs, map_zero]

private theorem secondBlockEnvelopingInclusion_place (r : Place) :
    (secondBlockEnvelopingInclusion F h).comp (placeEnvelopingInclusion F b r) =
      (placeEnvelopingInclusion F (a + b) r).comp (secondComplexMatrixBlockEnveloping a b) := by
  change (LieEnvelopingEquiv.map (secondBlockComplexLieInclusion F h)).comp
      (LieEnvelopingEquiv.map (placeLieInclusion F b r)) =
    (LieEnvelopingEquiv.map (placeLieInclusion F (a + b) r)).comp
      (LieEnvelopingEquiv.map (secondComplexMatrixBlockInclusion a b))
  rw [LieEnvelopingEquiv.map_comp, LieEnvelopingEquiv.map_comp]
  congr 1
  apply LieHom.ext
  intro X
  apply (archimedeanPlaceLieCoordinates F (a + b)).injective
  funext s
  change archimedeanPlaceLieCoordinates F (a + b)
      (secondBlockComplexLieInclusion F h (placeLieInclusion F b r X)) s =
    archimedeanPlaceLieCoordinates F (a + b)
      (placeLieInclusion F (a + b) r (secondComplexMatrixBlockInclusion a b X)) s
  rw [secondBlock_at_place F a b]
  change secondComplexMatrixBlockInclusion a b
      (archimedeanPlaceLieCoordinates F b ((archimedeanPlaceLieCoordinates F b).symm
        (Pi.single r X)) s) =
    archimedeanPlaceLieCoordinates F (a + b) ((archimedeanPlaceLieCoordinates F (a + b)).symm
      (Pi.single r (secondComplexMatrixBlockInclusion a b X))) s
  simp only [LieEquiv.apply_symm_apply]
  by_cases hs : s = r
  · subst s
    simp only [Pi.single_eq_same]
  · simp only [Pi.single_eq_of_ne hs, map_zero]

private def realSingleEntryDirection (n : ℕ) (i j : Fin n) : Mixed →ₗ[ℝ] RealLieAlgebra F n :=
  (realLieAlgebraToMatrix F n).symm.toLinearMap.comp (Matrix.singleLinearMap ℝ i j)

private theorem placeCoordinates_singleEntry (n : ℕ) (i j : Fin n)
    (t : ℂ ⊗[ℝ] Mixed) (r : Place) :
    archimedeanPlaceLieCoordinates F n ((realSingleEntryDirection F n i j).baseChange ℂ t) r =
      Matrix.single i j (complexifiedScalarCoordinates F t ((placeIndex F).symm r)) := by
  induction t using TensorProduct.inductionOn with
  | tmul c x =>
    ext k l
    rw [LinearMap.baseChange_tmul, archimedeanPlaceLieCoordinates_apply,
      complexLieMatrixCoordinates_tmul, complexifiedScalarCoordinates_tmul]
    have he : realLieAlgebraToMatrix F n (realSingleEntryDirection F n i j x) =
        Matrix.single i j x := (realLieAlgebraToMatrix F n).apply_symm_apply _
    rw [he]
    by_cases hh : i = k ∧ j = l
    · simp only [Matrix.single_apply, ite_eq_left hh]
    · simp only [Matrix.single_apply, ite_eq_right hh, complexifiedPlaceValue_zero, mul_zero]
  | add t s ht hs => simp only [map_add, Pi.add_apply, ht, hs, Matrix.single_add]

omit [NumberField F] in
private theorem upperSingleEntryDirection (i : Fin a) (j : Fin b) (x : Mixed) :
    realSingleEntryDirection F (a + b) (Fin.castAdd b i) (Fin.natAdd a j) x =
      upperBlockLieDirection F h (Matrix.single i j x) := by
  apply congrArg (realLieAlgebraToMatrix F (a + b)).symm
  change Matrix.single (Fin.castAdd b i) (Fin.natAdd a j) x =
    Matrix.reindex e e (Matrix.fromBlocks 0 (Matrix.single i j x) 0 0)
  have hs : Matrix.fromBlocks (0 : Matrix (Fin a) (Fin a) Mixed)
      (Matrix.single i j x) (0 : Matrix (Fin b) (Fin a) Mixed)
      (0 : Matrix (Fin b) (Fin b) Mixed) = Matrix.single (Sum.inl i) (Sum.inr j) x := by
    apply Matrix.ext
    intro k l
    cases k <;> cases l <;> simp [Matrix.single_apply]
  rw [hs, Matrix.reindex_apply, Matrix.submatrix_single_equiv]
  simp only [Equiv.symm_symm, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right]

omit [NumberField F] in
private theorem singleEntry_mul_mem_upperBlockSpan (i : Fin a) (j : Fin b)
    (t : ℂ ⊗[ℝ] Mixed) (v : U (a + b)) :
    envelopingGenerator F (a + b)
        ((realSingleEntryDirection F (a + b) (Fin.castAdd b i) (Fin.natAdd a j)).baseChange ℂ t) *
      v ∈ upperBlockEnvelopingSpan F h := by
  induction t using TensorProduct.inductionOn with
  | tmul c x =>
    rw [LinearMap.baseChange_tmul, upperSingleEntryDirection]
    let X := upperBlockLieDirection F h (Matrix.single i j x)
    have hx : c ⊗ₜ[ℝ] X = c • complexify F (a + b) X := by
      rw [complexify_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    change envelopingGenerator F (a + b) (c ⊗ₜ[ℝ] X) * v ∈ _
    rw [hx, map_smul, smul_mul_assoc]
    exact Submodule.smul_mem _ c (Submodule.subset_span ⟨(Matrix.single i j x, v), rfl⟩)
  | add t s ht hs =>
    rw [map_add, map_add, add_mul]
    exact Submodule.add_mem _ ht hs

private theorem place_upper_generator_mul (r : Place) (c : VermaPBW.Idx (a + b))
    (hc : blockLetterWeight (a + b) a c = 1) (v : U (a + b)) :
    envelopingGenerator F (a + b) (placeLieInclusion F (a + b) r (VermaPBW.unitE (a + b) c)) *
      v ∈ upperBlockEnvelopingSpan F h := by
  obtain ⟨hi, hj⟩ := (blockLetterWeight_eq_one_iff (a + b) a c.1 c.2).mp hc
  let i : Fin a := ⟨c.1.val, hi⟩
  let j : Fin b := ⟨c.2.val - a, by have := c.2.isLt; omega⟩
  have hi' : Fin.castAdd b i = c.1 := Fin.ext rfl
  have hj' : Fin.natAdd a j = c.2 := Fin.ext (by
    simp only [Fin.val_natAdd, j]
    omega)
  let t : ℂ ⊗[ℝ] Mixed := (complexifiedScalarCoordinates F).symm
    (fun w => if placeIndex F w = r then 1 else 0)
  have ht : placeLieInclusion F (a + b) r (VermaPBW.unitE (a + b) c) =
      (realSingleEntryDirection F (a + b) (Fin.castAdd b i) (Fin.natAdd a j)).baseChange ℂ t := by
    apply (archimedeanPlaceLieCoordinates F (a + b)).injective
    funext s
    change archimedeanPlaceLieCoordinates F (a + b) ((archimedeanPlaceLieCoordinates F (a + b)).symm
        (Pi.single r (VermaPBW.unitE (a + b) c))) s =
      archimedeanPlaceLieCoordinates F (a + b)
        ((realSingleEntryDirection F (a + b) (Fin.castAdd b i) (Fin.natAdd a j)).baseChange ℂ t) s
    rw [LieEquiv.apply_symm_apply, placeCoordinates_singleEntry, hi', hj']
    change (Pi.single r (VermaPBW.unitE (a + b) c) : Place → M (a + b)) s =
      Matrix.single c.1 c.2 ((complexifiedScalarCoordinates F)
        ((complexifiedScalarCoordinates F).symm _) ((placeIndex F).symm s))
    rw [AlgEquiv.apply_symm_apply, Equiv.apply_symm_apply]
    by_cases hs : s = r
    · subst s
      simp [VermaPBW.unitE]
    · simp only [Pi.single_eq_of_ne hs, ite_eq_right hs, Matrix.single_zero]
  rw [ht]
  exact singleEntry_mul_mem_upperBlockSpan F a b i j t v

private theorem placeEnveloping_mem_upperSpan (r : Place) {x : UP (a + b)}
    (hx : x ∈ upperRadicalRightSpan (a + b) a) :
    placeEnvelopingInclusion F (a + b) r x ∈ upperBlockEnvelopingSpan F h := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨c, u⟩, rfl⟩ := hx
    rw [map_mul]
    change LieEnvelopingEquiv.map (placeLieInclusion F (a + b) r)
      (UniversalEnvelopingAlgebra.ι ℂ (VermaPBW.unitE (a + b) c.val)) *
      placeEnvelopingInclusion F (a + b) r u ∈ _
    rw [LieEnvelopingEquiv.map_generator]
    exact place_upper_generator_mul F a b r c.val c.property _
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul k x _ hx => rw [map_smul]; exact Submodule.smul_mem _ k hx

private theorem placeEnveloping_mem_centralSpan (r : Place) (J : Ideal (Z (a + b)))
    {x : UP (a + b)}
    (hx : x ∈ complexMatrixCentralIdealSpan (a + b)
      (J.comap (placeCenterInclusion F (a + b) r).toRingHom)) :
    placeEnvelopingInclusion F (a + b) r x ∈ centralIdealRightSpan F (a + b) J := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨z, u⟩, rfl⟩ := hx
    rw [map_mul, ← placeCenterInclusion_val]
    exact Submodule.subset_span ⟨(⟨placeCenterInclusion F (a + b) r z.val, z.property⟩, _), rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul k x _ hx => rw [map_smul]; exact Submodule.smul_mem _ k hx

private theorem placeEnveloping_mem_congruenceSpan (r : Place) (J : Ideal (Z (a + b)))
    {x : UP (a + b)}
    (hx : x ∈ complexMatrixCentralIdealSpan (a + b)
      (J.comap (placeCenterInclusion F (a + b) r).toRingHom) ⊔ upperRadicalRightSpan (a + b) a) :
    placeEnvelopingInclusion F (a + b) r x ∈
      centralIdealRightSpan F (a + b) J ⊔ upperBlockEnvelopingSpan F h := by
  obtain ⟨x₁, h₁, x₂, h₂, rfl⟩ := Submodule.mem_sup.mp hx
  rw [map_add]
  exact Submodule.mem_sup.mpr ⟨_, placeEnveloping_mem_centralSpan F a b r J h₁,
    _, placeEnveloping_mem_upperSpan F a b r h₂, rfl⟩

omit [NumberField F] in
private theorem rightSpan_mul {n : ℕ} {ι : Type*} (g : ι → U n) {x : U n}
    (hx : x ∈ Submodule.span ℂ (Set.range fun p : ι × U n => g p.1 * p.2)) (y : U n) :
    x * y ∈ Submodule.span ℂ (Set.range fun p : ι × U n => g p.1 * p.2) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨z, u⟩, rfl⟩ := hx
    rw [mul_assoc]
    exact Submodule.subset_span ⟨(z, u * y), rfl⟩
  | zero => rw [zero_mul]; exact Submodule.zero_mem _
  | add x x' _ _ hx hx' => rw [add_mul]; exact Submodule.add_mem _ hx hx'
  | smul c x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ hx

private abbrev congruenceSpan (J : Ideal (Z (a + b))) : Submodule ℂ (U (a + b)) :=
  centralIdealRightSpan F (a + b) J ⊔ upperBlockEnvelopingSpan F h

omit [NumberField F] in
private theorem congruenceSpan_mul (J : Ideal (Z (a + b))) {x : U (a + b)}
    (hx : x ∈ congruenceSpan F a b J) (v : U (a + b)) : x * v ∈ congruenceSpan F a b J := by
  obtain ⟨x₁, h₁, x₂, h₂, rfl⟩ := Submodule.mem_sup.mp hx
  rw [add_mul]
  exact Submodule.mem_sup.mpr ⟨_, rightSpan_mul F (fun z : J => centerInclusion F (a + b) z.val) h₁ v, _,
    rightSpan_mul F (fun X : Matrix (Fin a) (Fin b) Mixed =>
      envelopingGenerator F (a + b) (complexify F (a + b) (upperBlockLieDirection F h X))) h₂ v, rfl⟩

/-- Lower-rank central elements whose embedded operators obey the constant-term congruence. -/
def constantTermTransferIdeal {k : ℕ} (incl : U k →ₐ[ℂ] U (a + b))
    (J : Ideal (Z (a + b))) : Ideal (Z k) where
  carrier := {z | incl z.val ∈ congruenceSpan F a b J}
  zero_mem' := by
    change incl 0 ∈ congruenceSpan F a b J
    rw [map_zero]
    exact Submodule.zero_mem _
  add_mem' := fun {x y} hx hy => by
    change incl (x.val + y.val) ∈ congruenceSpan F a b J
    rw [map_add]
    exact Submodule.add_mem _ hx hy
  smul_mem' := fun s x hx => by
    change incl (s * x).val ∈ congruenceSpan F a b J
    rw [mul_comm s x, Subalgebra.coe_mul, map_mul]
    exact congruenceSpan_mul F a b J hx _

private theorem constantTermTransferIdeal_cofinite {k : ℕ} (incl : U k →ₐ[ℂ] U (a + b))
    (J : Ideal (Z (a + b)))
    (hp : ∀ r : Place, ∃ I : Ideal (ZP k), Module.Finite ℂ (ZP k ⧸ I) ∧
      ∀ z ∈ I, incl (placeEnvelopingInclusion F k r z.val) ∈ congruenceSpan F a b J) :
    Module.Finite ℂ (Z k ⧸ constantTermTransferIdeal F a b incl J) := by
  let I := constantTermTransferIdeal F a b incl J
  let E := (placeCenterCoordinates F k).symm.toAlgHom
  let I' := I.comap E.toRingHom
  have : Module.Finite ℂ
      ((Subalgebra.center ℂ (UniversalEnvelopingAlgebra ℂ (Place → M k))) ⧸ I') := by
    apply LieEnvelopingEquiv.quotientFinite_center_pi
    intro r
    obtain ⟨Ir, hr, hr'⟩ := hp r
    have hle : Ir ≤ I'.comap (LieEnvelopingEquiv.coordinateCenterInclusion ℂ (M k) r).toRingHom := by
      intro z hz
      change incl (placeCenterInclusion F k r z).val ∈ congruenceSpan F a b J
      rw [placeCenterInclusion_val]
      exact hr' z hz
    exact Module.Finite.of_surjective (Ideal.Quotient.factorₐ ℂ hle).toLinearMap
      (Ideal.Quotient.factor_surjective hle)
  exact Module.Finite.of_surjective (Ideal.quotientMapₐ I E (I := I') le_rfl).toLinearMap
    (Ideal.quotientMap_surjective (H := le_rfl) (placeCenterCoordinates F k).symm.surjective)

/-- A cofinite ambient center ideal gives a uniform cofinite center ideal for the first block. -/
theorem exists_firstBlock_cofinite_center_ideal {a b n : ℕ} (hn : a + b = n)
    (J : Ideal (Z n)) (hJ : Module.Finite ℂ (Z n ⧸ J.restrictScalars ℂ)) :
    ∃ I : Ideal (Z a), Module.Finite ℂ (Z a ⧸ I.restrictScalars ℂ) ∧
      ∀ z ∈ I, firstBlockEnvelopingInclusion F hn z.val ∈
        centralIdealRightSpan F n J ⊔ upperBlockEnvelopingSpan F hn := by
  subst n
  change Module.Finite ℂ (Z (a + b) ⧸ J) at hJ
  let incl := firstBlockEnvelopingInclusion F (rfl : a + b = a + b)
  refine ⟨constantTermTransferIdeal F a b incl J, ?_, fun _ hz => hz⟩
  change Module.Finite ℂ (Z a ⧸ constantTermTransferIdeal F a b incl J)
  refine constantTermTransferIdeal_cofinite F a b incl J fun r => ?_
  let Jr := J.comap (placeCenterInclusion F (a + b) r).toRingHom
  have hJr : Module.Finite ℂ (ZP (a + b) ⧸ Jr) :=
    quotientFinite_comap (placeCenterInclusion F (a + b) r) J
  obtain ⟨I, hI, hI'⟩ := exists_firstComplexBlock_cofinite_ideal a b Jr hJr
  refine ⟨I, hI, fun z hz => ?_⟩
  change ((firstBlockEnvelopingInclusion F (rfl : a + b = a + b)).comp
    (placeEnvelopingInclusion F a r)) z.val ∈ congruenceSpan F a b J
  rw [firstBlockEnvelopingInclusion_place]
  exact placeEnveloping_mem_congruenceSpan F a b r J (hI' z hz)

/-- A cofinite ambient center ideal gives a uniform cofinite center ideal for the second block. -/
theorem exists_secondBlock_cofinite_center_ideal {a b n : ℕ} (hn : a + b = n)
    (J : Ideal (Z n)) (hJ : Module.Finite ℂ (Z n ⧸ J.restrictScalars ℂ)) :
    ∃ I : Ideal (Z b), Module.Finite ℂ (Z b ⧸ I.restrictScalars ℂ) ∧
      ∀ z ∈ I, secondBlockEnvelopingInclusion F hn z.val ∈
        centralIdealRightSpan F n J ⊔ upperBlockEnvelopingSpan F hn := by
  subst n
  change Module.Finite ℂ (Z (a + b) ⧸ J) at hJ
  let incl := secondBlockEnvelopingInclusion F (rfl : a + b = a + b)
  refine ⟨constantTermTransferIdeal F a b incl J, ?_, fun _ hz => hz⟩
  change Module.Finite ℂ (Z b ⧸ constantTermTransferIdeal F a b incl J)
  refine constantTermTransferIdeal_cofinite F a b incl J fun r => ?_
  let Jr := J.comap (placeCenterInclusion F (a + b) r).toRingHom
  have hJr : Module.Finite ℂ (ZP (a + b) ⧸ Jr) :=
    quotientFinite_comap (placeCenterInclusion F (a + b) r) J
  obtain ⟨I, hI, hI'⟩ := exists_secondComplexBlock_cofinite_ideal a b Jr hJr
  refine ⟨I, hI, fun z hz => ?_⟩
  change ((secondBlockEnvelopingInclusion F (rfl : a + b = a + b)).comp
    (placeEnvelopingInclusion F b r)) z.val ∈ congruenceSpan F a b J
  rw [secondBlockEnvelopingInclusion_place]
  exact placeEnveloping_mem_congruenceSpan F a b r J (hI' z hz)

end Langlands.Automorphic
