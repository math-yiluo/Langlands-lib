import Langlands.BushnellKutzko.IntertwinedResidueDeterminantStatement
import Langlands.BushnellKutzko.AdjointCentralizer
import Langlands.BushnellKutzko.LatticeChainGradedMatrices
import Langlands.Group.GL.Maps
import Langlands.GroupScheme.Rational.GeneralLinearCharacterMatrices
import Langlands.AllFieldBZ.Representation.Geometric.IntersectionLeviDiagonalCharacterInfinite

/-! # Determinant factorization on the residue blocks -/

noncomputable section

open ValuativeRel IsLocalRing Matrix
open Langlands.GroupScheme.GeneralLinear

namespace Langlands.BushnellKutzko

universe uF uV

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type uV} [AddCommGroup V] [Module F V]
  (L : LatticeChain 𝒪[F] F V) {π : 𝒪[F]} (hπ : Irreducible π)
  {d : ℕ} (b : Module.Basis (Fin d) F V)

local notation "ν" => (fun i => L.index hπ (b i))
local notation "grade" => (fun i : Fin d => - (ν i))
local notation "O" => 𝒪[F]
local notation "k" => ResidueField O
local notation "U" => L.unitFiltration 0
local notation "ρ" => (Units.map (RingHom.toMonoidHom (residue O)))

private def matrixToEnd : GL (Fin d) F ≃* (Module.End F V)ˣ :=
  (Units.mapEquiv (LinearMap.toMatrixAlgEquiv b).toMulEquiv).symm

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
@[simp] private theorem toMatrix_matrixToEnd (g : GL (Fin d) F) :
    LinearMap.toMatrix b b ((matrixToEnd b g : (Module.End F V)ˣ) : Module.End F V) = g.val :=
  congrArg Units.val ((matrixToEnd b).symm_apply_apply g)

private def unitToOrder : U →* L.order where
  toFun g := ⟨(g.val : Module.End F V), g.property.1⟩
  map_one' := rfl
  map_mul' _ _ := rfl

private def residueBlock (hs : L.Splits b) (hn : ∀ i, 0 ≤ ν i ∧ ν i < L.period)
    (s : ℤ) : U →* Matrix {i // grade i = s} {i // grade i = s} k :=
  (L.orderResidueBlock hπ b hs hn s).comp (unitToOrder L)

private def liftIntegralMatrix (g : GL (Fin d) O) : (Module.End F V)ˣ :=
  matrixToEnd b (Matrix.GeneralLinearGroup.map (𝒪[F].subtype) g)

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
@[simp] private theorem toMatrix_liftIntegralMatrix (g : GL (Fin d) O) :
    LinearMap.toMatrix b b (liftIntegralMatrix b g : Module.End F V) =
      (𝒪[F].subtype).mapMatrix g.val := toMatrix_matrixToEnd b _

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem liftIntegralMatrix_inv (g : GL (Fin d) O) :
    (liftIntegralMatrix b g)⁻¹ = liftIntegralMatrix b g⁻¹ := by
  simp only [liftIntegralMatrix, map_inv]

private theorem liftIntegralMatrix_mem (hs : L.Splits b) (hn : ∀ i, 0 ≤ ν i ∧ ν i < L.period)
    (g : GL (Fin d) O)
    (hg : ∀ i j, ν i ≠ ν j → g.val i j = 0)
    (hgi : ∀ i j, ν i ≠ ν j → (g⁻¹ : GL (Fin d) O).val i j = 0) :
    liftIntegralMatrix b g ∈ U := by
  have hh (g' : GL (Fin d) O) (hg' : ∀ i j, ν i ≠ ν j → g'.val i j = 0) :
      (liftIntegralMatrix b g' : Module.End F V) ∈ L.order := by
    apply L.mem_order_iff_mem_endFiltration.mpr
    apply (L.mem_endFiltration_iff_integral_entries hπ b hs hn le_rfl
      (by decide : (0 : ℤ) ≤ 1) _).mpr
    intro i j
    refine ⟨g'.val i j, by rw [toMatrix_liftIntegralMatrix]; rfl, fun h => ?_⟩
    rw [add_zero] at h
    rw [hg' i j h.ne]
    exact zero_mem _
  apply L.mem_unitFiltration_zero.mpr
  rw [liftIntegralMatrix_inv]
  exact ⟨hh g hg, hh g⁻¹ hgi⟩

private theorem residueMatrix_lift (hs : L.Splits b) (hn : ∀ i, 0 ≤ ν i ∧ ν i < L.period)
    (g : GL (Fin d) O) (hg : liftIntegralMatrix b g ∈ U) :
    L.orderResidueMatrix hπ b hs hn (unitToOrder L ⟨_, hg⟩) = (residue O).mapMatrix g.val := by
  have h : L.orderIntegralMatrix hπ b hs hn (unitToOrder L ⟨_, hg⟩) = g.val := by
    ext i j
    change LinearMap.toMatrix b b (liftIntegralMatrix b g : Module.End F V) i j = _
    rw [toMatrix_liftIntegralMatrix]
    rfl
  change (residue O).mapMatrix (L.orderIntegralMatrix hπ b hs hn (unitToOrder L ⟨_, hg⟩)) = _
  rw [h]

private def diagonalLift (hs : L.Splits b) (hn : ∀ i, 0 ≤ ν i ∧ ν i < L.period) :
    (Fin d → Oˣ) →* U := by
  let f := ((matrixToEnd b).toMonoidHom.comp (Matrix.GeneralLinearGroup.map (𝒪[F].subtype))).comp
    (diagonalMatrixUnits O)
  refine f.codRestrict U (fun a => ?_)
  change liftIntegralMatrix b (diagonalMatrixUnits O a) ∈ U
  apply liftIntegralMatrix_mem L hπ b hs hn
  · intro i j hij
    exact Matrix.diagonal_apply_ne _ (fun h => hij (congrArg ν h))
  · rw [← map_inv]
    intro i j hij
    exact Matrix.diagonal_apply_ne _ (fun h => hij (congrArg ν h))

private def coordinateLift (hs : L.Splits b) (hn : ∀ i, 0 ≤ ν i ∧ ν i < L.period)
    (i : Fin d) : Oˣ →* U :=
  (diagonalLift L hπ b hs hn).comp (MonoidHom.mulSingle (fun _ : Fin d => Oˣ) i)

private def transvectionOverIntegers {i j : Fin d} (hij : i ≠ j) (a : O) : GL (Fin d) O :=
  let t : Matrix.TransvectionStruct (Fin d) O := ⟨i, j, hij, a⟩
  ⟨t.toMatrix, t.inv.toMatrix, t.mul_inv, t.inv_mul⟩

private def transvectionLift (hs : L.Splits b) (hn : ∀ i, 0 ≤ ν i ∧ ν i < L.period)
    {i j : Fin d} (hij : i ≠ j) (hgrade : ν i = ν j) (a : O) : U := by
  refine ⟨liftIntegralMatrix b (transvectionOverIntegers hij a), ?_⟩
  apply liftIntegralMatrix_mem L hπ b hs hn
  all_goals
    intro r s hrs
    change (Matrix.transvection i j _) r s = 0
    have hne : r ≠ s := fun h => hrs (congrArg ν h)
    have hentry : ¬ (i = r ∧ j = s) := by rintro ⟨rfl, rfl⟩; exact hrs hgrade
    simp [Matrix.transvection, hne, hentry]

private theorem residueBlock_lift (hs : L.Splits b) (hn : ∀ i, 0 ≤ ν i ∧ ν i < L.period)
    (g : GL (Fin d) O) (hg : liftIntegralMatrix b g ∈ U) (s : ℤ) :
    residueBlock L hπ b hs hn s ⟨_, hg⟩ = ((residue O).mapMatrix g.val).toSquareBlock grade s :=
  congrArg (fun M : Matrix (Fin d) (Fin d) k => M.toSquareBlock grade s)
    (residueMatrix_lift L hπ b hs hn g hg)

private theorem residueBlock_diagonal (hs : L.Splits b) (hn : ∀ i, 0 ≤ ν i ∧ ν i < L.period)
    (a : Fin d → Oˣ) (s : ℤ) :
    residueBlock L hπ b hs hn s (diagonalLift L hπ b hs hn a) =
      Matrix.diagonal (fun i : {i // grade i = s} => (ρ (a i.val) : k)) := by
  have h := residueBlock_lift L hπ b hs hn (diagonalMatrixUnits O a)
    (diagonalLift L hπ b hs hn a).property s
  refine h.trans ?_
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.toSquareBlock_def, Matrix.of_apply, Matrix.map_apply,
    diagonalMatrixUnits_val, Matrix.diagonal_apply, Subtype.ext_iff]
  split_ifs <;> simp [Units.coe_map]

private theorem residueBlock_transvection (hs : L.Splits b)
    (hn : ∀ i, 0 ≤ ν i ∧ ν i < L.period) {i j : Fin d}
    (hij : i ≠ j) (hgrade : ν i = ν j) (a : O) (s : ℤ) :
    residueBlock L hπ b hs hn s (transvectionLift L hπ b hs hn hij hgrade a) =
      (Matrix.transvection i j (residue O a)).toSquareBlock grade s := by
  change residueBlock L hπ b hs hn s ⟨liftIntegralMatrix b (transvectionOverIntegers hij a), _⟩ = _
  rw [residueBlock_lift]
  congr 1
  change (residue O).mapMatrix (Matrix.transvection i j a) = _
  rw [Matrix.transvection, map_add, map_one, Matrix.transvection]
  congr 1
  ext r t
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.single_apply]
  split_ifs <;> simp

section Character

variable (hs : L.Splits b)
  (hn : ∀ i, 0 ≤ L.index hπ (b i) ∧ L.index hπ (b i) < L.period)
  (ξ : L.unitFiltration 0 →* ℂˣ)
  (htriv : ∀ x : L.unitFiltration 0, x.val ∈ L.unitFiltration 1 → ξ x = 1)
  (hI : ∀ y, y ∈ characterSelfIntertwining ξ)

include hI in
omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem character_eq_of_conj (s : (Module.End F V)ˣ) (x y : U)
    (he : s * x.val * s⁻¹ = y.val) : ξ y = ξ x := by
  have hm : s * x.val * s⁻¹ ∈ U := he.symm ▸ y.property
  have he' : (⟨_, hm⟩ : U) = y := Subtype.ext he
  exact (congrArg ξ he').symm.trans (hI s x hm)

include htriv in
private theorem character_eq_of_blocks (x y : U)
    (he : ∀ s, residueBlock L hπ b hs hn s x = residueBlock L hπ b hs hn s y) :
    ξ x = ξ y := by
  have h := htriv (y⁻¹ * x) ((L.mem_unitFiltration_one_iff_blocks hπ b hs hn _).mpr (by
    intro s
    change residueBlock L hπ b hs hn s (y⁻¹ * x) = 1
    rw [map_mul, he, ← map_mul, inv_mul_cancel, map_one]))
  rw [map_mul, map_inv, inv_mul_eq_one] at h
  exact h.symm

include hI in
private theorem character_coordinate_eq (i j : Fin d) (a : Oˣ) :
    ξ (coordinateLift L hπ b hs hn i a) = ξ (coordinateLift L hπ b hs hn j a) := by
  let D (r : Fin d) : GL (Fin d) F :=
    Matrix.GeneralLinearGroup.map (𝒪[F].subtype) (diagonalMatrixUnits O (Pi.mulSingle r a))
  let s := Equiv.swap i j
  let p := Langlands.GeneralLinear.permutation d F s
  have hD (r v w : Fin d) :
      D r v w = if v = w then if v = r then ((a : O) : F) else 1 else 0 := by
    change Matrix.GeneralLinearGroup.map (𝒪[F].subtype)
      (diagonalMatrixUnits O (Pi.mulSingle r a)) v w = _
    rw [Matrix.GeneralLinearGroup.map_apply]
    change (𝒪[F].subtype) (Matrix.diagonal (fun t => ((Pi.mulSingle r a : Fin d → Oˣ) t : O)) v w) = _
    by_cases h : v = w
    · subst w
      by_cases h' : v = r <;> simp [Pi.mulSingle_apply, h']
    · simp only [Matrix.diagonal_apply, ite_eq_right h, map_zero]
  have hh (r : Fin d) : s⁻¹ r = i ↔ r = j := by
    change (Equiv.swap i j).symm r = i ↔ r = j
    rw [Equiv.symm_apply_eq, Equiv.swap_apply_left]
  have he : p * D i * p⁻¹ = D j := by
    apply Units.ext
    ext r t
    change (Langlands.GeneralLinear.permutation d F s * D i *
      (Langlands.GeneralLinear.permutation d F s)⁻¹) r t = D j r t
    rw [Langlands.GeneralLinear.permutation_conjugate_entry, hD, hD]
    simp only [hh, Equiv.apply_eq_iff_eq]
  symm
  apply character_eq_of_conj L ξ hI (matrixToEnd b p)
  change matrixToEnd b p * matrixToEnd b (D i) * (matrixToEnd b p)⁻¹ =
    matrixToEnd b (D j)
  simpa only [map_mul, map_inv] using congrArg (matrixToEnd b) he

include htriv hI in
private theorem character_transvection_eq_one {i j : Fin d} (hij : i ≠ j) (hgrade : ν i = ν j)
    (a : O) : ξ (transvectionLift L hπ b hs hn hij hgrade a) = 1 := by
  let u := transvectionLift L hπ b hs hn hij hgrade a
  let v := transvectionLift L hπ b hs hn hij hgrade (π * a)
  have hπa : residue O (π * a) = 0 := by
    rw [map_mul, (residue_eq_zero_iff _).mpr ((IsLocalRing.mem_maximalIdeal _).2 hπ.not_isUnit),
      zero_mul]
  have hv : v.val ∈ L.unitFiltration 1 := by
    apply (L.mem_unitFiltration_one_iff_blocks hπ b hs hn v).mpr
    intro s
    change residueBlock L hπ b hs hn s v = 1
    rw [show v = transvectionLift L hπ b hs hn hij hgrade (π * a) from rfl,
      residueBlock_transvection, hπa, Matrix.transvection_zero]
    ext p q
    simp only [Matrix.toSquareBlock_def, Matrix.of_apply, Matrix.one_apply, Subtype.ext_iff]
  let D : GL (Fin d) F := Langlands.Geometric.DiagonalCharacter.diagonalUnit
    (fun r => if r = i then Units.mk0 (π : F) (coe_uniformizer_ne_zero hπ) else 1)
  let T (z : F) : GL (Fin d) F := Langlands.GeneralLinear.transvectionUnit i j hij z
  have hT (c : O) : Matrix.GeneralLinearGroup.map (𝒪[F].subtype)
      (transvectionOverIntegers hij c) = T c := by
    apply Units.ext
    ext r s
    change ((𝒪[F].subtype).mapMatrix (Matrix.transvection i j c)) r s =
      (Matrix.transvection i j (c : F)) r s
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.transvection, Matrix.add_apply,
      map_add, Matrix.one_apply, Matrix.single_apply]
    split_ifs <;> simp
  have he : D * T a * D⁻¹ = T ((π : F) * (a : F)) := by
    apply mul_inv_eq_of_eq_mul
    exact Langlands.AllFieldBZ.Geometric.DiagonalCharacter.scale_transvection_by i j hij
      (π : F) (coe_uniformizer_ne_zero hπ) (a : F)
  have he' : matrixToEnd b D * u.val * (matrixToEnd b D)⁻¹ = v.val := by
    change matrixToEnd b D *
      matrixToEnd b (Matrix.GeneralLinearGroup.map (𝒪[F].subtype) (transvectionOverIntegers hij a)) *
      (matrixToEnd b D)⁻¹ =
      matrixToEnd b (Matrix.GeneralLinearGroup.map (𝒪[F].subtype) (transvectionOverIntegers hij (π * a)))
    rw [hT, hT, Subring.coe_mul]
    simpa only [map_mul, map_inv] using congrArg (matrixToEnd b) he
  exact (character_eq_of_conj L ξ hI (matrixToEnd b D) u v he').symm.trans (htriv v hv)

private theorem residue_units_surjective : Function.Surjective (ρ : Oˣ →* kˣ) :=
  surjective_units_map_of_local_ringHom _ residue_surjective inferInstance

include htriv in
private theorem exists_residue_coordinate_character (i : Fin d) :
    ∃ χ : kˣ →* ℂˣ, ∀ a, χ (ρ a) = ξ (coordinateLift L hπ b hs hn i a) := by
  let c := ξ.comp (coordinateLift L hπ b hs hn i)
  let reduction : Oˣ →* kˣ := ρ
  have hker : reduction.ker ≤ c.ker := by
    intro a ha
    change ξ (coordinateLift L hπ b hs hn i a) = 1
    apply htriv
    apply (L.mem_unitFiltration_one_iff_blocks hπ b hs hn _).mpr
    intro s
    change residueBlock L hπ b hs hn s (diagonalLift L hπ b hs hn (Pi.mulSingle i a)) = 1
    rw [residueBlock_diagonal]
    change ρ a = 1 at ha
    have hd (j : Fin d) : ρ ((Pi.mulSingle i a : Fin d → Oˣ) j) = 1 := by
      by_cases h : j = i
      · subst j
        rwa [Pi.mulSingle_eq_same]
      · rw [Pi.mulSingle_eq_of_ne h, map_one]
    simp only [hd, Units.val_one, Matrix.diagonal_one]
  let χ := reduction.liftOfSurjective residue_units_surjective ⟨c, hker⟩
  exact ⟨χ, fun a => MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ a⟩

include hI in
private theorem character_diagonal_value (i : Fin d) (χ : kˣ →* ℂˣ)
    (hχ : ∀ a, χ (ρ a) = ξ (coordinateLift L hπ b hs hn i a)) (a : Fin d → Oˣ) :
    ξ (diagonalLift L hπ b hs hn a) = χ (∏ j, ρ (a j)) := by
  calc
    ξ (diagonalLift L hπ b hs hn a) = ∏ j, ξ (coordinateLift L hπ b hs hn j (a j)) := by
      change (ξ.comp (diagonalLift L hπ b hs hn)) a =
        ∏ j, (ξ.comp (diagonalLift L hπ b hs hn)) (Pi.mulSingle j (a j))
      rw [← map_prod, Finset.univ_prod_mulSingle]
    _ = χ (∏ j, ρ (a j)) := by
      rw [map_prod]
      apply Finset.prod_congr rfl
      intro j _
      exact (character_coordinate_eq L hπ b hs hn ξ hI j i (a j)).trans (hχ (a j)).symm

include htriv hI in
private theorem exists_lift_for_block (i : Fin d) (χ : kˣ →* ℂˣ)
    (hχ : ∀ a, χ (ρ a) = ξ (coordinateLift L hπ b hs hn i a))
    (s : ℤ) (A : Matrix {j // grade j = s} {j // grade j = s} k) (hA : A.det ≠ 0) :
    ∃ u : U, residueBlock L hπ b hs hn s u = A ∧
      (∀ t, t ≠ s → residueBlock L hπ b hs hn t u = 1) ∧
      ∀ a : kˣ, (a : k) = A.det → ξ u = χ a := by
  classical
  let P (M : Matrix {j // grade j = s} {j // grade j = s} k) : Prop :=
    ∃ u : U, residueBlock L hπ b hs hn s u = M ∧
      (∀ t, t ≠ s → residueBlock L hπ b hs hn t u = 1) ∧
      ∀ a : kˣ, (a : k) = M.det → ξ u = χ a
  change P A
  apply Matrix.diagonal_transvection_induction_of_det_ne_zero P A hA
  · intro D hD
    have hne (j : {j // grade j = s}) : D j ≠ 0 := by
      rw [Matrix.det_diagonal] at hD
      exact fun he => hD (Finset.prod_eq_zero (Finset.mem_univ j) he)
    let u (j : {j // grade j = s}) : kˣ := Units.mk0 (D j) (hne j)
    choose a ha using fun j => residue_units_surjective (u j)
    let diag (j : Fin d) : Oˣ := if hj : grade j = s then a ⟨j, hj⟩ else 1
    have hg (j : {j // grade j = s}) : ρ (diag j.val) = u j := by
      simp only [diag, dite_eq_left j.property]
      exact ha j
    refine ⟨diagonalLift L hπ b hs hn diag, ?_, ?_, ?_⟩
    · rw [residueBlock_diagonal]
      congr
      funext j
      rw [hg]
      rfl
    · intro t ht
      rw [residueBlock_diagonal]
      convert (Matrix.diagonal_one : Matrix.diagonal (fun _ : {j // grade j = t} => (1 : k)) = 1)
        using 2
      funext j
      have hjs : grade j.val ≠ s := fun h => ht (j.property.symm.trans h)
      simp [diag, hjs]
    · intro c hc
      rw [character_diagonal_value L hπ b hs hn ξ hI i χ hχ]
      congr 1
      have hp : (∏ j, ρ (diag j)) = ∏ j : {j // grade j = s}, u j := by
        rw [← Fintype.prod_subtype_mul_prod_subtype (fun j => grade j = s)]
        have hfun (j : {j // grade j ≠ s}) : ρ (diag j.val) = 1 := by
          simp [diag, j.property]
        simp only [hfun, Finset.prod_const_one, mul_one, hg]
      rw [hp]
      apply Units.ext
      rw [Units.coe_prod]
      change (∏ j, D j) = (c : k)
      simpa only [Matrix.det_diagonal] using hc.symm
  · intro T
    let r := T.i.val
    let t := T.j.val
    have hrt : r ≠ t := fun he => T.hij (Subtype.ext he)
    have hgrade : ν r = ν t := by
      have he := T.i.property.trans T.j.property.symm
      change - ν r = - ν t at he
      omega
    obtain ⟨a, ha⟩ := residue_surjective (R := O) T.c
    let w := transvectionLift L hπ b hs hn hrt hgrade a
    refine ⟨w, ?_, ?_, ?_⟩
    · change residueBlock L hπ b hs hn s (transvectionLift L hπ b hs hn hrt hgrade a) = T.toMatrix
      rw [residueBlock_transvection, ha]
      ext j l
      simp only [Matrix.toSquareBlock_def, Matrix.of_apply, Matrix.TransvectionStruct.toMatrix,
        Matrix.transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, Subtype.ext_iff]
      rfl
    · intro q hq
      change residueBlock L hπ b hs hn q (transvectionLift L hπ b hs hn hrt hgrade a) = 1
      rw [residueBlock_transvection]
      ext j l
      have hne : r ≠ j.val := fun he => hq (j.property.symm.trans
        ((congrArg grade he).symm.trans T.i.property))
      simp [Matrix.toSquareBlock_def, Matrix.transvection, Matrix.one_apply, Matrix.single_apply,
        Subtype.ext_iff, hne]
    · intro c hc
      have he : c = 1 := Units.ext (hc.trans T.det)
      rw [he, map_one]
      exact character_transvection_eq_one L hπ b hs hn ξ htriv hI hrt hgrade a
  · intro M N hM hN hPM hPN
    obtain ⟨x, hx, hx', hxχ⟩ := hPM
    obtain ⟨y, hy, hy', hyχ⟩ := hPN
    refine ⟨x * y, ?_, ?_, ?_⟩
    · rw [map_mul, hx, hy]
    · intro t ht
      rw [map_mul, hx' t ht, hy' t ht, mul_one]
    · intro c hc
      let a := Units.mk0 M.det hM
      let b := Units.mk0 N.det hN
      have he : a * b = c := Units.ext (by rw [hc, Matrix.det_mul]; rfl)
      rw [← he, map_mul ξ, hxχ a rfl, hyχ b rfl, map_mul χ]

include htriv hI in
private theorem character_of_residue_blocks (i : Fin d) (χ : kˣ →* ℂˣ)
    (hχ : ∀ a, χ (ρ a) = ξ (coordinateLift L hπ b hs hn i a))
    (x : U) (a : Oˣ) (ha : ((a : O) : F) = LinearMap.det (x.val : Module.End F V)) :
    ξ x = χ (ρ a) := by
  classical
  let Δ (s : ℤ) : kˣ :=
    Units.map Matrix.detMonoidHom ((residueBlock L hπ b hs hn s).toHomUnits x)
  let S : Finset ℤ := Finset.univ.image grade
  have lift (s : ℤ) :
      ∃ y : U, residueBlock L hπ b hs hn s y = residueBlock L hπ b hs hn s x ∧
        (∀ t, t ≠ s → residueBlock L hπ b hs hn t y = 1) ∧ ξ y = χ (Δ s) := by
    obtain ⟨y, hy, hy', hyχ⟩ := exists_lift_for_block L hπ b hs hn ξ htriv hI i χ hχ s
      (residueBlock L hπ b hs hn s x) (Δ s).ne_zero
    exact ⟨y, hy, hy', hyχ _ rfl⟩
  have build (T : Finset ℤ) : ∃ y : U,
      (∀ s ∈ T, residueBlock L hπ b hs hn s y = residueBlock L hπ b hs hn s x) ∧
      (∀ s ∉ T, residueBlock L hπ b hs hn s y = 1) ∧
      ξ y = χ (∏ s ∈ T, Δ s) := by
    induction T using Finset.induction with
    | empty => exact ⟨1, by simp, by simp, by simp⟩
    | insert s T hsT ih =>
      obtain ⟨y, hy, hy', hyχ⟩ := lift s
      obtain ⟨z, hz, hz', hzχ⟩ := ih
      refine ⟨y * z, ?_, ?_, ?_⟩
      · intro t ht
        rcases Finset.mem_insert.mp ht with rfl | ht
        · rw [map_mul, hy, hz' _ hsT, mul_one]
        · rw [map_mul, hy' _ (fun h => hsT (h ▸ ht)), hz _ ht, one_mul]
      · intro t ht
        rw [map_mul, hy' _ (fun h => ht (Finset.mem_insert.mpr (Or.inl h))),
          hz' _ (fun h => ht (Finset.mem_insert.mpr (Or.inr h))), one_mul]
      · rw [Finset.prod_insert hsT, map_mul ξ, hyχ, hzχ, map_mul χ]
  obtain ⟨y, hy, _, hyχ⟩ := build S
  have hxy (s : ℤ) : residueBlock L hπ b hs hn s x = residueBlock L hπ b hs hn s y := by
    by_cases h : s ∈ S
    · exact (hy s h).symm
    · ext j l
      exact False.elim (h (Finset.mem_image.mpr ⟨j.val, Finset.mem_univ _, j.property⟩))
  rw [character_eq_of_blocks L hπ b hs hn ξ htriv x y hxy, hyχ]
  congr 1
  let N := L.orderIntegralMatrix hπ b hs hn (unitToOrder L x)
  let R := L.orderResidueMatrix hπ b hs hn (unitToOrder L x)
  have hN : (𝒪[F].subtype).mapMatrix N =
      LinearMap.toMatrix b b (x.val : Module.End F V) := rfl
  have hdet : N.det = (a : O) := Subtype.ext (by
    change (𝒪[F].subtype) N.det = ((a : O) : F)
    rw [RingHom.map_det, hN, LinearMap.det_toMatrix, ha])
  have hred : R.det = residue O (a : O) := by
    change ((residue O).mapMatrix N).det = _
    rw [← RingHom.map_det, hdet]
  have htri := L.orderResidueMatrix_blockTriangular hπ b hs hn (unitToOrder L x)
  apply Units.ext
  change (↑(∏ s ∈ S, Δ s) : k) = residue O (a : O)
  rw [Units.coe_prod, ← hred, htri.det]
  rfl

end Character

/-- Triviality at depth one and full intertwining force residue determinant factorization. -/
theorem intertwinedResidueDeterminant : IntertwinedResidueDeterminantStatement.{uF, uV} := by
  classical
  intro F _ _ _ _ V _ _ L ξ htriv hI
  let _ : Nontrivial V := L.nontrivial_space
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  obtain ⟨d, b, hs, hn⟩ := L.exists_basis_splits_normalized hπ
  obtain ⟨i⟩ := b.index_nonempty
  obtain ⟨χ, hχ⟩ := exists_residue_coordinate_character L hπ b hs hn ξ htriv i
  exact ⟨χ, character_of_residue_blocks L hπ b hs hn ξ htriv hI i χ hχ⟩

end Langlands.BushnellKutzko
