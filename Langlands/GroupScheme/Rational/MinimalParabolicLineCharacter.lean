import Langlands.GroupScheme.Rational.RankOneStandardParabolicLineCharacter
import Langlands.GroupScheme.Rational.RankOneCharacterComparison

/-! # Nonnegative root relations for minimal-parabolic coordinate lines -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

universe u

open CategoryTheory AlgebraicGeometry Opposite TensorProduct
open scoped CategoryTheory.MonObj Matrix
open Langlands.LinearAlgebra.RationalSpan

namespace Langlands.GroupScheme.MatrixRepresentation

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {n : Type} [Fintype n] [DecidableEq n]

theorem affineMatrix_comp_of_diagonal (ρ : MatrixRepresentation G n)
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (e : n → ℤ) (hχ : χ ≫ ρ = GeneralLinear.diagonalCocharacter n (CommRingCat.of k) e)
    (A : CommAlgCat.{u} (CommRingCat.of k))
    (x : (algSpec (CommRingCat.of k)).obj (op A) ⟶ (Gm (Spec (CommRingCat.of k))).X) :
    ρ.affineMatrix A (x ≫ χ.hom.hom) =
      GeneralLinear.diagonalUnits A e
        (Gm.affinePointsEquiv ((algSpec (CommRingCat.of k)).obj (op A)).hom x) := by
  rw [affineMatrix_apply, Category.assoc, ← Grp.comp_hom_hom, hχ,
    GeneralLinear.CocharacterDiagonal.affinePointsEquiv_diagonalCocharacter]

/-- If conjugation by a rational point carries `χ'` to the diagonal cocharacter
`χ`, and `χ'` acts on the selected coordinate vector by the `m`-th power, then
that rational point moves the selected vector into the `χ`-weight block `m`. -/
theorem rationalMatrix_entry_eq_zero_of_conj_powerAction
    (ρ : MatrixRepresentation G n)
    (χ χ' : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (e : n → ℤ) (hχ : χ ≫ ρ = GeneralLinear.diagonalCocharacter n (CommRingCat.of k) e)
    {g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X}
    (hg : χ' ≫ (G.innerIso g).hom = χ)
    (j : n) (m : ℤ) (hm : (ρ.restrict χ').HasCoordinatePowerAction j m)
    {b : n} (hb : e b ≠ m) :
    (ρ.rationalMatrix g : Matrix n n k) b j = 0 := by
  let A := CommAlgCat.of k (LaurentPolynomial k)
  let Z := (algSpec (CommRingCat.of k)).obj (op A)
  let x : Z ⟶ (Gm (Spec (CommRingCat.of k))).X :=
    (Gm.affinePointsEquiv Z.hom).symm (Gm.relativeCoordUnit k)
  have ht := congrArg (fun f : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G =>
    x ≫ f.hom.hom) hg
  change x ≫ (χ' ≫ (G.innerIso g).hom).hom.hom = x ≫ χ.hom.hom at ht
  rw [Grp.comp_hom_hom, ← Category.assoc, comp_innerIso_hom] at ht
  have hM := congrArg (ρ.affineMatrix A) ht
  rw [map_mul, map_mul, map_inv, affineMatrix_constantPoint,
    ρ.affineMatrix_comp_of_diagonal χ e hχ,
    show Gm.affinePointsEquiv Z.hom x = Gm.relativeCoordUnit k from
      MulEquiv.apply_symm_apply _ _] at hM
  have hM' := (mul_inv_eq_iff_eq_mul).mp hM
  have hpow := hm (LaurentPolynomial k) x
  rw [affineMatrix_restrict] at hpow
  have hx : Gm.affineUnitsEquiv (CommRingCat.of k) (CommAlgCat.of k (LaurentPolynomial k)) x =
      Gm.relativeCoordUnit k := MulEquiv.apply_symm_apply _ _
  rw [hx] at hpow
  have he := congrArg (fun M : GL n (LaurentPolynomial k) =>
    (M : Matrix n n (LaurentPolynomial k)) b j) hM'
  simp only [Units.val_mul, GeneralLinear.coe_diagonalUnits, Matrix.diagonal_mul,
    Matrix.GeneralLinearGroup.map_apply] at he
  have hcol : ∀ c : n, ((ρ.affineMatrix A (x ≫ χ'.hom.hom) : GL n (LaurentPolynomial k)) :
      Matrix n n (LaurentPolynomial k)) c j =
        ((Gm.relativeCoordUnit k ^ m : (LaurentPolynomial k)ˣ) : LaurentPolynomial k) *
          (Pi.single j 1 : n → LaurentPolynomial k) c := by
    intro c
    have := congrFun hpow c
    simpa only [Matrix.mulVec_single_one, Matrix.col_apply, Pi.smul_apply,
      smul_eq_mul] using this
  rw [Matrix.mul_apply] at he
  simp only [hcol] at he
  rw [Finset.sum_eq_single j (fun c _ hc => by simp [hc])
    (by simp)] at he
  simp only [Pi.single_eq_same, mul_one] at he
  rw [Gm.relativeCoordUnit_zpow_val, Gm.relativeCoordUnit_zpow_val] at he
  change (algebraMap k (LaurentPolynomial k)) ((ρ.rationalMatrix g : Matrix n n k) b j) *
      LaurentPolynomial.T m =
    LaurentPolynomial.T (e b) *
      (algebraMap k (LaurentPolynomial k)) ((ρ.rationalMatrix g : Matrix n n k) b j) at he
  change LaurentPolynomial.C ((ρ.rationalMatrix g : Matrix n n k) b j) *
      LaurentPolynomial.T m =
    LaurentPolynomial.T (e b) *
      LaurentPolynomial.C ((ρ.rationalMatrix g : Matrix n n k) b j) at he
  apply GeneralLinear.eq_zero_of_C_mul_T_eq (m := e b - m) (sub_ne_zero.mpr hb)
  calc
    LaurentPolynomial.C ((ρ.rationalMatrix g : Matrix n n k) b j) *
        LaurentPolynomial.T (e b - m) =
      LaurentPolynomial.T (-m) *
        (LaurentPolynomial.T (e b) *
          LaurentPolynomial.C ((ρ.rationalMatrix g : Matrix n n k) b j)) := by
      rw [sub_eq_add_neg, LaurentPolynomial.T_add]; ring
    _ = LaurentPolynomial.T (-m) *
        (LaurentPolynomial.C ((ρ.rationalMatrix g : Matrix n n k) b j) *
          LaurentPolynomial.T m) := by rw [he]
    _ = _ := by
      rw [mul_comm (LaurentPolynomial.C _), ← mul_assoc, ← LaurentPolynomial.T_add,
        neg_add_cancel, LaurentPolynomial.T_zero, one_mul]

/-- A rational point carrying `χ'` to the diagonal cocharacter `χ` bounds the
`χ'`-weight of the selected vector by its `χ`-weight, when the `χ`-orbit of
that vector has no coordinate of larger weight. -/
theorem le_of_conj_powerAction_of_orbitWeightUpperBound
    (ρ : MatrixRepresentation G n)
    (χ χ' : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (e : n → ℤ) (hχ : χ ≫ ρ = GeneralLinear.diagonalCocharacter n (CommRingCat.of k) e)
    {g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X}
    (hg : χ' ≫ (G.innerIso g).hom = χ)
    (j : n) (hup : ρ.HasOrbitWeightUpperBound e j)
    (m : ℤ) (hm : (ρ.restrict χ').HasCoordinatePowerAction j m) :
    m ≤ e j := by
  by_contra hlt'
  have hlt := not_le.mp hlt'
  have hcol : ∀ b, (ρ.rationalMatrix g : Matrix n n k) b j = 0 := by
    intro b
    by_cases hb : e b = m
    · have hz := hup (Over.mk (𝟙 _)) g b (hb ▸ hlt)
      change (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom
        ((ρ.pointMatrix (Over.mk (𝟙 (Spec (CommRingCat.of k)))) g :
          Matrix n n Γ((Over.mk (𝟙 (Spec (CommRingCat.of k)))).left, ⊤)) b j) = 0
      rw [hz, map_zero]
    · exact ρ.rationalMatrix_entry_eq_zero_of_conj_powerAction χ χ' e hχ hg j m hm hb
  have hv : (ρ.rationalMatrix g : Matrix n n k) *ᵥ Pi.single j 1 = 0 := by
    ext b
    simp only [Matrix.mulVec_single_one, Matrix.col_apply, hcol, Pi.zero_apply]
  have h0 : (Pi.single j (1 : k) : n → k) = 0 :=
    Matrix.mulVec_injective_of_isUnit (Units.isUnit (ρ.rationalMatrix g))
      (by rw [hv, Matrix.mulVec_zero])
  have := congrFun h0 j
  simp at this

/-- The adapted change of basis keeps the actual coordinate-line character. -/
theorem basisConjugate_coordinateLineCharacter
    (ρ : MatrixRepresentation G n) (B : GL n k) (a j : n)
    (hB : IsCoordinateLineBasis B a j)
    (h : ρ.PreservesCoordinateLine j) (h' : (ρ.basisConjugate B).PreservesCoordinateLine a) :
    (ρ.basisConjugate B).coordinateLineCharacter a h' = ρ.coordinateLineCharacter j h := by
  apply hom_ext_points
  intro Z x
  apply (Gm.pointsEquiv (Spec (CommRingCat.of k)) Z).injective
  rw [coordinateLineCharacter_scalar, coordinateLineCharacter_scalar]
  have h1 := coordinateLineScalar_spec (ρ.basisConjugate B) a h' Z x
  have h2 := (ρ.basisConjugate_coordinateScalar_iff B a j hB Z x _).mp h1
  have h3 := coordinateLineScalar_spec ρ j h Z x
  apply Units.ext
  have := congrFun (h2.symm.trans h3) j
  simpa using this

/-- A conjugate cocharacter has selected-line weight at most the weight of a
cocharacter whose dynamic parabolic preserves that line. -/
theorem coordinateLineCocharacterWeight_le_of_conj_parabolic_eigenline
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    {U P : GroupScheme (Spec (CommRingCat.of k))}
    (ρ : MatrixRepresentation G n)
    (χ χ' : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (iU : U ⟶ G) (iP : P ⟶ G)
    (hU : (Dynamic.unipotent (Dynamic.oppositeCocharacter χ)).IsRepresentedBy iU)
    (hP : (Dynamic.parabolic χ).IsRepresentedBy iP)
    (j : n) (hline : (ρ.restrict iP).PreservesCoordinateLine j)
    (hχline : (ρ.restrict χ).PreservesCoordinateLine j)
    (hχ'line : (ρ.restrict χ').PreservesCoordinateLine j)
    {g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X}
    (hg : χ' ≫ (G.innerIso g).hom = χ) :
    (ρ.restrict χ').coordinateLineCocharacterWeight j hχ'line ≤
      (ρ.restrict χ).coordinateLineCocharacterWeight j hχline := by
  obtain ⟨B, e, a, hB, he, hdiag⟩ :=
    (ρ.restrict χ).exists_diagonalization_retaining_coordinateLine j hχline
  have hPline : ((ρ.basisConjugate B).restrict iP).PreservesCoordinateLine a := by
    change ((ρ.restrict iP).conjugate
      (GeneralLinear.CocharacterDiagonal.rationalMatrixPoint B⁻¹)).PreservesCoordinateLine a
    exact ((ρ.restrict iP).basisConjugate_preservesCoordinateLine_iff B a j hB).mpr hline
  have hd : χ ≫ ρ.basisConjugate B =
      GeneralLinear.diagonalCocharacter n (CommRingCat.of k) e :=
    (Category.assoc χ ρ _).symm.trans hdiag
  have hup := (ρ.basisConjugate B).hasOrbitWeightUpperBound_of_parabolic_eigenline
    χ e hd iU iP hU hP a hPline
  have hχ'a : ((ρ.basisConjugate B).restrict χ').PreservesCoordinateLine a := by
    change ((ρ.restrict χ').conjugate
      (GeneralLinear.CocharacterDiagonal.rationalMatrixPoint B⁻¹)).PreservesCoordinateLine a
    exact ((ρ.restrict χ').basisConjugate_preservesCoordinateLine_iff B a j hB).mpr hχ'line
  have hw : ((ρ.basisConjugate B).restrict χ').coordinateLineCocharacterWeight a hχ'a =
      (ρ.restrict χ').coordinateLineCocharacterWeight j hχ'line := by
    unfold coordinateLineCocharacterWeight coordinateLineRationalCharacter
    exact congrArg (fun f => gmEndEquiv k
      ((rationalCharacters.equivCharacterLattice (Gm (Spec (CommRingCat.of k))))
        (Additive.ofMul f)))
      ((ρ.restrict χ').basisConjugate_coordinateLineCharacter B a j hB hχ'line hχ'a)
  have hm := ((ρ.basisConjugate B).restrict χ').hasCoordinatePowerAction_coordinateLineCocharacterWeight
    a hχ'a
  have hle := (ρ.basisConjugate B).le_of_conj_powerAction_of_orbitWeightUpperBound
    χ χ' e hd hg a hup _ hm
  rw [hw, he] at hle
  exact hle

/-- Restricting along a further homomorphism keeps a preserved coordinate line. -/
theorem preservesCoordinateLine_restrict_comp {H K : GroupScheme (Spec (CommRingCat.of k))}
    (ρ : MatrixRepresentation G n) (f : H ⟶ G) (h : K ⟶ H) (j : n)
    (hline : (ρ.restrict f).PreservesCoordinateLine j) :
    (ρ.restrict (h ≫ f)).PreservesCoordinateLine j := by
  intro Z x
  obtain ⟨c, hc⟩ := hline Z (x ≫ h.hom.hom)
  refine ⟨c, ?_⟩
  simpa only [pointMatrix_restrict, Category.assoc, ← Grp.comp_hom_hom] using hc

variable {T : CommGroupScheme (Spec (CommRingCat.of k))}

/-- Every actual relative Weyl translate of a cocharacter whose dynamic
parabolic preserves the coordinate line has no larger line-character pairing. -/
theorem latticePairing_relativeWeyl_le_of_parabolic_eigenline
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    {U P : GroupScheme (Spec (CommRingCat.of k))}
    (ρ : MatrixRepresentation G n) (i : T.toGrp ⟶ G) [Mono i.hom.hom.left]
    (ζ : cocharacterLattice T) (iU : U ⟶ G) (iP : P ⟶ G)
    (hU : (Dynamic.unipotent (Dynamic.oppositeCocharacter
      (CommGroupScheme.groupHom ζ ≫ i))).IsRepresentedBy iU)
    (hP : (Dynamic.parabolic (CommGroupScheme.groupHom ζ ≫ i)).IsRepresentedBy iP)
    (j : n) (hline : (ρ.restrict iP).PreservesCoordinateLine j)
    (hTline : (ρ.restrict i).PreservesCoordinateLine j)
    (w : relativeWeylGroup i) :
    latticePairing T (ρ.torusCoordinateLineCharacter i j hTline)
        (relativeWeylCocharacterAction i w ζ) ≤
      latticePairing T (ρ.torusCoordinateLineCharacter i j hTline) ζ := by
  obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective w
  rw [relativeWeylCocharacterAction_mk, cocharacterAut_apply]
  let σ := normalizingAut i s
  let ζ' : cocharacterLattice T := ζ ≫ σ.hom
  have hζline := preservesCoordinateLine_restrict_comp ρ i (CommGroupScheme.groupHom ζ) j hTline
  have hζ'line := preservesCoordinateLine_restrict_comp ρ i (CommGroupScheme.groupHom ζ') j hTline
  have hinv := (isNormalizingPoint_normalizingAut i s).inv
  have hg : (CommGroupScheme.groupHom ζ' ≫ i) ≫
      (G.innerIso ((s : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)⁻¹)).hom =
        CommGroupScheme.groupHom ζ ≫ i := by
    rw [Category.assoc, hinv, ← Category.assoc]
    change CommGroupScheme.groupHom (ζ ≫ σ.hom ≫ σ.inv) ≫ i = _
    rw [Iso.hom_inv_id, Category.comp_id]
  have hle := ρ.coordinateLineCocharacterWeight_le_of_conj_parabolic_eigenline
    (CommGroupScheme.groupHom ζ ≫ i) (CommGroupScheme.groupHom ζ' ≫ i) iU iP hU hP j hline
    hζline hζ'line hg
  rwa [ρ.coordinateLineCocharacterWeight_eq_latticePairing i ζ j hTline hζline,
    ρ.coordinateLineCocharacterWeight_eq_latticePairing i ζ' j hTline hζ'line] at hle

/-- The integral Weyl norm-kernel correction of a cocharacter whose dynamic
parabolic preserves the coordinate line has nonnegative line-character pairing. -/
theorem latticePairing_normKernelCocharacter_nonneg_of_parabolic_eigenline
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    {U P : GroupScheme (Spec (CommRingCat.of k))}
    (ρ : MatrixRepresentation G n) (i : T.toGrp ⟶ G) [Mono i.hom.hom.left]
    [Fintype (relativeWeylGroup i)]
    (ζ : cocharacterLattice T) (iU : U ⟶ G) (iP : P ⟶ G)
    (hU : (Dynamic.unipotent (Dynamic.oppositeCocharacter
      (CommGroupScheme.groupHom ζ ≫ i))).IsRepresentedBy iU)
    (hP : (Dynamic.parabolic (CommGroupScheme.groupHom ζ ≫ i)).IsRepresentedBy iP)
    (j : n) (hline : (ρ.restrict iP).PreservesCoordinateLine j)
    (hTline : (ρ.restrict i).PreservesCoordinateLine j) :
    0 ≤ latticePairing T (ρ.torusCoordinateLineCharacter i j hTline)
      (normKernelCocharacter i ζ) := by
  classical
  rw [normKernelCocharacter, map_sub, map_nsmul, relativeWeylCocharacterSum_apply, map_sum,
    sub_nonneg]
  have h := Finset.sum_le_card_nsmul Finset.univ
    (fun w : relativeWeylGroup i => latticePairing T (ρ.torusCoordinateLineCharacter i j hTline)
      (relativeWeylCocharacterAction i w ζ))
    (latticePairing T (ρ.torusCoordinateLineCharacter i j hTline) ζ)
    (fun w _ => ρ.latticePairing_relativeWeyl_le_of_parabolic_eigenline i ζ iU iP hU hP j
      hline hTline w)
  simpa only [Finset.card_univ] using h

end Langlands.GroupScheme.MatrixRepresentation


namespace Langlands.LinearAlgebra.RationalSpan

/-- Every element of a rational span has a positive integral multiple coming
from the integral span of the same set. -/
theorem exists_pos_nsmul_eq_toRat_of_mem_ratSpan {M : Type*} [AddCommGroup M] {R : Set M}
    {x : ℚ ⊗[ℤ] M} (hx : x ∈ ratSpan R) :
    ∃ d : ℕ, 0 < d ∧ ∃ m ∈ Submodule.span ℤ R, d • x = toRat m := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨m, hm, rfl⟩ := hy
    exact ⟨1, one_pos, m, Submodule.subset_span hm, one_smul _ _⟩
  | zero => exact ⟨1, one_pos, 0, zero_mem _, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨d, hd, m, hm, hdm⟩ := hx
    obtain ⟨e, he, m', hm', hem⟩ := hy
    refine ⟨d * e, Nat.mul_pos hd he, e • m + d • m',
      add_mem (Submodule.smul_of_tower_mem _ e hm) (Submodule.smul_of_tower_mem _ d hm'), ?_⟩
    rw [smul_add, mul_comm d e, mul_smul, hdm, mul_comm e d, mul_smul, hem,
      map_add, map_nsmul, map_nsmul]
  | smul q x _ hx =>
    obtain ⟨d, hd, m, hm, hdm⟩ := hx
    refine ⟨q.den * d, Nat.mul_pos q.pos hd, q.num • m, Submodule.smul_mem _ _ hm, ?_⟩
    rw [map_zsmul, ← hdm, ← Nat.cast_smul_eq_nsmul ℚ, ← Nat.cast_smul_eq_nsmul ℚ,
      ← Int.cast_smul_eq_zsmul ℚ, smul_smul, smul_smul]
    congr 1
    push_cast
    rw [mul_comm (q.den : ℚ) d, mul_assoc, Rat.den_mul_eq_num, mul_comm]

end Langlands.LinearAlgebra.RationalSpan

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {n : Type} [Fintype n] [DecidableEq n]
  [IsAffineHom G.X.hom] (i : T.toGrp ⟶ G)

/-- Every actual torus character has a positive multiple equal to a restricted
ambient rational character plus an integral combination of simple roots. -/
theorem exists_pos_nsmul_eq_restrict_add_mem_span_simpleRelativeRoots
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (ν : cocharacterLattice T) (hν : IsGenericCocharacter i ν)
    (χ : characterLattice T) :
    ∃ d : ℕ, 0 < d ∧ ∃ θ : rationalCharacters G,
      ∃ r ∈ Submodule.span ℤ (simpleRelativeRoots i ν),
        d • χ = torusCharacterRestrict i θ + r := by
  let := hi.isSplitSubtorus.mono
  have hroots := relativeRootSystem k G hG T i hi
  have hχ : toRat χ ∈ relativeRootSpan i ⊔
      (rationalCharacterRestrictRat i).range := by
    rw [hG.relativeRootSpan_sup_restrictionRange_eq_top i hi]
    exact Submodule.mem_top
  obtain ⟨x, hx, y, ⟨θ, rfl⟩, hsum⟩ := Submodule.mem_sup.mp hχ
  rw [← ratSpan_simpleRelativeRoots_eq_relativeRootSpan i ν hν
    (fun _ hβ => hroots.neg_mem_relativeRoots i hi.1.1 hβ)] at hx
  obtain ⟨d, hd, r, hr, hdx⟩ := exists_pos_nsmul_eq_toRat_of_mem_ratSpan hx
  obtain ⟨e, he, θ', hθ'⟩ := exists_pos_nsmul_eq_toRat θ
  refine ⟨d * e, Nat.mul_pos hd he, d • θ', e • r, Submodule.smul_of_tower_mem _ e hr, ?_⟩
  apply hi.1.1.character_toRat_injective
  have hθi : e • rationalCharacterRestrictRat i θ =
      toRat (torusCharacterRestrict i θ') := by
    rw [← map_nsmul, hθ']
    rfl
  rw [map_add, map_nsmul, map_nsmul, map_nsmul, ← hsum, smul_add, mul_comm d e, mul_smul,
    hdx, mul_comm e d, mul_smul, hθi, add_comm, map_nsmul]

/-- Every standard cocharacter for the empty index has the minimal standard
parabolic as its dynamic parabolic. -/
theorem Dynamic.parabolic_eq_standardParabolic_empty_of_isStandardCocharacter
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (ν : cocharacterLattice T) (hν : IsGenericCocharacter i ν)
    {ζ : cocharacterLattice T} (hζ : IsStandardCocharacter i ν ∅ ζ) :
    Dynamic.parabolic (CommGroupScheme.groupHom ζ ≫ i) = standardParabolic i ν ∅ := by
  let := hi.isSplitSubtorus.mono
  have hroots := relativeRootSystem k G hG T i hi
  rw [standardParabolic_empty_eq_dynamic_of_generic i ν hG hi hν]
  apply le_antisymm
  · apply ((relativeRootSignInclusions k G hG T i hi ζ ν).1).mpr
    intro α hα hnonneg
    by_contra hneg
    have hneg' : 0 < latticePairing T (-α) ν := by
      rw [map_neg, LinearMap.neg_apply]
      omega
    have hpos := hζ.pairing_pos_of_positive_empty i ν
      ⟨hroots.neg_mem_relativeRoots i hi.1.1 hα, hneg'⟩
    rw [map_neg, LinearMap.neg_apply] at hpos
    omega
  · apply ((relativeRootSignInclusions k G hG T i hi ν ζ).1).mpr
    intro α hα hnonneg
    have hpos : 0 < latticePairing T α ν := by
      have hne := hν α hα
      omega
    exact (hζ.pairing_pos_of_positive_empty i ν ⟨hα, hpos⟩).le

/-- An integral combination of simple roots whose pairing with every
empty-index standard cocharacter is nonnegative has nonnegative coefficients. -/
theorem mem_closure_simpleRelativeRoots_of_standard_pairing_nonneg
    [Mono i.hom.hom.left] (hroots : HasRelativeRootSystem i) (hT : IsSplitTorus T.toGrp)
    (ν : cocharacterLattice T) (hν : IsGenericCocharacter i ν)
    {r : characterLattice T} (hr : r ∈ Submodule.span ℤ (simpleRelativeRoots i ν))
    (hnonneg : ∀ ζ, IsStandardCocharacter i ν ∅ ζ → 0 ≤ latticePairing T r ζ) :
    r ∈ AddSubmonoid.closure (simpleRelativeRoots i ν) := by
  classical
  obtain ⟨l, rfl⟩ := (Finsupp.mem_span_iff_linearCombination ℤ _ r).mp hr
  have hcoeff : ∀ β : simpleRelativeRoots i ν, 0 ≤ l β := by
    intro β
    by_contra hneg
    have hneg' : l β < 0 := not_le.mp hneg
    obtain ⟨ω, hω⟩ := hroots.exists_standardCocharacter i ν hT hν
      (simpleRelativeRoots i ν \ {(β : characterLattice T)}) Set.sdiff_subset
    have hβω : 0 < latticePairing T β ω :=
      hω.2.2 β β.2 (fun h => h.2 rfl)
    have hω0 : ∀ α ∈ simpleRelativeRoots i ν, 0 ≤ latticePairing T α ω := by
      intro α hα
      by_cases hαβ : α = β
      · rw [hαβ]; exact hβω.le
      · exact (hω.2.1 α ⟨hα, hαβ⟩).ge
    have hpair : latticePairing T (Finsupp.linearCombination ℤ Subtype.val l) ω =
        l β * latticePairing T β ω := by
      rw [← LinearMap.flip_apply (latticePairing T), Finsupp.apply_linearCombination,
        Finsupp.linearCombination_apply]
      rw [Finsupp.sum_eq_single β]
      · simp
      · intro α _ hαβ
        have hαβ' : (α : characterLattice T) ≠ β := fun h => hαβ (Subtype.ext h)
        simp [hω.2.1 α ⟨α.2, hαβ'⟩]
      · simp
    have hlt : latticePairing T (Finsupp.linearCombination ℤ Subtype.val l) ω < 0 := by
      rw [hpair]
      exact mul_neg_of_neg_of_pos hneg' hβω
    let M : ℕ := (latticePairing T (Finsupp.linearCombination ℤ Subtype.val l) ν).natAbs + 1
    have hstd : IsStandardCocharacter i ν ∅ (ν + M • ω) := by
      refine ⟨Set.empty_subset _, by simp, ?_⟩
      intro α hα _
      rw [map_add, map_nsmul]
      have h1 : 0 < latticePairing T α ν := hα.1.2
      have h2 : 0 ≤ M • latticePairing T α ω := nsmul_nonneg (hω0 α hα) M
      omega
    have h := hnonneg _ hstd
    rw [map_add, map_nsmul, nsmul_eq_mul] at h
    have hM : ((M : ℕ) : ℤ) = |latticePairing T (Finsupp.linearCombination ℤ Subtype.val l) ν| + 1 := by
      simp only [M, Nat.cast_add, Nat.cast_one, Int.natCast_natAbs]
    rw [hM] at h
    have habs := le_abs_self (latticePairing T (Finsupp.linearCombination ℤ Subtype.val l) ν)
    nlinarith
  rw [Finsupp.linearCombination_apply, Finsupp.sum]
  refine sum_mem (fun β _ => ?_)
  obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le (hcoeff β)
  rw [hm, natCast_zsmul]
  exact AddSubmonoid.nsmul_mem _ (AddSubmonoid.subset_closure β.2) m

end Langlands.GroupScheme

namespace Langlands.GroupScheme.MatrixRepresentation

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {n : Type} [Fintype n] [DecidableEq n]
  [IsAffineHom G.X.hom] (ρ : MatrixRepresentation G n) (i : T.toGrp ⟶ G)

/-- A coordinate line preserved by the minimal standard parabolic is preserved
by the maximal split torus. -/
theorem preservesCoordinateLine_torus_of_minimalStandardParabolic
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (ν : cocharacterLattice T) (hν : IsGenericCocharacter i ν) (j : n)
    (hline : (ρ.restrict (Standard.parabolicHom i ν ∅)).PreservesCoordinateLine j) :
    (ρ.restrict i).PreservesCoordinateLine j := by
  have hP : (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i)).IsRepresentedBy
      (Standard.parabolicHom i ν ∅) := by
    rw [← standardParabolic_empty_eq_dynamic_of_generic i ν hG hi hν]
    exact Standard.isRepresentedBy_parabolicHom i ν ∅
  exact ρ.preservesCoordinateLine_torus_of_parabolic i ν _ hP j hline

/-- The torus character of a coordinate line preserved by the minimal standard
parabolic has a positive multiple which, modulo a restricted ambient rational
character, is a nonnegative integral combination of simple relative roots. -/
theorem exists_pos_nsmul_sub_restrict_mem_closure_simpleRelativeRoots
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (ν : cocharacterLattice T) (hν : IsGenericCocharacter i ν) (j : n)
    (hline : (ρ.restrict (Standard.parabolicHom i ν ∅)).PreservesCoordinateLine j)
    (hTline : (ρ.restrict i).PreservesCoordinateLine j) :
    ∃ d : ℕ, 0 < d ∧ ∃ θ : rationalCharacters G,
      d • ρ.torusCoordinateLineCharacter i j hTline - torusCharacterRestrict i θ ∈
        AddSubmonoid.closure (simpleRelativeRoots i ν) := by
  let : Smooth G.X.hom := hG.smooth
  let : ConnectedSpace G.X.left := hG.connectedSpace
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : Mono i.hom.hom.left := hi.isSplitSubtorus.mono
  have hroots := relativeRootSystem k G hG T i hi
  let : Fintype (relativeWeylGroup i) := relativeWeylGroupFintype i hroots
  have hspan : ∀ x ∈ Submodule.span ℤ (simpleRelativeRoots i ν), ∀ ζ,
      latticePairing T x (normKernelCocharacter i ζ) =
        Fintype.card (relativeWeylGroup i) • latticePairing T x ζ := by
    intro x hx ζ
    induction hx using Submodule.span_induction with
    | mem x hx =>
      exact latticePairing_normKernelCocharacter_root_of_relativeRootSystem
        i hi.1.1 hroots ζ x hx.1.1
    | zero => simp
    | add x y _ _ hx hy =>
      rw [map_add, LinearMap.add_apply, LinearMap.add_apply, hx, hy, smul_add]
    | smul a x _ hx =>
      rw [map_zsmul, LinearMap.smul_apply, LinearMap.smul_apply, hx, smul_comm a]
  obtain ⟨d, hd, θ, r, hr, hrel⟩ :=
    exists_pos_nsmul_eq_restrict_add_mem_span_simpleRelativeRoots i hG hi ν hν
      (ρ.torusCoordinateLineCharacter i j hTline)
  refine ⟨d, hd, θ, ?_⟩
  rw [hrel, add_sub_cancel_left]
  apply mem_closure_simpleRelativeRoots_of_standard_pairing_nonneg i hroots hi.1.1 ν hν hr
  intro ζ hζ
  have hP : (Dynamic.parabolic (CommGroupScheme.groupHom ζ ≫ i)).IsRepresentedBy
      (Standard.parabolicHom i ν ∅) := by
    rw [Dynamic.parabolic_eq_standardParabolic_empty_of_isStandardCocharacter i hG hi ν hν hζ]
    exact Standard.isRepresentedBy_parabolicHom i ν ∅
  have hnn := ρ.latticePairing_normKernelCocharacter_nonneg_of_parabolic_eigenline i ζ
    (Dynamic.Affine.unipotentHom (Dynamic.oppositeCocharacter (CommGroupScheme.groupHom ζ ≫ i)))
    (Standard.parabolicHom i ν ∅)
    (Dynamic.Affine.isRepresentedBy_unipotentHom _) hP j hline hTline
  have h1 := congrArg (fun x => latticePairing T x (normKernelCocharacter i ζ)) hrel
  simp only [map_add, map_nsmul, LinearMap.add_apply, LinearMap.smul_apply,
    latticePairing_normKernelCocharacter_restrict, zero_add] at h1
  rw [hspan r hr ζ, nsmul_eq_mul, nsmul_eq_mul] at h1
  have hcard : (0 : ℤ) < Fintype.card (relativeWeylGroup i) := by
    exact_mod_cast Fintype.card_pos
  have hprod : 0 ≤ (d : ℤ) * latticePairing T (ρ.torusCoordinateLineCharacter i j hTline)
      (normKernelCocharacter i ζ) := mul_nonneg (by positivity) hnn
  rw [h1] at hprod
  exact (mul_nonneg_iff_of_pos_left hcard).mp hprod

end Langlands.GroupScheme.MatrixRepresentation
