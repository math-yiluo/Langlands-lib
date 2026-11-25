import Langlands.Global.AdelicParabolicProjectiveHeight
import Langlands.Global.AdelicOpenIwasawaCompact
import Langlands.Global.Adelic
import Langlands.ClassFieldTheory.Global.IdeleArchimedean
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace

/-! # Archimedean coordinates of the Iwasawa height of a line character -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain
open scoped CategoryTheory.MonObj NNReal Matrix

set_option autoImplicit false

namespace Langlands.Global.EisensteinGenericInjectivity

open Langlands.GroupScheme AdelicGroupPoints RepresentationGrowth

variable {F : Type u} [Field F] [NumberField F]

/-- The complex coordinate of an adele at an infinite place: the Library projection
`infiniteProjection` to the completion followed by its isometric embedding into `ℂ`. -/
def placeHom (w : InfinitePlace F) : AdeleRing (𝓞 F) F →+* ℂ :=
  (InfinitePlace.Completion.extensionEmbedding w).comp (infiniteProjection F w)

theorem placeHom_apply (w : InfinitePlace F) (x : AdeleRing (𝓞 F) F) :
    placeHom w x = InfinitePlace.Completion.extensionEmbedding w (x.1 w) := rfl

/-- On principal adeles, `placeHom w` is Mathlib's complex embedding `w.embedding`, by the
Library lemma `Langlands.ClassFieldTheory.Global.extensionEmbedding_algebraMap`. -/
theorem placeHom_algebraMap (w : InfinitePlace F) (x : F) :
    placeHom w (algebraMap F (AdeleRing (𝓞 F) F) x) = w.embedding x :=
  Langlands.ClassFieldTheory.Global.extensionEmbedding_algebraMap w x

theorem norm_placeHom (w : InfinitePlace F) (x : AdeleRing (𝓞 F) F) :
    ‖placeHom w x‖ = ‖x.1 w‖ :=
  (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) _

theorem continuous_placeHom (w : InfinitePlace F) : Continuous (placeHom (F := F) w) :=
  (InfinitePlace.Completion.isometry_extensionEmbedding w).continuous.comp
    (continuous_infiniteProjection F w)

variable {G : GroupScheme (Spec (CommRingCat.of F))} {N : ℕ}

/-- The complex matrix of a representation at an infinite place. -/
def placeMatrix (σ : MatrixRepresentation G (Fin N)) (w : InfinitePlace F)
    (x : AdelicGroupPoints F G) : Matrix (Fin N) (Fin N) ℂ :=
  ((adelicMatrix F G σ x : AdelicGL F N) : Matrix (Fin N) (Fin N) (AdeleRing (𝓞 F) F)).map
    (placeHom w)

theorem placeMatrix_mul (σ : MatrixRepresentation G (Fin N)) (w : InfinitePlace F)
    (x y : AdelicGroupPoints F G) :
    placeMatrix σ w (x * y) = placeMatrix σ w x * placeMatrix σ w y := by
  simp only [placeMatrix, map_mul, Units.val_mul, Matrix.map_mul]

theorem placeMatrix_one (σ : MatrixRepresentation G (Fin N)) (w : InfinitePlace F) :
    placeMatrix σ w (1 : AdelicGroupPoints F G) = 1 := by
  simp only [placeMatrix, map_one, Units.val_one, Matrix.map_one, map_zero, map_one]

theorem placeMatrix_mulVec_mulVec (σ : MatrixRepresentation G (Fin N)) (w : InfinitePlace F)
    (x y : AdelicGroupPoints F G) (z : Fin N → ℂ) :
    placeMatrix σ w x *ᵥ (placeMatrix σ w y *ᵥ z) = placeMatrix σ w (x * y) *ᵥ z := by
  rw [Matrix.mulVec_mulVec, placeMatrix_mul]

theorem placeMatrix_inv_mulVec (σ : MatrixRepresentation G (Fin N)) (w : InfinitePlace F)
    (x : AdelicGroupPoints F G) (z : Fin N → ℂ) :
    placeMatrix σ w x⁻¹ *ᵥ (placeMatrix σ w x *ᵥ z) = z := by
  rw [placeMatrix_mulVec_mulVec, inv_mul_cancel, placeMatrix_one, Matrix.one_mulVec]

/-- An archimedean energy: positive, of degree two under complex scalars and invariant under
the given compact subgroup at the place. -/
structure IsInvariantEnergy (σ : MatrixRepresentation G (Fin N)) (w : InfinitePlace F)
    (K : Subgroup (AdelicGroupPoints F G)) (Q : (Fin N → ℂ) → ℝ) : Prop where
  pos : ∀ z, z ≠ 0 → 0 < Q z
  smul : ∀ (c : ℂ) (z : Fin N → ℂ), Q (c • z) = ‖c‖ ^ 2 * Q z
  invariant : ∀ k ∈ K, ∀ z, Q (placeMatrix σ w k *ᵥ z) = Q z

section Character

variable {P : GroupScheme (Spec (CommRingCat.of F))} [IsAffine P.X.left]

/-- The infinite coordinates of an idele character value depend only on the infinite part. -/
theorem character_val_fst (χ : AlgebraicCharacter F P) (y : AdelicGroupPoints F P) :
    (character F P χ y).val.1 =
      (characterUnits F P χ (CommAlgCat.of F (InfiniteAdeleRing F)) (infinite F P y)).val :=
  (congrArg Units.val (characterUnits_naturality F P χ (CommAlgCat.ofHom
    (AlgHom.fst F (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))) y)).symm

/-- The finite coordinates of an idele character value depend only on the finite part. -/
theorem character_val_snd (χ : AlgebraicCharacter F P) (y : AdelicGroupPoints F P) :
    (character F P χ y).val.2 =
      (characterUnits F P χ (CommAlgCat.of F (FiniteAdeleRing (𝓞 F) F)) (finite F P y)).val :=
  (congrArg Units.val (characterUnits_naturality F P χ (CommAlgCat.ofHom
    (AlgHom.snd F (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))) y)).symm

/-- The character norm of a point whose finite part has norm one is the archimedean product. -/
theorem characterNorm_eq_prod_placeHom (χ : AlgebraicCharacter F P) (y : AdelicGroupPoints F P)
    (hy : characterNorm F P χ (ofFinite F P (finite F P y)) = 1) :
    ((characterNorm F P χ y : ℝ≥0) : ℝ) =
      ∏ w : InfinitePlace F, ‖placeHom w (character F P χ y).val‖ ^ w.mult := by
  have hsplit : y = ofInfinite F P (infinite F P y) * ofFinite F P (finite F P y) := by
    rw [ofInfinite_eq_pair, ofFinite_eq_pair, pair_mul, mul_one, one_mul, pair_projections]
  have hinf : characterNorm F P χ y = characterNorm F P χ (ofInfinite F P (infinite F P y)) := by
    conv_lhs => rw [hsplit]
    rw [map_mul, hy, mul_one]
  rw [hinf]
  change ((IdeleAbsoluteValue.full F (character F P χ (ofInfinite F P (infinite F P y))) :
    ℝ≥0) : ℝ) = _
  rw [IdeleAbsoluteValue.coe_full F]
  have h2 : (character F P χ (ofInfinite F P (infinite F P y))).val.2 = 1 := by
    rw [character_val_snd, finite_ofInfinite, map_one, Units.val_one]
  have h1 : (character F P χ (ofInfinite F P (infinite F P y))).val.1 =
      (character F P χ y).val.1 := by
    rw [character_val_fst, character_val_fst, infinite_ofInfinite]
  rw [h2, h1]
  simp only [norm_placeHom]
  have hf : (∏ᶠ v, ‖(1 : FiniteAdeleRing (𝓞 F) F) v‖) = 1 := by
    exact finprod_eq_one_of_forall_eq_one fun v => norm_one
  rw [hf, mul_one]

end Character

section Iwasawa

variable [IsAffine G.X.left] {P : GroupScheme (Spec (CommRingCat.of F))} [IsAffine P.X.left]
  {p : P ⟶ G} [IsClosedImmersion p.hom.hom.left] {K : Subgroup (AdelicGroupPoints F G)}

omit [IsClosedImmersion p.hom.hom.left] in
/-- The adelic map of a homomorphism preserves the included finite factor. -/
theorem map_ofFinite (y : FiniteAdelicGroupPoints F P) :
    map F P G p (ofFinite F P y) =
      ofFinite F G (P.affinePointsTarget p (CommAlgCat.of F (FiniteAdeleRing (𝓞 F) F)) y) := by
  apply (split F G).injective
  have hinf : infinite F G (map F P G p (ofFinite F P y)) =
      P.affinePointsTarget p (CommAlgCat.of F (InfiniteAdeleRing F))
        (infinite F P (ofFinite F P y)) :=
    DFunLike.congr_fun (P.affinePointsTarget_naturality p (CommAlgCat.ofHom
      (AlgHom.fst F (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)))) _
  rw [split_apply, split_apply, hinf, finite_map, infinite_ofFinite, finite_ofFinite,
    infinite_ofFinite, finite_ofFinite, map_one]

/-- A point of `P(𝔸)` whose finite part lies in the finite projection of the compact group
has finite part of character norm one. -/
theorem characterNorm_ofFinite_finite_eq_one (hK : IsIwasawaCompact p K)
    (χ : AlgebraicCharacter F P) (q : AdelicGroupPoints F P) {k : AdelicGroupPoints F G}
    (hk : k ∈ K) (h : finite F G (map F P G p q) = finite F G k) :
    characterNorm F P χ (ofFinite F P (finite F P q)) = 1 := by
  let f : AdelicGroupPoints F G →ₜ* AdelicGroupPoints F G :=
    (ofFinite F G).comp (finite F G)
  let K' : Subgroup (AdelicGroupPoints F G) := K.map f.toMonoidHom
  have hK' : IsCompact (K' : Set (AdelicGroupPoints F G)) := by
    rw [Subgroup.coe_map]
    exact hK.isCompact.image f.continuous
  have hmem : map F P G p (ofFinite F P (finite F P q)) ∈ K' := by
    rw [map_ofFinite, ← finite_map, h]
    exact ⟨k, hk, rfl⟩
  have hlog := characterLog_eq_zero_of_map_mem F p hK' hmem
  exact (mem_normOneSubgroup F P _).mp ((characterLog_eq_zero_iff F P _).mp hlog) χ

variable {σ : MatrixRepresentation G (Fin N)} {j : Fin N} {χ : AlgebraicCharacter F P}

omit [IsAffine G.X.left] [IsAffine P.X.left] [IsClosedImmersion p.hom.hom.left] in
/-- At an infinite place, the parabolic acts on the selected line through the character. -/
theorem placeMatrix_map_mulVec (w : InfinitePlace F)
    (ha : ∀ q : AdelicGroupPoints F P,
      ((adelicMatrix F G σ (map F P G p q) : AdelicGL F N) :
          Matrix (Fin N) (Fin N) (AdeleRing (𝓞 F) F)) *ᵥ Pi.single j 1 =
        (character F P χ q).val • Pi.single j 1)
    (q : AdelicGroupPoints F P) :
    placeMatrix σ w (map F P G p q) *ᵥ Pi.single j 1 =
      placeHom w (character F P χ q).val • Pi.single j 1 := by
  have h := ha q
  funext i
  have hi := congrFun h i
  simp only [Matrix.mulVec_single_one, Matrix.col_apply, Pi.smul_apply, smul_eq_mul] at hi ⊢
  simp only [placeMatrix, Matrix.map_apply, hi, map_mul]
  by_cases hij : i = j
  · subst hij
    simp
  · simp [hij]

omit [IsAffine G.X.left] [IsAffine P.X.left] [IsClosedImmersion p.hom.hom.left] in
/-- The invariant energy of the inverse orbit vector is governed by the line character of
the parabolic Iwasawa factor. -/
theorem energy_inv_mulVec {w : InfinitePlace F} {Q : (Fin N → ℂ) → ℝ}
    (hQ : IsInvariantEnergy σ w K Q)
    (ha : ∀ q : AdelicGroupPoints F P,
      ((adelicMatrix F G σ (map F P G p q) : AdelicGL F N) :
          Matrix (Fin N) (Fin N) (AdeleRing (𝓞 F) F)) *ᵥ Pi.single j 1 =
        (character F P χ q).val • Pi.single j 1)
    (q : AdelicGroupPoints F P) {k : AdelicGroupPoints F G} (hk : k ∈ K) :
    Q (placeMatrix σ w (map F P G p q * k)⁻¹ *ᵥ Pi.single j 1) =
      ‖placeHom w (character F P χ q⁻¹).val‖ ^ 2 * Q (Pi.single j 1) := by
  rw [mul_inv_rev, ← map_inv, ← placeMatrix_mulVec_mulVec, placeMatrix_map_mulVec w ha,
    Matrix.mulVec_smul, hQ.smul, hQ.invariant _ (K.inv_mem hk)]

omit [IsAffine P.X.left] in
theorem placeHom_character_mul (w : InfinitePlace F) (a b : AdelicGroupPoints F P) :
    placeHom w (character F P χ (a * b)).val =
      placeHom w (character F P χ a).val * placeHom w (character F P χ b).val := by
  rw [map_mul, Units.val_mul, map_mul]

omit [IsAffine P.X.left] in
theorem norm_placeHom_character_inv_mul (w : InfinitePlace F) (a : AdelicGroupPoints F P) :
    ‖placeHom w (character F P χ a⁻¹).val‖ * ‖placeHom w (character F P χ a).val‖ = 1 := by
  rw [← norm_mul, ← placeHom_character_mul, inv_mul_cancel, map_one, Units.val_one, map_one,
    norm_one]

/-- **Archimedean formula for height differences.** If two adelic points have the same finite
part, the difference of their Iwasawa heights at the line character is computed by the
invariant archimedean energies of their inverse orbit vectors. -/
theorem exp_two_mul_height_sub (hK : IsIwasawaCompact p K) {χ : rationalCharacters P}
    {Q : InfinitePlace F → (Fin N → ℂ) → ℝ} (hQ : ∀ w, IsInvariantEnergy σ w K (Q w))
    (ha : ∀ q : AdelicGroupPoints F P,
      ((adelicMatrix F G σ (map F P G p q) : AdelicGL F N) :
          Matrix (Fin N) (Fin N) (AdeleRing (𝓞 F) F)) *ᵥ Pi.single j 1 =
        (character F P χ.toMul q).val • Pi.single j 1)
    (x y : AdelicGroupPoints F G) (hxy : finite F G x = finite F G y) :
    Real.exp (2 * (hK.height y χ - hK.height x χ)) =
      ∏ w : InfinitePlace F, (Q w (placeMatrix σ w x⁻¹ *ᵥ Pi.single j 1) /
        Q w (placeMatrix σ w y⁻¹ *ᵥ Pi.single j 1)) ^ w.mult := by
  obtain ⟨qx, kx, hkx, rfl⟩ := hK.exists_eq x
  obtain ⟨qy, ky, hky, rfl⟩ := hK.exists_eq y
  let q := qx⁻¹ * qy
  have hmap : map F P G p q = kx * (map F P G p qx * kx)⁻¹ * (map F P G p qy * ky) * ky⁻¹ := by
    simp only [q, map_mul, map_inv]
    group
  have hxy' : finite F G (map F P G p qx) * finite F G kx =
      finite F G (map F P G p qy) * finite F G ky := by
    simpa only [map_mul] using hxy
  have hfin : finite F G (map F P G p q) = finite F G (kx * ky⁻¹) := by
    rw [hmap]
    simp only [map_mul, map_inv]
    rw [hxy']
    group
  have hN := characterNorm_ofFinite_finite_eq_one hK χ.toMul q
    (K.mul_mem hkx (K.inv_mem hky)) hfin
  have hprod := characterNorm_eq_prod_placeHom χ.toMul q hN
  have hpos : 0 < ((characterNorm F P χ.toMul q : ℝ≥0) : ℝ) :=
    NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (characterNorm F P χ.toMul q).ne_zero)
  have hheight : hK.height (map F P G p qy * ky) χ - hK.height (map F P G p qx * kx) χ =
      Real.log ((characterNorm F P χ.toMul q : ℝ≥0) : ℝ) := by
    rw [hK.height_eq hky rfl, hK.height_eq hkx rfl, characterLog_apply, characterLog_apply]
    have hq : characterNorm F P χ.toMul q =
        (characterNorm F P χ.toMul qx)⁻¹ * characterNorm F P χ.toMul qy := by
      simp only [q, map_mul, map_inv]
    have hx0 : ((characterNorm F P χ.toMul qx : ℝ≥0) : ℝ) ≠ 0 := by
      exact_mod_cast (characterNorm F P χ.toMul qx).ne_zero
    have hy0 : ((characterNorm F P χ.toMul qy : ℝ≥0) : ℝ) ≠ 0 := by
      exact_mod_cast (characterNorm F P χ.toMul qy).ne_zero
    rw [hq, Units.val_mul, Units.val_inv_eq_inv_val, NNReal.coe_mul, NNReal.coe_inv,
      Real.log_mul (inv_ne_zero hx0) hy0, Real.log_inv]
    ring
  rw [hheight, show (2 : ℝ) * Real.log ((characterNorm F P χ.toMul q : ℝ≥0) : ℝ) =
      ((2 : ℕ) : ℝ) * Real.log ((characterNorm F P χ.toMul q : ℝ≥0) : ℝ) by norm_num,
    Real.exp_nat_mul, Real.exp_log hpos, hprod, ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [← pow_mul, mul_comm, pow_mul]
  congr 1
  rw [energy_inv_mulVec (hQ w) ha qx hkx, energy_inv_mulVec (hQ w) ha qy hky]
  have he : 0 < Q w (Pi.single j 1) := (hQ w).pos _ (by
    intro h
    have := congrFun h j
    simp at this)
  have hy1 := norm_placeHom_character_inv_mul (χ := χ.toMul) w qy
  have hyn : ‖placeHom w (character F P χ.toMul qy⁻¹).val‖ ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hy1
    exact zero_ne_one hy1
  rw [mul_div_mul_right _ _ he.ne', placeHom_character_mul, norm_mul, mul_pow,
    div_eq_mul_inv, ← inv_pow]
  rw [eq_inv_of_mul_eq_one_right hy1]

end Iwasawa

end Langlands.Global.EisensteinGenericInjectivity
