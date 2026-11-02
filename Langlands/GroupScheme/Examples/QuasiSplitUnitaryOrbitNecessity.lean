import Langlands.GroupScheme.Examples.QuasiSplitUnitaryTensorCoordinates
import Langlands.GroupScheme.Examples.QuasiSplitUnitaryOrbitExtensions

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry Algebra
open scoped TensorProduct CategoryTheory.MonObj

namespace Langlands.GroupScheme.QuasiSplitUnitary

variable {F E : Type u} [Field F] [Field E] [Algebra F E]
  [IsQuadraticExtension F E]
attribute [local instance] Algebra.TensorProduct.rightAlgebra
variable {I : Type u} (v : Module.Basis I F E)
variable {κ : Type u} [Fintype κ]
  (b : Module.Basis κ F (Matrix (Fin 2) (Fin 2) E)) (c : E ≃ₐ[F] E) (m : ℤ)

local notation "S" => Spec (CommRingCat.of F)
local notation "𝔸¹" => AffineLine.scheme S

omit [IsQuadraticExtension F E] in
/-- Scalar coordinates commute with diagonal conjugation by scalar units. -/
theorem tensorCoeff_diagonal_conj {R : Type u} [CommRing R] [Algebra F R]
    (u : Rˣ) (M : GL (Fin 2) (E ⊗[F] R)) (i j : Fin 2) (k : I) :
    tensorCoeff v R
      ((GeneralLinear.diagonalUnits _ (weights m)
          (Units.map (algebraMap R (E ⊗[F] R)).toMonoidHom u) * M *
        (GeneralLinear.diagonalUnits _ (weights m)
          (Units.map (algebraMap R (E ⊗[F] R)).toMonoidHom u))⁻¹).val i j) k =
      ((u ^ weights m i : Rˣ) : R) * tensorCoeff v R (M.val i j) k *
        ((u⁻¹ ^ weights m j : Rˣ) : R) := by
  rw [GeneralLinear.diagonalUnits_conj_apply]
  simp only [← map_zpow, ← map_inv, Units.coe_map]
  erw [tensorCoeff_mul_scalar, tensorCoeff_scalar_mul]

/-- Scalar coordinates of the orbit have the same integral weights as matrix entries. -/
theorem entryCoeff_lift_orbit {T T' : Over S} (a : T' ⟶ T) (y : T' ⟶ (Gm S).X)
    (g : T ⟶ (groupScheme b c).X) (i j : Fin 2) (k : I) :
    entryCoeff v b c T' (lift a y ≫ Dynamic.orbit (weightCocharacter b c m) g) i j k =
      ((Gm.pointsEquiv S T' y ^ weights m i : Γ(T'.left, ⊤)ˣ) : Γ(T'.left, ⊤)) *
        a.left.appTop (entryCoeff v b c T g i j k) *
          (((Gm.pointsEquiv S T' y)⁻¹ ^ weights m j : Γ(T'.left, ⊤)ˣ) : Γ(T'.left, ⊤)) := by
  rw [Dynamic.orbit, MonObj.comp_mul, MonObj.comp_mul, GrpObj.comp_inv,
    lift_snd_assoc, lift_fst_assoc]
  unfold entryCoeff
  rw [map_mul, map_mul, map_inv, matrixCoordinates_weightCocharacter,
    matrixCoordinates_naturality]
  erw [tensorCoeff_diagonal_conj]
  erw [tensorCoeff_naturality]
  rfl

section Affine
open LaurentPolynomial
open _root_.Langlands.GroupScheme.GeneralLinear (polyScheme polyPoint polyProj laurentScheme laurentIncl laurentUnit
  polyC polyToLaurent polyEvalZero polyZero)

set_option autoImplicit false
variable {A : CommRingCat.{u}} {f : Spec A ⟶ Spec (CommRingCat.of F)}
/-- Every scalar coefficient of an orbit extension gives a polynomial with the prescribed
Laurent monomial. -/
theorem toLaurent_polyPoint_entryCoeff {g : Over.mk f ⟶ (groupScheme b c).X}
    {D : Over.mk f ⊗ 𝔸¹ ⟶ (groupScheme b c).X}
    (hD : Dynamic.IsOrbitExtension (weightCocharacter b c m) g D)
    (i j : Fin 2) (k : I) :
    Polynomial.toLaurent ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial A))).hom
      (entryCoeff v b c (polyScheme f) (polyPoint f ≫ D) i j k)) =
      C ((Scheme.ΓSpecIso A).hom (entryCoeff v b c (Over.mk f) g i j k)) *
        T (weights m i - weights m j) := by
  have h := entryCoeff_comp v b c (laurentIncl f) (polyPoint f ≫ D) i j k
  rw [← Category.assoc, GeneralLinear.laurentIncl_polyPoint, Category.assoc, hD,
    entryCoeff_lift_orbit, MulEquiv.apply_symm_apply] at h
  have ha : (laurentIncl f ≫ polyProj f).left = Spec.map (polyC A ≫ polyToLaurent A) := by
    rw [Over.comp_left, Spec.map_comp]
    rfl
  have hb : (laurentIncl f).left = Spec.map (polyToLaurent A) := rfl
  rw [ha, hb] at h
  have h2 := congrArg (Scheme.ΓSpecIso (CommRingCat.of (LaurentPolynomial A))).hom h
  rw [map_mul, map_mul, inv_zpow', GeneralLinear.ΓSpecIso_hom_laurentUnit_zpow,
    GeneralLinear.ΓSpecIso_hom_laurentUnit_zpow] at h2
  erw [GeneralLinear.ΓSpecIso_hom_appTop_SpecMap,
    GeneralLinear.ΓSpecIso_hom_appTop_SpecMap] at h2
  refine h2.symm.trans ?_
  rw [T_sub]
  simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp,
    Function.comp_apply, Polynomial.toLaurent_C]
  ring

/-- A negative orbit weight forces each scalar coefficient to vanish on an affine test. -/
theorem entryCoeff_eq_zero_of_isOrbitExtension {g : Over.mk f ⟶ (groupScheme b c).X}
    {D : Over.mk f ⊗ 𝔸¹ ⟶ (groupScheme b c).X}
    (hD : Dynamic.IsOrbitExtension (weightCocharacter b c m) g D)
    {i j : Fin 2} (hij : weights m i < weights m j) (k : I) :
    entryCoeff v b c (Over.mk f) g i j k = 0 := by
  have h := toLaurent_polyPoint_entryCoeff v b c m hD i j k
  obtain ⟨q, hq⟩ : ∃ q : ℕ, weights m j - weights m i = q + 1 :=
    ⟨(weights m j - weights m i - 1).toNat, by omega⟩
  have h2 : Polynomial.toLaurent (Polynomial.X ^ (q + 1) *
        (Scheme.ΓSpecIso (CommRingCat.of (Polynomial A))).hom (entryCoeff v b c (polyScheme f) (polyPoint f ≫ D) i j k)) =
      Polynomial.toLaurent (Polynomial.C
        ((Scheme.ΓSpecIso A).hom (entryCoeff v b c (Over.mk f) g i j k))) := by
    rw [map_mul, h, Polynomial.toLaurent_X_pow, Polynomial.toLaurent_C,
      mul_left_comm, ← T_add]
    have : (((q + 1 : ℕ) : ℤ) + (weights m i - weights m j)) = 0 := by push_cast; omega
    rw [this, T_zero, mul_one]
  have h3 := congrArg (Polynomial.coeff · 0) (Polynomial.toLaurent_injective h2)
  simp only [Polynomial.coeff_X_pow_mul', Polynomial.coeff_C_zero] at h3
  exact GeneralLinear.ΓSpecIso_injective_apply_eq_zero (by simpa using h3.symm)

/-- Constancy of an orbit forces each nonzero-weight scalar coefficient to vanish. -/
theorem entryCoeff_eq_zero_of_mem_centralizer {g : Over.mk f ⟶ (groupScheme b c).X}
    (hg : g ∈ (Dynamic.centralizer (weightCocharacter b c m)).carrier (Over.mk f))
    {i j : Fin 2} (hij : weights m i ≠ weights m j) (k : I) :
    entryCoeff v b c (Over.mk f) g i j k = 0 := by
  have h0 : lift (laurentIncl f ≫ polyProj f) ((Gm.pointsEquiv _ _).symm (laurentUnit f)) ≫
      Dynamic.orbit (weightCocharacter b c m) g = (laurentIncl f ≫ polyProj f) ≫ g := by
    rw [(Dynamic.mem_centralizer _).1 hg, lift_fst_assoc]
  have h := congrArg (fun z => entryCoeff v b c _ z i j k) h0
  rw [entryCoeff_lift_orbit, MulEquiv.apply_symm_apply, entryCoeff_comp] at h
  have h2 := congrArg (Scheme.ΓSpecIso (CommRingCat.of (LaurentPolynomial A))).hom h
  rw [map_mul, map_mul, inv_zpow', GeneralLinear.ΓSpecIso_hom_laurentUnit_zpow,
    GeneralLinear.ΓSpecIso_hom_laurentUnit_zpow] at h2
  erw [GeneralLinear.ΓSpecIso_hom_laurentProj] at h2
  refine GeneralLinear.ΓSpecIso_injective_apply_eq_zero
    (GeneralLinear.eq_zero_of_C_mul_T_eq (sub_ne_zero.2 hij) ?_)
  rw [T_sub]
  linear_combination h2

/-- The zero value of an orbit extension retains every scalar coefficient of weight zero. -/
theorem evalZero_entryCoeff_of_eq {g : Over.mk f ⟶ (groupScheme b c).X}
    {D : Over.mk f ⊗ 𝔸¹ ⟶ (groupScheme b c).X}
    (hD : Dynamic.IsOrbitExtension (weightCocharacter b c m) g D)
    {i j : Fin 2} (hij : weights m i = weights m j) (k : I) :
    entryCoeff v b c (Over.mk f) (Dynamic.evalZero D) i j k = entryCoeff v b c (Over.mk f) g i j k := by
  have h := toLaurent_polyPoint_entryCoeff v b c m hD i j k
  rw [hij, sub_self, T_zero, mul_one, ← Polynomial.toLaurent_C] at h
  have hP := Polynomial.toLaurent_injective h
  have h1 : Dynamic.evalZero D = polyZero f ≫ polyPoint f ≫ D := by
    rw [Dynamic.evalZero, ← Category.assoc, GeneralLinear.polyZero_polyPoint]
  rw [h1, entryCoeff_comp]
  apply GeneralLinear.ΓSpecIso_hom_injective A
  change (Scheme.ΓSpecIso A).hom ((Spec.map (polyEvalZero A)).appTop _) = _
  rw [GeneralLinear.ΓSpecIso_hom_appTop_SpecMap]
  erw [hP]
  simp

end Affine

section Cover
include v

/-- Parabolic membership forces the weighted triangular conditions on every test scheme. -/
theorem matrixCoordinates_mem_blockParabolic_of_mem_parabolic {T : Over S}
    {g : T ⟶ (groupScheme b c).X}
    (hg : g ∈ (Dynamic.parabolic (weightCocharacter b c m)).carrier T) :
    matrixCoordinates b c T g ∈ GeneralLinear.blockParabolicSubgroup _ (weights m) := by
  rw [GeneralLinear.mem_blockParabolicSubgroup]
  intro i j hij
  apply tensorCoeff_injective v ((algΓ (CommRingCat.of F)).obj T).unop
  ext k
  change entryCoeff v b c T g i j k = 0
  refine GeneralLinear.section_ext fun q => ?_
  obtain ⟨D, hD⟩ := (Dynamic.parabolic (weightCocharacter b c m)).comp_mem
    (GeneralLinear.affinePieceIncl T q) hg
  rw [map_zero, ← entryCoeff_comp]
  exact entryCoeff_eq_zero_of_isOrbitExtension v b c m hD hij k

/-- Centralizer membership forces the weighted diagonal conditions on every test scheme. -/
theorem matrixCoordinates_mem_blockLevi_of_mem_centralizer {T : Over S}
    {g : T ⟶ (groupScheme b c).X}
    (hg : g ∈ (Dynamic.centralizer (weightCocharacter b c m)).carrier T) :
    matrixCoordinates b c T g ∈ GeneralLinear.blockLeviSubgroup _ (weights m) := by
  change ∀ i j, weights m i ≠ weights m j → _ = 0
  intro i j hij
  apply tensorCoeff_injective v ((algΓ (CommRingCat.of F)).obj T).unop
  ext k
  change entryCoeff v b c T g i j k = 0
  refine GeneralLinear.section_ext fun q => ?_
  rw [map_zero, ← entryCoeff_comp]
  exact entryCoeff_eq_zero_of_mem_centralizer v b c m
    ((Dynamic.centralizer (weightCocharacter b c m)).comp_mem
      (GeneralLinear.affinePieceIncl T q) hg) hij k

/-- Unipotent membership forces the weighted unipotent conditions on every test scheme. -/
theorem matrixCoordinates_mem_blockUnipotent_of_mem_unipotent {T : Over S}
    {g : T ⟶ (groupScheme b c).X}
    (hg : g ∈ (Dynamic.unipotent (weightCocharacter b c m)).carrier T) :
    matrixCoordinates b c T g ∈ GeneralLinear.blockUnipotentSubgroup _ (weights m) := by
  have hP := matrixCoordinates_mem_blockParabolic_of_mem_parabolic v b c m
    (Dynamic.unipotent_le_parabolic (weightCocharacter b c m) T hg)
  change ∀ i j, weights m i ≤ weights m j → _ = _
  intro i j hij
  rcases hij.lt_or_eq with hlt | heq
  · rw [(GeneralLinear.mem_blockParabolicSubgroup _ (weights m)).1 hP i j hlt]
    exact (Matrix.one_apply_ne fun h => hlt.ne (congrArg (weights m) h)).symm
  · suffices h : matrixCoordinates b c T g i j = matrixCoordinates b c T (1 : T ⟶ _) i j by
      simpa only [map_one, Units.val_one] using h
    apply tensorCoeff_injective v ((algΓ (CommRingCat.of F)).obj T).unop
    ext k
    change entryCoeff v b c T g i j k = entryCoeff v b c T 1 i j k
    refine GeneralLinear.section_ext fun q => ?_
    obtain ⟨D, hD, hD0⟩ := (Dynamic.unipotent (weightCocharacter b c m)).comp_mem
      (GeneralLinear.affinePieceIncl T q) hg
    rw [← entryCoeff_comp, ← entryCoeff_comp, MonObj.comp_one,
      ← evalZero_entryCoeff_of_eq v b c m hD heq, hD0]

end Cover
end Langlands.GroupScheme.QuasiSplitUnitary
