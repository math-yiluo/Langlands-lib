import Langlands.GroupScheme.Dynamic.Basic
import Langlands.GroupScheme.Dynamic.GeneralLinear
import Langlands.GroupScheme.Dynamic.Decomposition
import Langlands.GroupScheme.MultiplicativeLaurent

/-! # Orbit extensions for block matrices in `GL_n`

For the diagonal cocharacter `λ(t) = diag(t ^ e i)` of `GL_n` over `Spec R`, this module constructs
for every block parabolic point `g` an explicit extension of the orbit map `t ↦ λ(t) g λ(t)⁻¹`
to `T ×_S 𝔸¹_S`, and computes its value at zero. It follows that the block parabolic, block Levi
and block unipotent subgroup functors lie in `P(λ)`, `Z(λ)` and `U(λ)`.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.GeneralLinear

variable {n : Type} [Fintype n] [DecidableEq n]

section Matrix

variable {A : Type*} [CommRing A] (e : n → ℤ)

/-- Conjugation by `diag(s ^ e i)` without inverting `s`: the `(i, j)` entry is multiplied by
`s ^ (e i - e j).toNat`. -/
def weightScale (s : A) (M : Matrix n n A) : Matrix n n A :=
  Matrix.of fun i j => s ^ (e i - e j).toNat * M i j

omit [Fintype n] [DecidableEq n] in
theorem weightScale_apply (s : A) (M : Matrix n n A) (i j : n) :
    weightScale e s M i j = s ^ (e i - e j).toNat * M i j :=
  rfl

omit [Fintype n] in
theorem weightScale_one (s : A) : weightScale e s 1 = 1 := by
  ext i j
  rw [weightScale_apply]
  by_cases h : i = j
  · subst h
    simp
  · simp [Matrix.one_apply_ne h]

omit [DecidableEq n] in
theorem weightScale_mul (s : A) {M N : Matrix n n A}
    (hM : M.BlockTriangular (OrderDual.toDual ∘ e))
    (hN : N.BlockTriangular (OrderDual.toDual ∘ e)) :
    weightScale e s (M * N) = weightScale e s M * weightScale e s N := by
  ext i j
  simp only [weightScale_apply, Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases hik : e i < e k
  · rw [hM (show OrderDual.toDual (e k) < OrderDual.toDual (e i) from hik)]
    simp
  by_cases hkj : e k < e j
  · rw [hN (show OrderDual.toDual (e j) < OrderDual.toDual (e k) from hkj)]
    simp
  have h : (e i - e j).toNat = (e i - e k).toNat + (e k - e j).toNat := by omega
  rw [h, pow_add]
  ring

omit [Fintype n] [DecidableEq n] in
theorem map_weightScale {B : Type*} [CommRing B] (f : A →+* B) (s : A) (M : Matrix n n A) :
    (weightScale e s M).map f = weightScale e (f s) (M.map f) := by
  ext i j
  simp [weightScale_apply]

omit [Fintype n] [DecidableEq n] in
/-- At `s = 0`, scaling a block upper triangular matrix gives its block diagonal part. -/
theorem weightScale_zero {M : Matrix n n A} (hM : M.BlockTriangular (OrderDual.toDual ∘ e)) :
    weightScale e 0 M = blockDiagonalPart A e M := by
  ext i j
  rw [weightScale_apply, blockDiagonalPart_apply]
  by_cases hij : e i = e j
  · rw [ite_eq_left hij, hij, sub_self]
    simp
  · rw [ite_eq_right hij]
    rcases lt_or_gt_of_ne hij with hlt | hlt
    · rw [hM (show OrderDual.toDual (e j) < OrderDual.toDual (e i) from hlt), mul_zero]
    · rw [zero_pow (by omega), zero_mul]

omit [Fintype n] [DecidableEq n] in
/-- Scaling does not change a block diagonal matrix. -/
theorem weightScale_of_blockLevi (s : A) {M : Matrix n n A}
    (hM : ∀ i j, e i ≠ e j → M i j = 0) : weightScale e s M = M := by
  ext i j
  rw [weightScale_apply]
  by_cases hij : e i = e j
  · rw [hij, sub_self]
    simp
  · rw [hM i j hij, mul_zero]

/-- Scaling as a homomorphism on block upper triangular invertible matrices. -/
def weightScaleHom (s : A) : blockParabolicSubgroup A e →* GL n A where
  toFun g :=
    { val := weightScale e s g.val
      inv := weightScale e s ((g.val⁻¹ : GL n A) : Matrix n n A)
      val_inv := by
        rw [← weightScale_mul e s g.property ((blockParabolicSubgroup A e).inv_mem g.property),
          ← Units.val_mul, mul_inv_cancel, Units.val_one, weightScale_one]
      inv_val := by
        rw [← weightScale_mul e s ((blockParabolicSubgroup A e).inv_mem g.property) g.property,
          ← Units.val_mul, inv_mul_cancel, Units.val_one, weightScale_one] }
  map_one' := Units.ext (weightScale_one e s)
  map_mul' g h := Units.ext (weightScale_mul e s g.property h.property)

theorem coe_weightScaleHom (s : A) (g : blockParabolicSubgroup A e) :
    (weightScaleHom e s g : Matrix n n A) = weightScale e s g.val :=
  rfl

/-- For a unit `u`, scaling is conjugation by `diag(u ^ e i)`. -/
theorem weightScale_units (u : Aˣ) {g : GL n A} (hg : g ∈ blockParabolicSubgroup A e) :
    weightScale e (u : A) g =
      ((diagonalUnits A e u * g * (diagonalUnits A e u)⁻¹ : GL n A) : Matrix n n A) := by
  ext i j
  rw [weightScale_apply, Units.val_mul, Units.val_mul, ← map_inv, coe_diagonalUnits,
    coe_diagonalUnits, Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases h : e i < e j
  · rw [hg (show OrderDual.toDual (e j) < OrderDual.toDual (e i) from h)]
    simp
  · have h2 : e i - e j = ((e i - e j).toNat : ℤ) := (Int.toNat_of_nonneg (by omega)).symm
    have h3 : ((u ^ e i : Aˣ) : A) * ((u⁻¹ ^ e j : Aˣ) : A) = (u : A) ^ (e i - e j).toNat := by
      rw [← Units.val_mul, inv_zpow', ← zpow_add, ← sub_eq_add_neg, h2, zpow_natCast,
        Units.val_pow_eq_pow_val, ← h2]
    rw [← h3]
    ring

end Matrix

section Scheme

variable {R : CommRingCat.{u}} (e : n → ℤ)

local notation "𝔸¹" => AffineLine.scheme (Spec R)

/-- The scaled matrix `(s ^ (e i - e j).toNat g_ij)` over `T ×_S 𝔸¹_S`, for a block parabolic
point `g` over `T`, where `s` is the coordinate of `𝔸¹`. This point of `GL_n` extends the
orbit map of `g`. -/
def orbitExtension {T : Over (Spec R)} (g : T ⟶ (groupScheme n R).X)
    (hg : g ∈ (blockParabolic n R e).carrier T) : T ⊗ 𝔸¹ ⟶ (groupScheme n R).X :=
  (pointsEquiv n R _).symm (weightScaleHom e (AffineLine.homEquiv _ (snd T 𝔸¹))
    ⟨pointsEquiv n R _ (fst T 𝔸¹ ≫ g), (blockParabolic n R e).comp_mem _ hg⟩)

theorem pointsEquiv_orbitExtension {T : Over (Spec R)} (g : T ⟶ (groupScheme n R).X)
    (hg : g ∈ (blockParabolic n R e).carrier T) :
    (pointsEquiv n R _ (orbitExtension e g hg) : Matrix n n Γ((T ⊗ 𝔸¹).left, ⊤)) =
      weightScale e (AffineLine.homEquiv _ (snd T 𝔸¹)) (pointsEquiv n R _ (fst T 𝔸¹ ≫ g)) := by
  rw [orbitExtension, MulEquiv.apply_symm_apply, coe_weightScaleHom]

theorem coe_map_GL {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (g : GL n A) :
    ((Matrix.GeneralLinearGroup.map f g : GL n B) : Matrix n n B) = (g : Matrix n n A).map f :=
  rfl

theorem isOrbitExtension_orbitExtension {T : Over (Spec R)} (g : T ⟶ (groupScheme n R).X)
    (hg : g ∈ (blockParabolic n R e).carrier T) :
    Dynamic.IsOrbitExtension (diagonalCocharacter n R e) g (orbitExtension e g hg) := by
  have hs : (T ◁ AffineLine.unitInclusion (Spec R)).left.appTop
      (AffineLine.homEquiv _ (snd T 𝔸¹)) =
        (Gm.pointsEquiv (Spec R) _ (snd T (Gm (Spec R)).X) : Γ(_, ⊤)) := by
    rw [← AffineLine.homEquiv_comp, whiskerLeft_snd, AffineLine.homEquiv_comp_unitInclusion]
  have hM : Matrix.GeneralLinearGroup.map (T ◁ AffineLine.unitInclusion (Spec R)).left.appTop.hom
      (pointsEquiv n R _ (fst T 𝔸¹ ≫ g)) = pointsEquiv n R _ (fst T (Gm (Spec R)).X ≫ g) := by
    rw [← pointsEquiv_naturality (T ◁ AffineLine.unitInclusion (Spec R)) (fst T 𝔸¹ ≫ g),
      whiskerLeft_fst_assoc]
  have hP : Matrix.GeneralLinearGroup.map (T ◁ AffineLine.unitInclusion (Spec R)).left.appTop.hom
      (pointsEquiv n R _ (fst T 𝔸¹ ≫ g)) ∈ blockParabolicSubgroup _ e :=
    map_mem_blockParabolicSubgroup e _ ((blockParabolic n R e).comp_mem (fst T 𝔸¹) hg)
  apply (pointsEquiv n R _).injective
  rw [Dynamic.orbit, map_mul, map_mul, map_inv, pointsEquiv_diagonalCocharacter,
    pointsEquiv_naturality (T ◁ AffineLine.unitInclusion (Spec R)), ← hM]
  apply Units.ext
  rw [← weightScale_units e _ hP, ← hs, coe_map_GL, coe_map_GL, pointsEquiv_orbitExtension,
    map_weightScale]

/-- The value at zero of the orbit extension is the block diagonal part of `g`. -/
theorem pointsEquiv_evalZero_orbitExtension {T : Over (Spec R)} (g : T ⟶ (groupScheme n R).X)
    (hg : g ∈ (blockParabolic n R e).carrier T) :
    pointsEquiv n R T (Dynamic.evalZero (orbitExtension e g hg)) =
      blockLeviProjection Γ(T.left, ⊤) e ⟨pointsEquiv n R T g, hg⟩ := by
  have hs : (lift (𝟙 T) (toUnit T ≫ AffineLine.zeroSection (Spec R))).left.appTop
      (AffineLine.homEquiv _ (snd T 𝔸¹)) = 0 := by
    rw [← AffineLine.homEquiv_comp, lift_snd, AffineLine.homEquiv_comp_zeroSection]
  have hM : (pointsEquiv n R _ (fst T 𝔸¹ ≫ g) : Matrix n n Γ((T ⊗ 𝔸¹).left, ⊤)).map
      (lift (𝟙 T) (toUnit T ≫ AffineLine.zeroSection (Spec R))).left.appTop.hom =
        pointsEquiv n R T g := by
    rw [← coe_map_GL, ← pointsEquiv_naturality, lift_fst_assoc, Category.id_comp]
  apply Units.ext
  rw [Dynamic.evalZero, pointsEquiv_naturality, coe_map_GL, pointsEquiv_orbitExtension,
    map_weightScale, coe_blockLeviProjection, hM]
  rw [show (lift (𝟙 T) (toUnit T ≫ AffineLine.zeroSection (Spec R))).left.appTop.hom
      (AffineLine.homEquiv _ (snd T 𝔸¹)) = 0 from hs]
  exact weightScale_zero e hg

variable (n R) in
/-- Block upper triangular points lie in the dynamic parabolic subgroup functor. -/
theorem blockParabolic_le_parabolic :
    blockParabolic n R e ≤ Dynamic.parabolic (diagonalCocharacter n R e) :=
  fun _ g hg => ⟨orbitExtension e g hg, isOrbitExtension_orbitExtension e g hg⟩

variable (n R) in
/-- Block unipotent points lie in the dynamic unipotent subgroup functor. -/
theorem blockUnipotent_le_unipotent :
    blockUnipotent n R e ≤ Dynamic.unipotent (diagonalCocharacter n R e) := by
  intro T g hg
  obtain ⟨hP', hD⟩ := (blockUnipotent_iff _ e _).1 hg
  have hP : g ∈ (blockParabolic n R e).carrier T := hP'
  refine ⟨orbitExtension e g hP, isOrbitExtension_orbitExtension e g hP, ?_⟩
  apply (pointsEquiv n R T).injective
  rw [pointsEquiv_evalZero_orbitExtension, map_one]
  exact Units.ext hD

variable (n R) in
/-- Block diagonal points lie in the dynamic centralizer subgroup functor. -/
theorem blockLevi_le_centralizer :
    blockLevi n R e ≤ Dynamic.centralizer (diagonalCocharacter n R e) := by
  intro T g hg
  rw [Dynamic.mem_centralizer]
  have hL : pointsEquiv n R _ (fst T (Gm (Spec R)).X ≫ g) ∈ blockLeviSubgroup _ e :=
    (blockLevi n R e).comp_mem _ hg
  have hP : pointsEquiv n R _ (fst T (Gm (Spec R)).X ≫ g) ∈ blockParabolicSubgroup _ e :=
    (mem_blockParabolicSubgroup _ e).2 fun i j h => hL i j h.ne
  apply (pointsEquiv n R _).injective
  rw [Dynamic.orbit, map_mul, map_mul, map_inv, pointsEquiv_diagonalCocharacter]
  apply Units.ext
  rw [← weightScale_units e _ hP, weightScale_of_blockLevi e _ hL]

end Scheme

section TestPoints

open LaurentPolynomial

variable {R : CommRingCat.{u}} (e : n → ℤ)

local notation "𝔸¹" => AffineLine.scheme (Spec R)

/-- The matrix of the orbit map at the point `(a, y)` of `T ×_S 𝔾_{m,S}`. -/
theorem pointsEquiv_lift_orbit {T T' : Over (Spec R)} (a : T' ⟶ T) (y : T' ⟶ (Gm (Spec R)).X)
    (g : T ⟶ (groupScheme n R).X) :
    pointsEquiv n R T' (lift a y ≫ Dynamic.orbit (diagonalCocharacter n R e) g) =
      diagonalUnits _ e (Gm.pointsEquiv (Spec R) T' y) *
        Matrix.GeneralLinearGroup.map a.left.appTop.hom (pointsEquiv n R T g) *
          (diagonalUnits _ e (Gm.pointsEquiv (Spec R) T' y))⁻¹ := by
  rw [Dynamic.orbit, MonObj.comp_mul, MonObj.comp_mul, GrpObj.comp_inv, lift_snd_assoc,
    lift_fst_assoc, map_mul, map_mul, map_inv, pointsEquiv_diagonalCocharacter,
    pointsEquiv_naturality]

/-- The `(i, j)` entry of `diag(u ^ e) M diag(u ^ e)⁻¹`. -/
theorem diagonalUnits_conj_apply {A : Type*} [CommRing A] (u : Aˣ) (M : GL n A) (i j : n) :
    ((diagonalUnits A e u * M * (diagonalUnits A e u)⁻¹ : GL n A) : Matrix n n A) i j =
      ((u ^ e i : Aˣ) : A) * (M : Matrix n n A) i j * ((u⁻¹ ^ e j : Aˣ) : A) := by
  rw [Units.val_mul, Units.val_mul, ← map_inv, coe_diagonalUnits, coe_diagonalUnits,
    Matrix.mul_diagonal, Matrix.diagonal_mul]

variable (A : CommRingCat.{u})

/-- `A → A[X]`. -/
abbrev polyC : A ⟶ CommRingCat.of (Polynomial A) := CommRingCat.ofHom Polynomial.C

/-- `A[X] → A[T, T⁻¹]`. -/
abbrev polyToLaurent : CommRingCat.of (Polynomial A) ⟶ CommRingCat.of (LaurentPolynomial A) :=
  CommRingCat.ofHom Polynomial.toLaurent

/-- Evaluation at zero, `A[X] → A`. -/
abbrev polyEvalZero : CommRingCat.of (Polynomial A) ⟶ A :=
  CommRingCat.ofHom (Polynomial.evalRingHom 0)

variable {A} (f : Spec A ⟶ Spec R)

/-- `Spec A[X]` over `Spec R`, through `Spec A`. -/
abbrev polyScheme : Over (Spec R) := Over.mk (Spec.map (polyC A) ≫ f)

/-- `Spec A[T, T⁻¹]` over `Spec R`, through `Spec A[X]`. -/
abbrev laurentScheme : Over (Spec R) := Over.mk (Spec.map (polyToLaurent A) ≫ (polyScheme f).hom)

/-- The projection `Spec A[X] ⟶ Spec A`. -/
def polyProj : polyScheme f ⟶ Over.mk f := Over.homMk (Spec.map (polyC A)) rfl

/-- The inclusion `Spec A[T, T⁻¹] ⟶ Spec A[X]`. -/
def laurentIncl : laurentScheme f ⟶ polyScheme f := Over.homMk (Spec.map (polyToLaurent A)) rfl

/-- The generic point `(Spec A[X] → Spec A, X)` of `Spec A ×_S 𝔸¹_S`. -/
def polyPoint : polyScheme f ⟶ Over.mk f ⊗ 𝔸¹ :=
  lift (polyProj f) ((AffineLine.homEquiv _).symm ((Scheme.ΓSpecIso _).inv Polynomial.X))

/-- The unit `T` as a global unit of `Spec A[T, T⁻¹]`. -/
def laurentUnit : (Γ((laurentScheme f).left, ⊤))ˣ :=
  Units.map (Scheme.ΓSpecIso (CommRingCat.of (LaurentPolynomial A))).inv.hom.toMonoidHom
    (Gm.relativeCoordUnit A)

theorem ΓSpecIso_hom_laurentUnit_zpow (m : ℤ) :
    (Scheme.ΓSpecIso (CommRingCat.of (LaurentPolynomial A))).hom
      ((laurentUnit f ^ m : (Γ((laurentScheme f).left, ⊤))ˣ) : Γ((laurentScheme f).left, ⊤)) =
        T m := by
  rw [laurentUnit, ← map_zpow, Units.coe_map]
  change (Scheme.ΓSpecIso _).hom ((Scheme.ΓSpecIso _).inv _) = _
  rw [← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply,
    Gm.relativeCoordUnit_zpow_val]

/-- On `Spec A[T, T⁻¹]`, the generic point of `𝔸¹` lands in `𝔾_m`. -/
theorem laurentIncl_polyPoint : laurentIncl f ≫ polyPoint f =
    lift (laurentIncl f ≫ polyProj f) ((Gm.pointsEquiv _ _).symm (laurentUnit f)) ≫
      (Over.mk f ◁ AffineLine.unitInclusion (Spec R)) := by
  rw [lift_whiskerLeft, polyPoint, comp_lift]
  congr 1
  apply AffineLine.hom_ext
  rw [AffineLine.homEquiv_comp, Equiv.apply_symm_apply, AffineLine.homEquiv_comp_unitInclusion,
    MulEquiv.apply_symm_apply]
  change (Spec.map (polyToLaurent A)).appTop ((Scheme.ΓSpecIso _).inv Polynomial.X) =
    (Scheme.ΓSpecIso _).inv (T 1)
  rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply]
  simp [Polynomial.toLaurent_X]

omit [Fintype n] [DecidableEq n] in
theorem ΓSpecIso_hom_appTop_SpecMap {B C : CommRingCat.{u}} (φ : B ⟶ C) (x : Γ(Spec B, ⊤)) :
    (Scheme.ΓSpecIso C).hom ((Spec.map φ).appTop x) = φ ((Scheme.ΓSpecIso B).hom x) := by
  rw [← CommRingCat.comp_apply, Scheme.ΓSpecIso_naturality, CommRingCat.comp_apply]

variable {f e}

/-- The master equation: for an extension `E` of the orbit map of `g`, the entries of `E` at the
generic point are polynomials `P i j` with `P i j = T ^ (e i - e j) g i j` as Laurent
polynomials. -/
theorem toLaurent_polyPoint_entry {g : Over.mk f ⟶ (groupScheme n R).X}
    {E : Over.mk f ⊗ 𝔸¹ ⟶ (groupScheme n R).X}
    (hE : Dynamic.IsOrbitExtension (diagonalCocharacter n R e) g E) (i j : n) :
    Polynomial.toLaurent ((Scheme.ΓSpecIso _).hom (pointsEquiv n R _ (polyPoint f ≫ E) i j)) =
      C ((Scheme.ΓSpecIso A).hom (pointsEquiv n R _ g i j)) * T (e i - e j) := by
  have h := pointsEquiv_comp_apply (laurentIncl f) (polyPoint f ≫ E) i j
  rw [← Category.assoc, laurentIncl_polyPoint, Category.assoc, hE, pointsEquiv_lift_orbit,
    MulEquiv.apply_symm_apply, diagonalUnits_conj_apply, coe_map_GL, Matrix.map_apply] at h
  have ha : (laurentIncl f ≫ polyProj f).left = Spec.map (polyC A ≫ polyToLaurent A) := by
    rw [Over.comp_left, Spec.map_comp]
    rfl
  have hb : (laurentIncl f).left = Spec.map (polyToLaurent A) := rfl
  rw [ha, hb] at h
  have h2 := congrArg (Scheme.ΓSpecIso (CommRingCat.of (LaurentPolynomial A))).hom h
  rw [map_mul, map_mul, inv_zpow', ΓSpecIso_hom_laurentUnit_zpow, ΓSpecIso_hom_laurentUnit_zpow]
    at h2
  erw [ΓSpecIso_hom_appTop_SpecMap, ΓSpecIso_hom_appTop_SpecMap] at h2
  refine h2.symm.trans ?_
  rw [T_sub]
  simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp, Function.comp_apply,
    Polynomial.toLaurent_C]
  ring

omit [Fintype n] [DecidableEq n] in
theorem eq_zero_of_C_mul_T_eq {B : Type*} [CommRing B] {γ : B} {m : ℤ} (hm : m ≠ 0)
    (h : C γ * T m = (C γ : LaurentPolynomial B)) : γ = 0 := by
  by_contra hγ
  have h1 : (AddMonoidAlgebra.single m γ : LaurentPolynomial B) = AddMonoidAlgebra.single 0 γ := by
    rw [single_eq_C_mul_T, single_eq_C_mul_T, T_zero, mul_one, h]
  exact hm ((AddMonoidAlgebra.single_left_inj hγ).1 h1)

theorem ΓSpecIso_hom_laurentProj (x : Γ(Spec A, ⊤)) :
    (Scheme.ΓSpecIso (CommRingCat.of (LaurentPolynomial A))).hom
      ((laurentIncl f ≫ polyProj f).left.appTop x) = C ((Scheme.ΓSpecIso A).hom x) := by
  have ha : (laurentIncl f ≫ polyProj f).left = Spec.map (polyC A ≫ polyToLaurent A) := by
    rw [Over.comp_left, Spec.map_comp]
    rfl
  rw [ha]
  erw [ΓSpecIso_hom_appTop_SpecMap]
  simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp, Function.comp_apply,
    Polynomial.toLaurent_C]

theorem ΓSpecIso_injective_apply_eq_zero {B : CommRingCat.{u}} {x : Γ(Spec B, ⊤)}
    (h : (Scheme.ΓSpecIso B).hom x = 0) : x = 0 := by
  have := congrArg (Scheme.ΓSpecIso B).inv h
  rwa [← CommRingCat.comp_apply, Iso.hom_inv_id, CommRingCat.id_apply, map_zero] at this

/-- Over `Spec A`, the entries `(i, j)` of a point of `P(λ)` with `e i < e j` vanish. -/
theorem entry_eq_zero_of_isOrbitExtension {g : Over.mk f ⟶ (groupScheme n R).X}
    {E : Over.mk f ⊗ 𝔸¹ ⟶ (groupScheme n R).X}
    (hE : Dynamic.IsOrbitExtension (diagonalCocharacter n R e) g E) {i j : n} (hij : e i < e j) :
    pointsEquiv n R _ g i j = 0 := by
  have h := toLaurent_polyPoint_entry hE i j
  obtain ⟨k, hk⟩ : ∃ k : ℕ, e j - e i = k + 1 := ⟨(e j - e i - 1).toNat, by omega⟩
  have h2 : Polynomial.toLaurent (Polynomial.X ^ (k + 1) *
        (Scheme.ΓSpecIso _).hom (pointsEquiv n R _ (polyPoint f ≫ E) i j)) =
      Polynomial.toLaurent (Polynomial.C ((Scheme.ΓSpecIso A).hom (pointsEquiv n R _ g i j))) := by
    rw [map_mul, h, Polynomial.toLaurent_X_pow, Polynomial.toLaurent_C, mul_left_comm, ← T_add]
    have : (((k + 1 : ℕ) : ℤ) + (e i - e j)) = 0 := by push_cast; omega
    rw [this, T_zero, mul_one]
  have h3 := congrArg (Polynomial.coeff · 0) (Polynomial.toLaurent_injective h2)
  simp only [Polynomial.coeff_X_pow_mul', Polynomial.coeff_C_zero] at h3
  exact ΓSpecIso_injective_apply_eq_zero (by simpa using h3.symm)

/-- Over `Spec A`, the entries `(i, j)` of a point of `Z(λ)` with `e i ≠ e j` vanish. -/
theorem entry_eq_zero_of_mem_centralizer {g : Over.mk f ⟶ (groupScheme n R).X}
    (hg : g ∈ (Dynamic.centralizer (diagonalCocharacter n R e)).carrier (Over.mk f)) {i j : n}
    (hij : e i ≠ e j) : pointsEquiv n R _ g i j = 0 := by
  have h0 : lift (laurentIncl f ≫ polyProj f) ((Gm.pointsEquiv _ _).symm (laurentUnit f)) ≫
      Dynamic.orbit (diagonalCocharacter n R e) g = (laurentIncl f ≫ polyProj f) ≫ g := by
    rw [(Dynamic.mem_centralizer _).1 hg, lift_fst_assoc]
  have h : pointsEquiv n R _ (lift (laurentIncl f ≫ polyProj f)
      ((Gm.pointsEquiv _ _).symm (laurentUnit f)) ≫ Dynamic.orbit (diagonalCocharacter n R e) g) i j =
      pointsEquiv n R _ ((laurentIncl f ≫ polyProj f) ≫ g) i j := by
    rw [h0]
  rw [pointsEquiv_lift_orbit, MulEquiv.apply_symm_apply, diagonalUnits_conj_apply, coe_map_GL,
    Matrix.map_apply, pointsEquiv_comp_apply] at h
  have h2 := congrArg (Scheme.ΓSpecIso (CommRingCat.of (LaurentPolynomial A))).hom h
  rw [map_mul, map_mul, inv_zpow', ΓSpecIso_hom_laurentUnit_zpow, ΓSpecIso_hom_laurentUnit_zpow]
    at h2
  erw [ΓSpecIso_hom_laurentProj] at h2
  refine ΓSpecIso_injective_apply_eq_zero (eq_zero_of_C_mul_T_eq (sub_ne_zero.2 hij) ?_)
  rw [T_sub]
  linear_combination h2

theorem ΓSpecIso_hom_injective (B : CommRingCat.{u}) :
    Function.Injective (Scheme.ΓSpecIso B).hom := fun x y h => by
  have := congrArg (Scheme.ΓSpecIso B).inv h
  rwa [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Iso.hom_inv_id, CommRingCat.id_apply,
    CommRingCat.id_apply] at this

variable (A) in
theorem polyC_comp_polyEvalZero : polyC A ≫ polyEvalZero A = 𝟙 A := by
  ext a
  simp [polyC, polyEvalZero]

variable (f) in
/-- The point `Spec A ⟶ Spec A[X]` given by `X = 0`. -/
def polyZero : Over.mk f ⟶ polyScheme f :=
  Over.homMk (Spec.map (polyEvalZero A)) (by
    change Spec.map (polyEvalZero A) ≫ Spec.map (polyC A) ≫ f = f
    rw [← Category.assoc, ← Spec.map_comp, polyC_comp_polyEvalZero, Spec.map_id,
      Category.id_comp])

variable (f) in
theorem polyZero_polyPoint : polyZero f ≫ polyPoint f =
    lift (𝟙 _) (toUnit _ ≫ AffineLine.zeroSection (Spec R)) := by
  rw [polyPoint, comp_lift]
  congr 1
  · apply Over.OverMorphism.ext
    rw [Over.comp_left, Over.id_left]
    change Spec.map (polyEvalZero A) ≫ Spec.map (polyC A) = 𝟙 _
    rw [← Spec.map_comp, polyC_comp_polyEvalZero, Spec.map_id]
  · apply AffineLine.hom_ext
    rw [AffineLine.homEquiv_comp, Equiv.apply_symm_apply, AffineLine.homEquiv_comp_zeroSection]
    change (Spec.map (polyEvalZero A)).appTop ((Scheme.ΓSpecIso _).inv Polynomial.X) = 0
    rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply]
    simp

/-- Over `Spec A`, the value at zero of an orbit extension of `g` has the `(i, j)` entry of `g`
whenever `e i = e j`. -/
theorem evalZero_entry_of_eq {g : Over.mk f ⟶ (groupScheme n R).X}
    {E : Over.mk f ⊗ 𝔸¹ ⟶ (groupScheme n R).X}
    (hE : Dynamic.IsOrbitExtension (diagonalCocharacter n R e) g E) {i j : n} (hij : e i = e j) :
    pointsEquiv n R _ (Dynamic.evalZero E) i j = pointsEquiv n R _ g i j := by
  have h := toLaurent_polyPoint_entry hE i j
  rw [hij, sub_self, T_zero, mul_one, ← Polynomial.toLaurent_C] at h
  have hP := Polynomial.toLaurent_injective h
  have h1 : Dynamic.evalZero E = polyZero f ≫ polyPoint f ≫ E := by
    rw [Dynamic.evalZero, ← Category.assoc, polyZero_polyPoint]
  rw [h1, pointsEquiv_comp_apply]
  apply ΓSpecIso_hom_injective A
  change (Scheme.ΓSpecIso A).hom ((Spec.map (polyEvalZero A)).appTop _) = _
  rw [ΓSpecIso_hom_appTop_SpecMap]
  erw [hP]
  simp

/-- Over `Spec A`, the value at zero of an orbit extension has `(i, j)` entry zero whenever
`e i ≠ e j`. -/
theorem evalZero_entry_of_ne {g : Over.mk f ⟶ (groupScheme n R).X}
    {E : Over.mk f ⊗ 𝔸¹ ⟶ (groupScheme n R).X}
    (hE : Dynamic.IsOrbitExtension (diagonalCocharacter n R e) g E) {i j : n} (hij : e i ≠ e j) :
    pointsEquiv n R _ (Dynamic.evalZero E) i j = 0 := by
  have h := toLaurent_polyPoint_entry hE i j
  have h1 : Dynamic.evalZero E = polyZero f ≫ polyPoint f ≫ E := by
    rw [Dynamic.evalZero, ← Category.assoc, polyZero_polyPoint]
  rw [h1, pointsEquiv_comp_apply]
  apply ΓSpecIso_hom_injective A
  change (Scheme.ΓSpecIso A).hom ((Spec.map (polyEvalZero A)).appTop _) = _
  rw [ΓSpecIso_hom_appTop_SpecMap, map_zero]
  rcases lt_or_gt_of_ne hij with hlt | hlt
  · rw [entry_eq_zero_of_isOrbitExtension hE hlt, map_zero, map_zero, zero_mul] at h
    have hP : (Scheme.ΓSpecIso _).hom (pointsEquiv n R _ (polyPoint f ≫ E) i j) = 0 :=
      Polynomial.toLaurent_injective (by rw [h, map_zero])
    erw [hP]
    simp
  · obtain ⟨k, hk⟩ : ∃ k : ℕ, e i - e j = k + 1 := ⟨(e i - e j - 1).toNat, by omega⟩
    have hP : (Scheme.ΓSpecIso _).hom (pointsEquiv n R _ (polyPoint f ≫ E) i j) =
        Polynomial.C ((Scheme.ΓSpecIso A).hom (pointsEquiv n R _ g i j)) *
          Polynomial.X ^ (k + 1) := by
      apply Polynomial.toLaurent_injective
      rw [h, map_mul, Polynomial.toLaurent_C, Polynomial.toLaurent_X_pow, hk]
      push_cast
      rfl
    erw [hP]
    simp

end TestPoints

section Cover

variable {R : CommRingCat.{u}} (e : n → ℤ)

/-- The affine pieces `Spec A_k ⟶ T` of the chosen affine open cover of a test scheme. -/
abbrev affinePiece (T : Over (Spec R)) (k : T.left.affineOpenCover.I₀) : Over (Spec R) :=
  Over.mk (T.left.affineOpenCover.f k ≫ T.hom)

/-- The inclusion of an affine piece. -/
def affinePieceIncl (T : Over (Spec R)) (k : T.left.affineOpenCover.I₀) : affinePiece T k ⟶ T :=
  Over.homMk (T.left.affineOpenCover.f k) rfl

/-- Global sections of a test scheme are determined on its affine pieces. -/
theorem section_ext {T : Over (Spec R)} {x y : Γ(T.left, ⊤)}
    (h : ∀ k, (affinePieceIncl T k).left.appTop x = (affinePieceIncl T k).left.appTop y) :
    x = y :=
  T.left.affineOpenCover.openCover.ext_elem x y h

variable (n R) in
theorem parabolic_le_blockParabolic :
    Dynamic.parabolic (diagonalCocharacter n R e) ≤ blockParabolic n R e := by
  intro T g hg
  rw [mem_blockParabolic]
  intro i j hij
  refine section_ext fun k => ?_
  obtain ⟨E, hE⟩ := (Dynamic.parabolic (diagonalCocharacter n R e)).comp_mem
    (affinePieceIncl T k) hg
  rw [map_zero, ← pointsEquiv_comp_apply]
  exact entry_eq_zero_of_isOrbitExtension hE hij

variable (n R) in
theorem centralizer_le_blockLevi :
    Dynamic.centralizer (diagonalCocharacter n R e) ≤ blockLevi n R e := by
  intro T g hg
  rw [mem_blockLevi]
  intro i j hij
  refine section_ext fun k => ?_
  rw [map_zero, ← pointsEquiv_comp_apply]
  exact entry_eq_zero_of_mem_centralizer
    ((Dynamic.centralizer (diagonalCocharacter n R e)).comp_mem (affinePieceIncl T k) hg) hij

variable (n R) in
theorem unipotent_le_blockUnipotent :
    Dynamic.unipotent (diagonalCocharacter n R e) ≤ blockUnipotent n R e := by
  intro T g hg
  have hP := parabolic_le_blockParabolic n R e T
    (Dynamic.unipotent_le_parabolic (diagonalCocharacter n R e) T hg)
  rw [mem_blockUnipotent]
  intro i j hij
  rcases hij.lt_or_eq with hlt | heq
  · rw [(mem_blockParabolic e).1 hP i j hlt]
    exact (Matrix.one_apply_ne fun h => hlt.ne (congrArg e h)).symm
  · refine section_ext fun k => ?_
    obtain ⟨E, hE, hE0⟩ := (Dynamic.unipotent (diagonalCocharacter n R e)).comp_mem
      (affinePieceIncl T k) hg
    rw [← pointsEquiv_comp_apply, ← evalZero_entry_of_eq hE heq, hE0, map_one]
    by_cases hij' : i = j
    · subst hij'
      simp
    · simp [Matrix.one_apply_ne hij']

variable (n R)

/-- `P(λ)` for the diagonal cocharacter is the block parabolic subgroup functor. -/
theorem parabolic_diagonalCocharacter :
    Dynamic.parabolic (diagonalCocharacter n R e) = blockParabolic n R e :=
  le_antisymm (parabolic_le_blockParabolic n R e) (blockParabolic_le_parabolic n R e)

/-- `Z(λ)` for the diagonal cocharacter is the block Levi subgroup functor. -/
theorem centralizer_diagonalCocharacter :
    Dynamic.centralizer (diagonalCocharacter n R e) = blockLevi n R e :=
  le_antisymm (centralizer_le_blockLevi n R e) (blockLevi_le_centralizer n R e)

/-- `U(λ)` for the diagonal cocharacter is the block unipotent subgroup functor. -/
theorem unipotent_diagonalCocharacter :
    Dynamic.unipotent (diagonalCocharacter n R e) = blockUnipotent n R e :=
  le_antisymm (unipotent_le_blockUnipotent n R e) (blockUnipotent_le_unipotent n R e)

variable {n R}

/-- The limits of the diagonal cocharacter: `l` is a limit at zero of the orbit of `g` exactly
when `g` is block upper triangular and `l` is its block diagonal part. -/
theorem hasLimit_diagonalCocharacter_iff {T : Over (Spec R)} {g l : T ⟶ (groupScheme n R).X} :
    Dynamic.HasLimit (diagonalCocharacter n R e) g l ↔
      ∃ hg : g ∈ (blockParabolic n R e).carrier T,
        pointsEquiv n R T l = blockLeviProjection Γ(T.left, ⊤) e ⟨pointsEquiv n R T g, hg⟩ := by
  constructor
  · rintro ⟨E, hE, rfl⟩
    refine ⟨parabolic_le_blockParabolic n R e T ⟨E, hE⟩, Units.ext ?_⟩
    ext i j
    rw [coe_blockLeviProjection, blockDiagonalPart_apply]
    split_ifs with hij
    · refine section_ext fun k => ?_
      rw [← pointsEquiv_comp_apply, ← pointsEquiv_comp_apply, ← Dynamic.evalZero_whiskerRight]
      exact evalZero_entry_of_eq (hE.whiskerRight _ (affinePieceIncl T k)) hij
    · refine section_ext fun k => ?_
      rw [← pointsEquiv_comp_apply, ← Dynamic.evalZero_whiskerRight, map_zero]
      exact evalZero_entry_of_ne (hE.whiskerRight _ (affinePieceIncl T k)) hij
  · rintro ⟨hg, hl⟩
    refine ⟨orbitExtension e g hg, isOrbitExtension_orbitExtension e g hg, ?_⟩
    apply (pointsEquiv n R T).injective
    rw [pointsEquiv_evalZero_orbitExtension, hl]

/-- The block diagonal part of a block upper triangular invertible matrix is block diagonal. -/
theorem blockLeviProjection_mem {A : Type*} [CommRing A] (g : blockParabolicSubgroup A e) :
    blockLeviProjection A e g ∈ blockLeviSubgroup A e := by
  intro i j hij
  rw [coe_blockLeviProjection, blockDiagonalPart_apply, ite_eq_right hij]

theorem hasLimit_diagonalCocharacter_unique {T : Over (Spec R)}
    {g l l' : T ⟶ (groupScheme n R).X} (hl : Dynamic.HasLimit (diagonalCocharacter n R e) g l)
    (hl' : Dynamic.HasLimit (diagonalCocharacter n R e) g l') : l = l' := by
  obtain ⟨hg, h⟩ := (hasLimit_diagonalCocharacter_iff e).1 hl
  obtain ⟨hg', h'⟩ := (hasLimit_diagonalCocharacter_iff e).1 hl'
  exact (pointsEquiv n R T).injective (h.trans h'.symm)

theorem hasLimit_diagonalCocharacter_mem_centralizer {T : Over (Spec R)}
    {g l : T ⟶ (groupScheme n R).X} (hl : Dynamic.HasLimit (diagonalCocharacter n R e) g l) :
    l ∈ (Dynamic.centralizer (diagonalCocharacter n R e)).carrier T := by
  obtain ⟨hg, h⟩ := (hasLimit_diagonalCocharacter_iff e).1 hl
  rw [centralizer_diagonalCocharacter, mem_blockLevi, h]
  exact blockLeviProjection_mem e _

variable (n R)

/-- On every test scheme, `U(λ)` is a normal subgroup of `P(λ)` with complement `Z(λ)`. -/
theorem leviDecomposition_diagonalCocharacter (T : Over (Spec R)) :
    (((Dynamic.unipotent (diagonalCocharacter n R e)).carrier T).subgroupOf
        ((Dynamic.parabolic (diagonalCocharacter n R e)).carrier T)).Normal ∧
      (((Dynamic.unipotent (diagonalCocharacter n R e)).carrier T).subgroupOf
          ((Dynamic.parabolic (diagonalCocharacter n R e)).carrier T)).IsComplement'
        (((Dynamic.centralizer (diagonalCocharacter n R e)).carrier T).subgroupOf
          ((Dynamic.parabolic (diagonalCocharacter n R e)).carrier T)) :=
  ⟨Dynamic.unipotent_subgroupOf_parabolic_normal _ T,
    Dynamic.isComplement'_unipotent_centralizer _
      (fun _ _ _ _ hl hl' => hasLimit_diagonalCocharacter_unique e hl hl')
      (fun _ _ _ hl => hasLimit_diagonalCocharacter_mem_centralizer e hl) T⟩

end Cover

section BlockShape

open Langlands.GeneralLinear (BlockShape)

variable {N : ℕ} (B : BlockShape N) (R : CommRingCat.{u})

theorem parabolic_blockShapeCocharacter :
    Dynamic.parabolic (blockShapeCocharacter B R) = blockShapeParabolic B R := by
  rw [blockShapeCocharacter, parabolic_diagonalCocharacter, blockParabolic_blockShapeWeight]

theorem centralizer_blockShapeCocharacter :
    Dynamic.centralizer (blockShapeCocharacter B R) = blockShapeLevi B R := by
  rw [blockShapeCocharacter, centralizer_diagonalCocharacter, blockLevi_blockShapeWeight]

theorem unipotent_blockShapeCocharacter :
    Dynamic.unipotent (blockShapeCocharacter B R) = blockShapeUnipotent B R := by
  rw [blockShapeCocharacter, unipotent_diagonalCocharacter, blockUnipotent_blockShapeWeight]

variable {B R} in
/-- The limits of the block-shape cocharacter, in terms of the Library's Levi projection
`B.leviProjection` and Levi embedding `B.leviEmbedding`. -/
theorem hasLimit_blockShapeCocharacter_iff {T : Over (Spec R)}
    {g l : T ⟶ (groupScheme (Fin N) R).X} :
    Dynamic.HasLimit (blockShapeCocharacter B R) g l ↔
      ∃ hg : pointsEquiv (Fin N) R T g ∈ B.parabolic Γ(T.left, ⊤),
        pointsEquiv (Fin N) R T l =
          B.leviEmbedding Γ(T.left, ⊤) (B.leviProjection Γ(T.left, ⊤) ⟨_, hg⟩) := by
  rw [blockShapeCocharacter, hasLimit_diagonalCocharacter_iff]
  constructor
  · rintro ⟨hg, hl⟩
    have hg' : pointsEquiv (Fin N) R T g ∈ B.parabolic Γ(T.left, ⊤) := by
      rw [← blockParabolicSubgroup_blockShapeWeight]
      exact hg
    refine ⟨hg', ?_⟩
    rw [hl, ← leviEmbedding_leviProjection]
    rfl
  · rintro ⟨hg, hl⟩
    have hg' : g ∈ (blockParabolic (Fin N) R (blockShapeWeight B)).carrier T := by
      change pointsEquiv (Fin N) R T g ∈ blockParabolicSubgroup _ _
      rw [blockParabolicSubgroup_blockShapeWeight]
      exact hg
    refine ⟨hg', ?_⟩
    rw [hl, ← leviEmbedding_leviProjection]
    rfl

end BlockShape

end Langlands.GroupScheme.GeneralLinear
