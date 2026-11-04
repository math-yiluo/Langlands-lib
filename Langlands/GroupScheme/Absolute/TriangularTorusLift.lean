import Langlands.GroupScheme.Absolute.TriangularLayerFiltration
import Langlands.GroupScheme.Torus.LaurentRootAverage
import Langlands.GroupScheme.Rational.SplitTorusVectorExtension

/-! # Correcting triangular lifts of split-torus points to homomorphisms -/

noncomputable section

universe u

open Matrix

namespace Langlands.GroupScheme.TriangularLayer

/-! ### Diagonal parts -/

section Diagonal

variable {A B : Type*} [CommRing A] [CommRing B] {N : ℕ}

variable (A N) in
/-- The diagonal part of an upper triangular invertible matrix. -/
abbrev diagPart : upper A N →* GL (Fin N) A :=
  GeneralLinear.blockLeviProjection A (fun i : Fin N => -(i.val : ℤ))

theorem diagPart_apply (g : upper A N) (i j : Fin N) :
    (diagPart A N g : Matrix (Fin N) (Fin N) A) i j =
      if i = j then ((g : GL (Fin N) A) : Matrix (Fin N) (Fin N) A) i j else 0 := by
  rw [GeneralLinear.coe_blockLeviProjection, GeneralLinear.blockDiagonalPart_apply]
  by_cases h : i = j
  · subst h
    simp
  · rw [ite_eq_right h, ite_eq_right fun h' => h (Fin.ext (by exact_mod_cast neg_inj.1 h'))]

theorem diagPart_apply_self (g : upper A N) (i : Fin N) :
    (diagPart A N g : Matrix (Fin N) (Fin N) A) i i =
      ((g : GL (Fin N) A) : Matrix (Fin N) (Fin N) A) i i := by
  rw [diagPart_apply, ite_eq_left rfl]

theorem diagPart_mem_upper (g : upper A N) : diagPart A N g ∈ upper A N :=
  mem_upper.2 fun i j h => by rw [diagPart_apply, ite_eq_right (ne_of_lt h).symm]

theorem diagPart_eq_one {g : upper A N} (hg : (g : GL (Fin N) A) ∈ W A N 0) :
    diagPart A N g = 1 := by
  apply Units.ext
  ext i j
  rw [diagPart_apply, Units.val_one]
  split_ifs with h
  · subst h
    rw [apply_self_of_mem_W hg, one_apply_eq]
  · exact (one_apply_ne h).symm

/-- Dividing an upper triangular matrix by its diagonal part gives a unitriangular matrix. -/
theorem inv_diagPart_mul_mem_W (g : upper A N) :
    (diagPart A N g)⁻¹ * (g : GL (Fin N) A) ∈ W A N 0 := by
  have hD : IsUpper (((diagPart A N g)⁻¹ : GL (Fin N) A) : Matrix (Fin N) (Fin N) A) :=
    isUpper_inv (mem_upper.1 (diagPart_mem_upper g))
  have hg : IsUpper ((g : GL (Fin N) A) : Matrix (Fin N) (Fin N) A) := mem_upper.1 g.2
  rw [mem_W, Units.val_mul]
  intro i j hij
  rw [Matrix.sub_apply]
  rcases lt_or_eq_of_le (show (j : ℕ) ≤ i by omega) with h | h
  · have h' : j < i := Fin.lt_def.2 h
    rw [hD.mul hg i j h', one_apply_ne (ne_of_lt h').symm, sub_zero]
  · have h' : j = i := Fin.ext h
    subst h'
    rw [hD.mul_apply_self hg, ← map_inv, diagPart_apply_self, InvMemClass.coe_inv,
      inv_apply_self_mul hg, one_apply_eq, sub_self]

theorem map_diagPart (f : A →+* B) (g : upper A N) :
    Matrix.GeneralLinearGroup.map f (diagPart A N g) =
      diagPart B N ⟨Matrix.GeneralLinearGroup.map f g, mem_upper.2 ((mem_upper.1 g.2).map f)⟩ := by
  apply Units.ext
  ext i j
  rw [coe_map, Matrix.map_apply, diagPart_apply, diagPart_apply]
  split_ifs
  · rfl
  · exact map_zero f

/-- Conjugation by a unitriangular matrix keeps the diagonal entries. -/
theorem conj_apply_self {x g : GL (Fin N) A} (hx : x ∈ W A N 0) (hg : g ∈ upper A N)
    (i : Fin N) :
    ((x⁻¹ * g * x : GL (Fin N) A) : Matrix (Fin N) (Fin N) A) i i =
      (g : Matrix (Fin N) (Fin N) A) i i := by
  have hx' := isUpper_of_mem_W hx
  have hxi := isUpper_of_mem_W ((W A N 0).inv_mem hx)
  rw [Units.val_mul, Units.val_mul, (hxi.mul (mem_upper.1 hg)).mul_apply_self hx',
    hxi.mul_apply_self (mem_upper.1 hg), apply_self_of_mem_W hx,
    apply_self_of_mem_W ((W A N 0).inv_mem hx), one_mul, mul_one]

theorem isLevel_layer (a : ℕ) (X : Matrix (Fin N) (Fin N) A) : IsLevel a (layer A N a X) :=
  fun i j h => by rw [layer_apply, ite_eq_right (by omega)]

/-- Over a field, every strictly upper triangular matrix of level `a` is `z - 1` for some `z`
in the `a`-th filtration term. -/
theorem exists_unitriangular {k : Type*} [Field k] {a : ℕ} {v : Matrix (Fin N) (Fin N) k}
    (hv : IsLevel a v) :
    ∃ z : GL (Fin N) k, z ∈ W k N a ∧ (z : Matrix (Fin N) (Fin N) k) - 1 = v := by
  have hu : IsUpper (1 + v) := isUpper_one.add hv.isUpper
  have hdet : (1 + v).det ≠ 0 := by
    rw [det_of_isUpperTriangular hu, Finset.prod_eq_one fun i _ => by
      rw [Matrix.add_apply, one_apply_eq, hv i i (by omega), add_zero]]
    exact one_ne_zero
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (1 + v) hdet, ?_, ?_⟩
  · rw [mem_W]
    change IsLevel a ((1 + v) - 1)
    rw [add_sub_cancel_left]
    exact hv
  · change (1 + v) - 1 = v
    rw [add_sub_cancel_left]

end Diagonal

/-! ### Laurent monomials -/

section Laurent

variable {k : Type u} [Field k] (I : Type u) [Fintype I] [DecidableEq I]

/-- The independent Laurent monomials: the universal family of units. -/
def laurentVar (A : Type u) [CommRing A] : I → (AddMonoidAlgebra A (I → ℤ))ˣ :=
  fun i => (AddMonoidAlgebra.of A (I → ℤ)).toHomUnits (Multiplicative.ofAdd (Pi.single i 1))

omit [Fintype I] in
theorem laurentVar_val (A : Type u) [CommRing A] (i : I) :
    (laurentVar I A i : AddMonoidAlgebra A (I → ℤ)) = AddMonoidAlgebra.single (Pi.single i 1) 1 :=
  rfl

omit [Fintype I] in
/-- Extending the coefficients of the universal family over the field. -/
theorem laurentVar_scalars (A : Type u) [CommRing A] [Algebra k A] :
    (fun i => Units.map (splitTorus.laurentScalars (k := k) I A).toMonoidHom (laurentVar I k i)) =
      laurentVar I A := by
  funext i
  apply Units.ext
  rw [Units.coe_map, laurentVar_val, laurentVar_val]
  change AddMonoidAlgebra.mapAlgHom (I → ℤ) (Algebra.ofId k A) (AddMonoidAlgebra.single _ 1) = _
  rw [AddMonoidAlgebra.mapAlgHom_single, map_one]

/-- Translating the universal family by a family of units. -/
theorem laurentVar_translate (A : Type u) [CommRing A] [Algebra k A] (t : I → Aˣ) :
    (fun i => Units.map ((splitTorus.laurentTranslation I t).restrictScalars k).toMonoidHom
      (laurentVar I A i)) =
      laurentVar I A * fun i => Units.map (splitTorus.laurentConst (k := k) I A).toMonoidHom (t i) := by
  funext i
  apply Units.ext
  rw [Units.coe_map, Pi.mul_apply, Units.val_mul, Units.coe_map, laurentVar_val]
  change splitTorus.laurentTranslation I t (AddMonoidAlgebra.single _ 1) =
    AddMonoidAlgebra.single _ 1 * algebraMap A (AddMonoidAlgebra A (I → ℤ)) (t i : A)
  rw [splitTorus.laurentTranslation_single, splitTorus.exponentValue_single,
    AddMonoidAlgebra.coe_algebraMap, Function.comp_apply, Algebra.algebraMap_self,
    RingHom.id_apply, AddMonoidAlgebra.single_mul_single, add_zero, one_mul]

end Laurent

/-! ### Lifts of torus points -/

variable (k : Type u) [Field k] (I : Type u) (N : ℕ)

/-- A natural family of upper triangular lifts of the points of the split torus `𝔾ₘ ^ I`,
multiplicative modulo a natural family of unitriangular subgroups normalized by the lifts. -/
structure TorusLift where
  /-- The lift of a point of the torus. -/
  lift : ∀ (A : Type u) [CommRing A] [Algebra k A], (I → Aˣ) → GL (Fin N) A
  /-- The subgroups modulo which the lift is multiplicative. -/
  kernel : ∀ (A : Type u) [CommRing A] [Algebra k A], Subgroup (GL (Fin N) A)
  lift_naturality : ∀ (A B : Type u) [CommRing A] [Algebra k A] [CommRing B] [Algebra k B]
    (φ : A →ₐ[k] B) (t : I → Aˣ),
    Matrix.GeneralLinearGroup.map (φ : A →+* B) (lift A t) =
      lift B (fun i => Units.map φ.toMonoidHom (t i))
  map_mem_kernel : ∀ (A B : Type u) [CommRing A] [Algebra k A] [CommRing B] [Algebra k B]
    (φ : A →ₐ[k] B) (x : GL (Fin N) A), x ∈ kernel A →
      Matrix.GeneralLinearGroup.map (φ : A →+* B) x ∈ kernel B
  lift_mem_upper : ∀ (A : Type u) [CommRing A] [Algebra k A] (t : I → Aˣ),
    lift A t ∈ upper A N
  kernel_le : ∀ (A : Type u) [CommRing A] [Algebra k A], kernel A ≤ W A N 0
  lift_mul_mem : ∀ (A : Type u) [CommRing A] [Algebra k A] (t t' : I → Aˣ),
    (lift A t * lift A t')⁻¹ * lift A (t * t') ∈ kernel A
  conj_mem : ∀ (A : Type u) [CommRing A] [Algebra k A] (t : I → Aˣ) (x : GL (Fin N) A),
    x ∈ kernel A → (lift A t)⁻¹ * x * lift A t ∈ kernel A

namespace TorusLift

variable {k I N} (𝓛 : TorusLift k I N)

section Correction

variable {A B : Type u} [CommRing A] [Algebra k A] [CommRing B] [Algebra k B]

/-- The diagonal part of the lift. -/
def diagLift (t : I → Aˣ) : GL (Fin N) A :=
  diagPart A N ⟨𝓛.lift A t, 𝓛.lift_mem_upper A t⟩

theorem diagLift_mul (t t' : I → Aˣ) :
    𝓛.diagLift (t * t') = 𝓛.diagLift t * 𝓛.diagLift t' := by
  have hd := 𝓛.lift_mul_mem A t t'
  have e : (⟨𝓛.lift A (t * t'), 𝓛.lift_mem_upper A _⟩ : upper A N) =
      ⟨𝓛.lift A t, 𝓛.lift_mem_upper A t⟩ * ⟨𝓛.lift A t', 𝓛.lift_mem_upper A t'⟩ *
        ⟨_, W_le_upper 0 (𝓛.kernel_le A hd)⟩ := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    group
  rw [diagLift, e, map_mul, map_mul, diagPart_eq_one (g := ⟨_, W_le_upper 0 (𝓛.kernel_le A hd)⟩) (𝓛.kernel_le A hd), mul_one]
  rfl

theorem diagLift_naturality (φ : A →ₐ[k] B) (t : I → Aˣ) :
    Matrix.GeneralLinearGroup.map (φ : A →+* B) (𝓛.diagLift t) =
      𝓛.diagLift (fun i => Units.map φ.toMonoidHom (t i)) := by
  rw [diagLift, map_diagPart, diagLift]
  exact congrArg _ (Subtype.ext (𝓛.lift_naturality A B φ t))

theorem map_algebraMap (φ : A →ₐ[k] B) (x : GL (Fin N) k) :
    Matrix.GeneralLinearGroup.map (φ : A →+* B)
        (Matrix.GeneralLinearGroup.map (algebraMap k A) x) =
      Matrix.GeneralLinearGroup.map (algebraMap k B) x := by
  rw [← Matrix.GeneralLinearGroup.map_comp_apply, ← Matrix.GeneralLinearGroup.map_comp,
    AlgHom.comp_algebraMap]

/-- The diagonal part of the lift, conjugated by an invertible matrix over the field. -/
def correction (x : GL (Fin N) k) (t : I → Aˣ) : GL (Fin N) A :=
  (Matrix.GeneralLinearGroup.map (algebraMap k A) x)⁻¹ * 𝓛.diagLift t *
    Matrix.GeneralLinearGroup.map (algebraMap k A) x

/-- The deviation of the lift from the corrected diagonal part. -/
def deviation (x : GL (Fin N) k) (t : I → Aˣ) : GL (Fin N) A :=
  (𝓛.correction x t)⁻¹ * 𝓛.lift A t

theorem correction_mul (x : GL (Fin N) k) (t t' : I → Aˣ) :
    𝓛.correction x (t * t') = 𝓛.correction x t * 𝓛.correction x t' := by
  simp only [correction, diagLift_mul]
  group

theorem correction_naturality (φ : A →ₐ[k] B) (x : GL (Fin N) k) (t : I → Aˣ) :
    Matrix.GeneralLinearGroup.map (φ : A →+* B) (𝓛.correction x t) =
      𝓛.correction x (fun i => Units.map φ.toMonoidHom (t i)) := by
  rw [correction, correction, map_mul, map_mul, map_inv, map_algebraMap, diagLift_naturality]

theorem deviation_naturality (φ : A →ₐ[k] B) (x : GL (Fin N) k) (t : I → Aˣ) :
    Matrix.GeneralLinearGroup.map (φ : A →+* B) (𝓛.deviation x t) =
      𝓛.deviation x (fun i => Units.map φ.toMonoidHom (t i)) := by
  rw [deviation, deviation, map_mul, map_inv, correction_naturality, 𝓛.lift_naturality A B φ t]

/-- The deviation is a crossed cocycle up to the multiplicativity defect of the lift. -/
theorem deviation_mul (x : GL (Fin N) k) (t₁ t₂ : I → Aˣ) :
    𝓛.deviation x (t₁ * t₂) = 𝓛.deviation x t₂ *
      ((𝓛.lift A t₂)⁻¹ * 𝓛.deviation x t₁ * 𝓛.lift A t₂ *
        ((𝓛.lift A t₁ * 𝓛.lift A t₂)⁻¹ * 𝓛.lift A (t₁ * t₂))) := by
  simp only [deviation, correction_mul]
  group

theorem correction_mem_upper {x : GL (Fin N) k} (hx : x ∈ W k N 0) (t : I → Aˣ) :
    𝓛.correction x t ∈ upper A N := by
  have hxA := W_le_upper 0 (map_mem_W hx (algebraMap k A))
  exact (upper A N).mul_mem ((upper A N).mul_mem ((upper A N).inv_mem hxA)
    (diagPart_mem_upper _)) hxA

/-- Conjugation by the correction scales the entries like conjugation by the lift. -/
theorem scale_correction {x : GL (Fin N) k} (hx : x ∈ W k N 0) (t : I → Aˣ)
    (V : Matrix (Fin N) (Fin N) A) :
    scale A N ((𝓛.correction x t)⁻¹ : GL (Fin N) A) (𝓛.correction x t) V =
      scale A N ((𝓛.lift A t)⁻¹ : GL (Fin N) A) (𝓛.lift A t) V := by
  have hxA := map_mem_W hx (algebraMap k A)
  apply scale_congr
  · intro i
    have e : (𝓛.correction x t)⁻¹ = (Matrix.GeneralLinearGroup.map (algebraMap k A) x)⁻¹ *
        diagPart A N ⟨𝓛.lift A t, 𝓛.lift_mem_upper A t⟩⁻¹ *
          Matrix.GeneralLinearGroup.map (algebraMap k A) x := by
      rw [correction, diagLift, map_inv]
      group
    rw [e, conj_apply_self hxA (diagPart_mem_upper _), diagPart_apply_self, InvMemClass.coe_inv]
  · intro i
    rw [correction, diagLift, conj_apply_self hxA (diagPart_mem_upper _), diagPart_apply_self]

theorem deviation_one_mem_W (t : I → Aˣ) : 𝓛.deviation 1 t ∈ W A N 0 := by
  rw [deviation, correction, map_one, inv_one, one_mul, mul_one]
  exact inv_diagPart_mul_mem_W ⟨𝓛.lift A t, 𝓛.lift_mem_upper A t⟩

/-- The corrected diagonal part, as a homomorphism. -/
def correctionHom (x : GL (Fin N) k) (A : Type u) [CommRing A] [Algebra k A] :
    (I → Aˣ) →* GL (Fin N) A :=
  MonoidHom.mk' (𝓛.correction x) (𝓛.correction_mul x)

theorem correctionHom_apply (x : GL (Fin N) k) (t : I → Aˣ) :
    𝓛.correctionHom x A t = 𝓛.correction x t :=
  rfl

end Correction

/-! ### Averaging the layers -/

section Averaging

variable [Fintype I] [DecidableEq I]

/-- The constant Laurent coefficients of the layer at the universal family, extended to `A`,
differ from their conjugate by the lift at `t` by the layer of the deviation at `t`, modulo the
layers of the kernel. -/
theorem layer_coeff_mem [IsAlgClosed k] {x : GL (Fin N) k} {a : ℕ}
    {C : Matrix (Fin N) (Fin N) (AddMonoidAlgebra k (I → ℤ))}
    (hC : Rel (𝓛.kernel _) a (𝓛.deviation x (laurentVar I k)) C)
    {A : Type u} [CommRing A] [Algebra k A] {t : I → Aˣ} {V : Matrix (Fin N) (Fin N) A}
    (hV : Rel (𝓛.kernel A) a (𝓛.deviation x t) V) :
    layer A N a ((C.map fun f => f.coeff 0).map (algebraMap k A)) - layer A N a V -
      scale A N ((𝓛.lift A t)⁻¹ : GL (Fin N) A) (𝓛.lift A t)
        (layer A N a ((C.map fun f => f.coeff 0).map (algebraMap k A))) ∈
      layerGroup (𝓛.kernel A) a := by
  let R := AddMonoidAlgebra A (I → ℤ)
  let κ : A →ₐ[k] R := splitTorus.laurentConst I A
  let σ : AddMonoidAlgebra k (I → ℤ) →ₐ[k] R := splitTorus.laurentScalars I A
  let τ : R →ₐ[k] R := (splitTorus.laurentTranslation I t).restrictScalars k
  let t₂ : I → Rˣ := fun i => Units.map κ.toMonoidHom (t i)
  have hk (B₁ B₂ : Type u) [CommRing B₁] [Algebra k B₁] [CommRing B₂] [Algebra k B₂]
      (φ : B₁ →ₐ[k] B₂) : ∀ y ∈ 𝓛.kernel B₁,
        Matrix.GeneralLinearGroup.map (φ : B₁ →+* B₂) y ∈ 𝓛.kernel B₂ :=
    fun y hy => 𝓛.map_mem_kernel B₁ B₂ φ y hy
  -- The deviation at the universal family over `A`.
  have h1 : Rel (𝓛.kernel R) a (𝓛.deviation x (laurentVar I A)) (C.map σ) := by
    have := hC.map (σ : AddMonoidAlgebra k (I → ℤ) →+* R) (hk _ _ σ)
    rwa [deviation_naturality, laurentVar_scalars] at this
  -- The deviation at the constant family `t`.
  have h2 : Rel (𝓛.kernel R) a (𝓛.deviation x t₂) (V.map κ) := by
    have := hV.map (κ : A →+* R) (hk _ _ κ)
    rwa [deviation_naturality] at this
  -- The deviation at the translated universal family, by the cocycle identity.
  have h3 := Rel.mul (𝓛.kernel_le R) h2 (Rel.mul (𝓛.kernel_le R)
    (Rel.conj (𝓛.lift_mem_upper R t₂) (𝓛.conj_mem R t₂) h1)
    (rel_of_mem (𝓛.lift_mul_mem R (laurentVar I A) t₂)))
  rw [← deviation_mul] at h3
  -- The deviation at the translated universal family, by naturality.
  have h4 : Rel (𝓛.kernel R) a (𝓛.deviation x (laurentVar I A * t₂)) ((C.map σ).map τ) := by
    have := h1.map (τ : R →+* R) (hk _ _ τ)
    rwa [deviation_naturality, laurentVar_translate] at this
  have h5 := h4.unique h3
  have h6 := splitTorus.map_coeff_zero_mem k I (layerGroup (𝓛.kernel A) a) _
    (fun φ => layerGroup_map (φ : R →+* A) (hk _ _ φ) h5)
  convert h6 using 1
  rw [← 𝓛.lift_naturality A R κ t, ← map_inv]
  have hτ (y : R) : (τ y).coeff 0 = y.coeff 0 :=
    splitTorus.coeff_zero_laurentTranslation I t y
  have hσ (f : AddMonoidAlgebra k (I → ℤ)) : (σ f).coeff 0 = algebraMap k A (f.coeff 0) :=
    AddMonoidAlgebra.coeff_mapAlgHom _ _ _
  have hκ (c d : A) (y : R) : ((κ : A →+* R) c * y * (κ : A →+* R) d).coeff 0 =
      c * y.coeff 0 * d := by
    change (AddMonoidAlgebra.single 0 c * y * AddMonoidAlgebra.single 0 d).coeff 0 = _
    rw [AddMonoidAlgebra.coeff_mul_single_zero, AddMonoidAlgebra.coeff_single_zero_mul]
  have hκ0 (c : A) : (κ c).coeff 0 = c := by
    change (AddMonoidAlgebra.single 0 c).coeff 0 = c
    simp
  ext i j
  simp only [Matrix.map_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.zero_apply,
    layer_apply, scale_apply, coe_map]
  split_ifs with h
  · rw [AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply, AddMonoidAlgebra.coeff_add,
      Finsupp.add_apply, hτ, hσ, add_zero, hκ, hσ, hκ0]
    ring
  · simp

/-- One step of the induction along the superdiagonal filtration. -/
theorem exists_approx_succ [IsAlgClosed k] {x : GL (Fin N) k} (hx : x ∈ W k N 0) {a : ℕ}
    (h : ∀ (A : Type u) [CommRing A] [Algebra k A] (t : I → Aˣ),
      Approx (𝓛.kernel A) a (𝓛.deviation x t)) :
    ∃ x' ∈ W k N 0, ∀ (A : Type u) [CommRing A] [Algebra k A] (t : I → Aˣ),
      Approx (𝓛.kernel A) (a + 1) (𝓛.deviation x' t) := by
  obtain ⟨C, hC⟩ := (h (AddMonoidAlgebra k (I → ℤ)) (laurentVar I k)).rel
  obtain ⟨z, hz, hzv⟩ := exists_unitriangular (isLevel_layer a (C.map fun f => f.coeff 0))
  refine ⟨x * z, (W k N 0).mul_mem hx (W_anti (Nat.zero_le a) hz), fun A _ _ t => ?_⟩
  obtain ⟨V, hV⟩ := (h A t).rel
  have key := 𝓛.layer_coeff_mem hC hV
  rw [layer_map] at key
  have hzA : Matrix.GeneralLinearGroup.map (algebraMap k A) z ∈ W A N a := map_mem_W hz _
  have hc : 𝓛.correction x t ∈ upper A N := 𝓛.correction_mem_upper hx t
  have e : 𝓛.deviation (x * z) t = (Matrix.GeneralLinearGroup.map (algebraMap k A) z)⁻¹ *
      ((𝓛.correction x t)⁻¹ * Matrix.GeneralLinearGroup.map (algebraMap k A) z *
        𝓛.correction x t * 𝓛.deviation x t) := by
    simp only [deviation, correction, map_mul]
    group
  rw [e]
  have hr := Rel.mul (𝓛.kernel_le A) (rel_of_mem_W ((W A N a).inv_mem hzA))
    (Rel.mul (𝓛.kernel_le A) (rel_of_mem_W (W_conj hc hzA)) hV)
  apply hr.approx_succ
  rw [map_add, map_add, layer_inv hzA, layer_conj hc hzA, layer_map_W, hzv, layer_layer,
    scale_correction 𝓛 hx]
  have := (layerGroup (𝓛.kernel A) a).neg_mem key
  convert this using 1
  abel

/-- **Correction of triangular lifts.** Over an algebraically closed field, some conjugate of
the diagonal part of the lift by a unitriangular matrix agrees with the lift modulo the kernel
at every point of the torus. -/
theorem exists_deviation_mem [IsAlgClosed k] :
    ∃ x ∈ W k N 0, ∀ (A : Type u) [CommRing A] [Algebra k A] (t : I → Aˣ),
      𝓛.deviation x t ∈ 𝓛.kernel A := by
  have key (a : ℕ) : ∃ x ∈ W k N 0, ∀ (A : Type u) [CommRing A] [Algebra k A] (t : I → Aˣ),
      Approx (𝓛.kernel A) a (𝓛.deviation x t) := by
    induction a with
    | zero =>
        exact ⟨1, (W k N 0).one_mem, fun A _ _ t => approx_of_mem_W (𝓛.deviation_one_mem_W t)⟩
    | succ a ih =>
        obtain ⟨x, hx, h⟩ := ih
        exact 𝓛.exists_approx_succ hx h
  obtain ⟨x, hx, h⟩ := key N
  exact ⟨x, hx, fun A _ _ t => mem_of_approx_top (h A t)⟩

end Averaging

end TorusLift

end Langlands.GroupScheme.TriangularLayer
