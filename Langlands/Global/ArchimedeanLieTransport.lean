import Langlands.Global.ArchimedeanGLTransport
import Langlands.Global.ArchimedeanLieAlgebra

/-! # Arithmetic transport of the actual archimedean Lie and enveloping algebras -/

noncomputable section
universe uK uL uM

open scoped Classical TensorProduct Matrix.Norms.Operator

set_option autoImplicit false

namespace Langlands.Global.ArchimedeanLieTransport

open NumberField AdelicFunctoriality ArchimedeanGL ArchimedeanGLTransport

variable {K : Type uK} {L : Type uL} {M : Type uM}
variable [Field K] [NumberField K] [Field L] [NumberField L] [Field M] [NumberField M]

@[simp] theorem mixedEquiv_refl (x : mixedEmbedding.mixedSpace K) :
    mixedEquiv (RingEquiv.refl K) x = x := by
  simp [mixedEquiv, infiniteAdeleEquiv_refl]

theorem mixedEquiv_trans (e : K ≃+* L) (a : L ≃+* M)
    (x : mixedEmbedding.mixedSpace K) :
    mixedEquiv (e.trans a) x = mixedEquiv a (mixedEquiv e x) := by
  change InfiniteAdeleRing.ringEquiv_mixedSpace M
      (infiniteAdeleEquiv (e.trans a) ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm x)) =
    InfiniteAdeleRing.ringEquiv_mixedSpace M
      (infiniteAdeleEquiv a ((InfiniteAdeleRing.ringEquiv_mixedSpace L).symm
        (InfiniteAdeleRing.ringEquiv_mixedSpace L
          (infiniteAdeleEquiv e ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm x)))))
  rw [RingEquiv.symm_apply_apply, infiniteAdeleEquiv_trans]
  rfl

/-- Arithmetic transport of the real matrix commutator Lie algebra. -/
def realLieEquiv (n : ℕ) (e : K ≃+* L) :
    RealLieAlgebra K n ≃ₗ⁅ℝ⁆ RealLieAlgebra L n :=
  { ((realLieAlgebraToMatrix K n).trans (matrixRealLinearEquiv n e).toLinearEquiv).trans
      (realLieAlgebraToMatrix L n).symm with
    map_lie' := by
      intro X Y
      change (mixedEquiv e).mapMatrix
          (realLieAlgebraToMatrix K n X * realLieAlgebraToMatrix K n Y -
            realLieAlgebraToMatrix K n Y * realLieAlgebraToMatrix K n X) =
        (mixedEquiv e).mapMatrix (realLieAlgebraToMatrix K n X) *
            (mixedEquiv e).mapMatrix (realLieAlgebraToMatrix K n Y) -
          (mixedEquiv e).mapMatrix (realLieAlgebraToMatrix K n Y) *
            (mixedEquiv e).mapMatrix (realLieAlgebraToMatrix K n X)
      rw [map_sub, map_mul, map_mul] }

@[simp] theorem realLieEquiv_matrix (n : ℕ) (e : K ≃+* L)
    (X : RealLieAlgebra K n) :
    realLieAlgebraToMatrix L n (realLieEquiv n e X) =
      matrixRealLinearEquiv n e (realLieAlgebraToMatrix K n X) := rfl

@[simp] theorem realLieEquiv_entry (n : ℕ) (e : K ≃+* L)
    (X : RealLieAlgebra K n) (i j : Fin n) :
    realLieAlgebraToMatrix L n (realLieEquiv n e X) i j =
      mixedEquiv e (realLieAlgebraToMatrix K n X i j) := rfl

@[simp] theorem realLieEquiv_refl (n : ℕ) :
    realLieEquiv n (RingEquiv.refl K) = LieEquiv.refl := by
  apply LieEquiv.ext
  intro X
  apply (realLieAlgebraToMatrix K n).injective
  apply Matrix.ext
  intro i j
  exact mixedEquiv_refl (realLieAlgebraToMatrix K n X i j)

theorem realLieEquiv_trans (n : ℕ) (e : K ≃+* L) (a : L ≃+* M) :
    realLieEquiv n (e.trans a) = (realLieEquiv n e).trans (realLieEquiv n a) := by
  apply LieEquiv.ext
  intro X
  apply (realLieAlgebraToMatrix M n).injective
  apply Matrix.ext
  intro i j
  exact mixedEquiv_trans e a (realLieAlgebraToMatrix K n X i j)

@[simp] theorem realLieEquiv_symm (n : ℕ) (e : K ≃+* L) :
    realLieEquiv n e.symm = (realLieEquiv n e).symm := by
  apply LieEquiv.ext
  intro X
  apply (realLieEquiv n e).injective
  have h := congrArg (fun f : RealLieAlgebra L n ≃ₗ⁅ℝ⁆ RealLieAlgebra L n => f X)
    (realLieEquiv_trans n e.symm e)
  simpa using h.symm

/-- Scalar extension fixes the complex coefficient of every pure tensor. -/
def complexLieEquiv (n : ℕ) (e : K ≃+* L) :
    ComplexLieAlgebra K n ≃ₗ⁅ℂ⁆ ComplexLieAlgebra L n :=
  { (realLieEquiv n e).toLinearEquiv.baseChange ℝ ℂ _ _ with
    map_lie' := by
      intro X Y
      exact (LieAlgebra.ExtendScalars.map (AlgHom.id ℝ ℂ)
        (realLieEquiv n e).toLieHom).map_lie X Y }

@[simp] theorem complexLieEquiv_tmul (n : ℕ) (e : K ≃+* L)
    (z : ℂ) (X : RealLieAlgebra K n) :
    complexLieEquiv n e (z ⊗ₜ[ℝ] X) = z ⊗ₜ[ℝ] realLieEquiv n e X := rfl

@[simp] theorem complexLieEquiv_complexify (n : ℕ) (e : K ≃+* L)
    (X : RealLieAlgebra K n) :
    complexLieEquiv n e (complexify K n X) = complexify L n (realLieEquiv n e X) := rfl

@[simp] theorem complexLieEquiv_refl (n : ℕ) :
    complexLieEquiv n (RingEquiv.refl K) = LieEquiv.refl := by
  apply LieEquiv.ext
  intro X
  induction X using TensorProduct.inductionOn with
  | tmul z X => simp
  | add X Y hX hY => simpa only [map_add] using congrArg₂ (· + ·) hX hY

theorem complexLieEquiv_trans (n : ℕ) (e : K ≃+* L) (a : L ≃+* M) :
    complexLieEquiv n (e.trans a) =
      (complexLieEquiv n e).trans (complexLieEquiv n a) := by
  apply LieEquiv.ext
  intro X
  induction X using TensorProduct.inductionOn with
  | tmul z X => simp [realLieEquiv_trans]
  | add X Y hX hY => simpa only [map_add] using congrArg₂ (· + ·) hX hY

@[simp] theorem complexLieEquiv_symm (n : ℕ) (e : K ≃+* L) :
    complexLieEquiv n e.symm = (complexLieEquiv n e).symm := by
  apply LieEquiv.ext
  intro X
  apply (complexLieEquiv n e).injective
  have h := congrArg (fun f : ComplexLieAlgebra L n ≃ₗ⁅ℂ⁆ ComplexLieAlgebra L n => f X)
    (complexLieEquiv_trans n e.symm e)
  simpa using h.symm

attribute [local instance 100] LieRing.ofAssociativeRing

private def envelopingHom (n : ℕ) (e : K ≃+* L) :
    EnvelopingAlgebra K n →ₐ[ℂ] EnvelopingAlgebra L n :=
  UniversalEnvelopingAlgebra.lift ℂ
    ((envelopingGenerator L n).comp (complexLieEquiv n e).toLieHom)

private theorem envelopingHom_generator (n : ℕ) (e : K ≃+* L)
    (X : ComplexLieAlgebra K n) :
    envelopingHom n e (envelopingGenerator K n X) =
      envelopingGenerator L n (complexLieEquiv n e X) :=
  UniversalEnvelopingAlgebra.lift_ι_apply ℂ _ X

private theorem envelopingHom_refl (n : ℕ) :
    envelopingHom n (RingEquiv.refl K) = AlgHom.id ℂ (EnvelopingAlgebra K n) := by
  apply UniversalEnvelopingAlgebra.hom_ext
  apply LieHom.ext
  intro X
  change envelopingHom n (RingEquiv.refl K) (envelopingGenerator K n X) =
    envelopingGenerator K n X
  rw [envelopingHom_generator, complexLieEquiv_refl]
  rfl

private theorem envelopingHom_trans (n : ℕ) (e : K ≃+* L) (a : L ≃+* M) :
    envelopingHom n (e.trans a) = (envelopingHom n a).comp (envelopingHom n e) := by
  apply UniversalEnvelopingAlgebra.hom_ext
  apply LieHom.ext
  intro X
  change envelopingHom n (e.trans a) (envelopingGenerator K n X) =
    envelopingHom n a (envelopingHom n e (envelopingGenerator K n X))
  simp only [envelopingHom_generator, complexLieEquiv_trans, LieEquiv.trans_apply]

/-- The genuine universal enveloping lift, with inverse induced by the inverse field map. -/
def envelopingEquiv (n : ℕ) (e : K ≃+* L) :
    EnvelopingAlgebra K n ≃ₐ[ℂ] EnvelopingAlgebra L n :=
  { envelopingHom n e with
    invFun := envelopingHom n e.symm
    left_inv := by
      intro a
      have h : (envelopingHom n e.symm).comp (envelopingHom n e) =
          AlgHom.id ℂ (EnvelopingAlgebra K n) := by
        rw [← envelopingHom_trans, RingEquiv.self_trans_symm, envelopingHom_refl]
      exact AlgHom.congr_fun h a
    right_inv := by
      intro a
      have h : (envelopingHom n e).comp (envelopingHom n e.symm) =
          AlgHom.id ℂ (EnvelopingAlgebra L n) := by
        rw [← envelopingHom_trans, RingEquiv.symm_trans_self, envelopingHom_refl]
      exact AlgHom.congr_fun h a }

@[simp] theorem envelopingEquiv_generator (n : ℕ) (e : K ≃+* L)
    (X : ComplexLieAlgebra K n) :
    envelopingEquiv n e (envelopingGenerator K n X) =
      envelopingGenerator L n (complexLieEquiv n e X) :=
  envelopingHom_generator n e X

@[simp] theorem envelopingEquiv_refl (n : ℕ) :
    envelopingEquiv n (RingEquiv.refl K) = AlgEquiv.refl := by
  apply AlgEquiv.ext
  intro a
  exact AlgHom.congr_fun (envelopingHom_refl n) a

theorem envelopingEquiv_trans (n : ℕ) (e : K ≃+* L) (a : L ≃+* M) :
    envelopingEquiv n (e.trans a) = (envelopingEquiv n e).trans (envelopingEquiv n a) := by
  apply AlgEquiv.ext
  intro x
  exact AlgHom.congr_fun (envelopingHom_trans n e a) x

@[simp] theorem envelopingEquiv_symm (n : ℕ) (e : K ≃+* L) :
    envelopingEquiv n e.symm = (envelopingEquiv n e).symm := by
  apply AlgEquiv.ext
  intro a
  rfl

/-- Restrict arithmetic transport to the actual center of the universal enveloping algebra. -/
def centerEquiv (n : ℕ) (e : K ≃+* L) :
    EnvelopingCenter K n ≃ₐ[ℂ] EnvelopingCenter L n where
  toFun z := ⟨envelopingEquiv n e z.val,
    Subalgebra.map_center_le_center (envelopingEquiv n e).surjective
      ⟨z.val, z.property, rfl⟩⟩
  invFun z := ⟨(envelopingEquiv n e).symm z.val,
    Subalgebra.map_center_le_center (envelopingEquiv n e).symm.surjective
      ⟨z.val, z.property, rfl⟩⟩
  left_inv z := Subtype.ext ((envelopingEquiv n e).symm_apply_apply z.val)
  right_inv z := Subtype.ext ((envelopingEquiv n e).apply_symm_apply z.val)
  map_mul' z w := Subtype.ext (map_mul (envelopingEquiv n e) z.val w.val)
  map_add' z w := Subtype.ext (map_add (envelopingEquiv n e) z.val w.val)
  commutes' c := Subtype.ext ((envelopingEquiv n e).commutes c)

@[simp] theorem centerInclusion_centerEquiv (n : ℕ) (e : K ≃+* L)
    (z : EnvelopingCenter K n) :
    centerInclusion L n (centerEquiv n e z) =
      envelopingEquiv n e (centerInclusion K n z) := rfl

@[simp] theorem centerEquiv_refl (n : ℕ) :
    centerEquiv n (RingEquiv.refl K) = AlgEquiv.refl := by
  apply AlgEquiv.ext
  intro z
  apply Subtype.ext
  change envelopingEquiv n (RingEquiv.refl K) z.val = z.val
  rw [envelopingEquiv_refl]
  rfl

theorem centerEquiv_trans (n : ℕ) (e : K ≃+* L) (a : L ≃+* M) :
    centerEquiv n (e.trans a) = (centerEquiv n e).trans (centerEquiv n a) := by
  apply AlgEquiv.ext
  intro z
  apply Subtype.ext
  change envelopingEquiv n (e.trans a) z.val =
    envelopingEquiv n a (envelopingEquiv n e z.val)
  rw [envelopingEquiv_trans]
  rfl

@[simp] theorem centerEquiv_symm (n : ℕ) (e : K ≃+* L) :
    centerEquiv n e.symm = (centerEquiv n e).symm := by
  apply AlgEquiv.ext
  intro z
  apply Subtype.ext
  rfl

end Langlands.Global.ArchimedeanLieTransport
