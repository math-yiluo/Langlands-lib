import Mathlib.Algebra.BrauerGroup.Defs
import Mathlib.Algebra.Central.Basic
import Mathlib.Algebra.Central.Matrix
import Mathlib.RingTheory.SimpleRing.Matrix
import Mathlib.RingTheory.SimpleRing.Congr
import Mathlib.RingTheory.SimpleModule.WedderburnArtin
import Mathlib.RingTheory.Idempotents
import Mathlib.RingTheory.Artinian.Algebra
import Mathlib.Data.Matrix.Composition

/-! # Corner algebras of central simple algebras -/

noncomputable section

universe u v

namespace Langlands.Brauer

variable {K : Type u} [Field K] {A : Type v} [Ring A] [Algebra K A] {e : A}

section CornerAlgebra

/-- The corner `e A e` is stable under scalar multiplication. -/
theorem corner_smul_mem (he : IsIdempotentElem e) (c : K) {x : A} (hx : x ∈ Subsemigroup.corner e) :
    c • x ∈ Subsemigroup.corner e := by
  rw [Subsemigroup.mem_corner_iff he] at hx ⊢
  exact ⟨by rw [mul_smul_comm, hx.1], by rw [smul_mul_assoc, hx.2]⟩

instance cornerSMul (he : IsIdempotentElem e) : SMul K he.Corner :=
  ⟨fun c x => ⟨c • x.1, corner_smul_mem he c x.2⟩⟩

/-- The additive inclusion of the corner into the ambient algebra. -/
def cornerAddHom (he : IsIdempotentElem e) : he.Corner →+ A where
  toFun x := x.1
  map_zero' := rfl
  map_add' _ _ := rfl

theorem cornerAddHom_injective (he : IsIdempotentElem e) : Function.Injective (cornerAddHom he) :=
  fun _ _ h => Subtype.ext h

instance cornerModule (he : IsIdempotentElem e) : Module K he.Corner :=
  Function.Injective.module K (cornerAddHom he) (cornerAddHom_injective he) fun _ _ => rfl

instance cornerAlgebra (he : IsIdempotentElem e) : Algebra K he.Corner :=
  Algebra.ofModule (fun c x y => Subtype.ext (smul_mul_assoc c x.1 y.1))
    (fun c x y => Subtype.ext (mul_smul_comm c x.1 y.1))

variable (K) in
/-- The `K`-linear inclusion of the corner `e A e` into `A`. -/
def cornerInclusion (he : IsIdempotentElem e) : he.Corner →ₗ[K] A where
  toFun x := x.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable (he : IsIdempotentElem e)

@[simp] theorem cornerInclusion_apply (x : he.Corner) : cornerInclusion K he x = x.1 := rfl

theorem cornerInclusion_injective : Function.Injective (cornerInclusion K he) :=
  fun _ _ h => Subtype.ext h

theorem cornerInclusion_mul (x y : he.Corner) :
    cornerInclusion K he (x * y) = cornerInclusion K he x * cornerInclusion K he y := rfl

theorem cornerInclusion_one : cornerInclusion K he 1 = e := rfl

theorem cornerInclusion_algebraMap (c : K) :
    cornerInclusion K he (algebraMap K he.Corner c) = c • e := by
  rw [Algebra.algebraMap_eq_smul_one]
  rfl

instance cornerFiniteDimensional [FiniteDimensional K A] : FiniteDimensional K he.Corner :=
  Module.Finite.of_injective (cornerInclusion K he) (cornerInclusion_injective he)

end CornerAlgebra

section LeftIdeal

variable (e) in
/-- The left ideal `A e`, described as the elements fixed by right multiplication
by `e`. -/
def cornerLeftIdeal : Submodule A A where
  carrier := {x | x * e = x}
  add_mem' := by
    intro a b ha hb
    change a * e = a at ha
    change b * e = b at hb
    change (a + b) * e = a + b
    rw [add_mul, ha, hb]
  zero_mem' := zero_mul e
  smul_mem' := by
    intro c x hx
    change x * e = x at hx
    change c * x * e = c * x
    rw [mul_assoc, hx]

theorem mem_cornerLeftIdeal {x : A} : x ∈ cornerLeftIdeal e ↔ x * e = x := Iff.rfl

variable (he : IsIdempotentElem e)

/-- The idempotent `e` as an element of the left ideal `A e`. -/
def cornerGenerator : cornerLeftIdeal e := ⟨e, he.eq⟩

theorem smul_cornerGenerator (x : cornerLeftIdeal e) :
    x.1 • cornerGenerator he = x := Subtype.ext x.2

theorem endo_apply_eq (f : Module.End A (cornerLeftIdeal e)) (x : cornerLeftIdeal e) :
    (f x).1 = x.1 * (f (cornerGenerator he)).1 := by
  conv_lhs => rw [← smul_cornerGenerator he x, map_smul]
  rfl

theorem endo_generator_mem (f : Module.End A (cornerLeftIdeal e)) :
    (f (cornerGenerator he)).1 ∈ Subsemigroup.corner e := by
  rw [Subsemigroup.mem_corner_iff he]
  refine ⟨?_, (f (cornerGenerator he)).2⟩
  have h := endo_apply_eq he f (cornerGenerator he)
  exact h.symm

/-- Right multiplication by an element of the corner, as an endomorphism of `A e`. -/
def cornerRightMul (c : he.Corner) : Module.End A (cornerLeftIdeal e) where
  toFun x := ⟨x.1 * c.1, by
    rw [mem_cornerLeftIdeal, mul_assoc, ((Subsemigroup.mem_corner_iff he).mp c.2).2]⟩
  map_add' x y := Subtype.ext (add_mul x.1 y.1 c.1)
  map_smul' a x := Subtype.ext (mul_assoc a x.1 c.1)

/-- The endomorphism algebra of the left ideal `A e` is the opposite of the
corner `e A e`. -/
def cornerEndEquiv : Module.End A (cornerLeftIdeal e) ≃ₐ[K] (he.Corner)ᵐᵒᵖ :=
  AlgEquiv.ofRingEquiv (f := {
    toFun := fun f => MulOpposite.op ⟨(f (cornerGenerator he)).1, endo_generator_mem he f⟩
    invFun := fun c => cornerRightMul he c.unop
    left_inv := by
      intro f
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      exact (endo_apply_eq he f x).symm
    right_inv := by
      intro c
      apply MulOpposite.unop_injective
      apply Subtype.ext
      exact ((Subsemigroup.mem_corner_iff he).mp c.unop.2).1
    map_mul' := by
      intro f g
      apply MulOpposite.unop_injective
      apply Subtype.ext
      exact endo_apply_eq he f (g (cornerGenerator he))
    map_add' := by
      intro f g
      rfl })
    (by
      intro c
      apply MulOpposite.unop_injective
      apply Subtype.ext
      change (c • cornerGenerator he).1 = cornerInclusion K he (algebraMap K he.Corner c)
      rw [cornerInclusion_algebraMap]
      rfl)

end LeftIdeal

section Matrix

/-- If a matrix algebra over `B` with a nonempty index type is central, then
`B` is central. -/
theorem isCentral_of_matrix {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {B : Type*} [Ring B] [Algebra K B] [Algebra.IsCentral K (Matrix ι ι B)] :
    Algebra.IsCentral K B where
  out := by
    intro z hz
    obtain ⟨i⟩ := ‹Nonempty ι›
    have hmem : Matrix.scalarAlgHom ι K z ∈ Subalgebra.center K (Matrix ι ι B) := by
      rw [Matrix.subalgebraCenter_eq_scalarAlgHom_map]
      exact ⟨z, hz, rfl⟩
    obtain ⟨c, hc⟩ := Algebra.mem_bot.mp (Algebra.IsCentral.out hmem)
    refine Algebra.mem_bot.mpr ⟨c, ?_⟩
    have h := congrFun (congrFun hc i) i
    simpa [Matrix.algebraMap_matrix_apply] using h

end Matrix

section Wedderburn

variable [FiniteDimensional K A] [IsSimpleRing A] (he : IsIdempotentElem e) (hne : e ≠ 0)

include hne in
/-- The corner of a finite-dimensional simple algebra at a nonzero idempotent is a
matrix algebra over the Wedderburn division algebra of the ambient algebra, and
the ambient algebra is a matrix algebra over the same division algebra. -/
theorem exists_matrix_divisionRing_corner :
    ∃ (n m : ℕ) (_ : NeZero n) (_ : NeZero m) (D : Type v) (_ : DivisionRing D)
      (_ : Algebra K D),
      Nonempty (A ≃ₐ[K] Matrix (Fin n) (Fin n) D) ∧
        Nonempty (he.Corner ≃ₐ[K] Matrix (Fin m) (Fin m) D) := by
  classical
  have : IsArtinianRing A := IsArtinianRing.of_finite K A
  obtain ⟨n, hn, I, hI, ⟨ψ⟩⟩ := IsSimpleRing.exists_algEquiv_matrix_end_mulOpposite K A
  have hiso : IsIsotypicOfType A (cornerLeftIdeal e) I :=
    (IsSimpleRing.isIsotypic A A I).of_injective (cornerLeftIdeal e).subtype
      Subtype.val_injective
  have : Module.Finite K (cornerLeftIdeal e) :=
    Module.Finite.of_injective ((cornerLeftIdeal e).restrictScalars K).subtype
      Subtype.val_injective
  have : Module.Finite A (cornerLeftIdeal e) := Module.Finite.of_restrictScalars_finite K A _
  obtain ⟨m, ⟨φ⟩⟩ := hiso.linearEquiv_fun
  have hm : NeZero m := by
    refine ⟨fun hm0 => hne ?_⟩
    subst hm0
    have h0 : φ (cornerGenerator he) = φ 0 := Subsingleton.elim _ _
    have h1 := congrArg Subtype.val (φ.injective h0)
    exact h1
  refine ⟨n, m, hn, hm, (Module.End A I)ᵐᵒᵖ, inferInstance, inferInstance, ⟨ψ⟩, ⟨?_⟩⟩
  exact (AlgEquiv.opOp K he.Corner).trans <|
    (AlgEquiv.op ((cornerEndEquiv (K := K) he).symm.trans <| (φ.conjAlgEquiv K).trans
      (endVecAlgEquivMatrixEnd (Fin m) K A I))).trans (AlgEquiv.mopMatrix).symm

include hne in
/-- Matrix algebras over the corner and over the ambient algebra are isomorphic. -/
theorem exists_matrix_corner_algEquiv :
    ∃ (n m : ℕ), n ≠ 0 ∧ m ≠ 0 ∧
      Nonempty (Matrix (Fin n) (Fin n) he.Corner ≃ₐ[K] Matrix (Fin m) (Fin m) A) := by
  classical
  obtain ⟨n, m, hn, hm, D, _, _, ⟨ψA⟩, ⟨ψC⟩⟩ := exists_matrix_divisionRing_corner (K := K) he hne
  refine ⟨n, m, hn.out, hm.out, ⟨?_⟩⟩
  exact ψC.mapMatrix.trans <| (Matrix.compAlgEquiv (Fin n) (Fin m) D K).trans <|
    (Matrix.reindexAlgEquiv K D (Equiv.prodComm (Fin n) (Fin m))).trans <|
    (Matrix.compAlgEquiv (Fin m) (Fin n) D K).symm.trans ψA.symm.mapMatrix

variable (K) in
include K hne in
/-- The corner of a finite-dimensional simple algebra at a nonzero idempotent is
simple. -/
theorem isSimpleRing_corner : IsSimpleRing he.Corner := by
  classical
  obtain ⟨n, m, hn, hm, D, _, _, -, ⟨ψC⟩⟩ := exists_matrix_divisionRing_corner (K := K) he hne
  exact IsSimpleRing.of_ringEquiv ψC.symm.toRingEquiv inferInstance

include hne in
/-- The corner of a finite-dimensional central simple algebra at a nonzero
idempotent is central. -/
theorem isCentral_corner [Algebra.IsCentral K A] : Algebra.IsCentral K he.Corner := by
  classical
  obtain ⟨n, m, hn, hm, ⟨χ⟩⟩ := exists_matrix_corner_algEquiv (K := K) he hne
  have : NeZero n := ⟨hn⟩
  have : Algebra.IsCentral K (Matrix (Fin n) (Fin n) he.Corner) :=
    Algebra.IsCentral.of_algEquiv K _ _ χ.symm
  exact isCentral_of_matrix (ι := Fin n)

end Wedderburn

/-- The corner `e A e` of a central simple algebra at a nonzero idempotent, as a
central simple algebra. -/
def cornerCSA (A : CSA.{u, v} K) {e : A} (he : IsIdempotentElem e) (hne : e ≠ 0) :
    CSA.{u, v} K where
  carrier := he.Corner
  isCentral := isCentral_corner he hne
  isSimple := isSimpleRing_corner K he hne
  fin_dim := inferInstance

/-- The corner of a central simple algebra at a nonzero idempotent is Brauer
equivalent to the algebra. -/
theorem isBrauerEquivalent_cornerCSA (A : CSA.{u, v} K) {e : A} (he : IsIdempotentElem e)
    (hne : e ≠ 0) : IsBrauerEquivalent (cornerCSA A he hne) A :=
  exists_matrix_corner_algEquiv he hne

/-- The corner of a central simple algebra at a nonzero idempotent has the same
class in Mathlib's Brauer group quotient. -/
theorem brauerClass_cornerCSA (A : CSA.{u, v} K) {e : A} (he : IsIdempotentElem e)
    (hne : e ≠ 0) :
    (Quotient.mk (Brauer.CSA_Setoid K) (cornerCSA A he hne) : BrauerGroup.{u, v} K) =
      Quotient.mk (Brauer.CSA_Setoid K) A :=
  Quotient.sound (isBrauerEquivalent_cornerCSA A he hne)

end Langlands.Brauer
