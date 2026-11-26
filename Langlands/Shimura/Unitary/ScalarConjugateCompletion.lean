import Langlands.Algebra.CentralSimple.ConjugateTensorInvolution
import Langlands.Algebra.NumberFieldBrauerSplitting
import Langlands.Algebra.LocalReducedCharpolyNeighborhood
import Langlands.ClassFieldTheory.Local.BrauerLocalInvariant
import Langlands.Shimura.Unitary.UnitaryLocalProfileRealizationStatement

/-! # Localization of the scalar conjugate of a central simple algebra -/

noncomputable section

universe u

namespace Langlands.Shimura.FiniteUnitary

open NumberField Langlands.Global Langlands.Global.AdelicFunctoriality
open Langlands.Algebra.CentralSimple Langlands.ClassFieldTheory.Local
open scoped TensorProduct ValuativeRel

local notation "FinitePlace" => Langlands.Global.FinitePlace

section Tensor

variable {K L M A : Type*} [Field K] [Field L] [Field M] [Ring A]
  [Algebra K L] [Algebra K M] [Algebra K A]
  (c : K ≃+* K) (j : L ≃+* M)
  (hj : ∀ r : K, j (algebraMap K L r) = algebraMap K M (c r))

local notation "B" => ScalarConjugate c.symm A

private def conjugateTensorEquiv : L ⊗[K] A ≃+* M ⊗[K] B := by
  let : RingHomInvPair c.toRingHom c.symm.toRingHom := RingHomInvPair.of_ringEquiv c
  let : RingHomInvPair c.symm.toRingHom c.toRingHom := RingHomInvPair.of_ringEquiv_symm c
  let l : L ≃ₛₗ[c.toRingHom] M :=
    { j.toAddEquiv with
      map_smul' := fun r x => by
        change j (r • x) = (c r) • (j x)
        rw [Algebra.smul_def, Algebra.smul_def, map_mul, hj] }
  let f := (ScalarConjugate.toRing c.symm A).symm
  let a : A ≃ₛₗ[c.toRingHom] B :=
    { f.toAddEquiv with
      map_smul' := fun r x => by
        apply (ScalarConjugate.toRing c.symm A).injective
        change r • x = c.symm (c r) • x
        rw [c.symm_apply_apply] }
  let e := TensorProduct.congr l a
  refine { e.toAddEquiv with map_mul' := ?_ }
  intro x y
  change e (x * y) = e x * e y
  induction x using TensorProduct.inductionOn with
  | add x x' hx hx' => simp only [add_mul, map_add, hx, hx']
  | tmul r x =>
    induction y using TensorProduct.inductionOn with
    | add y y' hy hy' => simp only [mul_add, map_add, hy, hy']
    | tmul s y =>
      simp only [e, Algebra.TensorProduct.tmul_mul_tmul, TensorProduct.congr_tmul]
      change j (r * s) ⊗ₜ[K] f (x * y) = (j r * j s) ⊗ₜ[K] (f x * f y)
      rw [map_mul, map_mul]

private theorem conjugateTensorEquiv_tmul (x : L) (a : A) :
    conjugateTensorEquiv c j hj (x ⊗ₜ[K] a) =
      j x ⊗ₜ[K] (ScalarConjugate.toRing c.symm A).symm a := rfl

end Tensor

variable {K : Type u} [Field K] [NumberField K]

/-- Scalar extension of a completed algebra along the isomorphism of conjugate
completions gives the completion of the scalar-conjugate algebra. -/
def scalarConjugateCompletionEquiv (c : K ≃+* K) (q : FinitePlace K) (A : CSA.{u, u} K) :
    let L := FiniteCompletion K (finitePlaceEquiv c q)
    let M := FiniteCompletion K q
    letI : Algebra L M := (finiteCompletionEquiv c q).toRingHom.toAlgebra
    M ⊗[L] (L ⊗[K] A) ≃ₐ[M] M ⊗[K] (ScalarConjugate.csa c.symm A) := by
  let L := FiniteCompletion K (finitePlaceEquiv c q)
  let M := FiniteCompletion K q
  let j : L ≃+* M := finiteCompletionEquiv c q
  let : Algebra L M := j.toRingHom.toAlgebra
  let i : (L ⊗[K] A) ≃ₐ[L] M ⊗[L] (L ⊗[K] A) :=
    AlgEquiv.ofBijective Algebra.TensorProduct.includeRight
      (Algebra.TensorProduct.includeRight_bijective j.bijective)
  let e : L ⊗[K] A ≃+* M ⊗[K] (ScalarConjugate.csa c.symm A) :=
    conjugateTensorEquiv c j (finiteCompletionEquiv_coe c q)
  refine AlgEquiv.ofRingEquiv (f := i.symm.toRingEquiv.trans e) ?_
  intro s
  obtain ⟨x, rfl⟩ := j.surjective s
  have hx : i (algebraMap L (L ⊗[K] A) x) =
      algebraMap M (M ⊗[L] (L ⊗[K] A)) (j x) := i.commutes x
  rw [← hx]
  change e (i.symm (i (x ⊗ₜ[K] (1 : A)))) =
    j x ⊗ₜ[K] (1 : ScalarConjugate.csa c.symm A)
  rw [i.symm_apply_apply]
  exact (conjugateTensorEquiv_tmul c j (finiteCompletionEquiv_coe c q) x 1).trans
    (congrArg (fun b => j x ⊗ₜ[K] b) (map_one (ScalarConjugate.toRing c.symm A).symm))

/-- The finite invariant of the scalar conjugate is the original invariant at
the corresponding conjugate place. -/
theorem finiteBrauerInvariant_scalarConjugate (c : K ≃+* K) (q : FinitePlace K) (A : CSA.{u, u} K) :
    finiteBrauerInvariant K q
      (Brauer.classOf (Brauer.baseChange (FiniteCompletion K q)
        (ScalarConjugate.csa c.symm A))) =
      finiteBrauerInvariant K (finitePlaceEquiv c q)
        (Brauer.classOf (Brauer.baseChange (FiniteCompletion K (finitePlaceEquiv c q)) A)) := by
  let L := FiniteCompletion K (finitePlaceEquiv c q)
  let M := FiniteCompletion K q
  let j : L ≃+* M := finiteCompletionEquiv c q
  let : Algebra L M := j.toRingHom.toAlgebra
  let : ValuativeRel L := FiniteCompletion.valuativeRel (finitePlaceEquiv c q)
  let : ValuativeRel M := FiniteCompletion.valuativeRel q
  let : IsNonarchimedeanLocalField L := FiniteCompletion.isNonarchimedeanLocalField _
  let : IsNonarchimedeanLocalField M := FiniteCompletion.isNonarchimedeanLocalField _
  let C := Brauer.baseChange L A
  let D := Brauer.baseChange M (ScalarConjugate.csa c.symm A)
  have he : Brauer.classOf (Brauer.baseChange M C) = Brauer.classOf D :=
    Brauer.classOf_eq_of_algEquiv (scalarConjugateCompletionEquiv c q A)
  have hv (a b : L) : j a ≤ᵥ j b ↔ a ≤ᵥ b := by
    rw [FiniteCompletion.valuativeRel_vle, FiniteCompletion.valuativeRel_vle,
      finiteCompletionEquiv_valuation, finiteCompletionEquiv_valuation]
  change localBrauerInvariant M (Brauer.classOf D) = localBrauerInvariant L (Brauer.classOf C)
  rw [← he, ← Brauer.scalarExtension_classOf]
  exact localBrauerInvariant_fieldEquiv L M j (continuous_finiteCompletionEquiv c q) hv _

/-- On a totally complex number field, the finite invariants determine a
global Brauer class. -/
theorem classOf_eq_of_finiteBrauerInvariants [IsTotallyComplex K]
    (A B : CSA.{u, u} K)
    (h : ∀ q : FinitePlace K, finiteBrauerInvariant K q
        (Brauer.classOf (Brauer.baseChange (FiniteCompletion K q) A)) =
        finiteBrauerInvariant K q
          (Brauer.classOf (Brauer.baseChange (FiniteCompletion K q) B))) :
    Brauer.classOf A = Brauer.classOf B := by
  have hs : Brauer.IsSplit (Brauer.tensor A (Brauer.opposite B)) := by
    apply Brauer.numberFieldBrauerSplitting
    · intro q
      let M := FiniteCompletion K q
      let I := (finiteBrauerInvariant K q).toAddMonoidHom.comp (Brauer.scalarExtension (K := K) M)
      have he : I (Brauer.classOf A) = I (Brauer.classOf B) := h q
      apply (Brauer.classOf_eq_zero_iff _).mp
      apply (finiteBrauerInvariant K q).injective
      change I (Brauer.classOf (Brauer.tensor A (Brauer.opposite B))) =
        finiteBrauerInvariant K q 0
      rw [Brauer.classOf_tensor, Brauer.classOf_opposite, map_add, map_neg, he,
        add_neg_cancel, map_zero]
    · intro w
      let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)
      let : IsAlgClosed w.Completion := ⟨fun f => Polynomial.Splits.of_splits_map
        e.toRingHom (IsAlgClosed.splits _) (fun x _ => e.surjective x)⟩
      exact Brauer.isSplit_of_isAlgClosed _
  have hz := (Brauer.classOf_eq_zero_iff _).mpr hs
  rw [Brauer.classOf_tensor, Brauer.classOf_opposite, ← sub_eq_add_neg] at hz
  exact sub_eq_zero.mp hz

end Langlands.Shimura.FiniteUnitary
