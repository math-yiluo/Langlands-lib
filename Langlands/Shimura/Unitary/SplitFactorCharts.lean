import Langlands.Shimura.Unitary.PlaceTensorDecomposition
import Langlands.Shimura.Unitary.SplitLocalPair

/-! # Extracting the actual completion charts from a split local pair -/

noncomputable section

universe u v w

namespace Langlands.Shimura.FiniteUnitary.SplitPlaceIdentification

open NumberField _root_.Algebra Langlands.Global Langlands.Global.AdelicFunctoriality
open Langlands.ClassFieldTheory.Local
open scoped FiniteExtension TensorProduct

private theorem map_firstFactor {A₁ A₂ B₁ B₂ : Type*}
    [Ring A₁] [Ring A₂] [Ring B₁] [Ring B₂]
    (e : (A₁ × A₂) ≃+* (B₁ × B₂)) (he : e (1, 0) = (1, 0)) (x : A₁ × A₂) :
    e (x.1, 0) = ((e x).1, 0) := by
  have hx : (x.1, 0) = x * (1, 0) := by ext <;> simp
  rw [hx, map_mul, he]
  ext <;> simp

private def firstFactorEquiv {A₁ A₂ B₁ B₂ : Type*} [Ring A₁] [Ring A₂] [Ring B₁] [Ring B₂]
    (e : (A₁ × A₂) ≃+* (B₁ × B₂)) (he : e (1, 0) = (1, 0)) : A₁ ≃+* B₁ where
  toFun a := (e (a, 0)).1
  invFun b := (e.symm (b, 0)).1
  left_inv a := by
    change (e.symm ((e (a, 0)).1, 0)).1 = a
    rw [← map_firstFactor e he (a, 0), RingEquiv.symm_apply_apply]
  right_inv b := by
    have he' : e.symm (1, 0) = (1, 0) := e.symm_apply_eq.mpr he.symm
    change (e ((e.symm (b, 0)).1, 0)).1 = b
    rw [← map_firstFactor e.symm he' (b, 0), RingEquiv.apply_symm_apply]
  map_mul' a b := by
    simpa only [Prod.mk_mul_mk, mul_zero, Prod.fst_mul] using
      congrArg Prod.fst (map_mul e (a, 0) (b, 0))
  map_add' a b := by
    simpa only [Prod.mk_add_mk, add_zero, Prod.fst_add] using
      congrArg Prod.fst (map_add e (a, 0) (b, 0))

private def firstFactorAlgEquiv (F : Type*) {A₁ A₂ B₁ B₂ : Type*}
    [CommRing F] [Ring A₁] [Ring A₂] [Ring B₁] [Ring B₂] [Algebra F A₁] [Algebra F B₁]
    (e : (A₁ × A₂) ≃+* (B₁ × B₂))
    (he : ∀ s : F, e (algebraMap F A₁ s, 0) = (algebraMap F B₁ s, 0)) : A₁ ≃ₐ[F] B₁ :=
  AlgEquiv.ofRingEquiv
    (f := firstFactorEquiv e (by simpa only [map_one] using he 1))
    (fun s => congrArg Prod.fst (he s))

variable {E : Type u} {K : Type v}
  [Field E] [NumberField E] [IsTotallyReal E]
  [Field K] [NumberField K] [IsTotallyComplex K] [Algebra E K] [IsQuadraticExtension E K]
  {p : Langlands.Global.FinitePlace E}

variable (A : Type w) [Ring A] [Algebra E A] [Algebra K A] [IsScalarTower E K A]

private theorem placeTensorEquiv_eq_toCompletedAlgebra
    (x : LocalAlgebra E A p) (r : FinitePlacesAbove K p) :
    PlaceTensor.placeTensorEquiv (K := K) p A x r = toCompletedAlgebra E K A p r.val x := by
  induction x using TensorProduct.inductionOn with
  | tmul s a => rw [PlaceTensor.placeTensorEquiv_tmul, toCompletedAlgebra_tmul]
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]

variable (h : SplitPlaceIdentification E K p) (q : FinitePlacesAbove K p)

private def splitCompletedAlgebraMap :
    LocalAlgebra E A p →+* (CompletedAlgebra K A q.val ×
      CompletedAlgebra K A (h.otherPlace q).val) :=
  (toCompletedAlgebra E K A p q.val).toRingHom.prod
    (toCompletedAlgebra E K A p (h.otherPlace q).val).toRingHom

private def splitCompletedAlgebraEquiv :
    LocalAlgebra E A p ≃+* (CompletedAlgebra K A q.val ×
      CompletedAlgebra K A (h.otherPlace q).val) :=
  RingEquiv.ofBijective (h.splitCompletedAlgebraMap A q) (by
    let e := PlaceTensor.placeTensorEquiv (K := K) p A
    constructor
    · intro x y hxy
      apply e.injective
      funext r
      change PlaceTensor.placeTensorEquiv (K := K) p A x r =
        PlaceTensor.placeTensorEquiv (K := K) p A y r
      rw [placeTensorEquiv_eq_toCompletedAlgebra, placeTensorEquiv_eq_toCompletedAlgebra]
      rcases h.eq_or_eq_otherPlace q r with rfl | rfl
      · exact congrArg Prod.fst hxy
      · exact congrArg Prod.snd hxy
    · rintro ⟨a, b⟩
      classical
      let g := Function.update (Function.update
        (fun r : FinitePlacesAbove K p => (0 : CompletedAlgebra K A r.val)) q a)
        (h.otherPlace q) b
      obtain ⟨x, hx⟩ := e.surjective g
      refine ⟨x, Prod.ext ?_ ?_⟩
      · change toCompletedAlgebra E K A p q.val x = a
        rw [← placeTensorEquiv_eq_toCompletedAlgebra A x q]
        simpa only [g, Function.update_of_ne (h.otherPlace_ne q).symm, Function.update_self] using
          congrFun hx q
      · change toCompletedAlgebra E K A p (h.otherPlace q).val x = b
        rw [← placeTensorEquiv_eq_toCompletedAlgebra A x (h.otherPlace q)]
        simpa only [g, Function.update_self] using congrFun hx (h.otherPlace q))

local notation "F" => FiniteCompletion E p
local notation "K₁" => FiniteCompletion K q.val
local notation "K₂" => FiniteCompletion K (Subtype.val (otherPlace h q))
local notation "A₁" => CompletedAlgebra K A q.val
local notation "A₂" => CompletedAlgebra K A (Subtype.val (otherPlace h q))

variable (B : CSA.{v, v} (FiniteCompletion K q.val))

/-- A center-preserving chart against the split pair induces algebra equivalences at
both actual completions, in the prescribed order. -/
def completedAlgebraEquivsOfSplitPair
    (e : LocalAlgebra E A p ≃ₐ[F] (B × h.otherFactor q B))
    (he : ∀ z, e (localCenterMap E K A p z) = h.splitPairCenterMap q B z) :
    (A₁ ≃ₐ[K₁] B) × (A₂ ≃ₐ[K₂] h.otherFactor q B) := by
  let f := (h.splitCompletedAlgebraEquiv A q).symm.trans e.toRingEquiv
  have hcenter (z : LocalCenter E K p) :
      f (algebraMap K₁ A₁ (completedCenterMap E K p q.val z),
        algebraMap K₂ A₂ (completedCenterMap E K p (h.otherPlace q).val z)) =
        h.splitPairCenterMap q B z := by
    have hz : h.splitCompletedAlgebraEquiv A q (localCenterMap E K A p z) =
        (algebraMap K₁ A₁ (completedCenterMap E K p q.val z),
          algebraMap K₂ A₂ (completedCenterMap E K p (h.otherPlace q).val z)) :=
      Prod.ext (toCompletedAlgebra_center E K A p q.val z)
        (toCompletedAlgebra_center E K A p (h.otherPlace q).val z)
    rw [← hz]
    simpa only [f, RingEquiv.trans_apply, RingEquiv.symm_apply_apply, AlgEquiv.coe_ringEquiv]
      using he z
  have hscalar (s : K₁) (t : K₂) :
      f (algebraMap K₁ A₁ s, algebraMap K₂ A₂ t) =
        (algebraMap K₁ B s, algebraMap K₂ (h.otherFactor q B) t) := by
    obtain ⟨z, hz⟩ := (h.oriented q).equiv.surjective
      ((h.completionEquiv q).symm s, (h.completionEquiv (h.otherPlace q)).symm t)
    have hs : completedCenterMap E K p q.val z = s := by
      apply (h.completionEquiv q).symm.injective
      simpa only [oriented_fst] using congrArg Prod.fst hz
    have ht : completedCenterMap E K p (h.otherPlace q).val z = t := by
      apply (h.completionEquiv (h.otherPlace q)).symm.injective
      simpa only [oriented_snd] using congrArg Prod.snd hz
    rw [← hs, ← ht, hcenter]
    rfl
  refine ⟨firstFactorAlgEquiv K₁ f ?_, ?_⟩
  · intro s
    simpa only [map_zero] using hscalar s 0
  · let swapSource : (A₂ × A₁) ≃+* (A₁ × A₂) := RingEquiv.prodComm
    let swapTarget : (B × h.otherFactor q B) ≃+* (h.otherFactor q B × B) := RingEquiv.prodComm
    refine firstFactorAlgEquiv K₂ (swapSource.trans (f.trans swapTarget)) ?_
    intro t
    simpa [swapSource, swapTarget] using congrArg Prod.swap (hscalar 0 t)

open Classical in
/-- With a prescribed split residue, the transported charts certify the signed invariant
at every actual place above the split finite place. -/
theorem hasCompletedBrauerInvariant_of_splitPair {n : ℕ} (hn : 0 < n) (a : ZMod n)
    (e : LocalAlgebra E A p ≃ₐ[F] (invariantFactor q hn (denominatorEquiv n hn a) ×
      h.otherFactor q (invariantFactor q hn (denominatorEquiv n hn a))))
    (he : ∀ z, e (localCenterMap E K A p z) =
      h.splitPairCenterMap q (invariantFactor q hn (denominatorEquiv n hn a)) z)
    (r : FinitePlacesAbove K p) : HasCompletedBrauerInvariant K A r.val
      (denominatorEquiv n hn (if r = q then a else -a)) := by
  let B := invariantFactor q hn (denominatorEquiv n hn a)
  let charts := h.completedAlgebraEquivsOfSplitPair A q B e he
  rcases h.eq_or_eq_otherPlace q r with hr | hr <;> subst r
  · rw [ite_eq_left rfl]
    exact ⟨B, ⟨charts.1⟩, finiteBrauerInvariant_invariantFactor q hn _⟩
  · rw [ite_eq_right (h.otherPlace_ne q), map_neg, AddSubgroup.coe_neg]
    exact ⟨h.otherFactor q B, ⟨charts.2⟩, by
      rw [finiteBrauerInvariant_otherFactor, finiteBrauerInvariant_invariantFactor]⟩

end Langlands.Shimura.FiniteUnitary.SplitPlaceIdentification
