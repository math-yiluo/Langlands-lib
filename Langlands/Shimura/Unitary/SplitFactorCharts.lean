import Langlands.Shimura.Unitary.PlaceTensorDecomposition
import Langlands.Shimura.Unitary.SplitLocalPair
import Langlands.Algebra.BrauerSplitting

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
    simpa only [f, RingEquiv.trans_apply, RingEquiv.symm_apply_apply, AlgEquiv.coe_toRingEquiv]
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

namespace Langlands.Shimura.FiniteUnitary

open NumberField _root_.Algebra Langlands.Global Langlands.Global.AdelicFunctoriality
open scoped FiniteExtension

section Exchange

variable {R B₁ B₂ C : Type*} [CommRing R]
  [Ring B₁] [Algebra R B₁] [Ring B₂] [Algebra R B₂] [Ring C] [Algebra R C]
  (ρ : AlgebraInvolution R (B₁ × B₂)) (hρ : ρ (1, 0) = (0, 1))
  (τ : AlgebraInvolution R C) (f : B₁ ≃ₐ[R] C)

include hρ in
private theorem exchange_on_second : ρ (0, 1) = (1, 0) := by
  rw [← hρ, ρ.apply_apply]

include hρ in
private theorem exchange_fst (a : B₁) (b : B₂) :
    (ρ (a, b)).1 = (ρ (0, b)).1 := by
  simpa only [Prod.mk_mul_mk, mul_zero, mul_one, exchange_on_second ρ hρ,
    Prod.fst_mul, one_mul] using (congrArg Prod.fst (ρ.apply_mul (a, b) (0, 1))).symm

include hρ in
private theorem exchange_snd (a : B₁) (b : B₂) :
    (ρ (a, b)).2 = (ρ (a, 0)).2 := by
  simpa only [Prod.mk_mul_mk, mul_zero, mul_one, hρ, Prod.snd_mul, one_mul]
    using (congrArg Prod.snd (ρ.apply_mul (a, b) (1, 0))).symm

private def secondFactorChart : B₂ ≃ₐ[R] C where
  toFun b := τ (f (ρ (0, b)).1)
  invFun c := (ρ (f.symm (τ c), 0)).2
  left_inv b := by
    change (ρ (f.symm (τ (τ (f (ρ (0, b)).1))), 0)).2 = b
    rw [τ.apply_apply, f.symm_apply_apply, ← exchange_snd ρ hρ,
      Prod.mk.eta, ρ.apply_apply]
  right_inv c := by
    change τ (f (ρ (0, (ρ (f.symm (τ c), 0)).2)).1) = c
    rw [← exchange_fst ρ hρ, Prod.mk.eta, ρ.apply_apply, f.apply_symm_apply,
      τ.apply_apply]
  map_mul' b b' := by
    have h := congrArg Prod.fst (ρ.apply_mul (0, b) (0, b'))
    rw [Prod.mk_mul_mk, zero_mul, Prod.fst_mul] at h
    change τ (f (ρ (0, b * b')).1) = τ (f (ρ (0, b)).1) * τ (f (ρ (0, b')).1)
    rw [h, map_mul, τ.apply_mul]
  map_add' b b' := by
    have h := congrArg Prod.fst (ρ.apply_add (0, b) (0, b'))
    rw [Prod.mk_add_mk, zero_add, Prod.fst_add] at h
    change τ (f (ρ (0, b + b')).1) = τ (f (ρ (0, b)).1) + τ (f (ρ (0, b')).1)
    rw [h, map_add, τ.apply_add]
  commutes' r := by
    have hr := ρ.apply_smul r (0, 1)
    rw [exchange_on_second ρ hρ] at hr
    have hfst : (ρ (0, algebraMap R B₂ r)).1 = algebraMap R B₁ r := by
      have h₁ : r • ((0, 1) : B₁ × B₂) = (0, algebraMap R B₂ r) := by
        ext <;> simp [Algebra.smul_def]
      have h₂ : r • ((1, 0) : B₁ × B₂) = (algebraMap R B₁ r, 0) := by
        ext <;> simp [Algebra.smul_def]
      rw [h₁, h₂] at hr
      exact congrArg Prod.fst hr
    change τ (f (ρ (0, algebraMap R B₂ r)).1) = _
    rw [hfst, f.commutes, τ.apply_algebraMap]

include hρ in
private theorem secondFactorChart_apply (x : B₁ × B₂) :
    secondFactorChart ρ hρ τ f x.2 = τ (f (ρ x).1) := by
  rcases x with ⟨a, b⟩
  exact congrArg (fun z => τ (f z)) (exchange_fst ρ hρ a b).symm

private def scalarIdentity (R : Type*) [CommRing R] : AlgebraInvolution R R where
  linear := LinearMap.id
  map_one := rfl
  map_mul _ _ := mul_comm _ _
  involutive _ := rfl

end Exchange

namespace SplitPlaceIdentification

variable {E : Type u} {K : Type v}
  [Field E] [NumberField E] [IsTotallyReal E]
  [Field K] [NumberField K] [IsTotallyComplex K] [Algebra E K] [IsQuadraticExtension E K]
  {A : Type w} [Ring A] [Algebra E A] [Algebra K A] [IsScalarTower E K A]
  {p : Langlands.Global.FinitePlace E}
  (h : SplitPlaceIdentification E K p) (q : FinitePlacesAbove K p)

local notation "F" => FiniteCompletion E p
local notation "K₁" => FiniteCompletion K q.val
local notation "A₁" => CompletedAlgebra K A q.val
local notation "A₂" => CompletedAlgebra K A (Subtype.val (otherPlace h q))

private def completedProduct : LocalAlgebra E A p ≃ₐ[F] (A₁ × A₂) :=
  AlgEquiv.ofRingEquiv (f := h.splitCompletedAlgebraEquiv A q) fun t =>
    Prod.ext ((toCompletedAlgebra E K A p q.val).commutes t)
      ((toCompletedAlgebra E K A p (h.otherPlace q).val).commutes t)

private theorem completedProduct_center (z : LocalCenter E K p) :
    h.completedProduct q (localCenterMap E K A p z) =
      (algebraMap K₁ A₁ (completedCenterMap E K p q.val z),
        algebraMap (FiniteCompletion K (h.otherPlace q).val) A₂
          (completedCenterMap E K p (h.otherPlace q).val z)) :=
  Prod.ext (toCompletedAlgebra_center E K A p q.val z)
    (toCompletedAlgebra_center E K A p (h.otherPlace q).val z)

/-- Over a split finite place, a matrix chart at one of the two actual upper
places supplies the whole maximal-Witt chart for any second-kind involution. -/
def maxWittChartOfSplitCompletion (σ : SecondKindInvolution E K A) (n : ℕ)
    (e₁ : A₁ ≃ₐ[K₁] Matrix (Fin n) (Fin n) K₁) :
    {e : LocalAlgebra E A p ≃ₐ[F] Matrix (Fin n) (Fin n) (LocalCenter E K p) //
      (∀ z : LocalCenter E K p,
        e (localCenterMap E K A p z) = Matrix.scalar (Fin n) z) ∧
      ∀ x, e (localInvolution σ p x) = maxWittAdjoint (localConjugation E K p) n (e x)} := by
  classical
  let χ := (h.oriented q).equiv
  let P : LocalAlgebra E A p ≃ₐ[F] (A₁ × A₂) := h.completedProduct q
  let ρ := (localInvolution σ p).transport P
  let τ := maxWittAdjoint (scalarIdentity F) n
  let f := (e₁.restrictScalars F).trans (h.completionEquiv q).symm.mapMatrix
  have hχ (z : LocalCenter E K p) : χ (localConjugation E K p z) = (χ z).swap :=
    (h.oriented q).conjugation_eq z
  have haxis (z : LocalCenter E K p) (a b : F) (hz : χ z = (a, b)) :
      P (localCenterMap E K A p z) = (algebraMap F A₁ a, algebraMap F A₂ b) := by
    have hfst : completedCenterMap E K p q.val z = h.completionEquiv q a := by
      apply (h.completionEquiv q).symm.injective
      rw [← h.oriented_fst q z, AlgEquiv.symm_apply_apply]
      exact congrArg Prod.fst hz
    have hsnd : completedCenterMap E K p (h.otherPlace q).val z =
        h.completionEquiv (h.otherPlace q) b := by
      apply (h.completionEquiv (h.otherPlace q)).symm.injective
      rw [← h.oriented_snd q z, AlgEquiv.symm_apply_apply]
      exact congrArg Prod.snd hz
    rw [show P (localCenterMap E K A p z) = _ from h.completedProduct_center q z, hfst, hsnd]
    rfl
  have hcenter₁ (z : LocalCenter E K p) :
      f (P (localCenterMap E K A p z)).1 = Matrix.scalar (Fin n) (χ z).1 := by
    rw [haxis z (χ z).1 (χ z).2 rfl]
    exact f.commutes _
  have hρ : ρ (1, 0) = (0, 1) := by
    let z := χ.symm (1, 0)
    have hz : χ z = (1, 0) := χ.apply_symm_apply _
    have hz' : χ (localConjugation E K p z) = (0, 1) := by rw [hχ, hz]; rfl
    have hz₁ : P (localCenterMap E K A p z) = (1, 0) := by
      simpa only [map_one, map_zero] using haxis z 1 0 hz
    have hz₂ : P (localCenterMap E K A p (localConjugation E K p z)) = (0, 1) := by
      simpa only [map_one, map_zero] using haxis _ 0 1 hz'
    change ((localInvolution σ p).transport P) (1, 0) = (0, 1)
    rw [← hz₁, AlgebraInvolution.transport_equiv, localInvolution_center, hz₂]
  let g := χ.mapMatrix.trans (ComplexMatrix.prodAlgEquiv F F n F)
  let H := P.trans (AlgEquiv.prodCongr f (secondFactorChart ρ hρ τ f))
  have hH (x : LocalAlgebra E A p) :
      H x = (f (P x).1, τ (f (P (localInvolution σ p x)).1)) := by
    change (f (P x).1, secondFactorChart ρ hρ τ f (P x).2) = _
    rw [secondFactorChart_apply]
    change (f (P x).1, τ (f (((localInvolution σ p).transport P) (P x)).1)) = _
    rw [AlgebraInvolution.transport_equiv]
  have hGram : g (maxWittGram (LocalCenter E K p) n) =
      (maxWittGram F n, maxWittGram F n) := by
    refine Prod.ext (Matrix.ext fun i j => ?_) (Matrix.ext fun i j => ?_)
    · change (χ (maxWittGram (LocalCenter E K p) n i j)).1 = _
      by_cases hij : i.rev = j <;> simp [maxWittGram, hij]
    · change (χ (maxWittGram (LocalCenter E K p) n i j)).2 = _
      by_cases hij : i.rev = j <;> simp [maxWittGram, hij]
  have hTranspose (M : Matrix (Fin n) (Fin n) (LocalCenter E K p)) :
      g (matrixTranspose (localConjugation E K p) n M) =
        (matrixTranspose (scalarIdentity F) n (g M).2,
         matrixTranspose (scalarIdentity F) n (g M).1) := by
    refine Prod.ext (Matrix.ext fun i j => ?_) (Matrix.ext fun i j => ?_)
    · exact congrArg Prod.fst (hχ (M j i))
    · exact congrArg Prod.snd (hχ (M j i))
  have hAdj (M : Matrix (Fin n) (Fin n) (LocalCenter E K p)) :
      g (maxWittAdjoint (localConjugation E K p) n M) =
        (τ (g M).2, τ (g M).1) := by
    rw [maxWittAdjoint_formula, map_mul, map_mul, hGram, hTranspose]
    rfl
  refine ⟨H.trans g.symm, ?_, ?_⟩
  · intro z
    apply g.injective
    change g (g.symm (H (localCenterMap E K A p z))) = g (Matrix.scalar (Fin n) z)
    rw [g.apply_symm_apply, hH, localInvolution_center, hcenter₁,
      hcenter₁, hχ]
    have hscalar (c : F) : τ (Matrix.scalar (Fin n) c) = Matrix.scalar (Fin n) c :=
      τ.apply_algebraMap c
    rw [hscalar]
    apply Prod.ext <;> ext i j <;> by_cases hij : i = j <;>
      simp [g, Matrix.scalar_apply, hij, ComplexMatrix.prodAlgEquiv_apply]
  · intro x
    apply g.injective
    change g (g.symm (H (localInvolution σ p x))) =
      g (maxWittAdjoint (localConjugation E K p) n (g.symm (H x)))
    rw [g.apply_symm_apply, hAdj, g.apply_symm_apply, hH, hH,
      (localInvolution σ p).apply_apply, τ.apply_apply]

include h in
/-- A zero Brauer invariant at one upper place implies the maximal-Witt
chart at the split base place, with the original center action. -/
theorem isQuasiSplitAt_of_zeroCompletedBrauerInvariant
    {n : ℕ} (D : CentralSimpleUnitaryData E K A n)
    (hzero : HasCompletedBrauerInvariant K A q.val 0) :
    IsQuasiSplitAt D.toSecondKindInvolution n p := by
  obtain ⟨B, ⟨e⟩, hB⟩ := hzero
  have hz : Brauer.classOf B = 0 :=
    (finiteBrauerInvariant K q.val).injective (hB.trans (map_zero _).symm)
  obtain ⟨m, -, ⟨f⟩⟩ := (Brauer.classOf_eq_zero_iff B).mp hz
  let : FiniteDimensional K A := D.finite
  have hdim : m * m = n * n := by
    have h := (e.trans f).toLinearEquiv.finrank_eq
    rwa [Module.finrank_baseChange, D.dimension, Module.finrank_matrix, Fintype.card_fin,
      Module.finrank_self, mul_one, pow_two, eq_comm] at h
  have hm : m = n := by nlinarith
  subst m
  exact ⟨_, (h.maxWittChartOfSplitCompletion q D.toSecondKindInvolution n (e.trans f)).property⟩

end SplitPlaceIdentification

end Langlands.Shimura.FiniteUnitary
