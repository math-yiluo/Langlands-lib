import Langlands.Group.GL.Basic
import Langlands.Shimura.Unitary.HarrisInnerFormLevels
import Langlands.Shimura.Unitary.HarrisSplitPrimeFactorLevels
import Mathlib.Topology.Instances.Matrix

/-!
# Harris's groups split at the distinguished place

For Harris's unitary similitude groups `GJ` and `GG` (Harris 1999, §4) with `p` split in the
imaginary quadratic field, the finite adelic points split, as topological groups, into the
factor at the distinguished place `w₀ = v^(1)` above `p` and a complement:

`G(A_f) ≃ₜ* (K_{w₀} ⊗[K] A)ˣ × (((Π_{w ≠ w₀} (K_w ⊗[K] A)ˣ) × ℚ_pˣ) × G(A_f^p))`.

For `GJ`, a splitting `K_{w₀} ⊗[K] 𝒟 ≃ GL_n(K_{w₀})` turns the factor at `w₀` into
`GL_n(K_{w₀})`. Identifications of the local algebras at the places `w ≠ w₀` and of the
prime-to-`p` groups give an identification of the complements. See `HarrisAwaySplitting.md`.
-/

noncomputable section

open scoped TensorProduct NumberField
open NumberField IsDedekindDomain

set_option autoImplicit false

universe u v w z z' uM uN uP uM' uN' uι uY uY'

namespace Langlands.JacquetLanglands

open Langlands.Shimura Langlands.Global Langlands.Global.AdelicFunctoriality

section ContinuousMulEquiv

variable {M : Type uM} {N : Type uN} {P : Type uP} {M' : Type uM'} {N' : Type uN'}
  [Mul M] [Mul N] [Mul P] [Mul M'] [Mul N']
  [TopologicalSpace M] [TopologicalSpace N] [TopologicalSpace P] [TopologicalSpace M']
  [TopologicalSpace N']

/-- The product of two continuous multiplicative isomorphisms. -/
def continuousMulEquivProdCongr (e₁ : M ≃ₜ* M') (e₂ : N ≃ₜ* N') : M × N ≃ₜ* M' × N' :=
  ContinuousMulEquiv.mk' (e₁.toHomeomorph.prodCongr e₂.toHomeomorph)
    fun x y => Prod.ext (map_mul e₁ x.1 y.1) (map_mul e₂ x.2 y.2)

@[simp] theorem continuousMulEquivProdCongr_apply (e₁ : M ≃ₜ* M') (e₂ : N ≃ₜ* N')
    (x : M × N) : continuousMulEquivProdCongr e₁ e₂ x = (e₁ x.1, e₂ x.2) :=
  rfl

variable (M N P) in
/-- The associativity isomorphism `(M × N) × P ≃ₜ* M × (N × P)`. -/
def continuousMulEquivProdAssoc : (M × N) × P ≃ₜ* M × (N × P) :=
  ContinuousMulEquiv.mk' (Homeomorph.prodAssoc M N P) fun _ _ => rfl

@[simp] theorem continuousMulEquivProdAssoc_apply (x : (M × N) × P) :
    continuousMulEquivProdAssoc M N P x = (x.1.1, (x.1.2, x.2)) :=
  rfl

variable {ι : Type uι} {Y : ι → Type uY} {Y' : ι → Type uY'} [∀ i, Mul (Y i)]
  [∀ i, TopologicalSpace (Y i)] [∀ i, Mul (Y' i)] [∀ i, TopologicalSpace (Y' i)]

variable (Y) in
/-- Splitting a product at one index: `Π j, Y j ≃ₜ* Y i × Π_{j ≠ i} Y j`. -/
def continuousMulEquivPiSplitAt [DecidableEq ι] (i : ι) :
    (∀ j, Y j) ≃ₜ* Y i × ∀ j : {j // j ≠ i}, Y j :=
  ContinuousMulEquiv.mk' (Homeomorph.piSplitAt i Y) fun _ _ => rfl

@[simp] theorem continuousMulEquivPiSplitAt_apply [DecidableEq ι] (i : ι) (x : ∀ j, Y j) :
    continuousMulEquivPiSplitAt Y i x = (x i, fun j : {j // j ≠ i} => x j.1) :=
  rfl

/-- The product of a family of continuous multiplicative isomorphisms. -/
def continuousMulEquivPiCongrRight (e : ∀ i, Y i ≃ₜ* Y' i) : (∀ i, Y i) ≃ₜ* ∀ i, Y' i :=
  ContinuousMulEquiv.mk' (Homeomorph.piCongrRight fun i => (e i).toHomeomorph)
    fun x y => funext fun i => map_mul (e i) (x i) (y i)

@[simp] theorem continuousMulEquivPiCongrRight_apply (e : ∀ i, Y i ≃ₜ* Y' i) (x : ∀ i, Y i)
    (i : ι) : continuousMulEquivPiCongrRight e x i = e i (x i) :=
  rfl

end ContinuousMulEquiv

section FactorUnits

variable {K : Type v} [Field K] {A : Type z} {B : Type z'} [Ring A] [Ring B] [Algebra K A]
  [Algebra K B] {S : Type w} [CommRing S] [Algebra K S] [TopologicalSpace S] [IsTopologicalRing S]

/-- An isomorphism `S ⊗[K] A ≃ₐ[S] S ⊗[K] B` of `S`-algebras induces an isomorphism of the unit
groups with the units topologies of the `S`-module topologies. -/
def factorUnitsEquiv (f : S ⊗[K] A ≃ₐ[S] S ⊗[K] B) :
    ImaginaryQuadraticSplit.FactorUnits K A S ≃ₜ* ImaginaryQuadraticSplit.FactorUnits K B S where
  toMulEquiv := Units.mapEquiv f.toRingEquiv.toMulEquiv
  continuous_toFun := by
    let : TopologicalSpace (S ⊗[K] A) := moduleTopology S _
    let : TopologicalSpace (S ⊗[K] B) := moduleTopology S _
    have := ModuleTopology.continuousAdd S (S ⊗[K] B)
    have := ModuleTopology.continuousSMul S (S ⊗[K] B)
    exact (IsModuleTopology.continuous_of_linearMap f.toLinearMap).units_map
      f.toRingHom.toMonoidHom
  continuous_invFun := by
    let : TopologicalSpace (S ⊗[K] A) := moduleTopology S _
    let : TopologicalSpace (S ⊗[K] B) := moduleTopology S _
    have := ModuleTopology.continuousAdd S (S ⊗[K] A)
    have := ModuleTopology.continuousSMul S (S ⊗[K] A)
    exact (IsModuleTopology.continuous_of_linearMap f.symm.toLinearMap).units_map
      f.symm.toRingHom.toMonoidHom

omit [IsTopologicalRing S] in
@[simp] theorem factorUnitsEquiv_apply_val (f : S ⊗[K] A ≃ₐ[S] S ⊗[K] B)
    (x : ImaginaryQuadraticSplit.FactorUnits K A S) :
    Units.val (α := S ⊗[K] B) (factorUnitsEquiv f x) = f (Units.val (α := S ⊗[K] A) x) :=
  rfl

/-- A splitting `S ⊗[K] A ≃ₐ[S] M_n(S)` induces an isomorphism of `(S ⊗[K] A)ˣ`, with the units
topology of the `S`-module topology, onto `GL_n(S)` with its matrix topology. -/
def factorUnitsMatrixEquiv {n : ℕ} (s : S ⊗[K] A ≃ₐ[S] Matrix (Fin n) (Fin n) S) :
    ImaginaryQuadraticSplit.FactorUnits K A S ≃ₜ* GeneralLinear n S where
  toMulEquiv := Units.mapEquiv s.toRingEquiv.toMulEquiv
  continuous_toFun := by
    let : TopologicalSpace (S ⊗[K] A) := moduleTopology S _
    exact (IsModuleTopology.continuous_of_linearMap s.toLinearMap).units_map
      s.toRingHom.toMonoidHom
  continuous_invFun := by
    let : TopologicalSpace (S ⊗[K] A) := moduleTopology S _
    have := ModuleTopology.continuousAdd S (S ⊗[K] A)
    have := ModuleTopology.continuousSMul S (S ⊗[K] A)
    have : IsModuleTopology S (Matrix (Fin n) (Fin n) S) :=
      inferInstanceAs (IsModuleTopology S (Fin n → Fin n → S))
    exact (IsModuleTopology.continuous_of_linearMap s.symm.toLinearMap).units_map
      s.symm.toRingHom.toMonoidHom

@[simp] theorem factorUnitsMatrixEquiv_apply_val {n : ℕ}
    (s : S ⊗[K] A ≃ₐ[S] Matrix (Fin n) (Fin n) S) (x : ImaginaryQuadraticSplit.FactorUnits K A S) :
    ((factorUnitsMatrixEquiv s x : GeneralLinear n S) : Matrix (Fin n) (Fin n) S) =
      s (Units.val (α := S ⊗[K] A) x) :=
  rfl

end FactorUnits

section Harris

variable {E : Type u} {K : Type v}
variable [Field E] [NumberField E] [IsTotallyReal E]
variable [Field K] [NumberField K] [IsTotallyComplex K]
variable [Algebra E K] [Algebra.IsQuadraticExtension E K]
variable {F : Type w} [Field F] [NumberField F] [IsCMField F] [Algebra.IsQuadraticExtension ℚ F]
variable {A : Type z} [Ring A] [Algebra K A] [Algebra E A] [IsScalarTower E K A]
  [Algebra ℚ A] [IsScalarTower ℚ E A] [IsScalarTower ℚ K A] [Module.Finite ℚ A]

variable (σ : SecondKindInvolution E K A) (ι : F →+* K) (p : ℕ) (hp : p.Prime)
  (v : {v : Global.FinitePlace ℚ // (p : 𝓞 ℚ) ∈ v.asIdeal}) (𝔭 : FinitePlacesAbove F v.1)
  (h𝔭 : Function.Bijective (FiniteExtension.completionMap v.1 𝔭.1))
  (w₀ : letI := ι.toAlgebra; FinitePlacesAbove K 𝔭.1)

/-- The complement of the distinguished place `w₀` in Harris's group:
`(Π_{w ∣ 𝔭, w ≠ w₀} (K_w ⊗[K] A)ˣ × ℚ_vˣ) × G(A_f^p)`. -/
abbrev HarrisAwayComplement : Type _ :=
  ((∀ w : {w : (letI := ι.toAlgebra; FinitePlacesAbove K 𝔭.1) // w ≠ w₀},
      ImaginaryQuadraticSplit.FactorUnits K A (w.1.1.adicCompletion K)) ×
    (FiniteCompletion ℚ v.1)ˣ) × σ.rationalInvolution.PrimeToPoints p

/-- Harris's splitting of `G(ℚ_v)` at `w₀`: `G(ℚ_v) ≃ₜ* (K_{w₀} ⊗[K] A)ˣ ×
(Π_{w ≠ w₀} (K_w ⊗[K] A)ˣ × ℚ_vˣ)`, from the published decomposition (4.2) through
`splitPrimeHomeomorph` and `splitPlaceUnitsHomeomorph`. -/
def harrisLocalSplit :
    σ.rationalInvolution.Points (FiniteCompletion ℚ v.1) ≃ₜ*
      ImaginaryQuadraticSplit.FactorUnits K A (w₀.1.adicCompletion K) ×
        ((∀ w : {w : (letI := ι.toAlgebra; FinitePlacesAbove K 𝔭.1) // w ≠ w₀},
            ImaginaryQuadraticSplit.FactorUnits K A (w.1.1.adicCompletion K)) ×
          (FiniteCompletion ℚ v.1)ˣ) :=
  letI := ι.toAlgebra
  haveI := Classical.decEq (FinitePlacesAbove K 𝔭.1)
  ((σ.splitPrimeHomeomorph ι v.1 (splitPlaceEmbedding v.1 𝔭 h𝔭)).trans
    (continuousMulEquivProdCongr
      ((splitPlaceUnitsHomeomorph ι v.1 𝔭 h𝔭).trans
        (continuousMulEquivPiSplitAt
          (fun w : FinitePlacesAbove K 𝔭.1 =>
            ImaginaryQuadraticSplit.FactorUnits K A (w.1.adicCompletion K)) w₀))
      (ContinuousMulEquiv.refl _))).trans
    (continuousMulEquivProdAssoc _ _ _)

/-- Harris's splitting of the finite adelic points at the distinguished place `w₀`:
`G(A_f) ≃ₜ* (K_{w₀} ⊗[K] A)ˣ × HarrisAwayComplement`. -/
def harrisAwaySplit :
    σ.rationalInvolution.FiniteAdelicPoints ≃ₜ*
      ImaginaryQuadraticSplit.FactorUnits K A (w₀.1.adicCompletion K) ×
        HarrisAwayComplement σ ι p v 𝔭 w₀ :=
  ((σ.rationalInvolution.finiteAdelicPointsSplit p hp.ne_zero).trans
    (continuousMulEquivProdCongr
      ((σ.rationalInvolution.dividingPrimePointsEquiv p hp v).trans
        (harrisLocalSplit σ ι p v 𝔭 h𝔭 w₀))
      (ContinuousMulEquiv.refl _))).trans
    (continuousMulEquivProdAssoc _ _ _)

omit [IsScalarTower E K A] in
/-- The factor at `w₀` is the `w₀`-component of the local point at `v` in the published product
decomposition `splitPlacePoints`. -/
theorem harrisAwaySplit_apply_fst (g : σ.rationalInvolution.FiniteAdelicPoints) :
    (harrisAwaySplit σ ι p hp v 𝔭 h𝔭 w₀ g).1 =
      (σ.splitPlacePoints ι v.1 𝔭 h𝔭 (σ.rationalInvolution.finiteLocalMap v.1 g)).1 w₀ := by
  change (σ.splitPlacePoints ι v.1 𝔭 h𝔭 (σ.rationalInvolution.dividingLocalMap p v
    (σ.rationalInvolution.finiteAdelicPointsSplit p hp.ne_zero g).1)).1 w₀ = _
  rw [AlgebraInvolution.dividingLocalMap_finiteAdelicPointsSplit]

omit [IsScalarTower E K A] in
/-- The prime-to-`p` component of the complement is the published prime-to-`p` projection. -/
theorem harrisAwaySplit_apply_snd_snd (g : σ.rationalInvolution.FiniteAdelicPoints) :
    (harrisAwaySplit σ ι p hp v 𝔭 h𝔭 w₀ g).2.2 =
      (σ.rationalInvolution.finiteAdelicPointsSplit p hp.ne_zero g).2 :=
  rfl

/-- For `GJ`: a splitting `s : K_{w₀} ⊗[K] A ≃ₐ M_n(K_{w₀})` turns the factor at `w₀` into
`GL_n(K_{w₀})`. -/
def harrisAwaySplitGL {n : ℕ}
    (s : w₀.1.adicCompletion K ⊗[K] A ≃ₐ[w₀.1.adicCompletion K]
      Matrix (Fin n) (Fin n) (w₀.1.adicCompletion K)) :
    σ.rationalInvolution.FiniteAdelicPoints ≃ₜ*
      GeneralLinear n (w₀.1.adicCompletion K) × HarrisAwayComplement σ ι p v 𝔭 w₀ :=
  (harrisAwaySplit σ ι p hp v 𝔭 h𝔭 w₀).trans
    (continuousMulEquivProdCongr (factorUnitsMatrixEquiv s) (ContinuousMulEquiv.refl _))

omit [IsScalarTower E K A] in
theorem harrisAwaySplitGL_apply_fst {n : ℕ}
    (s : w₀.1.adicCompletion K ⊗[K] A ≃ₐ[w₀.1.adicCompletion K]
      Matrix (Fin n) (Fin n) (w₀.1.adicCompletion K))
    (g : σ.rationalInvolution.FiniteAdelicPoints) :
    ((harrisAwaySplitGL σ ι p hp v 𝔭 h𝔭 w₀ s g).1 :
        Matrix (Fin n) (Fin n) (w₀.1.adicCompletion K)) =
      s (Units.val (α := w₀.1.adicCompletion K ⊗[K] A)
        ((σ.splitPlacePoints ι v.1 𝔭 h𝔭 (σ.rationalInvolution.finiteLocalMap v.1 g)).1 w₀)) := by
  change s (Units.val (α := w₀.1.adicCompletion K ⊗[K] A)
    (harrisAwaySplit σ ι p hp v 𝔭 h𝔭 w₀ g).1) = _
  rw [harrisAwaySplit_apply_fst]

end Harris

section InnerForm

variable {E : Type u} {K : Type v}
variable [Field E] [NumberField E] [IsTotallyReal E]
variable [Field K] [NumberField K] [IsTotallyComplex K]
variable [Algebra E K] [Algebra.IsQuadraticExtension E K]
variable {F : Type w} [Field F] [NumberField F] [IsCMField F] [Algebra.IsQuadraticExtension ℚ F]
variable {B : Type z} [Ring B] [Algebra K B] [Algebra E B] [IsScalarTower E K B]
  [Algebra ℚ B] [IsScalarTower ℚ E B]
variable {D : Type z'} [Ring D] [Algebra K D] [Algebra E D] [IsScalarTower E K D]
  [Algebra ℚ D] [IsScalarTower ℚ E D]
variable (σB : SecondKindInvolution E K B) (σD : SecondKindInvolution E K D) (ι : F →+* K)
  (p : ℕ) (v : {v : Global.FinitePlace ℚ // (p : 𝓞 ℚ) ∈ v.asIdeal})
  (𝔭 : FinitePlacesAbove F v.1) (w₀ : letI := ι.toAlgebra; FinitePlacesAbove K 𝔭.1)

/-- Harris's identification of the complements of `w₀` for `GJ` (algebra `D`) and `GG`
(algebra `B`): local algebra isomorphisms `K_w ⊗[K] D ≃ K_w ⊗[K] B` at the places `w ≠ w₀`
above `𝔭`, the identity on `ℚ_vˣ`, and the identification `GJ(A_f^p) ≃ GG(A_f^p)` of
`innerFormPrimeToEquiv`. -/
def harrisComplementEquiv
    (f : ∀ w : {w : (letI := ι.toAlgebra; FinitePlacesAbove K 𝔭.1) // w ≠ w₀},
      w.1.1.adicCompletion K ⊗[K] D ≃ₐ[w.1.1.adicCompletion K] w.1.1.adicCompletion K ⊗[K] B)
    (e : PrimeToFiniteAdeles p ⊗[ℚ] D ≃ₐ[PrimeToFiniteAdeles p] PrimeToFiniteAdeles p ⊗[ℚ] B)
    (he : ∀ x, e (σD.rationalInvolution.baseChange _ x) =
      σB.rationalInvolution.baseChange _ (e x)) :
    HarrisAwayComplement σD ι p v 𝔭 w₀ ≃ₜ* HarrisAwayComplement σB ι p v 𝔭 w₀ :=
  continuousMulEquivProdCongr
    (continuousMulEquivProdCongr (continuousMulEquivPiCongrRight fun w => factorUnitsEquiv (f w))
      (ContinuousMulEquiv.refl _))
    (σB.innerFormPrimeToEquiv σD p e he)

end InnerForm

end Langlands.JacquetLanglands
