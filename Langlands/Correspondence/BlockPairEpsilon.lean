import Langlands.Correspondence.ArithmeticEpsilonDirectSum

/-!
# Arithmetic epsilon factors of pairs of special blocks

The epsilon value of a pair of uncentered special blocks `ρ ⊗ S_(n+1)`,
`ρ' ⊗ S_(m+1)` is the double product of the epsilon values of the twisted
factors `ν^(i+j) (ρ ⊗ ρ')`, times the quotient correction of the block tensor,
which is a constant times a power of `q_E^(-s)`. Under the published block-pair
gamma law (Henniart 2.4) the quotient correction times the L-ratio of the block
tensor is the product of the L-ratios of the twisted factors.
-/

noncomputable section

universe uK uG uH uV uW uF uP

namespace Langlands.WeilDeligneRepresentation

open scoped DirectSum TensorProduct

variable {K : Type uK} {G : Type uG} [Field K] [Group G]

/-- The Weil action on an uncentered block `A ⊗ S_m` is the direct sum of the
twists `ν^i A`, `i < m`. Monodromy is not preserved. -/
def blockRepresentationEquiv (ν : G →* Kˣ) (A : FiniteRepresentation.{uK, uG, uV} K G)
    (m : ℕ) :
    (block ν A m).representation.Equiv
      (directSum fun i : Fin m =>
        zeroMonodromy ν (FiniteRepresentation.twist (ν ^ (i : ℕ)) A)).representation :=
  Representation.Equiv.mk
    (TensorProduct.piScalarRight K K A (Fin m) ≪≫ₗ
      (DirectSum.linearEquivFunOnFintype K (Fin m) fun _ => A).symm)
    (fun g => TensorProduct.ext' fun (a : (A : Type uV)) (v : Fin m → K) => by
      apply (DirectSum.linearEquivFunOnFintype K (Fin m) fun _ => (A : Type uV)).injective
      funext j
      change (DirectSum.linearEquivFunOnFintype K (Fin m) fun _ => (A : Type uV))
          ((DirectSum.linearEquivFunOnFintype K (Fin m) fun _ => (A : Type uV)).symm
            (TensorProduct.piScalarRight K K A (Fin m)
              (A.representation g a ⊗ₜ[K] Special.action ν m g v))) j =
        (ν ^ (j : ℕ)) g • A.representation g
          ((DirectSum.linearEquivFunOnFintype K (Fin m) fun _ => (A : Type uV))
            ((DirectSum.linearEquivFunOnFintype K (Fin m) fun _ => (A : Type uV)).symm
              (TensorProduct.piScalarRight K K A (Fin m) (a ⊗ₜ[K] v))) j)
      simp only [LinearEquiv.apply_symm_apply, TensorProduct.piScalarRight_apply,
        TensorProduct.piScalarRightHom_tmul]
      change ((ν g : K) ^ (j : ℕ) * v j) • A.representation g a =
        (((ν ^ (j : ℕ)) g : Kˣ) : K) • A.representation g (v j • a)
      rw [(A.representation g).map_smul (v j) a, MonoidHom.pow_apply, Units.val_pow_eq_pow_val,
        smul_smul])

/-- A pair whose monodromy vanishes is equivalent to the zero-monodromy pair on
any equivalent representation. -/
def zeroMonodromyEquivOfEquiv (ν : G →* Kˣ) {A : WeilDeligneRepresentation.{uK, uG, uV} K G ν}
    {B : WeilDeligneRepresentation.{uK, uG, uW} K G ν} (hA : A.monodromy = 0)
    (hB : B.monodromy = 0) (f : A.representation.Equiv B.representation) : Equiv A B where
  representationEquiv := f
  comm_monodromy := by rw [hA, hB, LinearMap.comp_zero, LinearMap.zero_comp]

theorem directSum_zeroMonodromy_monodromy {ι : Type} [Fintype ι] (ν : G →* Kˣ)
    (A : ι → FiniteRepresentation.{uK, uG, uV} K G) :
    (directSum fun i => zeroMonodromy ν (A i)).monodromy = 0 := by
  change DirectSum.lmap (fun i => (0 : Module.End K (A i))) = 0
  exact lmap_zero

theorem tensor_monodromy_eq_zero {ν : G →* Kˣ} {A : WeilDeligneRepresentation.{uK, uG, uV} K G ν}
    {B : WeilDeligneRepresentation.{uK, uG, uW} K G ν} (hA : A.monodromy = 0)
    (hB : B.monodromy = 0) : (tensor A B).monodromy = 0 := by
  change TensorProduct.map A.monodromy 1 + TensorProduct.map 1 B.monodromy = 0
  rw [hA, hB, TensorProduct.map_zero_left, TensorProduct.map_zero_right]
  exact add_zero 0

end Langlands.WeilDeligneRepresentation

namespace Langlands.FiniteRepresentation

variable {K : Type uK} {G : Type uG} [Field K] [Group G]

/-- The tensor product of two twists is the twist of the tensor product by the
product character; the underlying linear map is the identity. -/
def tensorTwistEquiv (χ η : G →* Kˣ) (A : FiniteRepresentation.{uK, uG, uV} K G)
    (B : FiniteRepresentation.{uK, uG, uW} K G) :
    Equiv (tensor (twist χ A) (twist η B)) (twist (χ * η) (tensor A B)) :=
  Representation.Equiv.mk (LinearEquiv.refl K _)
    (fun g => TensorProduct.ext' fun (a : (A : Type uV)) (b : (B : Type uW)) => by
      change ((χ g : K) • A.representation g a) ⊗ₜ[K] ((η g : K) • B.representation g b) =
        (((χ * η) g : Kˣ) : K) • (A.representation g a ⊗ₜ[K] B.representation g b)
      rw [TensorProduct.tmul_smul, ← TensorProduct.smul_tmul', smul_smul, MonoidHom.mul_apply,
        Units.val_mul, mul_comm])

/-- Twists by equal characters are equivalent through the identity map. -/
def twistEquivOfEq {χ η : G →* Kˣ} (h : χ = η) (A : FiniteRepresentation.{uK, uG, uV} K G) :
    Equiv (twist χ A) (twist η A) := by
  subst h
  exact Representation.Equiv.refl _

end Langlands.FiniteRepresentation

namespace Langlands.LocalFactor.CommonClosureGamma

open CommonClosure CommonClosureSpectral CommonClosureWeilDeligne PairBlock

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- The twisted factor is the zero-monodromy pair of the twist by the power of
the norm character taken in the monoid of homomorphisms. -/
theorem twistedFactor_eq_zeroMonodromy (E : Extension F)
    (ρ : FiniteRepresentation.{0, uF, max uF uP} ℂ (weilSubgroup F E)) (k : ℕ) :
    twistedFactor.{uF, uP} F E ρ k =
      WeilDeligneRepresentation.zeroMonodromy (normCharacter F E).toMonoidHom
        (FiniteRepresentation.twist ((normCharacter F E).toMonoidHom ^ k) ρ) := by
  rw [twistedFactor]
  congr 2
  ext g
  simp

/-- The zero-monodromy pair on the Weil action of a block is the direct sum of
its twisted factors. -/
def blockZeroMonodromyEquiv (E : Extension F)
    (ρ : FiniteRepresentation.{0, uF, max uF uP} ℂ (weilSubgroup F E)) (n : ℕ) :
    WeilDeligneRepresentation.Equiv
      (WeilDeligneRepresentation.zeroMonodromy (normCharacter F E).toMonoidHom
        (WeilDeligneRepresentation.block (normCharacter F E).toMonoidHom ρ n).toFiniteRepresentation)
      (WeilDeligneRepresentation.directSum fun i : Fin n => twistedFactor.{uF, uP} F E ρ i) :=
  (WeilDeligneRepresentation.zeroMonodromyEquivOfEquiv (normCharacter F E).toMonoidHom
    (A := WeilDeligneRepresentation.zeroMonodromy (normCharacter F E).toMonoidHom
      (WeilDeligneRepresentation.block (normCharacter F E).toMonoidHom ρ n).toFiniteRepresentation)
    (B := WeilDeligneRepresentation.directSum fun i : Fin n =>
      WeilDeligneRepresentation.zeroMonodromy (normCharacter F E).toMonoidHom
        (FiniteRepresentation.twist ((normCharacter F E).toMonoidHom ^ (i : ℕ)) ρ)) rfl
    (WeilDeligneRepresentation.directSum_zeroMonodromy_monodromy
      (normCharacter F E).toMonoidHom _)
    (WeilDeligneRepresentation.blockRepresentationEquiv (normCharacter F E).toMonoidHom ρ n)).trans
    (by
      rw [show (fun i : Fin n => twistedFactor.{uF, uP} F E ρ i) = _ from
        funext fun i => twistedFactor_eq_zeroMonodromy F E ρ i]
      exact WeilDeligneRepresentation.Equiv.refl _)

/-- Pair epsilon of two blocks is the double product of the pair epsilon values of
their twisted factors, times the quotient correction of the block tensor. -/
theorem conditionalPairEpsilonValue_block (e : ReciprocityFamily F)
    (ε : NonabelianSystem.Assignment.{uF, uP} F) (hε : NonabelianSystem.IsSystem F e ε)
    (E : Extension F) (ψ : AdditiveCharacter F E) (μ : HaarMeasure F E)
    (ρ ρ' : FiniteRepresentation.{0, uF, max uF uP} ℂ (weilSubgroup F E))
    (hρ : ρ.IsContinuous) (hρ' : ρ'.IsContinuous) (n m : ℕ) (Φ : GeometricFrobenius F E)
    (s : ℂ) :
    conditionalPairEpsilonValue F e ε hε E ψ μ
        (WeilDeligneRepresentation.block (normCharacter F E).toMonoidHom ρ (n + 1))
        (WeilDeligneRepresentation.block (normCharacter F E).toMonoidHom ρ' (m + 1))
        (block_isContinuous F E ρ hρ (n + 1)) (block_isContinuous F E ρ' hρ' (m + 1)) Φ s =
      (∏ i : Fin (n + 1), ∏ j : Fin (m + 1),
        conditionalPairEpsilonValue F e ε hε E ψ μ (twistedFactor F E ρ i)
          (twistedFactor F E ρ' j) (twistedFactor_isContinuous F E ρ hρ i)
          (twistedFactor_isContinuous F E ρ' hρ' j) Φ s) *
        quotientValue F E (WeilDeligneRepresentation.tensor
          (WeilDeligneRepresentation.block (normCharacter F E).toMonoidHom ρ (n + 1))
          (WeilDeligneRepresentation.block (normCharacter F E).toMonoidHom ρ' (m + 1))) Φ s := by
  set ν := (normCharacter F E).toMonoidHom
  set X := WeilDeligneRepresentation.block ν ρ (n + 1)
  set Y := WeilDeligneRepresentation.block ν ρ' (m + 1)
  have hX : X.toFiniteRepresentation.IsContinuous := block_isContinuous F E ρ hρ (n + 1)
  have hY : Y.toFiniteRepresentation.IsContinuous := block_isContinuous F E ρ' hρ' (m + 1)
  have hX0 : (WeilDeligneRepresentation.zeroMonodromy ν
      X.toFiniteRepresentation).toFiniteRepresentation.IsContinuous := hX
  have hY0 : (WeilDeligneRepresentation.zeroMonodromy ν
      Y.toFiniteRepresentation).toFiniteRepresentation.IsContinuous := hY
  have hDeligne : conditionalDeligneValue F e ε hε E ψ μ
      (underlyingClass F E (WeilDeligneRepresentation.tensor X Y)
        (tensor_isContinuous F E X Y hX hY)) s =
      conditionalPairEpsilonValue F e ε hε E ψ μ
        (WeilDeligneRepresentation.zeroMonodromy ν X.toFiniteRepresentation)
        (WeilDeligneRepresentation.zeroMonodromy ν Y.toFiniteRepresentation) hX0 hY0 Φ s :=
    (conditionalEpsilonValue_of_monodromy_zero F e ε hε E ψ μ _ _
      (WeilDeligneRepresentation.tensor_monodromy_eq_zero
        (A := WeilDeligneRepresentation.zeroMonodromy ν X.toFiniteRepresentation)
        (B := WeilDeligneRepresentation.zeroMonodromy ν Y.toFiniteRepresentation) rfl rfl)
      Φ s).symm
  rw [conditionalPairEpsilonValue, conditionalEpsilonValue, hDeligne,
    conditionalPairEpsilonValue_eq_of_equiv F e ε hε E ψ μ hX0
      (directSum_isContinuous F E _ fun i => twistedFactor_isContinuous F E ρ hρ i) hY0
      (directSum_isContinuous F E _ fun j => twistedFactor_isContinuous F E ρ' hρ' j)
      (blockZeroMonodromyEquiv F E ρ (n + 1)) (blockZeroMonodromyEquiv F E ρ' (m + 1)) Φ s,
    conditionalPairEpsilonValue_directSum F e ε hε E ψ μ _ _
      (fun i => twistedFactor_isContinuous F E ρ hρ i)
      (fun j => twistedFactor_isContinuous F E ρ' hρ' j)]

/-- The quotient correction is a monomial in the spectral variable: the constant
`det(-Q)` times `q_E^(-ds)`, with `d` the conductor correction. -/
theorem quotientValue_eq_monomial (E : Extension F) (A : Pair.{uF, uP} F E)
    (Φ : GeometricFrobenius F E) (s : ℂ) :
    quotientValue F E A Φ s =
      WeilDeligne.quotientConstantCorrection A (inertia F E) Φ.val *
        spectralParameter (residueCardinality F E) (residueCardinality_pos F E) s ^
          WeilDeligne.conductorCorrection A (inertia F E) :=
  rfl

/-- The tensor of two twisted factors is the twisted factor of the tensor, with
the exponents added. -/
def twistedPairEquiv (E : Extension F)
    (ρ ρ' : FiniteRepresentation.{0, uF, max uF uP} ℂ (weilSubgroup F E)) (i j : ℕ) :
    WeilDeligneRepresentation.Equiv
      (WeilDeligneRepresentation.tensor (twistedFactor.{uF, uP} F E ρ i)
        (twistedFactor.{uF, uP} F E ρ' j))
      (twistedFactor.{uF, uP} F E (FiniteRepresentation.tensor ρ ρ') (i + j)) := by
  set ν := (normCharacter F E).toMonoidHom
  have h : ν ^ i * ν ^ j = ν ^ (i + j) := (pow_add ν i j).symm
  have e1 : FiniteRepresentation.Equiv
      (FiniteRepresentation.tensor (FiniteRepresentation.twist (ν ^ i) ρ)
        (FiniteRepresentation.twist (ν ^ j) ρ'))
      (FiniteRepresentation.twist (ν ^ (i + j)) (FiniteRepresentation.tensor ρ ρ')) :=
    (FiniteRepresentation.tensorTwistEquiv _ _ ρ ρ').trans
      (FiniteRepresentation.twistEquivOfEq h _)
  rw [twistedFactor_eq_zeroMonodromy, twistedFactor_eq_zeroMonodromy,
    twistedFactor_eq_zeroMonodromy]
  exact WeilDeligneRepresentation.zeroMonodromyEquivOfEquiv ν
    (WeilDeligneRepresentation.tensor_monodromy_eq_zero
      (A := WeilDeligneRepresentation.zeroMonodromy ν (FiniteRepresentation.twist (ν ^ i) ρ))
      (B := WeilDeligneRepresentation.zeroMonodromy ν (FiniteRepresentation.twist (ν ^ j) ρ'))
      rfl rfl) rfl e1

/-- Pair epsilon of two twisted factors is epsilon of the twisted factor of the
tensor, with the exponents added. -/
theorem conditionalPairEpsilonValue_twistedFactor (e : ReciprocityFamily F)
    (ε : NonabelianSystem.Assignment.{uF, uP} F) (hε : NonabelianSystem.IsSystem F e ε)
    (E : Extension F) (ψ : AdditiveCharacter F E) (μ : HaarMeasure F E)
    (ρ ρ' : FiniteRepresentation.{0, uF, max uF uP} ℂ (weilSubgroup F E))
    (hρ : ρ.IsContinuous) (hρ' : ρ'.IsContinuous) (i j : ℕ) (Φ : GeometricFrobenius F E)
    (s : ℂ) :
    conditionalPairEpsilonValue F e ε hε E ψ μ (twistedFactor F E ρ i) (twistedFactor F E ρ' j)
        (twistedFactor_isContinuous F E ρ hρ i) (twistedFactor_isContinuous F E ρ' hρ' j) Φ s =
      conditionalEpsilonValue F e ε hε E ψ μ
        (twistedFactor F E (FiniteRepresentation.tensor ρ ρ') (i + j))
        (twistedFactor_isContinuous F E _ (FiniteRepresentation.isContinuous_tensor hρ hρ')
          (i + j)) Φ s :=
  conditionalEpsilonValue_eq_of_equiv F e ε hε E ψ μ _ _ (twistedPairEquiv F E ρ ρ' i j) Φ s

/-- Henniart 2.4 at the level of L-ratios: at a point regular for the block tensor
and for every twisted factor `ν^(i+j) (ρ ⊗ ρ')`, the block-pair gamma law gives
`quot_T(s) · LR_T(s) = ∏_i ∏_j LR_(i+j)(s)`, where `T` is the tensor of the two
blocks. The epsilon values cancel. -/
theorem quotientValue_mul_lRatioValue_block (hBPG : PairBlock.BlockPairGamma.{uF, uP} F)
    (e : ReciprocityFamily F)
    (ε : NonabelianSystem.Assignment.{uF, uP} F) (hε : NonabelianSystem.IsSystem F e ε)
    (E : Extension F) (ψ : AdditiveCharacter F E) (μ : HaarMeasure F E)
    (ρ ρ' : FiniteRepresentation.{0, uF, max uF uP} ℂ (weilSubgroup F E))
    (hρ : ρ.IsContinuous) (hρ' : ρ'.IsContinuous) (n m : ℕ) (Φ : GeometricFrobenius F E)
    (s : RegularPoint F E
      (WeilDeligneRepresentation.tensor
        (WeilDeligneRepresentation.block (normCharacter F E).toMonoidHom ρ (n + 1))
        (WeilDeligneRepresentation.block (normCharacter F E).toMonoidHom ρ' (m + 1))) Φ)
    (t : (i : Fin (n + 1)) → (j : Fin (m + 1)) → RegularPoint F E
      (twistedFactor F E (FiniteRepresentation.tensor ρ ρ') (i.val + j.val)) Φ)
    (ht : ∀ i j, (t i j).val = s.val) :
    quotientValue F E
        (WeilDeligneRepresentation.tensor
          (WeilDeligneRepresentation.block (normCharacter F E).toMonoidHom ρ (n + 1))
          (WeilDeligneRepresentation.block (normCharacter F E).toMonoidHom ρ' (m + 1))) Φ s.val *
        lRatioValue F E _ Φ s =
      ∏ i : Fin (n + 1), ∏ j : Fin (m + 1),
        lRatioValue F E (twistedFactor F E (FiniteRepresentation.tensor ρ ρ') (i.val + j.val))
          Φ (t i j) := by
  have h := hBPG e ε hε E ψ μ ρ ρ' hρ hρ' n m Φ s t ht
  rw [conditionalPairGammaValue_eq,
    conditionalPairEpsilonValue_block F e ε hε E ψ μ ρ ρ' hρ hρ' n m Φ] at h
  simp only [conditionalGammaValue, ht, ← conditionalPairEpsilonValue_twistedFactor F e ε hε E ψ μ
    ρ ρ' hρ hρ', Finset.prod_mul_distrib] at h
  rw [mul_assoc] at h
  exact mul_left_cancel h

end Langlands.LocalFactor.CommonClosureGamma
