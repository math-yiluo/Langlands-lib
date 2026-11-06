import Langlands.Correspondence.ArithmeticFactors
import Langlands.LocalFactor.PairBlockStatement
import Langlands.Representation.RankinSelberg.LanglandsFactors
import Langlands.WeilDeligne.DirectSum
import Langlands.Weil.Representation.SubquotientContinuity
import Langlands.LocalField.Normalization.Proof

/-!
# Arithmetic pair epsilon factors of direct sums

For every supplied common-closure local-constant system, the conditional epsilon
value is multiplicative on binary sums of continuous pairs (Henniart 2002 §2.1,
proving the published `PairBlock.EpsilonDirectSum`), the conditional pair epsilon
value distributes over sums in either tensor leg (the epsilon part of §2.2), and
hence the arithmetic pair epsilon factor `IsArithmeticPairEpsilonFactor` of
`A ⊗ A'` is the product monomial of the factors of `B_i ⊗ B'_j` whenever
`A ≅ ⊕_i B_i` and `A' ≅ ⊕_j B'_j` are nonempty finite direct sums. Nothing is
assumed beyond the system axioms.
-/

noncomputable section

universe uK uG uH uV uW uι uF uP

namespace Langlands.LocalFactor.WeilDeligne

open WeilDeligneRepresentation

section Sum

variable {K : Type uK} {G : Type uG} [Field K] [Group G] {ν : G →* Kˣ}
  (I : Subgroup G) [I.Normal]
  (A : WeilDeligneRepresentation.{uK, uG, uV} K G ν)
  (B : WeilDeligneRepresentation.{uK, uG, uW} K G ν)

/-- First projection of a binary sum of pairs. -/
def sumFst : Hom (WeilDeligneRepresentation.sum A B) A :=
  ⟨Representation.IntertwiningMap.fst K A.representation B.representation,
    LinearMap.ext fun _ => rfl⟩

/-- Second projection of a binary sum of pairs. -/
def sumSnd : Hom (WeilDeligneRepresentation.sum A B) B :=
  ⟨Representation.IntertwiningMap.snd K A.representation B.representation,
    LinearMap.ext fun _ => rfl⟩

/-- First inclusion into a binary sum of pairs. -/
def sumInl : Hom A (WeilDeligneRepresentation.sum A B) :=
  ⟨Representation.IntertwiningMap.inl K A.representation B.representation,
    LinearMap.ext fun _ => Prod.ext rfl (map_zero B.monodromy).symm⟩

/-- Second inclusion into a binary sum of pairs. -/
def sumInr : Hom B (WeilDeligneRepresentation.sum A B) :=
  ⟨Representation.IntertwiningMap.inr K A.representation B.representation,
    LinearMap.ext fun _ => Prod.ext (map_zero A.monodromy).symm rfl⟩

/-- The invariant quotient `V^I / (ker N)^I` of a binary sum is the sum of the
invariant quotients. -/
def quotientSumEquiv :
    FiniteRepresentation.Equiv (quotientRepresentation (WeilDeligneRepresentation.sum A B) I)
      (FiniteRepresentation.sum (quotientRepresentation A I) (quotientRepresentation B I)) where
  toLinearEquiv := {
    ((quotientMap I (sumFst A B)).prod (quotientMap I (sumSnd A B))).toLinearMap with
    invFun := (quotientMap I (sumInl A B)).toLinearMap.coprod
      (quotientMap I (sumInr A B)).toLinearMap
    left_inv := fun x => by
      obtain ⟨x, rfl⟩ := (kernelInInvariants (WeilDeligneRepresentation.sum A B) I).mkQ_surjective x
      change (kernelInInvariants _ I).mkQ _ + (kernelInInvariants _ I).mkQ _ =
        (kernelInInvariants _ I).mkQ x
      rw [← map_add]
      apply congrArg
      apply Subtype.ext
      exact Prod.ext (add_zero _) (zero_add _)
    right_inv := fun x => by
      obtain ⟨a, b⟩ := x
      obtain ⟨a, rfl⟩ := (kernelInInvariants A I).mkQ_surjective a
      obtain ⟨b, rfl⟩ := (kernelInInvariants B I).mkQ_surjective b
      refine Prod.ext ?_ ?_
      · change quotientMap I (sumFst A B)
            (quotientMap I (sumInl A B) ((kernelInInvariants A I).mkQ a) +
              quotientMap I (sumInr A B) ((kernelInInvariants B I).mkQ b)) =
          (kernelInInvariants A I).mkQ a
        rw [map_add, quotientMap_mk, quotientMap_mk, quotientMap_mk, quotientMap_mk]
        exact (map_add (kernelInInvariants A I).mkQ _ _).symm.trans
          (congrArg (kernelInInvariants A I).mkQ (Subtype.ext (add_zero _)))
      · change quotientMap I (sumSnd A B)
            (quotientMap I (sumInl A B) ((kernelInInvariants A I).mkQ a) +
              quotientMap I (sumInr A B) ((kernelInInvariants B I).mkQ b)) =
          (kernelInInvariants B I).mkQ b
        rw [map_add, quotientMap_mk, quotientMap_mk, quotientMap_mk, quotientMap_mk]
        exact (map_add (kernelInInvariants B I).mkQ _ _).symm.trans
          (congrArg (kernelInInvariants B I).mkQ (Subtype.ext (zero_add _))) }
  isIntertwining' := ((quotientMap I (sumFst A B)).prod (quotientMap I (sumSnd A B))).isIntertwining'

theorem conductorCorrection_sum :
    conductorCorrection (WeilDeligneRepresentation.sum A B) I =
      conductorCorrection A I + conductorCorrection B I := by
  unfold conductorCorrection
  rw [FiniteRepresentation.rank_eq_of_equiv (quotientSumEquiv I A B)]
  exact Module.finrank_prod

/-- The determinant of `-(f × g)` is the product of the determinants of `-f`, `-g`. -/
private theorem det_neg_prodMap {M : Type uV} {N : Type uW} [AddCommGroup M] [Module K M]
    [FiniteDimensional K M] [AddCommGroup N] [Module K N] [FiniteDimensional K N]
    (f : Module.End K M) (g : Module.End K N) :
    LinearMap.det (-(LinearMap.prodMap f g)) = LinearMap.det (-f) * LinearMap.det (-g) := by
  have h : -(LinearMap.prodMap f g) = LinearMap.prodMap (-f) (-g) :=
    LinearMap.ext fun _ => rfl
  rw [h, LinearMap.det_prodMap]

theorem quotientDeterminant_sum (g : G) :
    quotientDeterminant (WeilDeligneRepresentation.sum A B) I g =
      quotientDeterminant A I g * quotientDeterminant B I g := by
  have hc := Representation.Equiv.conj_apply_self g (quotientSumEquiv I A B)
  have hd := LinearMap.det_conj (-quotientOperator (WeilDeligneRepresentation.sum A B) I g)
    (quotientSumEquiv I A B).toLinearEquiv
  change LinearMap.det ((quotientSumEquiv I A B).toLinearEquiv.conj
    (-quotientOperator _ I g)) = quotientDeterminant _ I g at hd
  rw [map_neg, hc] at hd
  rw [← hd]
  exact det_neg_prodMap ((quotientRepresentation A I).representation g)
    ((quotientRepresentation B I).representation g)

theorem quotientCorrectionValue_sum (g : G) (z : Kˣ) :
    quotientCorrectionValue (WeilDeligneRepresentation.sum A B) I g z =
      quotientCorrectionValue A I g z * quotientCorrectionValue B I g z := by
  apply Units.ext
  simp only [quotientCorrectionValue, quotientConstantCorrection, Units.val_mul,
    Units.val_pow_eq_pow_val, Units.val_mk0, quotientDeterminant_sum, conductorCorrection_sum,
    pow_add]
  ring

end Sum

end Langlands.LocalFactor.WeilDeligne

namespace Langlands.LocalFactor.CommonClosureWeilDeligne

open CommonClosure CommonClosureSpectral VirtualRepresentation

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- The underlying exact class of a binary sum is the sum of the classes, by the
split exact sequence `0 → A → A ⊕ B → B → 0`. -/
theorem underlyingClass_sum (E : Extension F) (A B : Pair.{uF, uV} F E)
    (hA : A.toFiniteRepresentation.IsContinuous) (hB : B.toFiniteRepresentation.IsContinuous) :
    underlyingClass F E (WeilDeligneRepresentation.sum A B)
        (PairBlock.sum_isContinuous F E A B hA hB) =
      underlyingClass F E A hA + underlyingClass F E B hB :=
  ExactGrothendieckGroup.ofRepresentation_shortExact (ContinuousPredicate F E)
    (f := Representation.IntertwiningMap.inl ℂ A.representation B.representation)
    (g := Representation.IntertwiningMap.snd ℂ A.representation B.representation)
    ⟨fun _ _ h => congrArg Prod.fst h, fun b => ⟨(0, b), rfl⟩, LinearMap.range_inl ℂ _ _⟩

/-- Deligne's spectral value of a supplied system is multiplicative on sums of
exact virtual classes. -/
theorem conditionalDeligneValue_add (e : ReciprocityFamily F)
    (ε : NonabelianSystem.Assignment.{uF, uV} F) (hε : NonabelianSystem.IsSystem F e ε)
    (E : Extension F) (ψ : AdditiveCharacter F E) (μ : HaarMeasure F E)
    (x y : Virtual.{uF, uV} F E) (s : ℂ) :
    conditionalDeligneValue F e ε hε E ψ μ (x + y) s =
      conditionalDeligneValue F e ε hε E ψ μ x s *
        conditionalDeligneValue F e ε hε E ψ μ y s := by
  simp only [conditionalDeligneValue, map_add]
  exact hε.2.1 _ _ _ _ _

/-- The quotient correction is multiplicative on binary sums. -/
theorem quotientValue_sum (E : Extension F) (A B : Pair.{uF, uV} F E)
    (Φ : GeometricFrobenius F E) (s : ℂ) :
    quotientValue F E (WeilDeligneRepresentation.sum A B) Φ s =
      quotientValue F E A Φ s * quotientValue F E B Φ s :=
  WeilDeligne.quotientCorrectionValue_sum _ A B _ _

/-- The full conditional epsilon value of a supplied system is multiplicative on
binary sums of continuous pairs. -/
theorem conditionalEpsilonValue_sum (e : ReciprocityFamily F)
    (ε : NonabelianSystem.Assignment.{uF, uV} F) (hε : NonabelianSystem.IsSystem F e ε)
    (E : Extension F) (ψ : AdditiveCharacter F E) (μ : HaarMeasure F E)
    (A B : Pair.{uF, uV} F E)
    (hA : A.toFiniteRepresentation.IsContinuous) (hB : B.toFiniteRepresentation.IsContinuous)
    (Φ : GeometricFrobenius F E) (s : ℂ) :
    conditionalEpsilonValue F e ε hε E ψ μ (WeilDeligneRepresentation.sum A B)
        (PairBlock.sum_isContinuous F E A B hA hB) Φ s =
      conditionalEpsilonValue F e ε hε E ψ μ A hA Φ s *
        conditionalEpsilonValue F e ε hε E ψ μ B hB Φ s := by
  unfold conditionalEpsilonValue
  rw [underlyingClass_sum F E A B hA hB, conditionalDeligneValue_add, quotientValue_sum]
  exact mul_mul_mul_comm _ _ _ _

end Langlands.LocalFactor.CommonClosureWeilDeligne

/-- Henniart 2.1, epsilon part, is a theorem for every supplied system. -/
theorem Langlands.LocalFactor.PairBlock.epsilonDirectSum {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) : Langlands.LocalFactor.PairBlock.EpsilonDirectSum.{uF, uV} F :=
  fun _ _ _ _ _ _ A B hA hB _ _ =>
    Langlands.LocalFactor.CommonClosureWeilDeligne.conditionalEpsilonValue_sum F _ _ _ _ _ _ A B
      hA hB _ _

namespace Langlands.WeilDeligneRepresentation

section Distributivity

open scoped DirectSum TensorProduct

variable {K : Type uK} {G : Type uG} [Field K] [Group G] {ν : G →* Kˣ}

/-- Splitting off the first summand of a direct sum over `Fin (n + 1)`. -/
def directSumSuccLinearEquiv {n : ℕ} (V : Fin (n + 1) → Type uV) [∀ i, AddCommGroup (V i)]
    [∀ i, Module K (V i)] : (⨁ i, V i) ≃ₗ[K] V 0 × ⨁ i : Fin n, V i.succ :=
  DirectSum.linearEquivFunOnFintype K _ V ≪≫ₗ (Fin.consLinearEquiv K V).symm ≪≫ₗ
    (LinearEquiv.refl K (V 0)).prodCongr (DirectSum.linearEquivFunOnFintype K _ _).symm

theorem directSumSuccLinearEquiv_comp_lmap {n : ℕ} (V : Fin (n + 1) → Type uV)
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)] (f : ∀ i, Module.End K (V i)) :
    (directSumSuccLinearEquiv V).toLinearMap ∘ₗ DirectSum.lmap f =
      LinearMap.prodMap (f 0) (DirectSum.lmap fun i : Fin n => f i.succ) ∘ₗ
        (directSumSuccLinearEquiv V).toLinearMap :=
  LinearMap.ext fun _ => Prod.ext rfl (DFinsupp.ext fun _ => rfl)

/-- A direct sum over `Fin 1` is its only summand. -/
def directSumOneLinearEquiv (V : Fin 1 → Type uV) [∀ i, AddCommGroup (V i)]
    [∀ i, Module K (V i)] : (⨁ i, V i) ≃ₗ[K] V 0 :=
  DirectSum.linearEquivFunOnFintype K _ V ≪≫ₗ LinearEquiv.piUnique K V

theorem directSumOneLinearEquiv_comp_lmap (V : Fin 1 → Type uV)
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)] (f : ∀ i, Module.End K (V i)) :
    (directSumOneLinearEquiv V).toLinearMap ∘ₗ DirectSum.lmap f =
      f 0 ∘ₗ (directSumOneLinearEquiv V).toLinearMap :=
  LinearMap.ext fun _ => rfl

/-- `⊕_{i < n+1} A_i ≅ A_0 ⊕ ⊕_{i < n} A_(i+1)`. -/
def directSumSuccEquiv {n : ℕ} (b : Fin (n + 1) → WeilDeligneRepresentation.{uK, uG, uV} K G ν) :
    Equiv (directSum b) (sum (b 0) (directSum fun i : Fin n => b i.succ)) where
  representationEquiv :=
    { toLinearEquiv := directSumSuccLinearEquiv fun i => b i
      isIntertwining' := fun g =>
        directSumSuccLinearEquiv_comp_lmap (fun i => b i) fun i => (b i).representation g }
  comm_monodromy := directSumSuccLinearEquiv_comp_lmap (fun i => b i) fun i => (b i).monodromy

/-- `⊕_{i < 1} A_i ≅ A_0`. -/
def directSumOneEquiv (b : Fin 1 → WeilDeligneRepresentation.{uK, uG, uV} K G ν) :
    Equiv (directSum b) (b 0) where
  representationEquiv :=
    { toLinearEquiv := directSumOneLinearEquiv fun i => b i
      isIntertwining' := fun g =>
        directSumOneLinearEquiv_comp_lmap (fun i => b i) fun i => (b i).representation g }
  comm_monodromy := directSumOneLinearEquiv_comp_lmap (fun i => b i) fun i => (b i).monodromy

/-- `(A ⊕ A') ⊗ B ≅ (A ⊗ B) ⊕ (A' ⊗ B)`. -/
def tensorSumLeftEquiv (A A' : WeilDeligneRepresentation.{uK, uG, uV} K G ν)
    (B : WeilDeligneRepresentation.{uK, uG, uW} K G ν) :
    Equiv (tensor (sum A A') B) (sum (tensor A B) (tensor A' B)) where
  representationEquiv :=
    { toLinearEquiv := TensorProduct.prodLeft K K A A' B
      isIntertwining' := fun _ => TensorProduct.ext' fun _ _ => rfl }
  comm_monodromy := TensorProduct.ext' fun x y => by
    obtain ⟨a, a'⟩ := x
    change TensorProduct.prodLeft K K A A' B
        (((A.monodromy a, A'.monodromy a') ⊗ₜ y) + ((a, a') ⊗ₜ B.monodromy y)) =
      (A.monodromy a ⊗ₜ y + a ⊗ₜ B.monodromy y, A'.monodromy a' ⊗ₜ y + a' ⊗ₜ B.monodromy y)
    rw [map_add]
    rfl

/-- `B ⊗ (A ⊕ A') ≅ (B ⊗ A) ⊕ (B ⊗ A')`. -/
def tensorSumRightEquiv (B : WeilDeligneRepresentation.{uK, uG, uW} K G ν)
    (A A' : WeilDeligneRepresentation.{uK, uG, uV} K G ν) :
    Equiv (tensor B (sum A A')) (sum (tensor B A) (tensor B A')) where
  representationEquiv :=
    { toLinearEquiv := TensorProduct.prodRight K K B A A'
      isIntertwining' := fun _ => TensorProduct.ext' fun _ _ => rfl }
  comm_monodromy := TensorProduct.ext' fun y x => by
    obtain ⟨a, a'⟩ := x
    change TensorProduct.prodRight K K B A A'
        ((B.monodromy y ⊗ₜ (a, a')) + (y ⊗ₜ (A.monodromy a, A'.monodromy a'))) =
      (B.monodromy y ⊗ₜ a + y ⊗ₜ A.monodromy a, B.monodromy y ⊗ₜ a' + y ⊗ₜ A'.monodromy a')
    rw [map_add]
    rfl

end Distributivity

end Langlands.WeilDeligneRepresentation

namespace Langlands.WeilDeligneRepresentation

section Heterogeneous

open scoped DirectSum

variable {K : Type uK} {G : Type uG} {H : Type uH} [Field K] [Group G] [Group H] {ν : G →* Kˣ}
  {ι : Type uι} [Fintype ι]

/-- Restriction along a group homomorphism commutes with finite direct sums. -/
def restrictDirectSumEquiv (φ : H →* G) (A : ι → WeilDeligneRepresentation.{uK, uG, uV} K G ν) :
    Equiv (restrict φ (directSum A)) (directSum fun i => restrict φ (A i)) where
  representationEquiv :=
    { toLinearEquiv := LinearEquiv.refl K _
      isIntertwining' := fun _ => rfl }
  comm_monodromy := rfl

end Heterogeneous

end Langlands.WeilDeligneRepresentation

namespace Langlands.LocalFactor.CommonClosureGamma

open CommonClosure CommonClosureWeilDeligne

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- A direct sum of continuous pairs over `Fin (n + 1)` is continuous. -/
theorem directSum_isContinuous (E : Extension F) {n : ℕ} (b : Fin (n + 1) → Pair.{uF, uV} F E)
    (hb : ∀ i, (b i).toFiniteRepresentation.IsContinuous) :
    (WeilDeligneRepresentation.directSum b).toFiniteRepresentation.IsContinuous := by
  induction n with
  | zero =>
    exact (FiniteRepresentation.isContinuous_iff_of_equiv
      (WeilDeligneRepresentation.directSumOneEquiv b).representationEquiv).2 (hb 0)
  | succ n ih =>
    exact (FiniteRepresentation.isContinuous_iff_of_equiv
      (WeilDeligneRepresentation.directSumSuccEquiv b).representationEquiv).2
      (PairBlock.sum_isContinuous F E _ _ (hb 0) (ih _ fun i => hb i.succ))

/-- A unit-valued invariant of continuous pairs that is invariant under pair
equivalence and multiplicative on binary sums is multiplicative on direct sums
over `Fin (n + 1)`. -/
theorem prod_of_directSum (E : Extension F)
    (P : ∀ X : Pair.{uF, uV} F E, X.toFiniteRepresentation.IsContinuous → ℂˣ)
    (hequiv : ∀ {X Y : Pair.{uF, uV} F E} (hX : X.toFiniteRepresentation.IsContinuous)
      (hY : Y.toFiniteRepresentation.IsContinuous), WeilDeligneRepresentation.Equiv X Y →
      P X hX = P Y hY)
    (hsum : ∀ (X Y : Pair.{uF, uV} F E) (hX : X.toFiniteRepresentation.IsContinuous)
      (hY : Y.toFiniteRepresentation.IsContinuous),
      P (WeilDeligneRepresentation.sum X Y) (PairBlock.sum_isContinuous F E X Y hX hY) =
        P X hX * P Y hY)
    {n : ℕ} (b : Fin (n + 1) → Pair.{uF, uV} F E)
    (hb : ∀ i, (b i).toFiniteRepresentation.IsContinuous)
    (h : (WeilDeligneRepresentation.directSum b).toFiniteRepresentation.IsContinuous) :
    P (WeilDeligneRepresentation.directSum b) h = ∏ i, P (b i) (hb i) := by
  induction n with
  | zero =>
    rw [Fin.prod_univ_one]
    exact hequiv h (hb 0) (WeilDeligneRepresentation.directSumOneEquiv b)
  | succ n ih =>
    have hc := directSum_isContinuous F E (fun i : Fin (n + 1) => b i.succ) fun i => hb i.succ
    calc P (WeilDeligneRepresentation.directSum b) h
        = P (WeilDeligneRepresentation.sum (b 0)
            (WeilDeligneRepresentation.directSum fun i : Fin (n + 1) => b i.succ))
            (PairBlock.sum_isContinuous F E _ _ (hb 0) hc) :=
          hequiv _ _ (WeilDeligneRepresentation.directSumSuccEquiv b)
      _ = P (b 0) (hb 0) *
            P (WeilDeligneRepresentation.directSum fun i : Fin (n + 1) => b i.succ) hc :=
          hsum _ _ _ _
      _ = P (b 0) (hb 0) * ∏ i : Fin (n + 1), P (b i.succ) (hb i.succ) := by
          rw [ih _ (fun i => hb i.succ) hc]
      _ = ∏ i, P (b i) (hb i) := (Fin.prod_univ_succ fun i => P (b i) (hb i)).symm

/-- Henniart 2.2, epsilon part, first leg: pair epsilon of `(A ⊕ A') ⊗ B` is the
product of the pair epsilon values of `A ⊗ B` and `A' ⊗ B`. -/
theorem conditionalPairEpsilonValue_sum_left (e : ReciprocityFamily F)
    (ε : NonabelianSystem.Assignment.{uF, uV} F) (hε : NonabelianSystem.IsSystem F e ε)
    (E : Extension F) (ψ : AdditiveCharacter F E) (μ : HaarMeasure F E)
    (A A' B : Pair.{uF, uV} F E)
    (hA : A.toFiniteRepresentation.IsContinuous) (hA' : A'.toFiniteRepresentation.IsContinuous)
    (hB : B.toFiniteRepresentation.IsContinuous) (Φ : GeometricFrobenius F E) (s : ℂ) :
    conditionalPairEpsilonValue F e ε hε E ψ μ (WeilDeligneRepresentation.sum A A') B
        (PairBlock.sum_isContinuous F E A A' hA hA') hB Φ s =
      conditionalPairEpsilonValue F e ε hε E ψ μ A B hA hB Φ s *
        conditionalPairEpsilonValue F e ε hε E ψ μ A' B hA' hB Φ s := by
  unfold conditionalPairEpsilonValue
  rw [conditionalEpsilonValue_eq_of_equiv F e ε hε E ψ μ _
    (PairBlock.sum_isContinuous F E _ _ (tensor_isContinuous F E A B hA hB)
      (tensor_isContinuous F E A' B hA' hB))
    (WeilDeligneRepresentation.tensorSumLeftEquiv A A' B) Φ s]
  exact conditionalEpsilonValue_sum F e ε hε E ψ μ _ _ _ _ Φ s

/-- Henniart 2.2, epsilon part, second leg: pair epsilon of `B ⊗ (A ⊕ A')` is the
product of the pair epsilon values of `B ⊗ A` and `B ⊗ A'`. -/
theorem conditionalPairEpsilonValue_sum_right (e : ReciprocityFamily F)
    (ε : NonabelianSystem.Assignment.{uF, uV} F) (hε : NonabelianSystem.IsSystem F e ε)
    (E : Extension F) (ψ : AdditiveCharacter F E) (μ : HaarMeasure F E)
    (A A' B : Pair.{uF, uV} F E)
    (hA : A.toFiniteRepresentation.IsContinuous) (hA' : A'.toFiniteRepresentation.IsContinuous)
    (hB : B.toFiniteRepresentation.IsContinuous) (Φ : GeometricFrobenius F E) (s : ℂ) :
    conditionalPairEpsilonValue F e ε hε E ψ μ B (WeilDeligneRepresentation.sum A A')
        hB (PairBlock.sum_isContinuous F E A A' hA hA') Φ s =
      conditionalPairEpsilonValue F e ε hε E ψ μ B A hB hA Φ s *
        conditionalPairEpsilonValue F e ε hε E ψ μ B A' hB hA' Φ s := by
  unfold conditionalPairEpsilonValue
  rw [conditionalEpsilonValue_eq_of_equiv F e ε hε E ψ μ _
    (PairBlock.sum_isContinuous F E _ _ (tensor_isContinuous F E B A hB hA)
      (tensor_isContinuous F E B A' hB hA'))
    (WeilDeligneRepresentation.tensorSumRightEquiv B A A') Φ s]
  exact conditionalEpsilonValue_sum F e ε hε E ψ μ _ _ _ _ Φ s

/-- Pair epsilon of two finite direct sums is the double product of the pair
epsilon values of the summands. -/
theorem conditionalPairEpsilonValue_directSum (e : ReciprocityFamily F)
    (ε : NonabelianSystem.Assignment.{uF, uV} F) (hε : NonabelianSystem.IsSystem F e ε)
    (E : Extension F) (ψ : AdditiveCharacter F E) (μ : HaarMeasure F E) {n m : ℕ}
    (a : Fin (n + 1) → Pair.{uF, uV} F E) (b : Fin (m + 1) → Pair.{uF, uV} F E)
    (ha : ∀ i, (a i).toFiniteRepresentation.IsContinuous)
    (hb : ∀ j, (b j).toFiniteRepresentation.IsContinuous)
    (hA : (WeilDeligneRepresentation.directSum a).toFiniteRepresentation.IsContinuous)
    (hB : (WeilDeligneRepresentation.directSum b).toFiniteRepresentation.IsContinuous)
    (Φ : GeometricFrobenius F E) (s : ℂ) :
    conditionalPairEpsilonValue F e ε hε E ψ μ (WeilDeligneRepresentation.directSum a)
        (WeilDeligneRepresentation.directSum b) hA hB Φ s =
      ∏ i, ∏ j, conditionalPairEpsilonValue F e ε hε E ψ μ (a i) (b j) (ha i) (hb j) Φ s := by
  refine (prod_of_directSum F E
    (fun X hX => conditionalPairEpsilonValue F e ε hε E ψ μ X _ hX hB Φ s)
    (fun hX hX' f => conditionalPairEpsilonValue_eq_of_equiv F e ε hε E ψ μ hX hX' hB hB f
      (WeilDeligneRepresentation.Equiv.refl _) Φ s)
    (fun X X' hX hX' => conditionalPairEpsilonValue_sum_left F e ε hε E ψ μ X X' _ hX hX' hB Φ s)
    a ha hA).trans (Finset.prod_congr rfl fun i _ => ?_)
  exact prod_of_directSum F E
    (fun Y hY => conditionalPairEpsilonValue F e ε hε E ψ μ (a i) Y (ha i) hY Φ s)
    (fun hY hY' g => conditionalPairEpsilonValue_eq_of_equiv F e ε hε E ψ μ (ha i) (ha i) hY hY'
      (WeilDeligneRepresentation.Equiv.refl _) g Φ s)
    (fun Y Y' hY hY' => conditionalPairEpsilonValue_sum_right F e ε hε E ψ μ Y Y' _ hY hY' (ha i)
      Φ s)
    b hb hB

end Langlands.LocalFactor.CommonClosureGamma

namespace Langlands.Correspondence

open Weil.Local LocalFactor LocalFactor.CommonClosure LocalFactor.CommonClosureWeilDeligne

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance arithmeticEpsilonDirectSumFieldTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology

/-- A bottom-field restriction datum of a class is equivalent to the restriction
of every representative of the class. -/
theorem IsBaseRestriction.nonempty_equiv {X : LocalPairClass.{uF, uP} F}
    {A : LocalWeilDeligneRepresentation.{uF, uP} F} (hA : WeilDeligneRepresentation.classOf A = X)
    {P : Pair.{uF, uV} F (baseExtension F)} (h : IsBaseRestriction F X P) :
    Nonempty (WeilDeligneRepresentation.Equiv
      (WeilDeligneRepresentation.restrict (weilSubgroup F (baseExtension F)).subtype A) P) := by
  obtain ⟨B, hB, ⟨f⟩⟩ := h
  obtain ⟨g⟩ := (WeilDeligneRepresentation.classOf_eq_iff A B).1 (hA.trans hB.symm)
  exact ⟨(WeilDeligneRepresentation.restrictEquiv _ g).trans f⟩

/-- If `A ≅ ⊕_i B_i` and each `P_i` is a bottom-field restriction datum of the
class of `B_i`, then the restriction of `A` to the bottom field is equivalent to
`⊕_i P_i`. -/
theorem restrict_equiv_directSum {ι : Type} [Fintype ι]
    (B : ι → LocalWeilDeligneRepresentation.{uF, uP} F)
    (A : LocalWeilDeligneRepresentation.{uF, uP} F)
    (fA : WeilDeligneRepresentation.Equiv (WeilDeligneRepresentation.directSum B) A)
    (P : ι → Pair.{uF, uV} F (baseExtension F))
    (hP : ∀ i, IsBaseRestriction F (WeilDeligneRepresentation.classOf (B i)) (P i)) :
    Nonempty (WeilDeligneRepresentation.Equiv
      (WeilDeligneRepresentation.restrict (weilSubgroup F (baseExtension F)).subtype A)
      (WeilDeligneRepresentation.directSum P)) :=
  ⟨(WeilDeligneRepresentation.restrictEquiv _ fA.symm).trans
    ((WeilDeligneRepresentation.restrictDirectSumEquiv _ B).trans
      (WeilDeligneRepresentation.directSumCongr fun i =>
        Classical.choice (IsBaseRestriction.nonempty_equiv F rfl (hP i))))⟩

/-- Henniart 2.2, epsilon part, on the correspondence domains: arithmetic pair
epsilon factors for a supplied system are multiplicative on nonempty finite direct
sums. If `A ≅ ⊕_i B_i`, `A' ≅ ⊕_j B'_j` with `r, t > 0` summands and `e_ij` is the
arithmetic epsilon factor of `B_i ⊗ B'_j`, then the product monomial of the
`e_ij` is the arithmetic epsilon factor of `A ⊗ A'`. -/
theorem isArithmeticPairEpsilonFactor_directSum (eC : ReciprocityFamily F)
    (ε : NonabelianSystem.Assignment.{uF, uP} F) (hε : NonabelianSystem.IsSystem F eC ε)
    (ψ : NontrivialAdditiveCharacter F) {r t : ℕ} (hr : 0 < r) (ht : 0 < t)
    (B : Fin r → LocalWeilDeligneRepresentation.{uF, uP} F)
    (B' : Fin t → LocalWeilDeligneRepresentation.{uF, uP} F)
    (A A' : LocalWeilDeligneRepresentation.{uF, uP} F) (e : Fin r → Fin t → ℂˣ × ℤ)
    (hA : Nonempty (WeilDeligneRepresentation.Equiv (WeilDeligneRepresentation.directSum B) A))
    (hA' : Nonempty (WeilDeligneRepresentation.Equiv (WeilDeligneRepresentation.directSum B') A'))
    (he : ∀ i j, IsArithmeticPairEpsilonFactor F eC ε hε ψ
      (WeilDeligneRepresentation.classOf (B i)) (WeilDeligneRepresentation.classOf (B' j))
      (e i j).1 (e i j).2) :
    IsArithmeticPairEpsilonFactor F eC ε hε ψ (WeilDeligneRepresentation.classOf A)
      (WeilDeligneRepresentation.classOf A')
      (RankinSelberg.epsilonFactorProduct e).1 (RankinSelberg.epsilonFactorProduct e).2 := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hr.ne'
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero ht.ne'
  obtain ⟨fA⟩ := hA
  obtain ⟨fA'⟩ := hA'
  have hL : ∀ i, ∃ P : Pair.{uF, uP} F (baseExtension F),
      IsBaseRestriction F (WeilDeligneRepresentation.classOf (B i)) P ∧
        P.toFiniteRepresentation.IsContinuous := fun i => by
    obtain ⟨⟨_, _, P, _, ⟨_, _, hP, _⟩, hPc, _⟩, _⟩ := he i 0
    exact ⟨P, hP, hPc⟩
  have hR : ∀ j, ∃ P : Pair.{uF, uP} F (baseExtension F),
      IsBaseRestriction F (WeilDeligneRepresentation.classOf (B' j)) P ∧
        P.toFiniteRepresentation.IsContinuous := fun j => by
    obtain ⟨⟨_, _, _, P, ⟨_, _, _, hP⟩, _, hPc⟩, _⟩ := he 0 j
    exact ⟨P, hP, hPc⟩
  choose a ha hac using hL
  choose a' ha' hac' using hR
  obtain ⟨g⟩ := restrict_equiv_directSum F B A fA a ha
  obtain ⟨g'⟩ := restrict_equiv_directSum F B' A' fA' a' ha'
  have hc := CommonClosureGamma.directSum_isContinuous F _ a hac
  have hc' := CommonClosureGamma.directSum_isContinuous F _ a' hac'
  obtain ⟨⟨ψ', μ, -, -, ⟨hψ', hμ, -, -⟩, -, -⟩, hΦ, -⟩ := he 0 0
  refine ⟨⟨ψ', μ, _, _, ⟨hψ', hμ, ⟨A, rfl, ⟨g⟩⟩, ⟨A', rfl, ⟨g'⟩⟩⟩, hc, hc'⟩, hΦ, ?_⟩
  rintro ψ'' μ'' X Y ⟨hψ'', hμ'', hX, hY⟩ hXc hYc Φ s
  obtain ⟨x⟩ := IsBaseRestriction.nonempty_equiv F rfl hX
  obtain ⟨y⟩ := IsBaseRestriction.nonempty_equiv F rfl hY
  rw [CommonClosureGamma.conditionalPairEpsilonValue_eq_of_equiv F eC ε hε _ ψ'' μ'' hXc hc hYc
      hc' (x.symm.trans g) (y.symm.trans g') Φ s,
    CommonClosureGamma.conditionalPairEpsilonValue_directSum F eC ε hε _ ψ'' μ'' a a' hac hac'
      hc hc' Φ s,
    RankinSelberg.epsilonMonomial_factorProduct e
      F.canonicalTopologicalData.residueCardinality_gt_one s]
  push_cast
  exact Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ =>
    (he i j).2.2 ψ'' μ'' (a i) (a' j) ⟨hψ'', hμ'', ha i, ha' j⟩ (hac i) (hac' j) Φ s

end Langlands.Correspondence
