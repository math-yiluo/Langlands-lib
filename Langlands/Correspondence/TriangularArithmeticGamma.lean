import Langlands.Weil.Representation.TriangularExactClass
import Langlands.Automorphic.PrincipalSeriesRankOneGamma
import Langlands.Correspondence.RankOneArithmeticEpsilonData
import Langlands.Correspondence.RankOneArithmeticEpsilon
import Langlands.Correspondence.BaseGeometricResidue
import Langlands.Correspondence.RankOnePairFactorCompatibility
import Langlands.Global.Factors.RelativeWeilLocalEulerBridge
import Langlands.Representation.RankinSelberg.HighlyRamified.MonomialGamma

/-! # Arithmetic pair gamma factors of upper triangular zero-monodromy pairs -/

noncomputable section

universe u uG uV uW uE

open Polynomial

namespace Langlands.FiniteRepresentation

variable {G : Type uG} [Group G]

/-- A representation moved along a linear equivalence of carriers:
`g ↦ f ∘ ρ(g) ∘ f⁻¹`. -/
def transportRepresentation {V : Type uV} {W : Type uW} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G V) (f : V ≃ₗ[ℂ] W) :
    Representation ℂ G W where
  toFun g := f.toLinearMap ∘ₗ ρ g ∘ₗ f.symm.toLinearMap
  map_one' := by ext w; simp
  map_mul' g h := by ext w; simp

/-- The carrier equivalence intertwines a representation with its transport. -/
def transportEquiv {V : Type uV} {W : Type uW} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G V) (f : V ≃ₗ[ℂ] W) :
    ρ.Equiv (transportRepresentation ρ f) :=
  Representation.Equiv.mk f fun g => by ext v; simp [transportRepresentation]

/-- Restriction along a homomorphism preserves upper triangularity of a basis. -/
theorem IsUpperTriangularBasis.restrict {H : Type uW} [Group H] (φ : H →* G)
    {A : FiniteRepresentation.{0, uG, uV} ℂ G} {n : ℕ} {b : Module.Basis (Fin n) ℂ A}
    (hb : IsUpperTriangularBasis A b) : IsUpperTriangularBasis (restrict φ A) b :=
  fun h i j hij => hb (φ h) i j hij

end Langlands.FiniteRepresentation

namespace Langlands.WeilDeligneRepresentation

variable {K : Type*} {G : Type uG} [Field K] [Group G] {ν : G →* Kˣ}

/-- A pair with zero monodromy has the class of the zero-monodromy pair of its
representation. -/
theorem classOf_eq_zeroMonodromy (A : WeilDeligneRepresentation.{_, uG, uV} K G ν)
    (h : A.monodromy = 0) : classOf A = classOf (zeroMonodromy ν A.toFiniteRepresentation) :=
  (classOf_eq_iff _ _).2 ⟨⟨Representation.Equiv.refl _, by
    rw [h, LinearMap.comp_zero]
    exact (LinearMap.zero_comp _).symm⟩⟩

end Langlands.WeilDeligneRepresentation

namespace Langlands.LocalFactor.CommonClosureWeilDeligne

open CommonClosure CommonClosureSpectral VirtualRepresentation

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)

/-- Deligne's spectral value of a supplied system is multiplicative on finite sums
of exact virtual classes. -/
theorem conditionalDeligneValue_finsetSum (e : ReciprocityFamily F)
    (ε : NonabelianSystem.Assignment.{u, uV} F) (hε : NonabelianSystem.IsSystem F e ε)
    (E : Extension F) (ψ : AdditiveCharacter F E) (μ : HaarMeasure F E) {ι : Type*}
    (s : Finset ι) (x : ι → Virtual.{u, uV} F E) (z : ℂ) :
    conditionalDeligneValue F e ε hε E ψ μ (∑ i ∈ s, x i) z =
      ∏ i ∈ s, conditionalDeligneValue F e ε hε E ψ μ (x i) z := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h := conditionalDeligneValue_add F e ε hε E ψ μ 0 0 z
    rw [add_zero] at h
    simpa using h
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi, conditionalDeligneValue_add, ih]

end Langlands.LocalFactor.CommonClosureWeilDeligne

namespace Langlands.Correspondence

open LocalFactor LocalFactor.CommonClosure LocalFactor.CommonClosureWeilDeligne Weil.Local
  VirtualRepresentation

variable {p : ℕ} [Fact p.Prime] (K : PadicField.{u} p)

local instance triangularArithmeticTopology : TopologicalSpace K.Carrier :=
  K.canonicalTopologicalData.topology

section BasePair

/-- The restriction of a pair to the bottom Weil subgroup, carried by the coordinates of
a basis lifted to the carrier universe of a supplied system, with zero monodromy. -/
def baseCoordinatePair (B : LocalWeilDeligneRepresentation.{u, uV} K) {n : ℕ}
    (b : Module.Basis (Fin n) ℂ B) : Pair.{u, uE} K (baseExtension K) :=
  WeilDeligneRepresentation.zeroMonodromy _
    (FiniteRepresentation.of (FiniteRepresentation.transportRepresentation
      (FiniteRepresentation.restrict (weilSubgroup K (baseExtension K)).subtype
        B.toFiniteRepresentation).representation
      (b.equivFun.trans (ULift.moduleEquiv (R := ℂ)).symm :
        B ≃ₗ[ℂ] ULift.{max u uE} (Fin n → ℂ))))

/-- For zero monodromy, the coordinate pair is equivalent to the actual restriction. -/
def baseCoordinatePairEquiv (B : LocalWeilDeligneRepresentation.{u, uV} K)
    (hN : B.monodromy = 0) {n : ℕ} (b : Module.Basis (Fin n) ℂ B) :
    WeilDeligneRepresentation.Equiv
      (WeilDeligneRepresentation.restrict (weilSubgroup K (baseExtension K)).subtype B)
      (baseCoordinatePair.{u, uV, uE} K B b) where
  representationEquiv := FiniteRepresentation.transportEquiv _ _
  comm_monodromy := by
    have h0 : (WeilDeligneRepresentation.restrict
        (weilSubgroup K (baseExtension K)).subtype B).monodromy = 0 := hN
    rw [h0, LinearMap.comp_zero]
    exact (LinearMap.zero_comp _).symm

theorem baseCoordinatePair_isContinuous (B : LocalWeilDeligneRepresentation.{u, uV} K)
    (hB : B.toFiniteRepresentation.IsContinuous) {n : ℕ} (b : Module.Basis (Fin n) ℂ B) :
    (baseCoordinatePair.{u, uV, uE} K B b).toFiniteRepresentation.IsContinuous :=
  (FiniteRepresentation.isContinuous_iff_of_equiv
    (A := FiniteRepresentation.restrict (weilSubgroup K (baseExtension K)).subtype
      B.toFiniteRepresentation)
    (B := (baseCoordinatePair.{u, uV, uE} K B b).toFiniteRepresentation)
    (FiniteRepresentation.transportEquiv _ _)).1
    (FiniteRepresentation.isContinuous_restrict _ continuous_subtype_val hB)

theorem isBaseRestriction_baseCoordinatePair (B : LocalWeilDeligneRepresentation.{u, uV} K)
    (hN : B.monodromy = 0) {n : ℕ} (b : Module.Basis (Fin n) ℂ B) :
    IsBaseRestriction K (WeilDeligneRepresentation.classOf B)
      (baseCoordinatePair.{u, uV, uE} K B b) :=
  ⟨B, rfl, ⟨baseCoordinatePairEquiv K B hN b⟩⟩

/-- Every bottom restriction datum of the class of an upper triangular pair has exact
class the sum of the restricted diagonal characters. -/
theorem ofRepresentation_eq_sum_of_isBaseRestriction
    (B : LocalWeilDeligneRepresentation.{u, uV} K) {n : ℕ} (b : Module.Basis (Fin n) ℂ B)
    (χ : Fin n → localWeilGroup K →ₜ* ℂˣ)
    (hb : FiniteRepresentation.IsUpperTriangularBasis B.toFiniteRepresentation b)
    (hd : ∀ (g : localWeilGroup K) (i : Fin n), b.repr (B.representation g (b i)) i = χ i g)
    {A : Pair.{u, uE} K (baseExtension K)}
    (hA : IsBaseRestriction K (WeilDeligneRepresentation.classOf B) A)
    (hAc : A.toFiniteRepresentation.IsContinuous) :
    ExactGrothendieckGroup.ofRepresentation
        (fun C : FiniteRepresentation.{0, u, max u uE} ℂ (weilSubgroup K (baseExtension K)) =>
          C.IsContinuous) ⟨A.toFiniteRepresentation, hAc⟩ =
      ∑ i, ExactGrothendieckGroup.characterClass.{u, max u uE}
        (baseRestrictedWeilCharacter K (χ i)) := by
  obtain ⟨f⟩ := IsBaseRestriction.nonempty_equiv K rfl hA
  exact FiniteRepresentation.ofRepresentation_eq_sum_characterClass_of_equiv_triangular
    A.toFiniteRepresentation hAc
    (FiniteRepresentation.restrict (weilSubgroup K (baseExtension K)).subtype
      B.toFiniteRepresentation)
    f.representationEquiv b _ (hb.restrict _) fun g i => hd g.val i

end BasePair

section Epsilon

/-- Arithmetic pair epsilon factors of upper triangular zero-monodromy pairs: the product
of the rank-one data of the products of the diagonal quasi-characters. -/
theorem isArithmeticPairEpsilonFactor_triangular (eC : ReciprocityFamily K)
    (ε : NonabelianSystem.Assignment.{u, uE} K) (hε : NonabelianSystem.IsSystem K eC ε)
    (e : ReciprocityCandidate K) (h : IsBaseReciprocity K e eC)
    (ψ : NontrivialAdditiveCharacter K) {r t : ℕ}
    (χ : Fin r → QuasiCharacter K) (η : Fin t → QuasiCharacter K)
    (B B' : LocalWeilDeligneRepresentation.{u, uV} K)
    (hN : B.monodromy = 0) (hN' : B'.monodromy = 0)
    (hB : B.toFiniteRepresentation.IsContinuous) (hB' : B'.toFiniteRepresentation.IsContinuous)
    (b : Module.Basis (Fin r) ℂ B) (b' : Module.Basis (Fin t) ℂ B')
    (hb : FiniteRepresentation.IsUpperTriangularBasis B.toFiniteRepresentation b)
    (hb' : FiniteRepresentation.IsUpperTriangularBasis B'.toFiniteRepresentation b')
    (hd : ∀ (g : localWeilGroup K) (i : Fin r),
      b.repr (B.representation g (b i)) i = RankOne.weilCharacter K e (χ i) g)
    (hd' : ∀ (g : localWeilGroup K) (j : Fin t),
      b'.repr (B'.representation g (b' j)) j = RankOne.weilCharacter K e (η j) g) :
    IsArithmeticPairEpsilonFactor K eC ε hε ψ (WeilDeligneRepresentation.classOf B)
      (WeilDeligneRepresentation.classOf B')
      (RankinSelberg.epsilonFactorProduct fun i j =>
        (rankOneArithmeticEpsilonCoefficient K ψ (χ i * η j),
          PadicAbelian.epsilonExponent K.canonicalTopologicalData (χ i * η j) ψ)).1
      (RankinSelberg.epsilonFactorProduct fun i j =>
        (rankOneArithmeticEpsilonCoefficient K ψ (χ i * η j),
          PadicAbelian.epsilonExponent K.canonicalTopologicalData (χ i * η j) ψ)).2 := by
  obtain ⟨⟨ψ', μ, -, -, ⟨hψ', hμ, -, -⟩, -, -⟩, hΦ, -⟩ :=
    isArithmeticPairEpsilonFactor_rankOne_constructed.{u, u, uE} K e eC h ε hε ψ 1 1
  refine ⟨⟨ψ', μ, baseCoordinatePair.{u, uV, uE} K B b, baseCoordinatePair.{u, uV, uE} K B' b',
    ⟨hψ', hμ, isBaseRestriction_baseCoordinatePair K B hN b,
      isBaseRestriction_baseCoordinatePair K B' hN' b'⟩,
    baseCoordinatePair_isContinuous K B hB b, baseCoordinatePair_isContinuous K B' hB' b'⟩,
    hΦ, ?_⟩
  rintro ψ'' μ'' A A' ⟨hψ'', hμ'', hA, hA'⟩ hAc hA'c Φ s
  obtain ⟨f⟩ := IsBaseRestriction.nonempty_equiv K rfl hA
  obtain ⟨f'⟩ := IsBaseRestriction.nonempty_equiv K rfl hA'
  have hTN : (WeilDeligneRepresentation.tensor A A').monodromy = 0 :=
    WeilDeligneRepresentation.tensor_monodromy_eq_zero
      (WeilDeligneRepresentation.monodromy_eq_zero_of_equiv f hN)
      (WeilDeligneRepresentation.monodromy_eq_zero_of_equiv f' hN')
  have hcl := FiniteRepresentation.ofRepresentation_tensor_eq_sum_characterClass
    A.toFiniteRepresentation A'.toFiniteRepresentation hAc hA'c _ _
    (ofRepresentation_eq_sum_of_isBaseRestriction K B b _ hb hd hA hAc)
    (ofRepresentation_eq_sum_of_isBaseRestriction K B' b' _ hb' hd' hA' hA'c)
  have hterm : ∀ i j, (CommonClosureSpectral.conditionalDeligneValue K eC ε hε
      (baseExtension K) ψ'' μ'' (ExactGrothendieckGroup.characterClass
        (baseRestrictedWeilCharacter K (RankOne.weilCharacter K e (χ i)) *
          baseRestrictedWeilCharacter K (RankOne.weilCharacter K e (η j)))) s : ℂ) =
      RankinSelberg.epsilonMonomial K.canonicalTopologicalData.residueCardinality
        (rankOneArithmeticEpsilonCoefficient K ψ (χ i * η j))
        (PadicAbelian.epsilonExponent K.canonicalTopologicalData (χ i * η j) ψ) s := by
    intro i j
    rw [CommonClosureSpectral.conditionalDeligneValue_characterClass]
    exact ((isArithmeticPairEpsilonFactor_rankOneWeilCharacterClass_iff.{u, u, uE}
      K e eC ε hε ψ (χ i) (η j) _ _).1
      (isArithmeticPairEpsilonFactor_rankOne_constructed.{u, u, uE}
        K e eC h ε hε ψ (χ i) (η j))).2.2 ψ'' μ'' hψ'' hμ'' s
  rw [CommonClosureGamma.conditionalPairEpsilonValue,
    conditionalEpsilonValue_of_monodromy_zero (hN := hTN), underlyingClass]
  erw [hcl]
  rw [conditionalDeligneValue_finsetSum, Units.coe_prod,
    RankinSelberg.epsilonMonomial_factorProduct _
      K.canonicalTopologicalData.residueCardinality_gt_one s]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [conditionalDeligneValue_finsetSum, Units.coe_prod]
  exact Finset.prod_congr rfl fun j _ => hterm i j

end Epsilon

section LRatio

open FiniteRepresentation ExactGrothendieckGroup Weil.Local.InertiaEuler

/-- If the exact class of a continuous representation is a double sum of character
classes, its L-factor is the double product of the character L-factors. -/
theorem coe_lFactorUnit_eq_prod_characterLFactor (T : LocalWeilRepresentation.{u, uW} K)
    (hT : T.IsContinuous) {ι κ : Type*} [Fintype ι] [Fintype κ]
    (α : ι → κ → localWeilGroup K →ₜ* ℂˣ)
    (h : ofRepresentation (fun C : LocalWeilRepresentation.{u, uW} K => C.IsContinuous)
      ⟨T, hT⟩ = ∑ i, ∑ j, characterClass.{u, uW} (α i j)) :
    (lFactorUnit K T : RatFunc ℂ) = ∏ i, ∏ j, characterLFactor K (α i j) := by
  have hL := congrArg (fun x => Additive.toMul (lFactorHom K x)) h
  simp only [map_sum, lFactorHom_ofRepresentation, lFactorHom_characterClass, toMul_sum,
    toMul_ofMul] at hL
  rw [hL, Units.coe_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Units.coe_prod]
  exact Finset.prod_congr rfl fun j _ => coe_lFactorUnit_characterLine K (α i j)

variable {K}

/-- The arithmetic pair L-factor of the zero-monodromy pairs of two upper triangular
continuous representations: the product of the L-factors of the products of the diagonal
characters. -/
theorem arithmeticPairLFactor_triangular (V W : LocalWeilRepresentation.{u, uV} K)
    (hV : V.IsContinuous) (hW : W.IsContinuous) {r t : ℕ}
    (χ : Fin r → localWeilGroup K →ₜ* ℂˣ) (η : Fin t → localWeilGroup K →ₜ* ℂˣ)
    (b : Module.Basis (Fin r) ℂ V) (b' : Module.Basis (Fin t) ℂ W)
    (hb : IsUpperTriangularBasis V b) (hb' : IsUpperTriangularBasis W b')
    (hd : ∀ (g : localWeilGroup K) (i : Fin r), b.repr (V.representation g (b i)) i = χ i g)
    (hd' : ∀ (g : localWeilGroup K) (j : Fin t),
      b'.repr (W.representation g (b' j)) j = η j g) :
    arithmeticPairLFactor K
        (WeilDeligneRepresentation.classOf
          (WeilDeligneRepresentation.zeroMonodromy (localNormCharacter K).toMonoidHom V))
        (WeilDeligneRepresentation.classOf
          (WeilDeligneRepresentation.zeroMonodromy (localNormCharacter K).toMonoidHom W)) =
      ∏ i, ∏ j, characterLFactor K (χ i * η j) := by
  rw [arithmeticPairLFactor_zeroMonodromy K V W (tensor V W) (Representation.Equiv.refl _)]
  exact coe_lFactorUnit_eq_prod_characterLFactor K _ (isContinuous_tensor hV hW) _
    (ofRepresentation_tensor_eq_sum_characterClass V W hV hW χ η
      (ofRepresentation_eq_sum_characterClass_of_triangular V hV b χ hb hd)
      (ofRepresentation_eq_sum_characterClass_of_triangular W hW b' η hb' hd'))

/-- The dual form: the arithmetic pair L-factor of the zero-monodromy pairs of the duals
is the product of the L-factors of the inverse products of the diagonal characters. -/
theorem arithmeticPairLFactor_dual_triangular (V W : LocalWeilRepresentation.{u, uV} K)
    (hV : V.IsContinuous) (hW : W.IsContinuous) {r t : ℕ}
    (χ : Fin r → localWeilGroup K →ₜ* ℂˣ) (η : Fin t → localWeilGroup K →ₜ* ℂˣ)
    (b : Module.Basis (Fin r) ℂ V) (b' : Module.Basis (Fin t) ℂ W)
    (hb : IsUpperTriangularBasis V b) (hb' : IsUpperTriangularBasis W b')
    (hd : ∀ (g : localWeilGroup K) (i : Fin r), b.repr (V.representation g (b i)) i = χ i g)
    (hd' : ∀ (g : localWeilGroup K) (j : Fin t),
      b'.repr (W.representation g (b' j)) j = η j g) :
    arithmeticPairLFactor K
        (WeilDeligneRepresentation.classOf
          (WeilDeligneRepresentation.zeroMonodromy (localNormCharacter K).toMonoidHom
            (dual V)))
        (WeilDeligneRepresentation.classOf
          (WeilDeligneRepresentation.zeroMonodromy (localNormCharacter K).toMonoidHom
            (dual W))) =
      ∏ i, ∏ j, characterLFactor K (χ i * η j)⁻¹ := by
  rw [arithmeticPairLFactor_zeroMonodromy K (dual V) (dual W) (dual (tensor V W))
    (FiniteRepresentation.tensorDualEquiv V W).symm]
  have hT := ofRepresentation_tensor_eq_sum_characterClass V W hV hW χ η
    (ofRepresentation_eq_sum_characterClass_of_triangular V hV b χ hb hd)
    (ofRepresentation_eq_sum_characterClass_of_triangular W hW b' η hb' hd')
  have hTd := congrArg continuousDual hT
  simp only [continuousDual_ofRepresentation, map_sum, continuousDual_characterClass] at hTd
  exact coe_lFactorUnit_eq_prod_characterLFactor K _ _ _ hTd

/-- The class-level reflected L-ratio of the tensor product of two upper triangular
zero-monodromy pairs with diagonal characters `χ_i ∘ e`, `η_j ∘ e`, for a geometric
candidate `e`: the product over `i, j` of `L(χ_i η_j)(X) / L((χ_i η_j)⁻¹)(q⁻¹ / X)`. -/
theorem rationalLRatioClass_triangular (e : ReciprocityCandidate K)
    (he : IsGeometricReciprocity K e) {r t : ℕ}
    (χ : Fin r → QuasiCharacter K) (η : Fin t → QuasiCharacter K)
    (B B' : LocalWeilDeligneRepresentation.{u, uV} K)
    (hN : B.monodromy = 0) (hN' : B'.monodromy = 0)
    (hB : B.toFiniteRepresentation.IsContinuous) (hB' : B'.toFiniteRepresentation.IsContinuous)
    (b : Module.Basis (Fin r) ℂ B) (b' : Module.Basis (Fin t) ℂ B')
    (hb : IsUpperTriangularBasis B.toFiniteRepresentation b)
    (hb' : IsUpperTriangularBasis B'.toFiniteRepresentation b')
    (hd : ∀ (g : localWeilGroup K) (i : Fin r),
      b.repr (B.representation g (b i)) i = RankOne.weilCharacter K e (χ i) g)
    (hd' : ∀ (g : localWeilGroup K) (j : Fin t),
      b'.repr (B'.representation g (b' j)) j = RankOne.weilCharacter K e (η j) g) :
    WeilDeligne.rationalLRatioClass (localInertia K) (localGeometricFrobenius K)
        (residueReflection K)
        (WeilDeligneRepresentation.tensorClass (WeilDeligneRepresentation.classOf B)
          (WeilDeligneRepresentation.classOf B')) =
      ∏ i, ∏ j,
        (algebraMap ℂ[X] (RatFunc ℂ)
            (PadicAbelian.lPolynomial K.canonicalTopologicalData (χ i * η j)) /
          aeval (RationalReflection.reflectedVariable (residueReflection K))
            (PadicAbelian.lPolynomial K.canonicalTopologicalData (χ i * η j)⁻¹)) := by
  have hdual : ∀ V : LocalWeilRepresentation.{u, uV} K,
      WeilDeligneRepresentation.dualClass (WeilDeligneRepresentation.classOf
          (WeilDeligneRepresentation.zeroMonodromy (localNormCharacter K).toMonoidHom V)) =
        WeilDeligneRepresentation.classOf
          (WeilDeligneRepresentation.zeroMonodromy (localNormCharacter K).toMonoidHom
            (dual V)) :=
    fun V => Quotient.sound ⟨WeilDeligneRepresentation.dualZeroMonodromyEquiv V⟩
  rw [WeilDeligne.rationalLRatioClass_eq, WeilDeligneRepresentation.dualClass_tensorClass,
    WeilDeligneRepresentation.classOf_eq_zeroMonodromy B hN,
    WeilDeligneRepresentation.classOf_eq_zeroMonodromy B' hN', hdual, hdual]
  have hL : ∀ X Y : LocalPairClass.{u, uV} K,
      WeilDeligne.rationalLFactorClass (localInertia K) (localGeometricFrobenius K)
        (WeilDeligneRepresentation.tensorClass X Y) = arithmeticPairLFactor K X Y :=
    fun _ _ => rfl
  rw [hL, hL, arithmeticPairLFactor_dual_triangular _ _ hB hB' _ _ b b' hb hb' hd hd',
    arithmeticPairLFactor_triangular _ _ hB hB' _ _ b b' hb hb' hd hd', map_prod,
    ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [map_prod, ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  have hm : RankOne.weilCharacter K e (χ i) * RankOne.weilCharacter K e (η j) =
      RankOne.weilCharacter K e (χ i * η j) := rfl
  rw [hm, weilCharacter_inv', characterLFactor_weilCharacter K he,
    characterLFactor_weilCharacter K he, PadicAbelian.rationalLFactor,
    PadicAbelian.rationalLFactor, map_inv₀, RationalReflection.subst_polynomial, inv_div_inv]

end LRatio

section Gamma

open RankinSelberg

/-- Epsilon monomials of a finite product of constants and a finite sum of exponents
multiply. -/
theorem rationalEpsilonMonomial_finset {ι : Type*} (s : Finset ι) (c : ι → ℂˣ) (m : ι → ℤ) :
    rationalEpsilonMonomial (∏ i ∈ s, c i) (∑ i ∈ s, m i) =
      ∏ i ∈ s, rationalEpsilonMonomial (c i) (m i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [rationalEpsilonMonomial]
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi, Finset.prod_insert hi, ← ih]
    simp only [rationalEpsilonMonomial, map_mul, zpow_add]
    exact mul_mul_mul_comm _ _ _ _

/-- The epsilon monomial of a double product of rank-one data is the double product of
the rank-one epsilon monomials. -/
theorem coe_rationalEpsilonMonomial_factorProduct {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι → κ → ℂˣ × ℤ) :
    (rationalEpsilonMonomial (epsilonFactorProduct e).1 (epsilonFactorProduct e).2 :
        RatFunc ℂ) =
      ∏ i, ∏ j, (rationalEpsilonMonomial (e i j).1 (e i j).2 : RatFunc ℂ) := by
  change (rationalEpsilonMonomial (∏ i, ∏ j, (e i j).1) (∑ i, ∑ j, (e i j).2) :
    RatFunc ℂ) = _
  rw [rationalEpsilonMonomial_finset, Units.coe_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [rationalEpsilonMonomial_finset, Units.coe_prod]

/-- Arithmetic pair gamma factors of upper triangular zero-monodromy pairs with diagonal
characters `χ_i ∘ e`, `η_j ∘ e`: the product of Tate's rational gamma functions of the
products `χ_i η_j`, for every self-dual measure. -/
theorem isArithmeticPairGammaFactor_triangular (eC : ReciprocityFamily K)
    (ε : NonabelianSystem.Assignment.{u, uE} K) (hε : NonabelianSystem.IsSystem K eC ε)
    (e : ReciprocityCandidate K) (h : IsBaseReciprocity K e eC)
    (ψ : NontrivialAdditiveCharacter K) (ν : LocalAdditiveHaarMeasure K)
    (hν : IsSelfDualMeasure K ψ ν) {r t : ℕ}
    (χ : Fin r → QuasiCharacter K) (η : Fin t → QuasiCharacter K)
    (B B' : LocalWeilDeligneRepresentation.{u, uV} K)
    (hN : B.monodromy = 0) (hN' : B'.monodromy = 0)
    (hB : B.toFiniteRepresentation.IsContinuous) (hB' : B'.toFiniteRepresentation.IsContinuous)
    (b : Module.Basis (Fin r) ℂ B) (b' : Module.Basis (Fin t) ℂ B')
    (hb : FiniteRepresentation.IsUpperTriangularBasis B.toFiniteRepresentation b)
    (hb' : FiniteRepresentation.IsUpperTriangularBasis B'.toFiniteRepresentation b')
    (hd : ∀ (g : localWeilGroup K) (i : Fin r),
      b.repr (B.representation g (b i)) i = RankOne.weilCharacter K e (χ i) g)
    (hd' : ∀ (g : localWeilGroup K) (j : Fin t),
      b'.repr (B'.representation g (b' j)) j = RankOne.weilCharacter K e (η j) g) :
    IsArithmeticPairGammaFactor K eC ε hε ψ (WeilDeligneRepresentation.classOf B)
      (WeilDeligneRepresentation.classOf B')
      (∏ i, ∏ j, tateRationalGamma K ψ ν (χ i * η j)) := by
  have he : IsGeometricReciprocity K e :=
    isGeometricReciprocity_of_isBaseReciprocity K e eC h hε.1
  refine ⟨_, _, isArithmeticPairEpsilonFactor_triangular K eC ε hε e h ψ χ η B B' hN hN'
    hB hB' b b' hb hb' hd hd', ?_⟩
  rw [rationalLRatioClass_triangular e he χ η B B' hN hN' hB hB' b b' hb hb' hd hd',
    coe_rationalEpsilonMonomial_factorProduct, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [tateRationalGamma, rationalGammaExpression,
    tateEpsilonCoefficient_eq_rankOneArithmetic K ψ ν hν, mul_div_assoc]

end Gamma

end Langlands.Correspondence
