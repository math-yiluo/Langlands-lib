import Langlands.Shimura.Unitary.ImaginaryQuadraticSplitTopology
import Langlands.Shimura.Unitary.HarrisSplitPrimePoints
import Langlands.Shimura.Unitary.HarrisSplitTower
import Langlands.Shimura.PEL.TraceSimilitudesLevels
import Langlands.Shimura.PartialLevelTower
import Langlands.Global.IntegralFiniteAdeles
import Langlands.Global.PrimeToFiniteAdeles

/-!
# Harris's levels at a prime split in the imaginary quadratic field

At a finite place `v` of `ℚ` with an embedding `u : F →+* ℚ_v` of the imaginary
quadratic field, the identification `GG(ℚ_v) ≅ (ℚ_v ⊗[F, u] A)ˣ × ℚ_vˣ` is an
isomorphism of topological groups. A compact open subgroup `C` of
`(ℚ_v ⊗[F, u] A)ˣ` gives the level `K_p = C × ℤ_vˣ` of Harris (1999), (4.1), and
its transport to the finite adelic points with a prime-to-`p` level. Fixing
`K_p`, the Harris tower at the levels `K_p × K^p` is the published prime-to-`p`
tower.
-/

noncomputable section

open scoped TensorProduct NumberField
open NumberField CategoryTheory

set_option autoImplicit false

universe u v w z

namespace Langlands.Shimura

open Global CompactOpenLevel

/-- The units `ℤ_vˣ` of the completed integers, as a compact open level of `ℚ_vˣ`. -/
def integerUnitsLevel (v : Global.FinitePlace ℚ) : CompactOpenLevel (FiniteCompletion ℚ v)ˣ where
  openSubgroup :=
    { toSubgroup := (v.adicCompletionIntegers ℚ).toSubmonoid.units
      isOpen' := by
        have hO : IsOpen (v.adicCompletionIntegers ℚ : Set (FiniteCompletion ℚ v)) :=
          Valued.isOpen_valuationSubring _
        have h₁ : IsOpen {c : (FiniteCompletion ℚ v)ˣ |
            (c : FiniteCompletion ℚ v) ∈ v.adicCompletionIntegers ℚ} :=
          hO.preimage Units.continuous_val
        have h₂ : IsOpen {c : (FiniteCompletion ℚ v)ˣ |
            ((c⁻¹ : (FiniteCompletion ℚ v)ˣ) : FiniteCompletion ℚ v) ∈
              v.adicCompletionIntegers ℚ} :=
          hO.preimage Units.continuous_coe_inv
        exact h₁.inter h₂ }
  isCompact := Submonoid.units_isCompact (isCompact_adicCompletionIntegers ℚ v)

theorem mem_integerUnitsLevel (v : Global.FinitePlace ℚ) (c : (FiniteCompletion ℚ v)ˣ) :
    c ∈ (integerUnitsLevel v).subgroup ↔
      (c : FiniteCompletion ℚ v) ∈ v.adicCompletionIntegers ℚ ∧
        ((c⁻¹ : (FiniteCompletion ℚ v)ˣ) : FiniteCompletion ℚ v) ∈
          v.adicCompletionIntegers ℚ :=
  Iff.rfl

namespace AlgebraInvolution

/-- For a prime `p` and a finite place `v` of `ℚ` whose prime ideal contains `p`, the
places whose prime ideal contains `p` consist of `v` alone. -/
abbrev dividingPlaceUnique (p : ℕ) (hp : p.Prime)
    (v : {v : Global.FinitePlace ℚ // (p : 𝓞 ℚ) ∈ v.asIdeal}) :
    Unique {v : Global.FinitePlace ℚ // (p : 𝓞 ℚ) ∈ v.asIdeal} where
  default := v
  uniq w := Subtype.ext ((existsUnique_finitePlace_natCast_mem p hp).unique w.2 v.2)

/-- For a prime `p`, the product of the completions at the places dividing `p` is the
completion `ℚ_v` at the unique such place, through evaluation at `v`. -/
def dividingCompletionEquiv (p : ℕ) (hp : p.Prime)
    (v : {v : Global.FinitePlace ℚ // (p : 𝓞 ℚ) ∈ v.asIdeal}) :
    (Π w : {v : Global.FinitePlace ℚ // (p : 𝓞 ℚ) ∈ v.asIdeal}, FiniteCompletion ℚ w.1) ≃A[ℚ]
      FiniteCompletion ℚ v.1 :=
  letI := dividingPlaceUnique p hp v
  { (RingEquiv.piUnique fun w : {v : Global.FinitePlace ℚ // (p : 𝓞 ℚ) ∈ v.asIdeal} =>
        FiniteCompletion ℚ w.1).toRatAlgEquiv with
    continuous_toFun := continuous_apply v
    continuous_invFun := (Homeomorph.piUnique fun w : {v : Global.FinitePlace ℚ //
        (p : 𝓞 ℚ) ∈ v.asIdeal} => FiniteCompletion ℚ w.1).symm.continuous }

@[simp] theorem dividingCompletionEquiv_apply (p : ℕ) (hp : p.Prime)
    (v : {v : Global.FinitePlace ℚ // (p : 𝓞 ℚ) ∈ v.asIdeal})
    (x : Π w : {v : Global.FinitePlace ℚ // (p : 𝓞 ℚ) ∈ v.asIdeal}, FiniteCompletion ℚ w.1) :
    dividingCompletionEquiv p hp v x = x v := rfl

variable {A : Type z} [Ring A] [Algebra ℚ A] (σ : AlgebraInvolution ℚ A) [Module.Finite ℚ A]

/-- For a prime `p`, the points over `Π_{w ∣ p} ℚ_w` are the points over `ℚ_v`, for the
unique place `v` dividing `p`. -/
def dividingPrimePointsEquiv (p : ℕ) (hp : p.Prime)
    (v : {v : Global.FinitePlace ℚ // (p : 𝓞 ℚ) ∈ v.asIdeal}) :
    σ.DividingPoints p ≃ₜ* σ.Points (FiniteCompletion ℚ v.1) :=
  σ.pointsContinuousEquiv (dividingCompletionEquiv p hp v)

/-- The isomorphism is the published local projection `dividingLocalMap`. -/
theorem dividingPrimePointsEquiv_apply (p : ℕ) (hp : p.Prime)
    (v : {v : Global.FinitePlace ℚ // (p : 𝓞 ℚ) ∈ v.asIdeal}) (g : σ.DividingPoints p) :
    σ.dividingPrimePointsEquiv p hp v g = σ.dividingLocalMap p v g := rfl

end AlgebraInvolution

section Harris

variable {E : Type u} {K : Type v}
variable [Field E] [NumberField E] [IsTotallyReal E]
variable [Field K] [NumberField K] [IsTotallyComplex K]
variable [Algebra E K] [Algebra.IsQuadraticExtension E K]
variable {F : Type w} [Field F] [NumberField F] [IsCMField F] [Algebra.IsQuadraticExtension ℚ F]
variable {A : Type z} [Ring A] [Algebra K A]

variable (A) in
/-- The units of `ℚ_v ⊗[F, u] A`, where `A` is an `F`-algebra through `ι : F →+* K`
and `ℚ_v` through `u`, with the units topology of the `ℚ_v`-module topology. -/
def SplitPrimeUnits (ι : F →+* K) (v : Global.FinitePlace ℚ) (u : F →+* FiniteCompletion ℚ v) :
    Type z :=
  @ImaginaryQuadraticSplit.FactorUnits F A (FiniteCompletion ℚ v) _ _
    (imaginaryQuadraticAlgebra (A := A) ι) _ u.toAlgebra

section Instances

variable (ι : F →+* K) (v : Global.FinitePlace ℚ) (u : F →+* FiniteCompletion ℚ v)

instance : Group (SplitPrimeUnits A ι v u) :=
  inferInstanceAs (Group (@ImaginaryQuadraticSplit.FactorUnits F A (FiniteCompletion ℚ v) _ _
    (imaginaryQuadraticAlgebra (A := A) ι) _ u.toAlgebra))

instance : TopologicalSpace (SplitPrimeUnits A ι v u) :=
  inferInstanceAs (TopologicalSpace (@ImaginaryQuadraticSplit.FactorUnits F A
    (FiniteCompletion ℚ v) _ _ (imaginaryQuadraticAlgebra (A := A) ι) _ u.toAlgebra))

end Instances

variable [Algebra E A] [IsScalarTower E K A] [Algebra ℚ A] [IsScalarTower ℚ E A]

namespace SecondKindInvolution

variable (σ : SecondKindInvolution E K A) (ι : F →+* K)

section Local

variable (v : Global.FinitePlace ℚ) (u : F →+* FiniteCompletion ℚ v)

/-- Harris's identification at a split prime as an isomorphism of topological groups:
`GG(ℚ_v) ≃ₜ* (ℚ_v ⊗[F, u] A)ˣ × ℚ_vˣ`. -/
def splitPrimeHomeomorph :
    σ.rationalInvolution.Points (FiniteCompletion ℚ v) ≃ₜ*
      SplitPrimeUnits A ι v u × (FiniteCompletion ℚ v)ˣ :=
  letI := imaginaryQuadraticAlgebra (A := A) ι
  letI := u.toAlgebra
  ImaginaryQuadraticSplit.pointsHomeomorph σ.rationalInvolution (σ.isConjugationOn ι)

omit [IsScalarTower E K A] in
/-- The underlying group isomorphism is `splitPrimePoints`. -/
theorem splitPrimeHomeomorph_apply (g : σ.rationalInvolution.Points (FiniteCompletion ℚ v)) :
    σ.splitPrimeHomeomorph ι v u g = σ.splitPrimePoints ι v u g := rfl

/-- Harris's level `K_p = C × ℤ_vˣ` of `GG(ℚ_v)`, for a compact open subgroup `C` of
`(ℚ_v ⊗[F, u] A)ˣ`: the points whose algebra component lies in `C` and whose
multiplier lies in `ℤ_vˣ`. -/
def splitPrimeLevel (C : CompactOpenLevel (SplitPrimeUnits A ι v u)) :
    CompactOpenLevel (σ.rationalInvolution.Points (FiniteCompletion ℚ v)) :=
  transport (σ.splitPrimeHomeomorph ι v u).symm (prod C (integerUnitsLevel v))

omit [IsScalarTower E K A] in
theorem mem_splitPrimeLevel (C : CompactOpenLevel (SplitPrimeUnits A ι v u))
    (g : σ.rationalInvolution.Points (FiniteCompletion ℚ v)) :
    g ∈ (σ.splitPrimeLevel ι v u C).subgroup ↔
      (σ.splitPrimeHomeomorph ι v u g).1 ∈ C.subgroup ∧
        AlgebraInvolution.Points.multiplier σ.rationalInvolution _ g ∈
          (integerUnitsLevel v).subgroup :=
  Iff.rfl

omit [IsScalarTower E K A] in
theorem splitPrimeLevel_mono {C C' : CompactOpenLevel (SplitPrimeUnits A ι v u)}
    (h : C.subgroup ≤ C'.subgroup) :
    (σ.splitPrimeLevel ι v u C).subgroup ≤ (σ.splitPrimeLevel ι v u C').subgroup :=
  fun _ hg => ⟨h hg.1, hg.2⟩

end Local

variable [Module.Finite ℚ A] (p : ℕ) (hp : p.Prime)
  (v : {v : Global.FinitePlace ℚ // (p : 𝓞 ℚ) ∈ v.asIdeal}) (u : F →+* FiniteCompletion ℚ v.1)

/-- The level `K_p = C × ℤ_vˣ` as a level of `GG(Π_{w ∣ p} ℚ_w)`. -/
def splitPrimeDividingLevel (C : CompactOpenLevel (SplitPrimeUnits A ι v.1 u)) :
    CompactOpenLevel (σ.rationalInvolution.DividingPoints p) :=
  transport (σ.rationalInvolution.dividingPrimePointsEquiv p hp v).symm
    (σ.splitPrimeLevel ι v.1 u C)

omit [IsScalarTower E K A] in
theorem mem_splitPrimeDividingLevel (C : CompactOpenLevel (SplitPrimeUnits A ι v.1 u))
    (g : σ.rationalInvolution.DividingPoints p) :
    g ∈ (σ.splitPrimeDividingLevel ι p hp v u C).subgroup ↔
      σ.rationalInvolution.dividingLocalMap p v g ∈ (σ.splitPrimeLevel ι v.1 u C).subgroup :=
  Iff.rfl

/-- Harris's level `K_p × K^p` of `GG(A_f)`: the inverse image, under the published
splitting `GG(A_f) ≃ₜ* GG(Π_{w ∣ p} ℚ_w) × GG(A_f^p)`, of the product of
`K_p = C × ℤ_vˣ` and a level `K'` of `GG(A_f^p)`. -/
def splitPrimeAdelicLevel (C : CompactOpenLevel (SplitPrimeUnits A ι v.1 u))
    (K' : CompactOpenLevel (σ.rationalInvolution.PrimeToPoints p)) :
    CompactOpenLevel σ.rationalInvolution.FiniteAdelicPoints :=
  transport (σ.rationalInvolution.finiteAdelicPointsSplit p hp.ne_zero).symm
    (prod (σ.splitPrimeDividingLevel ι p hp v u C) K')

omit [IsScalarTower E K A] in
/-- A finite adelic point lies in `K_p × K^p` exactly when its local image at `v` lies in
`K_p` and its prime-to-`p` component lies in `K^p`. -/
theorem mem_splitPrimeAdelicLevel (C : CompactOpenLevel (SplitPrimeUnits A ι v.1 u))
    (K' : CompactOpenLevel (σ.rationalInvolution.PrimeToPoints p))
    (g : σ.rationalInvolution.FiniteAdelicPoints) :
    g ∈ (σ.splitPrimeAdelicLevel ι p hp v u C K').subgroup ↔
      σ.rationalInvolution.finiteLocalMap v.1 g ∈ (σ.splitPrimeLevel ι v.1 u C).subgroup ∧
        (σ.rationalInvolution.finiteAdelicPointsSplit p hp.ne_zero g).2 ∈ K'.subgroup := by
  change σ.rationalInvolution.dividingLocalMap p v
      (σ.rationalInvolution.finiteAdelicPointsSplit p hp.ne_zero g).1 ∈
        (σ.splitPrimeLevel ι v.1 u C).subgroup ∧
      (σ.rationalInvolution.finiteAdelicPointsSplit p hp.ne_zero g).2 ∈ K'.subgroup ↔ _
  rw [AlgebraInvolution.dividingLocalMap_finiteAdelicPointsSplit]

end SecondKindInvolution

section Tower

open _root_.Algebra

variable [IsScalarTower ℚ K A] [Module.Finite ℚ A] {n : ℕ}
  (D : CentralSimpleUnitaryData E K A n) (h : HasHarrisSignature D.toSecondKindInvolution n)
  (ιF : F →+* K) (τ₀ : F →+* ℂ)
  (p : ℕ) (hp : p.Prime) (v : {v : Global.FinitePlace ℚ // (p : 𝓞 ℚ) ∈ v.asIdeal})
  (u : F →+* FiniteCompletion ℚ v.1) (C : CompactOpenLevel (SplitPrimeUnits A ιF v.1 u))

/-- The Harris tower away from `p` at the fixed level `K_p = C × ℤ_vˣ`: the published
prime-to-`p` tower for the level `K_p` of `GG(Π_{w ∣ p} ℚ_w)`. -/
def harrisSplitPrimeTower :
    CompactOpenLevel (D.toSecondKindInvolution.rationalInvolution.PrimeToPoints p) ⥤
      TopCat.{max z u} :=
  harrisPrimeToLevelTower D h ιF τ₀ p
    (D.toSecondKindInvolution.splitPrimeDividingLevel ιF p hp v u C)

omit [IsScalarTower E K A] [IsScalarTower ℚ K A] in
/-- At a prime-to-`p` level `K'`, the away functor gives the level `K_p × K'` of
`GG(A_f)`. -/
theorem awayOver_splitPrime_obj
    (K' : CompactOpenLevel (D.toSecondKindInvolution.rationalInvolution.PrimeToPoints p)) :
    (awayOver (D.toSecondKindInvolution.rationalInvolution.finiteAdelicPointsSplit p
        hp.ne_zero) (D.toSecondKindInvolution.splitPrimeDividingLevel ιF p hp v u C)).functor.obj
        K' =
      D.toSecondKindInvolution.splitPrimeAdelicLevel ιF p hp v u C K' :=
  rfl

/-- The Harris level tower at the levels `K_p × K^p`, with `K_p = C × ℤ_vˣ` fixed, is the
Harris tower away from `p` at `K_p`. -/
def harrisSplitPrimeTowerIso :
    (awayOver (D.toSecondKindInvolution.rationalInvolution.finiteAdelicPointsSplit p
        hp.ne_zero) (D.toSecondKindInvolution.splitPrimeDividingLevel ιF p hp v u C)).functor ⋙
        harrisUnitaryLevelTower D h ιF τ₀ ≅
      harrisSplitPrimeTower D h ιF τ₀ p hp v u C :=
  harrisPrimeToTowerIso D h ιF τ₀ p hp.ne_zero _

end Tower

end Harris

end Langlands.Shimura
