import Langlands.TraceFormula.DivisionAlgebraSimpleTraceComparisonStatement
import Langlands.TraceFormula.GeneralLinearBaseChangeLocal
import Langlands.JacquetLanglands.DivisionMatching
import Langlands.Global.ArchimedeanConvolution
import Langlands.HarmonicAnalysis.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology

/-!
# The trace comparison between `GL_n` and the units of a division algebra for restricted tensor products

Let `E` be a number field, `A` a central division algebra of dimension `n²` over `E`,
`G' = Aˣ` its unit group scheme and `G = GL_n`. Suppose that `A` is a division algebra at two
distinct finite places `p₁`, `p₂` and split at every other place, finite and infinite. The
statement `DivisionAlgebraProductTraceComparisonStatement` asserts that, after a choice of
matrix charts of `E_p ⊗ A` at the split places and of a positive constant `c`, for all
restricted tensor products `f = f_∞ ⊗ ⊗_p f_p` on `G(𝔸_E)` and `f'` on `G'(𝔸_E)` whose
components at `p₁`, `p₂` are matching functions with regular support and whose other
components correspond through the charts, `R'(f')` on `L²([G'])` and `R_disc(f)` on
`L²_disc([G])` are trace class and `tr R'(f') = c · tr R_disc(f)`.

The module also defines the predicate `IsAdelicInfiniteFactorization` (a restricted tensor
product with one factor on the whole archimedean group `G(E_∞)`) and the charts
`finiteAlgebraPlaceUnitEquiv` and `finiteAlgebraInfiniteUnitEquiv` of the local and
archimedean points of the unit group scheme of a finite-dimensional algebra.

The statement is derived from Deligne–Kazhdan–Vignéras 1984, §B.1.a (printed p. 78) and §C.1
(printed pp. 90–91), from the passage from local to global matching in Arthur–Clozel 1989,
Chapter 1, §4 (printed pp. 42–44), and from the factorization of global orbital integrals of
product functions in Getz–Hahn 2024, §17.8, Lemma 17.8.3 (printed pp. 463–464). It is not
proved here. See `DivisionAlgebraProductTraceComparisonStatement.md`.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj TensorProduct
open Langlands.Global Langlands.Global.AdelicGroupPoints
open Langlands.GroupScheme Langlands.JacquetLanglands
open Langlands.Analysis.OperatorIdeals
open Langlands.HarmonicAnalysis (SchwartzBruhat)
open Langlands.BaseChange (IsEllipticSupported)

namespace Langlands.TraceFormula

section Factorization

variable (F : Type) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
  [IsAffine G.X.left]

/-- A function `f` on `G(𝔸_F)` is the restricted tensor product of a function `φInf` on the
archimedean points `G(F_∞) = G(F ⊗ ℝ)` (`InfiniteAdelicGroupPoints`), of local functions
`φ p` at the finite places `p ∈ S` and of the indicator functions of the subgroups `U p` at the
finite places `p ∉ S`:
`f(x) = φInf(x_∞) ∏_{p ∈ S} φ p (x_p)` if `x_p ∈ U p` for every finite `p ∉ S`, and `f(x) = 0`
otherwise. Here `x_∞` is `AdelicGroupPoints.infinite F G x` and `x_p` is
`AdelicGroupPoints.atPlace F G (.inr p) x`. -/
def IsAdelicInfiniteFactorization (S : Finset (Langlands.Global.FinitePlace F))
    (φInf : InfiniteAdelicGroupPoints F G → ℂ)
    (φ : (p : Langlands.Global.FinitePlace F) → PlaceGroupPoints F G (.inr p) → ℂ)
    (U : (p : Langlands.Global.FinitePlace F) → Subgroup (PlaceGroupPoints F G (.inr p)))
    (f : AdelicGroupPoints F G → ℂ) : Prop :=
  ∀ x : AdelicGroupPoints F G,
    f x = {y : AdelicGroupPoints F G | ∀ p ∉ S, atPlace F G (.inr p) y ∈ U p}.indicator
      (fun y => φInf (AdelicGroupPoints.infinite F G y) *
        ∏ p ∈ S, φ p (atPlace F G (.inr p) y)) x

end Factorization

section Charts

variable (F : Type) [Field F] [NumberField F] (A : Type) [Ring A] [Algebra F A]
  [FiniteDimensional F A]

/-- The points of the unit group scheme `FiniteAlgebraUnits.groupScheme (Module.finBasis F A)`
of `A` over the completion `F_p` at a finite place `p`, identified with the units of
`F_p ⊗[F] A` by `FiniteAlgebraUnits.affinePointsEquiv`. -/
def finiteAlgebraPlaceUnitEquiv (p : Langlands.Global.FinitePlace F) :
    PlaceGroupPoints F (FiniteAlgebraUnits.groupScheme (Module.finBasis F A)) (.inr p) ≃*
      (FiniteCompletion F p ⊗[F] A)ˣ :=
  FiniteAlgebraUnits.affinePointsEquiv (Module.finBasis F A) (placeCompletion F (.inr p))

/-- The archimedean points of the unit group scheme
`FiniteAlgebraUnits.groupScheme (Module.finBasis F A)` of `A`, its points over
`InfiniteAdeleRing F = F ⊗ ℝ`, identified with the units of `InfiniteAdeleRing F ⊗[F] A` by
`FiniteAlgebraUnits.affinePointsEquiv`. -/
def finiteAlgebraInfiniteUnitEquiv :
    InfiniteAdelicGroupPoints F (FiniteAlgebraUnits.groupScheme (Module.finBasis F A)) ≃*
      (InfiniteAdeleRing F ⊗[F] A)ˣ :=
  FiniteAlgebraUnits.affinePointsEquiv (Module.finBasis F A)
    (CommAlgCat.of F (InfiniteAdeleRing F))

end Charts

local instance divisionProductComparisonIsAffine (F : Type) [Field F] (n : ℕ) :
    IsAffine (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of F)

local instance divisionProductComparisonSmooth (F : Type) [Field F] (n : ℕ) :
    Smooth (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement (Fin n) (CommRingCat.of F)

/-- The Borel σ-algebra on `GL_n(F_p)` at a finite place `p`. -/
local instance divisionProductComparisonMeasurable (F : Type) [Field F] [NumberField F]
    (n : ℕ) (p : Langlands.Global.FinitePlace F) :
    MeasurableSpace (GeneralLinear n (FiniteCompletion F p)) :=
  borel _

local instance divisionProductComparisonBorel (F : Type) [Field F] [NumberField F] (n : ℕ)
    (p : Langlands.Global.FinitePlace F) :
    BorelSpace (GeneralLinear n (FiniteCompletion F p)) :=
  ⟨rfl⟩

set_option hygiene false in
/-- The `GL_n` group scheme over `E`, for the bound variables `E` and `n`. -/
local notation "GLₙ" => GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of E)

set_option hygiene false in
/-- The unit group scheme `G'` of `A`, for the bound variables `E` and `A`. -/
local notation "Gₐ" => FiniteAlgebraUnits.groupScheme (Module.finBasis E A)

/-- The trace comparison between `G = GL_n` and the unit group `G' = Aˣ` of a central division
algebra `A` of dimension `n²` over a number field `E`, for restricted tensor products of
locally matching test functions.

Let `A` be a finite-dimensional central `E`-algebra with `finrank E A = n²` and let `p₁ ≠ p₂` be
finite places of `E`. At `p_j` let `Δ_j` be a central division algebra over `E_{p_j}` with its
module topology and `t_j : E_{p_j} ⊗[E] A ≃ Δ_j` an `E_{p_j}`-algebra isomorphism, so that
`G'(E_{p_j}) ≅ Δ_jˣ` (`A` is then a division algebra, since `A` embeds in `E_{p₁} ⊗[E] A`);
let `μ_j` and `μ'_j` be Haar measures on
`GL_n(E_{p_j})` and on `Δ_jˣ` (Borel σ-algebras). Assume that `E_p ⊗[E] A ≅ M_n(E_p)` at every
finite place `p ≠ p₁, p₂` and that `E_∞ ⊗[E] A ≅ M_n(E_∞)`, `E_∞ = InfiniteAdeleRing E`.

Then there are a finite set `S₀` of finite places containing `p₁` and `p₂`, algebra
isomorphisms `s p : E_p ⊗[E] A ≃ M_n(E_p)` for `p ≠ p₁, p₂` and `sInf : E_∞ ⊗[E] A ≃ M_n(E_∞)`,
subgroups `U' i` of `G'(E_i)` forming a uniformly integral family, compact and open at every
finite place, containing the component `x_p` of every `x ∈ G'(𝔸_E)` at almost every finite `p`,
with `U' p = (s p)⁻¹(GL_n(O_p))` (through `finiteAlgebraPlaceUnitEquiv`) for finite `p ∉ S₀`,
and a real `c > 0` with the following property. Let `S ⊇ S₀` be a finite set of finite places, let
`fInf` be a smooth compactly supported function on `GL_n(E_∞)` and `floc p` a locally constant
compactly supported function on `GL_n(E_p)` for every finite `p`, and let `f'_j` be a locally
constant compactly supported function on `Δ_jˣ`. Assume that `floc p_j` is supported in the
regular elliptic set, `f'_j` in the regular set, and that `floc p_j` and `f'_j` match for
`μ_j`, `μ'_j` (`AreMatching`). Let `φ' p` be functions on `G'(E_p)` with
`φ' p_j = f'_j ∘ t_j` and `φ' p = floc p ∘ s p` for `p ∈ S`, `p ≠ p₁, p₂` (through the charts).
Let `f` on `G(𝔸_E)` be the restricted tensor product of `fInf`, of `floc p` at `p ∈ S` and of
the indicator functions of `GL_n(O_p)` at `p ∉ S`, and `f'` on `G'(𝔸_E)` that of `fInf ∘ sInf`,
of `φ' p` at `p ∈ S` and of the indicator functions of `U' p` at `p ∉ S`
(`IsAdelicInfiniteFactorization`). Then `f` and `f'` are smooth compactly supported test
functions (`IsAdelicTestFunction`), they are integrable, `R'(f') = canonicalIntegratedAction`
on `L²([G'])` and `R_disc(f) = canonicalDiscreteIntegratedAction` on `L²_disc([G])` are trace
class, and `tr R'(f') = c · tr R_disc(f)`. -/
def DivisionAlgebraProductTraceComparisonStatement : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (A : Type) [Ring A] [Algebra E A]
    [FiniteDimensional E A] [Algebra.IsCentral E A] (n : ℕ),
    Module.finrank E A = n ^ 2 →
    ∀ (hD : IsConnectedReductive Gₐ) (hG : IsConnectedReductive GLₙ)
      (p₁ p₂ : Langlands.Global.FinitePlace E), p₁ ≠ p₂ →
    ∀ (Δ₁ : Type) [DivisionRing Δ₁] [Algebra (FiniteCompletion E p₁) Δ₁]
      [FiniteDimensional (FiniteCompletion E p₁) Δ₁]
      [Algebra.IsCentral (FiniteCompletion E p₁) Δ₁]
      [TopologicalSpace Δ₁] [IsModuleTopology (FiniteCompletion E p₁) Δ₁]
      (t₁ : FiniteCompletion E p₁ ⊗[E] A ≃ₐ[FiniteCompletion E p₁] Δ₁)
      (Δ₂ : Type) [DivisionRing Δ₂] [Algebra (FiniteCompletion E p₂) Δ₂]
      [FiniteDimensional (FiniteCompletion E p₂) Δ₂]
      [Algebra.IsCentral (FiniteCompletion E p₂) Δ₂]
      [TopologicalSpace Δ₂] [IsModuleTopology (FiniteCompletion E p₂) Δ₂]
      (t₂ : FiniteCompletion E p₂ ⊗[E] A ≃ₐ[FiniteCompletion E p₂] Δ₂),
    haveI := IsModuleTopology.isTopologicalRing (FiniteCompletion E p₁) Δ₁
    haveI := IsModuleTopology.isTopologicalRing (FiniteCompletion E p₂) Δ₂
    letI : MeasurableSpace Δ₁ˣ := borel _
    haveI : BorelSpace Δ₁ˣ := ⟨rfl⟩
    letI : MeasurableSpace Δ₂ˣ := borel _
    haveI : BorelSpace Δ₂ˣ := ⟨rfl⟩
    ∀ (μ₁ : Measure (GeneralLinear n (FiniteCompletion E p₁))) [μ₁.IsHaarMeasure]
      (μ'₁ : Measure Δ₁ˣ) [μ'₁.IsHaarMeasure]
      (μ₂ : Measure (GeneralLinear n (FiniteCompletion E p₂))) [μ₂.IsHaarMeasure]
      (μ'₂ : Measure Δ₂ˣ) [μ'₂.IsHaarMeasure],
    (∀ p : Langlands.Global.FinitePlace E, p ≠ p₁ → p ≠ p₂ →
      Nonempty (FiniteCompletion E p ⊗[E] A ≃ₐ[FiniteCompletion E p]
        Matrix (Fin n) (Fin n) (FiniteCompletion E p))) →
    Nonempty (InfiniteAdeleRing E ⊗[E] A ≃ₐ[InfiniteAdeleRing E]
      Matrix (Fin n) (Fin n) (InfiniteAdeleRing E)) →
    ∃ (S₀ : Finset (Langlands.Global.FinitePlace E))
      (s : ∀ p : Langlands.Global.FinitePlace E, p ≠ p₁ → p ≠ p₂ →
        (FiniteCompletion E p ⊗[E] A ≃ₐ[FiniteCompletion E p]
          Matrix (Fin n) (Fin n) (FiniteCompletion E p)))
      (sInf : InfiniteAdeleRing E ⊗[E] A ≃ₐ[InfiniteAdeleRing E]
        Matrix (Fin n) (Fin n) (InfiniteAdeleRing E))
      (U' : ∀ i : Place E, Subgroup (PlaceGroupPoints E Gₐ i)) (c : ℝ),
      p₁ ∈ S₀ ∧ p₂ ∈ S₀ ∧ 0 < c ∧ IsUniformlyIntegral E Gₐ U' ∧
      (∀ x : AdelicGroupPoints E Gₐ,
        ∀ᶠ p : Langlands.Global.FinitePlace E in Filter.cofinite,
          atPlace E Gₐ (.inr p) x ∈ U' (.inr p)) ∧
      (∀ p : Langlands.Global.FinitePlace E,
        IsOpen (U' (.inr p) : Set (PlaceGroupPoints E Gₐ (.inr p))) ∧
          IsCompact (U' (.inr p) : Set (PlaceGroupPoints E Gₐ (.inr p)))) ∧
      (∀ (p : Langlands.Global.FinitePlace E) (h₁ : p ≠ p₁) (h₂ : p ≠ p₂), p ∉ S₀ →
        U' (.inr p) = (Langlands.GeneralLinearGroup.integralSubgroup (Fin n)
            (p.adicCompletionIntegers E).toSubring).comap
          ((finiteAlgebraPlaceUnitEquiv E A p).trans
            (Units.mapEquiv (s p h₁ h₂).toRingEquiv.toMulEquiv)).toMonoidHom) ∧
      ∀ S : Finset (Langlands.Global.FinitePlace E), S₀ ⊆ S →
      ∀ (fInf : ArchimedeanGL.SmoothCompactKernel E n)
        (floc : ∀ p : Langlands.Global.FinitePlace E,
          SchwartzBruhat (GeneralLinear n (FiniteCompletion E p)))
        (f'₁ : SchwartzBruhat Δ₁ˣ) (f'₂ : SchwartzBruhat Δ₂ˣ),
        IsEllipticSupported (floc p₁ : GeneralLinear n (FiniteCompletion E p₁) → ℂ) →
        IsEllipticSupported (floc p₂ : GeneralLinear n (FiniteCompletion E p₂) → ℂ) →
        IsDivisionRegularSupported (FiniteCompletion E p₁) Δ₁ (f'₁ : Δ₁ˣ → ℂ) →
        IsDivisionRegularSupported (FiniteCompletion E p₂) Δ₂ (f'₂ : Δ₂ˣ → ℂ) →
        AreMatching μ₁ μ'₁ (floc p₁ : GeneralLinear n (FiniteCompletion E p₁) → ℂ)
          (f'₁ : Δ₁ˣ → ℂ) →
        AreMatching μ₂ μ'₂ (floc p₂ : GeneralLinear n (FiniteCompletion E p₂) → ℂ)
          (f'₂ : Δ₂ˣ → ℂ) →
      ∀ (φ' : ∀ p : Langlands.Global.FinitePlace E, PlaceGroupPoints E Gₐ (.inr p) → ℂ),
        (∀ x : PlaceGroupPoints E Gₐ (.inr p₁), φ' p₁ x =
          f'₁ (Units.mapEquiv t₁.toRingEquiv.toMulEquiv (finiteAlgebraPlaceUnitEquiv E A p₁ x))) →
        (∀ x : PlaceGroupPoints E Gₐ (.inr p₂), φ' p₂ x =
          f'₂ (Units.mapEquiv t₂.toRingEquiv.toMulEquiv (finiteAlgebraPlaceUnitEquiv E A p₂ x))) →
        (∀ p ∈ S, ∀ (h₁ : p ≠ p₁) (h₂ : p ≠ p₂) (x : PlaceGroupPoints E Gₐ (.inr p)),
          φ' p x = floc p (Units.mapEquiv (s p h₁ h₂).toRingEquiv.toMulEquiv
            (finiteAlgebraPlaceUnitEquiv E A p x))) →
      ∀ (f : AdelicGroupPoints E GLₙ → ℂ) (f' : AdelicGroupPoints E Gₐ → ℂ),
        IsAdelicInfiniteFactorization E GLₙ S
          (fun x => fInf.1.1 (GeneralLinearGroupPoints.infiniteEquiv E n x))
          (fun p x => floc p (localGLEquiv E n (.inr p) x))
          (fun p => glIntegralSubgroup E n p) f →
        IsAdelicInfiniteFactorization E Gₐ S
          (fun x => fInf.1.1
            (Units.mapEquiv sInf.toRingEquiv.toMulEquiv (finiteAlgebraInfiniteUnitEquiv E A x)))
          φ' (fun p => U' (.inr p)) f' →
        IsAdelicTestFunction E GLₙ f ∧ IsAdelicTestFunction E Gₐ f' ∧
        ∃ (hf' : Integrable f' (Measure.haar : Measure (AdelicGroupPoints E Gₐ)))
          (hf : Integrable f (Measure.haar : Measure (AdelicGroupPoints E GLₙ))),
          IsTraceClass (canonicalIntegratedAction E Gₐ hD f' hf') ∧
          IsTraceClass (canonicalDiscreteIntegratedAction E GLₙ hG f hf) ∧
          operatorTrace (canonicalIntegratedAction E Gₐ hD f' hf') =
            (c : ℂ) * operatorTrace (canonicalDiscreteIntegratedAction E GLₙ hG f hf)

end Langlands.TraceFormula
