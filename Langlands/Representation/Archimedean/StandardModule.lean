import Langlands.Representation.Archimedean.GeneralLinear
import Langlands.Representation.FiniteVectors
import Langlands.Representation.Whittaker.Algebraic
import Langlands.Representation.Whittaker.Iwasawa
import Langlands.LocalFactor.ArchimedeanPresentation
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex

/-!
# Standard modules of `GL_n(ℝ)` and `GL_n(ℂ)` and their parameters

A representation by bounded operators has the standard-module parameter of a list of the
Library's Weil-group blocks when its smooth `K`-finite vectors are isomorphic, as a
`(𝔤, K)`-module, to the `K`-finite functions of the standard module of the blocks. For a
generic irreducible representation this is having the sum of the blocks as Langlands
parameter. The standard module is realized inside a principal series of smooth functions on
`GL_n(F)` under right translation. Over `ℂ` it is the whole principal series of the
characters of the blocks. Over `ℝ`, a two-dimensional block contributes two characters of the
diagonal torus and the vanishing of the Fourier coefficients of low weight along the
rotations in its two coordinates, which cuts out the discrete series in the principal series
of `GL_2(ℝ)`.
-/

noncomputable section

open scoped Manifold ContDiff Matrix.Norms.Operator

namespace Langlands.Archimedean

open Langlands.GeneralLinear Langlands.HarmonicAnalysis Langlands.LocalFactor.Archimedean

-- As in `GeneralLinear`: the charts on units need reduction through the normed-ring
-- instances of matrices.
set_option backward.isDefEq.respectTransparency false

universe u𝔤 uH uG u𝔤' uH' uG' uE uW uF

/-! ## `K`-finite vectors and infinitesimal equivalence -/

section Generic

variable {𝔤 : Type u𝔤} [NormedAddCommGroup 𝔤] [NormedSpace ℝ 𝔤]
  {H : Type uH} [TopologicalSpace H] (I : ModelWithCorners ℝ 𝔤 H)
  {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace H G]
  {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The `K`-finite vectors of a representation: the vectors whose `K`-orbit spans a
finite-dimensional subspace. -/
def kFiniteVectors {W : Type uW} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G W)
    (K : Subgroup G) : Submodule ℂ W :=
  (FiniteVectors.subrepresentation (ρ.comp K.subtype)).toSubmodule

omit [TopologicalSpace G] in
theorem mem_kFiniteVectors_iff {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ G W) (K : Subgroup G) (v : W) :
    v ∈ kFiniteVectors ρ K ↔
      FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : K => ρ (k : G) v)) :=
  Iff.rfl

/-- The linear representation underlying a representation by bounded operators. -/
abbrev linearRepresentation (π : G →* (E →L[ℂ] E)) : Representation ℂ G E :=
  ContinuousLinearMap.toLinearMapRingHom.toMonoidHom.comp π

/-- The smooth `K`-finite vectors of `π`, the space of its `(𝔤, K)`-module. -/
def kFiniteSmoothVectors (π : G →* (E →L[ℂ] E)) (K : Subgroup G) : Submodule ℂ E :=
  smoothVectors I π ⊓ kFiniteVectors (linearRepresentation π) K

theorem mem_kFiniteSmoothVectors_iff (π : G →* (E →L[ℂ] E)) (K : Subgroup G) (v : E) :
    v ∈ kFiniteSmoothVectors I π K ↔
      IsSmoothVector I π v ∧
        FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : K => π (k : G) v)) :=
  Iff.rfl

/-- The `K`-finite functions in a space `V` of functions on `G`, for right translation. -/
def kFiniteFunctions (V : Submodule ℂ (G → ℂ)) (K : Subgroup G) : Submodule ℂ (G → ℂ) :=
  V ⊓ kFiniteVectors (Whittaker.rightTranslation ℂ G) K

/-- The derivative of `f` along right translation in the tangent direction `X` at the
identity: `(R(X) f)(g)` is the derivative at `1` of `h ↦ f(g h)` applied to `X`. -/
def rightDerivative (X : 𝔤) (f : G → ℂ) : G → ℂ :=
  fun g => mfderiv I 𝓘(ℝ, ℂ) (fun h => f (g * h)) 1 X

/-- Infinitesimal equivalence of `π` with a space `V` of functions under right translation: a
linear isomorphism `e` from the smooth `K`-finite vectors of `π` onto the `K`-finite functions
of `V` such that, for `k ∈ K` and `X ∈ 𝔤`, the vectors `π(k)v` and `dπ(X)v` are again smooth
and `K`-finite, and `e` carries them to the right translate by `k` and the right derivative
along `X` of `e v`. -/
def IsInfinitesimallyEquivalent (π : G →* (E →L[ℂ] E)) (K : Subgroup G)
    (V : Submodule ℂ (G → ℂ)) : Prop :=
  ∃ e : kFiniteSmoothVectors I π K ≃ₗ[ℂ] kFiniteFunctions V K,
    (∀ (k : K) (v : kFiniteSmoothVectors I π K),
      ∃ hv : π (k : G) v ∈ kFiniteSmoothVectors I π K,
        (e ⟨π (k : G) v, hv⟩ : G → ℂ) =
          Whittaker.rightTranslation ℂ G (k : G) (e v)) ∧
    ∀ (X : 𝔤) (v : kFiniteSmoothVectors I π K),
      ∃ hv : lieDerivative I π X v ∈ kFiniteSmoothVectors I π K,
        (e ⟨lieDerivative I π X v, hv⟩ : G → ℂ) = rightDerivative I X (e v)

end Generic

section PairFunctions

variable {𝔤 : Type u𝔤} [NormedAddCommGroup 𝔤] [NormedSpace ℝ 𝔤]
  {H : Type uH} [TopologicalSpace H] (I : ModelWithCorners ℝ 𝔤 H)
  {G : Type uG} [TopologicalSpace G] [ChartedSpace H G]
  {𝔤' : Type u𝔤'} [NormedAddCommGroup 𝔤'] [NormedSpace ℝ 𝔤']
  {H' : Type uH'} [TopologicalSpace H'] (I' : ModelWithCorners ℝ 𝔤' H')
  {G' : Type uG'} [TopologicalSpace G'] [ChartedSpace H' G']

/-- The external product of spaces of functions: jointly smooth functions on `G × G'` all of
whose slices `f(·, g')` lie in `V` and `f(g, ·)` lie in `V'`. -/
def pairFunctions (V : Submodule ℂ (G → ℂ)) (V' : Submodule ℂ (G' → ℂ)) :
    Submodule ℂ (G × G' → ℂ) where
  carrier := {f | ContMDiff (I.prod I') 𝓘(ℝ, ℂ) ∞ f ∧
    (∀ g' : G', (fun g => f (g, g')) ∈ V) ∧ ∀ g : G, (fun g' => f (g, g')) ∈ V'}
  zero_mem' := ⟨contMDiff_const, fun _ => V.zero_mem, fun _ => V'.zero_mem⟩
  add_mem' hf₁ hf₂ :=
    ⟨hf₁.1.add hf₂.1, fun g' => V.add_mem (hf₁.2.1 g') (hf₂.2.1 g'),
      fun g => V'.add_mem (hf₁.2.2 g) (hf₂.2.2 g)⟩
  smul_mem' c _ hf :=
    ⟨((c • ContinuousLinearMap.id ℂ ℂ).restrictScalars ℝ).contDiff.contMDiff.comp hf.1,
      fun g' => V.smul_mem c (hf.2.1 g'), fun g => V'.smul_mem c (hf.2.2 g)⟩

theorem mem_pairFunctions_iff (V : Submodule ℂ (G → ℂ)) (V' : Submodule ℂ (G' → ℂ))
    (f : G × G' → ℂ) :
    f ∈ pairFunctions I I' V V' ↔
      ContMDiff (I.prod I') 𝓘(ℝ, ℂ) ∞ f ∧
        (∀ g' : G', (fun g => f (g, g')) ∈ V) ∧ ∀ g : G, (fun g' => f (g, g')) ∈ V' :=
  Iff.rfl

end PairFunctions

/-! ## Principal series of `GL_N(F)` -/

section PrincipalSeries

variable (F : Type uF) [RCLike F]

/-- The character `diag(a) ↦ ∏ᵢ χᵢ(aᵢ) |aᵢ|_F^((N-1)/2 - i)` of the diagonal torus, with
`|x|_F = ‖x‖^[F:ℝ]` and positions `i = 0, …, N-1`: the characters `χᵢ` times the square root
of the modulus character of the upper triangular Borel subgroup. -/
def principalSeriesCharacter (N : ℕ) (χ : ℕ → Fˣ → ℂ) (a : Fin N → Fˣ) : ℂ :=
  ∏ i : Fin N, χ i (a i) *
    ((‖(a i : F)‖ ^ Module.finrank ℝ F : ℝ) : ℂ) ^ (((N : ℂ) - 1) / 2 - ((i : ℕ) : ℂ))

/-- The smooth principal series of the characters `χ 0, …, χ (N-1)`: real `C^∞` functions on
`GL_N(F)` with `f(diag(a) u g) = principalSeriesCharacter F N χ a · f(g)` for `u` upper
unipotent. -/
def principalSeries (N : ℕ) (χ : ℕ → Fˣ → ℂ) :
    Submodule ℂ (Langlands.GeneralLinear N F → ℂ) where
  carrier := {f | ContMDiff (matrixModel F N) 𝓘(ℝ, ℂ) ∞ f ∧
    ∀ (a : Fin N → Fˣ) (u : upperUnipotent N F) (g : Langlands.GeneralLinear N F),
      f ((Iwasawa.diagonalUnits a : Langlands.GeneralLinear N F) *
          (u : Langlands.GeneralLinear N F) * g) =
        principalSeriesCharacter F N χ a * f g}
  zero_mem' := ⟨contMDiff_const, fun _ _ _ => by simp⟩
  add_mem' {f₁ f₂} hf₁ hf₂ :=
    ⟨hf₁.1.add hf₂.1, fun a u g => by
      change f₁ _ + f₂ _ = _ * (f₁ g + f₂ g)
      rw [hf₁.2 a u g, hf₂.2 a u g, mul_add]⟩
  smul_mem' c f hf :=
    ⟨((c • ContinuousLinearMap.id ℂ ℂ).restrictScalars ℝ).contDiff.contMDiff.comp hf.1,
      fun a u g => by
        change c * f _ = _ * (c * f g)
        rw [hf.2 a u g]
        ring⟩

theorem mem_principalSeries_iff (N : ℕ) (χ : ℕ → Fˣ → ℂ)
    (f : Langlands.GeneralLinear N F → ℂ) :
    f ∈ principalSeries F N χ ↔
      ContMDiff (matrixModel F N) 𝓘(ℝ, ℂ) ∞ f ∧
        ∀ (a : Fin N → Fˣ) (u : upperUnipotent N F) (g : Langlands.GeneralLinear N F),
          f ((Iwasawa.diagonalUnits a : Langlands.GeneralLinear N F) *
              (u : Langlands.GeneralLinear N F) * g) =
            principalSeriesCharacter F N χ a * f g :=
  Iff.rfl

end PrincipalSeries

/-! ## Real standard modules -/

section Real

/-- The first character `x ↦ sgn(x)^(|m|+1) |x|^(t + |m|/2)` attached to the real induction
of the complex character `(z/|z|)^m |z|^(2t)`. -/
def realInducedFirstCharacter (d : ComplexCharacterData) (x : ℝˣ) : ℂ :=
  (((x : ℝ) / |(x : ℝ)| : ℝ) : ℂ) ^ (d.weight.natAbs + 1) *
    ((|(x : ℝ)| : ℝ) : ℂ) ^ (d.exponent + (d.weight.natAbs : ℂ) / 2)

/-- The second character `x ↦ |x|^(t - |m|/2)` attached to the real induction of the complex
character `(z/|z|)^m |z|^(2t)`. -/
def realInducedSecondCharacter (d : ComplexCharacterData) (x : ℝˣ) : ℂ :=
  ((|(x : ℝ)| : ℝ) : ℂ) ^ (d.exponent - (d.weight.natAbs : ℂ) / 2)

/-- The character at each diagonal position of the blocks in order: a real character block
occupies one position, a real induction two. Positions past the end get the trivial
character. -/
def realPositionCharacter : List RealBlock → ℕ → ℝˣ → ℂ
  | [], _ => fun _ => 1
  | .character d :: _, 0 => fun x => (d.character x : ℂ)
  | .character _ :: ds, p + 1 => realPositionCharacter ds p
  | .induced d :: _, 0 => realInducedFirstCharacter d
  | .induced d :: _, 1 => realInducedSecondCharacter d
  | .induced _ :: ds, p + 2 => realPositionCharacter ds p

/-- The real induction block whose first position is `p`, if any. -/
def realInducedBlockAt : List RealBlock → ℕ → Option ComplexCharacterData
  | [], _ => none
  | .character _ :: _, 0 => none
  | .character _ :: ds, p + 1 => realInducedBlockAt ds p
  | .induced d :: _, 0 => some d
  | .induced _ :: _, 1 => none
  | .induced _ :: ds, p + 2 => realInducedBlockAt ds p

/-- Both positions `p, p + 1` of an induction block lie inside the rank. -/
theorem realInducedBlockAt_lt : ∀ {ds : List RealBlock} {p : ℕ} {d : ComplexCharacterData},
    realInducedBlockAt ds p = some d → p + 1 < realRank ds
  | [], _, _, h => by simp [realInducedBlockAt] at h
  | .character _ :: _, 0, _, h => by simp [realInducedBlockAt] at h
  | .character _ :: ds, p + 1, _, h => by
      have := realInducedBlockAt_lt (ds := ds) (p := p) h
      rw [realRank_cons]
      simp only [RealBlock.rank]
      omega
  | .induced _ :: ds, 0, _, _ => by
      rw [realRank_cons]
      simp only [RealBlock.rank]
      omega
  | .induced _ :: _, 1, _, h => by simp [realInducedBlockAt] at h
  | .induced _ :: ds, p + 2, _, h => by
      have := realInducedBlockAt_lt (ds := ds) (p := p) h
      rw [realRank_cons]
      simp only [RealBlock.rank]
      omega

/-- The generator `E_{p+1,p} - E_{p,p+1}` of the rotations in the coordinates `p, p + 1`. -/
def rotationGenerator (N p : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.of fun i j =>
    if (i : ℕ) = p + 1 ∧ (j : ℕ) = p then 1
    else if (i : ℕ) = p ∧ (j : ℕ) = p + 1 then -1 else 0

/-- The rotation `exp(θ (E_{p+1,p} - E_{p,p+1}))` by the angle `θ` in the coordinates
`p, p + 1`, with inverse `exp(-θ (E_{p+1,p} - E_{p,p+1}))`. -/
def blockRotation (N p : ℕ) (θ : ℝ) : Langlands.GeneralLinear N ℝ where
  val := NormedSpace.exp (θ • rotationGenerator N p)
  inv := NormedSpace.exp (-(θ • rotationGenerator N p))
  val_inv := by
    rw [← Matrix.exp_add_of_commute _ _ (Commute.refl _).neg_right, add_neg_cancel,
      NormedSpace.exp_zero]
  inv_val := by
    rw [← Matrix.exp_add_of_commute _ _ (Commute.refl _).neg_left, neg_add_cancel,
      NormedSpace.exp_zero]

@[simp]
theorem blockRotation_val (N p : ℕ) (θ : ℝ) :
    (blockRotation N p θ : Matrix (Fin N) (Fin N) ℝ) =
      NormedSpace.exp (θ • rotationGenerator N p) :=
  rfl

theorem continuous_blockRotation (N p : ℕ) : Continuous (blockRotation N p) := by
  rw [Units.continuous_iff]
  exact ⟨NormedSpace.exp_continuous.comp (continuous_id.smul continuous_const),
    NormedSpace.exp_continuous.comp (continuous_id.smul continuous_const).neg⟩

/-- The rotation generator is antisymmetric. -/
theorem rotationGenerator_mem_skewAdjoint (N p : ℕ) :
    rotationGenerator N p ∈ skewAdjoint (Matrix (Fin N) (Fin N) ℝ) := by
  rw [skewAdjoint.mem_iff]
  ext i j
  simp only [Matrix.star_apply, rotationGenerator, Matrix.of_apply, Matrix.neg_apply,
    star_trivial]
  split_ifs <;> first | omega | norm_num

/-- The rotations lie in the compact subgroup `O(N)`. -/
theorem blockRotation_mem_unitaryCompact (N p : ℕ) (θ : ℝ) :
    blockRotation N p θ ∈ unitaryCompact ℝ N :=
  NormedSpace.exp_mem_unitary_of_mem_skewAdjoint
    (skewAdjoint.smul_mem θ (rotationGenerator_mem_skewAdjoint N p))

/-- The `k`-th Fourier coefficient at `g` of `f` along the rotations in the coordinates
`p, p + 1`: `∫₀^{2π} f(r_p(θ) g) e^{-ikθ} dθ`. -/
def blockFourierCoefficient (N p : ℕ) (k : ℤ) (f : Langlands.GeneralLinear N ℝ → ℂ)
    (g : Langlands.GeneralLinear N ℝ) : ℂ :=
  ∫ θ in (0 : ℝ)..2 * Real.pi,
    f (blockRotation N p θ * g) * Complex.exp (-((k : ℂ) * (θ : ℂ) * Complex.I))

theorem intervalIntegrable_blockFourier {N : ℕ} {f : Langlands.GeneralLinear N ℝ → ℂ}
    (hf : Continuous f) (p : ℕ) (k : ℤ) (g : Langlands.GeneralLinear N ℝ) (a b : ℝ) :
    IntervalIntegrable (fun θ : ℝ =>
      f (blockRotation N p θ * g) * Complex.exp (-((k : ℂ) * (θ : ℂ) * Complex.I)))
      MeasureTheory.volume a b :=
  ((hf.comp ((continuous_blockRotation N p).mul continuous_const)).mul
    (Complex.continuous_exp.comp (by fun_prop))).intervalIntegrable a b

/-- The standard module of a list of real blocks on `GL_N(ℝ)`: the functions of the principal
series of the position characters whose Fourier coefficients of weight `|k| < |m|` along the
rotations in the coordinates of every induction block of weight `m` vanish. -/
def realStandardModule (N : ℕ) (ds : List RealBlock) :
    Submodule ℂ (Langlands.GeneralLinear N ℝ → ℂ) where
  carrier := {f | f ∈ principalSeries ℝ N (realPositionCharacter ds) ∧
    ∀ (p : ℕ) (d : ComplexCharacterData), realInducedBlockAt ds p = some d →
      ∀ k : ℤ, |k| < |d.weight| → ∀ g, blockFourierCoefficient N p k f g = 0}
  zero_mem' := ⟨(principalSeries ℝ N _).zero_mem, fun p d _ k _ g => by
    simp [blockFourierCoefficient]⟩
  add_mem' {f₁ f₂} hf₁ hf₂ := ⟨(principalSeries ℝ N _).add_mem hf₁.1 hf₂.1,
    fun p d hd k hk g => by
      have h₁ := hf₁.2 p d hd k hk g
      have h₂ := hf₂.2 p d hd k hk g
      unfold blockFourierCoefficient at h₁ h₂ ⊢
      simp only [Pi.add_apply, add_mul]
      rw [intervalIntegral.integral_add
        (intervalIntegrable_blockFourier hf₁.1.1.continuous p k g _ _)
        (intervalIntegrable_blockFourier hf₂.1.1.continuous p k g _ _), h₁, h₂, add_zero]⟩
  smul_mem' c f hf := ⟨(principalSeries ℝ N _).smul_mem c hf.1,
    fun p d hd k hk g => by
      have h := hf.2 p d hd k hk g
      unfold blockFourierCoefficient at h ⊢
      simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]
      rw [intervalIntegral.integral_const_mul]
      simp only [← mul_assoc] at h ⊢
      rw [h, mul_zero]⟩

theorem mem_realStandardModule_iff (N : ℕ) (ds : List RealBlock)
    (f : Langlands.GeneralLinear N ℝ → ℂ) :
    f ∈ realStandardModule N ds ↔
      f ∈ principalSeries ℝ N (realPositionCharacter ds) ∧
        ∀ (p : ℕ) (d : ComplexCharacterData), realInducedBlockAt ds p = some d →
          ∀ k : ℤ, |k| < |d.weight| → ∀ g, blockFourierCoefficient N p k f g = 0 :=
  Iff.rfl

end Real

/-! ## Complex standard modules -/

section Complex

/-- The character at each diagonal position: the character of the block at that position,
and the trivial character past the end. -/
def complexPositionCharacter : List ComplexCharacterData → ℕ → ℂˣ → ℂ
  | [], _ => fun _ => 1
  | d :: _, 0 => fun z => (d.character z : ℂ)
  | _ :: ds, p + 1 => complexPositionCharacter ds p

/-- The standard module of a list of complex character blocks on `GL_N(ℂ)`: the principal
series of their characters. -/
abbrev complexStandardModule (N : ℕ) (ds : List ComplexCharacterData) :
    Submodule ℂ (Langlands.GeneralLinear N ℂ → ℂ) :=
  principalSeries ℂ N (complexPositionCharacter ds)

end Complex

/-! ## Standard-module parameters -/

section Parameters

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- `π` has the standard-module parameter of the real blocks `ds`, in the given order: the
blocks have total rank `N` and `π` is infinitesimally equivalent, for `K = O(N)`, to their
standard module. For a generic irreducible `π`, whose standard module is irreducible, this
says that the Langlands parameter of `π` is the sum of the blocks; see the Markdown. -/
def HasRealParameter {N : ℕ} (π : Langlands.GeneralLinear N ℝ →* (E →L[ℂ] E))
    (ds : List RealBlock) : Prop :=
  realRank ds = N ∧
    IsInfinitesimallyEquivalent (matrixModel ℝ N) π (unitaryCompact ℝ N)
      (realStandardModule N ds)

/-- `π` has the standard-module parameter of the complex blocks `ds`, in the given order:
there are `N` blocks and `π` is infinitesimally equivalent, for `K = U(N)`, to their standard
module. For a generic irreducible `π` this says that the Langlands parameter of `π` is the
sum of the blocks; see the Markdown. -/
def HasComplexParameter {N : ℕ} (π : Langlands.GeneralLinear N ℂ →* (E →L[ℂ] E))
    (ds : List ComplexCharacterData) : Prop :=
  ds.length = N ∧
    IsInfinitesimallyEquivalent (matrixModel ℂ N) π (unitaryCompact ℂ N)
      (complexStandardModule N ds)

/-- `σ` on `GL_m(ℝ) × GL_n(ℝ)` has the standard-module parameter `(ds₁, ds₂)`, in the given
orders: the ranks are `m` and `n` and `σ` is infinitesimally equivalent, for
`K = O(m) × O(n)`, to the external product of the two standard modules. -/
def HasRealPairParameter {m n : ℕ}
    (σ : Langlands.GeneralLinear m ℝ × Langlands.GeneralLinear n ℝ →* (E →L[ℂ] E))
    (ds₁ ds₂ : List RealBlock) : Prop :=
  realRank ds₁ = m ∧ realRank ds₂ = n ∧
    IsInfinitesimallyEquivalent (pairModel ℝ m n) σ (pairCompact ℝ m n)
      (pairFunctions (matrixModel ℝ m) (matrixModel ℝ n) (realStandardModule m ds₁)
        (realStandardModule n ds₂))

/-- `σ` on `GL_m(ℂ) × GL_n(ℂ)` has the standard-module parameter `(ds₁, ds₂)`, in the given
orders: the numbers of blocks are `m` and `n` and `σ` is infinitesimally equivalent, for
`K = U(m) × U(n)`, to the external product of the two standard modules. -/
def HasComplexPairParameter {m n : ℕ}
    (σ : Langlands.GeneralLinear m ℂ × Langlands.GeneralLinear n ℂ →* (E →L[ℂ] E))
    (ds₁ ds₂ : List ComplexCharacterData) : Prop :=
  ds₁.length = m ∧ ds₂.length = n ∧
    IsInfinitesimallyEquivalent (pairModel ℂ m n) σ (pairCompact ℂ m n)
      (pairFunctions (matrixModel ℂ m) (matrixModel ℂ n) (complexStandardModule m ds₁)
        (complexStandardModule n ds₂))

end Parameters

end Langlands.Archimedean
