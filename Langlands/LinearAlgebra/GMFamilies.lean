import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # `(G, M)`-families

Arthur 2005, §17. The data are a finite-dimensional real inner product space `E` (the space `𝔞_0`
with a Weyl-invariant inner product) and a finite set `R ⊆ E` of root vectors (the roots of
`(G, A_0)`, through the inner product). A Levi subgroup `M ⊇ M_0` is recorded by its space
`𝔞_M ⊆ E`, an intersection of root hyperplanes (`IsLeviSpace`). For such `a = 𝔞_M`:

* `parabolics R a` is `𝓟(M)`, the chambers of `a`, each recorded by its set of positive roots;
* `faces R a` is `𝓕(M)`;
* `simpleRoots R a S` is `Δ_P` (as vectors of `a`), `theta R a S` is `θ_P`;
* `IsFamily R a c` says that `{c_P}` is a `(G, M)`-family, and `cM R a c` is
  `c_M(λ) = ∑_P c_P(λ) θ_P(λ)⁻¹`.

A point `λ ∈ i𝔞_M^*` is written `λ = iΛ` with `Λ : StrongDual ℝ a`.
-/

noncomputable section

open scoped RealInnerProductSpace ContDiff
open Classical

namespace Langlands.GMFamily

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- A finite set of root vectors of a root system in its span, possibly nonreduced: it omits `0`,
is stable under the orthogonal reflections `s_α`, and the numbers `2⟪β, α⟫/⟪α, α⟫` are
integers. -/
def IsRootSet (R : Finset E) : Prop :=
  (0 : E) ∉ R ∧
    (∀ α ∈ R, ∀ β ∈ R, β - (2 * ⟪β, α⟫ / ⟪α, α⟫) • α ∈ R) ∧
    ∀ α ∈ R, ∀ β ∈ R, ∃ n : ℤ, 2 * ⟪β, α⟫ / ⟪α, α⟫ = n

variable (R : Finset E)

/-- The flat of a point `h₀`: the common kernel of the roots vanishing at `h₀`. -/
def leviSpaceOf (h₀ : E) : Submodule ℝ E :=
  ⨅ α ∈ R.filter (fun α => ⟪α, h₀⟫ = 0), (ℝ ∙ α)ᗮ

/-- `a` is the space `𝔞_M` of a Levi subgroup `M ⊇ M_0`: an intersection of root hyperplanes,
written as the flat of one of its points. -/
def IsLeviSpace (a : Submodule ℝ E) : Prop :=
  ∃ h₀ : E, a = leviSpaceOf R h₀

/-- `𝔞_G`: the common kernel of all roots. -/
def centralSpace : Submodule ℝ E :=
  ⨅ α ∈ R, (ℝ ∙ α)ᗮ

variable (a : Submodule ℝ E)

/-- The restriction to `a` of the root `α`, as a vector of `a`: its orthogonal projection. -/
def restrictedRoot (α : E) : a :=
  a.orthogonalProjectionOnto α

/-- A point of `a` is regular if no root that is nonzero on `a` vanishes at it. -/
def IsRegular (h : E) : Prop :=
  h ∈ a ∧ ∀ α ∈ R, restrictedRoot a α ≠ 0 → ⟪α, h⟫ ≠ 0

/-- The roots positive at `h`. -/
def posSet (h : E) : Finset E :=
  R.filter fun α => 0 < ⟪α, h⟫

/-- `𝓟(M)`: the parabolic subgroups with Levi component `M`, that is, the chambers of `a = 𝔞_M`,
each recorded by its set of positive roots `posSet R h` at a regular point `h`. -/
def parabolics : Finset (Finset E) :=
  R.powerset.filter fun S => ∃ h, IsRegular R a h ∧ S = posSet R h

/-- `𝓕(M)`: the parabolic subgroups containing `M`, that is, the faces of the chambers of `a`,
each recorded by its set of positive roots at a point of the face. -/
def faces : Finset (Finset E) :=
  R.powerset.filter fun S => ∃ h ∈ a, S = posSet R h

/-- The restricted positive roots of `S`, as vectors of `a`. -/
def restrictedRoots (S : Finset E) : Finset a :=
  S.image (restrictedRoot a)

/-- `Δ_P`: the simple roots of `(P, A_M)`, the restricted positive roots that are not sums of two
restricted positive roots. -/
def simpleRoots (S : Finset E) : Finset a :=
  (restrictedRoots a S).filter fun v =>
    ¬ ∃ u ∈ restrictedRoots a S, ∃ w ∈ restrictedRoots a S, v = u + w

/-- The Euclidean volume `√det(⟪v_i, v_j⟫)` of the parallelepiped spanned by a finite family.
For a linearly independent family it is the covolume of the lattice the family spans in its
span, for the measure of the inner product; for a dependent family it is `0`. -/
def gramVolume {ι : Type*} [Fintype ι] (v : ι → E) : ℝ :=
  Real.sqrt (Matrix.det (Matrix.of fun i j => ⟪v i, v j⟫))

/-- `gramVolume(v)⁻¹ ∏_i λ(v_i)` at `λ = iΛ`, for a finite family `v` of vectors of `a`; for a
linearly independent family this is `vol(Z(v))⁻¹ ∏_i λ(v_i)`. -/
def thetaOf {ι : Type*} [Fintype ι] (v : ι → a) (Λ : StrongDual ℝ a) : ℂ :=
  ((gramVolume fun i => (v i : E) : ℝ) : ℂ)⁻¹ * ∏ i, (Complex.I * (Λ (v i) : ℂ))

/-- `θ_P(λ) = vol(𝔞_M^G / Z(Δ_P^∨))⁻¹ ∏_{α ∈ Δ_P} λ(α^∨)` at `λ = iΛ`, with the coroots `α^∨`
replaced by the vectors `simpleRoots a S` of the inner product, which are positive multiples of
them; `thetaOf_smul` shows that this does not change the value. -/
def theta (S : Finset E) (Λ : StrongDual ℝ a) : ℂ :=
  thetaOf a (fun v : simpleRoots a S => (v : a)) Λ

omit [FiniteDimensional ℝ E] in
/-- Rescaling the vectors by positive numbers multiplies the Gram volume by their product. -/
theorem gramVolume_smul {ι : Type*} [Fintype ι] (v : ι → E) (c : ι → ℝ)
    (hc : ∀ i, 0 < c i) : gramVolume (fun i => c i • v i) = (∏ i, c i) * gramVolume v := by
  have hmat : (Matrix.of fun i j => ⟪c i • v i, c j • v j⟫) =
      Matrix.diagonal c * Matrix.of (fun i j => ⟪v i, v j⟫) * Matrix.diagonal c := by
    ext i j
    simp [Matrix.mul_apply, Matrix.diagonal, real_inner_smul_left, real_inner_smul_right]
    ring
  have hprod : 0 ≤ ∏ i, c i := Finset.prod_nonneg fun i _ => (hc i).le
  rw [gramVolume, gramVolume, hmat, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal,
    mul_comm (∏ i, c i) _, mul_assoc, ← sq, Real.sqrt_mul' _ (sq_nonneg _), Real.sqrt_sq hprod,
    mul_comm]

omit [FiniteDimensional ℝ E] in
/-- **Scale invariance of `θ`.** Rescaling the vectors by positive numbers does not change
`vol(Z(v))⁻¹ ∏ λ(v_i)`. So `θ_P` depends only on the rays of the coroots. -/
theorem thetaOf_smul {ι : Type*} [Fintype ι] (v : ι → a) (c : ι → ℝ)
    (hc : ∀ i, 0 < c i) (Λ : StrongDual ℝ a) :
    thetaOf a (fun i => c i • v i) Λ = thetaOf a v Λ := by
  have hv : gramVolume (fun i => ((c i • v i : a) : E)) =
      (∏ i, c i) * gramVolume (fun i => (v i : E)) :=
    gramVolume_smul (fun i => (v i : E)) c hc
  have hprod : (∏ i, c i) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => (hc i).ne'
  simp only [thetaOf, hv, map_smul, smul_eq_mul, Complex.ofReal_mul, Complex.ofReal_prod,
    mul_inv, mul_left_comm Complex.I, Finset.prod_mul_distrib]
  have hprodC : ((∏ i, c i : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hprod
  rw [Complex.ofReal_prod] at hprodC
  field_simp

/-- Two chambers `S`, `S'` of `a` are adjacent along `v`: `v ∈ Δ_P`, `-v ∈ Δ_{P'}`, and the
chambers lie on the same side of every root hyperplane other than that of `v`. -/
def IsAdjacentAlong (S S' : Finset E) (v : a) : Prop :=
  v ∈ simpleRoots a S ∧ -v ∈ simpleRoots a S' ∧
    ∀ α ∈ R, (∀ t : ℝ, restrictedRoot a α ≠ t • v) → (α ∈ S ↔ α ∈ S')

/-- Arthur's `(G, M)`-family: smooth functions `c_P` on `i𝔞_M^*`, `P ∈ 𝓟(M)`, with
`c_P(λ) = c_{P'}(λ)` for adjacent `P, P'` and `λ` in the hyperplane spanned by the common wall
of their chambers in `i𝔞_M^*`, that is, `λ(α^∨) = 0`. -/
def IsFamily (c : Finset E → StrongDual ℝ a → ℂ) : Prop :=
  (∀ S ∈ parabolics R a, ContDiff ℝ ∞ (c S)) ∧
    ∀ S ∈ parabolics R a, ∀ S' ∈ parabolics R a, ∀ v : a, IsAdjacentAlong R a S S' v →
      ∀ Λ : StrongDual ℝ a, Λ v = 0 → c S Λ = c S' Λ

/-- `c_M(λ) = ∑_{P ∈ 𝓟(M)} c_P(λ) θ_P(λ)⁻¹`, at `λ = iΛ`. -/
def cM (c : Finset E → StrongDual ℝ a → ℂ) (Λ : StrongDual ℝ a) : ℂ :=
  ∑ S ∈ parabolics R a, c S Λ * (theta a S Λ)⁻¹

/-- The product family `(cd)_P = c_P d_P`. -/
def familyMul (c d : Finset E → StrongDual ℝ a → ℂ) : Finset E → StrongDual ℝ a → ℂ :=
  fun S Λ => c S Λ * d S Λ

section Faces

/-- The roots of the Levi component `M_Q` of a face `Q`: those that are neither positive nor
negative on `Q`. -/
def leviRoots (Q : Finset E) : Finset E :=
  R.filter fun α => α ∉ Q ∧ -α ∉ Q

/-- `𝔞_Q ⊆ 𝔞_M` for a face `Q ∈ 𝓕(M)`: the points of `a` on which the roots of `M_Q` vanish. -/
def faceSpace (Q : Finset E) : Submodule ℝ E :=
  a ⊓ ⨅ α ∈ leviRoots R Q, (ℝ ∙ α)ᗮ

/-- `𝓛(M)`: the spaces `𝔞_L` of the Levi subgroups `L ⊇ M`. -/
def leviSpaces : Finset (Submodule ℝ E) :=
  (faces R a).image (faceSpace R a)

/-- For `b ⊆ a`, the projection `λ ↦ λ_b` of `i𝔞_M^*` onto `i𝔞_b^* ⊆ i𝔞_M^*`, through the
orthogonal projection of `a` onto `b`. -/
def paramProj (b : Submodule ℝ E) (Λ : StrongDual ℝ a) : StrongDual ℝ a :=
  Λ.comp (a.orthogonalProjectionOnto.comp (b.starProjection.comp a.subtypeL))

/-- For `b ⊆ a`, the restriction of `Λ` to `b`. -/
def restrictParam (b : Submodule ℝ E) (Λ : StrongDual ℝ a) : StrongDual ℝ b :=
  Λ.comp (a.orthogonalProjectionOnto.comp b.subtypeL)

/-- For `a ⊆ a₁`, the extension of `Λ ∈ 𝔞_M^*` to `𝔞_{M₁}^*` through the orthogonal projection
`𝔞_{M₁} → 𝔞_M`. -/
def extendParam (a₁ : Submodule ℝ E) (Λ : StrongDual ℝ a) : StrongDual ℝ a₁ :=
  Λ.comp (a.orthogonalProjectionOnto.comp a₁.subtypeL)

/-- The restriction `c_Q(λ) = c_P(λ)`, `P ∈ 𝓟(M)`, `P ⊆ Q`, of a `(G, M)`-family to a
`(G, M_Q)`-family, evaluated at `λ_Q`. The group `P` is chosen; for a `(G, M)`-family the value
does not depend on the choice (Arthur 2005, p.97). -/
def famRestrict (c : Finset E → StrongDual ℝ a → ℂ) (Q : Finset E) (Λ : StrongDual ℝ a) : ℂ :=
  if h : ∃ P ∈ parabolics R a, Q ⊆ P then c h.choose (paramProj a (faceSpace R a Q) Λ) else 0

/-- `c_M^Q(λ) = ∑_{R ∈ 𝓟^{M_Q}(M)} c_{Q(R)}(λ) θ_R^Q(λ)⁻¹` for `Q ∈ 𝓕(M)`, where `Q(R) ∈ 𝓟(M)`
is the group contained in `Q` with `Q(R) ∩ M_Q = R`; its positive roots are `Q ∪ R`. -/
def cQM (c : Finset E → StrongDual ℝ a → ℂ) (Q : Finset E) (Λ : StrongDual ℝ a) : ℂ :=
  ∑ S ∈ parabolics (leviRoots R Q) a, c (Q ∪ S) Λ * (theta a S Λ)⁻¹

end Faces

section Coweights

variable {b : Submodule ℝ E}

/-- The Gram matrix of a finite set of vectors of `b`. -/
def gram (s : Finset b) : Matrix s s ℝ :=
  Matrix.of fun x y => ⟪((x : b) : E), ((y : b) : E)⟫

/-- The coweight `ϖ_v^∨ = ∑_u (G⁻¹)_{vu} u` dual to the simple root `v ∈ s`, `G = gram s`:
`⟪u, ϖ_v^∨⟫ = δ_{uv}` for `u ∈ s` when `s` is linearly independent. -/
def coweight (s : Finset b) (v : s) : b :=
  ∑ u : s, (gram s)⁻¹ v u • (u : b)

/-- `θ̂_P^Q(λ) = vol(𝔞_P^Q / Z((Δ̂_P^Q)^∨))⁻¹ ∏_{ϖ ∈ Δ̂_P^Q} λ(ϖ^∨)` at `λ = iΛ`, for the chamber
`S` of `b = 𝔞_P` in the arrangement of the roots of `M_Q`; the coweights are dual to
`Δ_P^Q = simpleRoots b S`. -/
def thetaHat (S : Finset E) (Λ : StrongDual ℝ b) : ℂ :=
  ((gramVolume fun v : simpleRoots b S => ((coweight (simpleRoots b S) v : b) : E) : ℝ) : ℂ)⁻¹ *
    ∏ v : simpleRoots b S, (Complex.I * (Λ (coweight (simpleRoots b S) v) : ℂ))

end Coweights

/-- Arthur's (17.7) for `Q ∈ 𝓕(M)` and the `(G, M_Q)`-family `{d_{Q'}}` restricted from `d`:
`d'_Q(λ) = ∑_{Q' ⊇ Q} (−1)^{dim(A_Q/A_{Q'})} d_{Q'}(λ_{Q'}) θ̂_Q^{Q'}(λ)⁻¹ θ_{Q'}(λ_{Q'})⁻¹`. -/
def dPrime (d : Finset E → StrongDual ℝ a → ℂ) (Q : Finset E) (Λ : StrongDual ℝ a) : ℂ :=
  ∑ Q' ∈ (faces R a).filter (· ⊆ Q),
    (-1 : ℂ) ^ (Module.finrank ℝ (faceSpace R a Q) - Module.finrank ℝ (faceSpace R a Q')) *
      famRestrict R a d Q' Λ *
      (thetaHat (Q ∩ leviRoots R Q') (restrictParam a (faceSpace R a Q) Λ))⁻¹ *
      (theta (faceSpace R a Q') Q' (restrictParam a (faceSpace R a Q') Λ))⁻¹

section Measures

/-- The factor `d` with `dV = d · (dU × dW)` for the map `U ⊕ W → V`, `(u, w) ↦ u + w`, and the
Euclidean measures: the volume of the parallelepiped spanned by orthonormal bases of `U` and
`W`. It is `0` unless `dim U + dim W = dim V`; for `U, W ⊆ V` it is then nonzero exactly when the
map is an isomorphism. -/
def measureFactor (U W V : Submodule ℝ E) : ℝ :=
  if Module.finrank ℝ U + Module.finrank ℝ W = Module.finrank ℝ V then
    gramVolume (Sum.elim (fun i => ((stdOrthonormalBasis ℝ U i : U) : E))
      fun j => ((stdOrthonormalBasis ℝ W j : W) : E))
  else 0

/-- `d_M^G(L₁, L₂)` (Arthur 2005, p.101): the factor for `𝔞_M^{L₁} ⊕ 𝔞_M^{L₂} → 𝔞_M^G`, `0` unless
this map is an isomorphism. -/
def dCoeff (L₁ L₂ : Submodule ℝ E) : ℝ :=
  measureFactor (a ⊓ L₁ᗮ) (a ⊓ L₂ᗮ) (a ⊓ (centralSpace R)ᗮ)

/-- `d_{M₁}^G(M, L₁)` for `a = 𝔞_M ⊆ a₁ = 𝔞_{M₁}` and `z = 𝔞_G` (Arthur 2005, pp.99–100): the
factor for `𝔞_{M₁}^M ⊕ 𝔞_{M₁}^{L₁} → 𝔞_{M₁}^G`, `0` unless this map is an isomorphism. -/
def dDescent (z a₁ L₁ : Submodule ℝ E) : ℝ :=
  measureFactor (a₁ ⊓ aᗮ) (a₁ ⊓ L₁ᗮ) (a₁ ⊓ zᗮ)

/-- The section `L₁ ↦ Q₁ ∈ 𝓟(L₁)` of Lemma 17.5 attached to `ξ ∈ 𝔞_{M₁}^M`, with `z = 𝔞_G`: the
chamber of `𝔞_{L₁}` containing the point of `(ξ + 𝔞_M^G) ∩ 𝔞_{L₁}^G`. -/
def descentSection (z : Submodule ℝ E) (ξ : E) (L₁ : Submodule ℝ E) : Finset E :=
  if h : ∃ p, p ∈ L₁ ⊓ zᗮ ∧ p - ξ ∈ a ⊓ zᗮ then posSet R h.choose else ∅

/-- The section `(L₁, L₂) ↦ (Q₁, Q₂)` of Lemma 17.6 attached to `ξ ∈ 𝔞_M^G`: writing
`ξ = ½ξ₁ − ½ξ₂` with `ξᵢ ∈ 𝔞_{Lᵢ}^G`, `Qᵢ` is the chamber of `𝔞_{Lᵢ}` containing `ξᵢ`. -/
def splittingSection (ξ : E) (L₁ L₂ : Submodule ℝ E) : Finset E × Finset E :=
  if h : ∃ ξ₁ ξ₂, ξ₁ ∈ L₁ ⊓ (centralSpace R)ᗮ ∧ ξ₂ ∈ L₂ ⊓ (centralSpace R)ᗮ ∧
      (2 : ℝ) • ξ = ξ₁ - ξ₂ then
    (posSet R h.choose, posSet R h.choose_spec.choose)
  else (∅, ∅)

end Measures

/-- The `(G, M)`-family `c_P(λ) = c_{P₁}(λ)` induced on `a = 𝔞_M ⊆ a₁ = 𝔞_{M₁}` by a
`(G, M₁)`-family, for `P₁ ∈ 𝓟(M₁)` with `P₁ ⊆ P` (positive roots of `P` among those of `P₁`) and
`λ ∈ i𝔞_M^* ⊆ i𝔞_{M₁}^*`. The group `P₁` is chosen; the value does not depend on the choice
(Arthur 2005, p.99). -/
def inducedFamily (a₁ : Submodule ℝ E) (c₁ : Finset E → StrongDual ℝ a₁ → ℂ) :
    Finset E → StrongDual ℝ a → ℂ :=
  fun S Λ => if h : ∃ S₁ ∈ parabolics R a₁, S ⊆ S₁ then c₁ h.choose (extendParam a a₁ Λ) else 0

end Langlands.GMFamily
