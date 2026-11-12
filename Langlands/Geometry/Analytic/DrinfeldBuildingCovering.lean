import Langlands.Geometry.Analytic.DrinfeldReduction

/-! # Vertices, facets and Harris's distinguished covering of Drinfeld's upper half space -/

noncomputable section

universe u v w

namespace Langlands.Analytic

open Set
open scoped ENNReal Pointwise

/-! ## The Goldman–Iwahori distance -/

namespace VectorNorm

variable {F : Type v} [NormedField F] {V : Type w} [AddCommGroup V] [Module F V]

/-- The supremum of `ν / μ`, in `[0, ∞]`. -/
def ratioSup (ν μ : VectorNorm F V) : ℝ≥0∞ := ⨆ x : V, ENNReal.ofReal (ν x / μ x)

/-- The multiplicative Goldman–Iwahori distance `sup(ν/μ) · sup(μ/ν)`; its logarithm is the
distance of the two norms in the building. -/
def distRatio (ν μ : VectorNorm F V) : ℝ≥0∞ := ratioSup ν μ * ratioSup μ ν

theorem distRatio_comm (ν μ : VectorNorm F V) : distRatio ν μ = distRatio μ ν :=
  mul_comm _ _

theorem ratioSup_of_eq_mul_left {ν ν' μ : VectorNorm F V} {c : ℝ} (hc : 0 < c)
    (h : ∀ x, ν' x = c * ν x) : ratioSup ν' μ = ENNReal.ofReal c * ratioSup ν μ := by
  unfold ratioSup
  rw [ENNReal.mul_iSup]
  refine iSup_congr fun x => ?_
  rw [h x, mul_div_assoc, ENNReal.ofReal_mul hc.le]

theorem ratioSup_of_eq_mul_right {ν ν' μ : VectorNorm F V} {c : ℝ} (hc : 0 < c)
    (h : ∀ x, ν' x = c * ν x) : ratioSup μ ν' = ENNReal.ofReal c⁻¹ * ratioSup μ ν := by
  unfold ratioSup
  rw [ENNReal.mul_iSup]
  refine iSup_congr fun x => ?_
  rw [h x, ← ENNReal.ofReal_mul (inv_pos.2 hc).le]
  congr 1
  ring

theorem distRatio_of_eq_mul_left {ν ν' μ : VectorNorm F V} {c : ℝ} (hc : 0 < c)
    (h : ∀ x, ν' x = c * ν x) : distRatio ν' μ = distRatio ν μ := by
  unfold distRatio
  rw [ratioSup_of_eq_mul_left hc h, ratioSup_of_eq_mul_right hc h]
  calc ENNReal.ofReal c * ratioSup ν μ * (ENNReal.ofReal c⁻¹ * ratioSup μ ν)
      = (ENNReal.ofReal c * ENNReal.ofReal c⁻¹) * (ratioSup ν μ * ratioSup μ ν) := by ring
    _ = ratioSup ν μ * ratioSup μ ν := by
      rw [← ENNReal.ofReal_mul hc.le, mul_inv_cancel₀ hc.ne', ENNReal.ofReal_one, one_mul]

theorem Homothetic.distRatio_eq {ν ν' μ μ' : VectorNorm F V} (h : Homothetic ν ν')
    (h' : Homothetic μ μ') : distRatio ν' μ' = distRatio ν μ := by
  obtain ⟨c, hc, hc'⟩ := h
  obtain ⟨c', hc₁, hc₁'⟩ := h'
  rw [distRatio_of_eq_mul_left hc hc', distRatio_comm, distRatio_of_eq_mul_left hc₁ hc₁',
    distRatio_comm]

theorem one_le_distRatio [Nontrivial V] (ν μ : VectorNorm F V) : 1 ≤ distRatio ν μ := by
  obtain ⟨x, hx⟩ := exists_ne (0 : V)
  have h1 : ENNReal.ofReal (ν x / μ x) ≤ ratioSup ν μ :=
    le_iSup (fun y => ENNReal.ofReal (ν y / μ y)) x
  have h2 : ENNReal.ofReal (μ x / ν x) ≤ ratioSup μ ν :=
    le_iSup (fun y => ENNReal.ofReal (μ y / ν y)) x
  calc (1 : ℝ≥0∞) = ENNReal.ofReal (ν x / μ x) * ENNReal.ofReal (μ x / ν x) := by
        rw [← ENNReal.ofReal_mul (div_nonneg (ν.nonneg x) (μ.nonneg x)), div_mul_div_comm,
          mul_comm (ν x), div_self (mul_pos (μ.pos hx) (ν.pos hx)).ne', ENNReal.ofReal_one]
    _ ≤ distRatio ν μ := mul_le_mul' h1 h2

theorem ratioSup_self_le_one (ν : VectorNorm F V) : ratioSup ν ν ≤ 1 :=
  iSup_le fun x => ENNReal.ofReal_le_one.2 (div_self_le_one (ν x))

theorem distRatio_self [Nontrivial V] (ν : VectorNorm F V) : distRatio ν ν = 1 :=
  le_antisymm (mul_le_one' (ratioSup_self_le_one ν) (ratioSup_self_le_one ν))
    (one_le_distRatio ν ν)

/-- A norm whose values are absolute values of scalars. It is the norm of its unit ball
`L = {ν ≤ 1}`, `ν(x) = inf {|t| : t ≠ 0, t⁻¹ x ∈ L}` (`IsLatticeNorm.eq_sInf`). -/
def IsLatticeNorm (ν : VectorNorm F V) : Prop := ∀ x, ∃ t : F, ν x = ‖t‖

/-- A lattice norm is the gauge of its unit ball. -/
theorem IsLatticeNorm.eq_sInf {ν : VectorNorm F V} (h : ν.IsLatticeNorm) {x : V} (hx : x ≠ 0) :
    ν x = sInf {r : ℝ | ∃ t : F, t ≠ 0 ∧ r = ‖t‖ ∧ ν (t⁻¹ • x) ≤ 1} := by
  obtain ⟨t₀, ht₀⟩ := h x
  have ht₀' : t₀ ≠ 0 := by
    rintro rfl
    rw [norm_zero] at ht₀
    exact (ν.pos hx).ne' ht₀
  symm
  refine IsLeast.csInf_eq ⟨⟨t₀, ht₀', ht₀, ?_⟩, ?_⟩
  · rw [ν.map_smul, ht₀, norm_inv, inv_mul_cancel₀ (norm_ne_zero_iff.2 ht₀')]
  · rintro r ⟨t, ht, rfl, hle⟩
    rw [ν.map_smul, norm_inv] at hle
    have htpos : 0 < ‖t‖ := norm_pos_iff.2 ht
    rwa [inv_mul_le_iff₀ htpos, mul_one] at hle

/-- A chain of lattices `L₀ ⊇ L₁ ⊇ ⋯ ⊇ L_k ⊇ t L₀` (for every scalar `|t| < 1`), in terms of
their norms: `ν₀ ≤ ν₁ ≤ ⋯ ≤ ν_k` and `|t| ν_k ≤ ν₀`. -/
structure IsLatticeChain {k : ℕ} (ν : Fin (k + 1) → VectorNorm F V) : Prop where
  isLatticeNorm : ∀ i, (ν i).IsLatticeNorm
  mono : ∀ i j, i ≤ j → ∀ x, ν i x ≤ ν j x
  bounded : ∀ t : F, ‖t‖ < 1 → ∀ x, ‖t‖ * ν (Fin.last k) x ≤ ν 0 x

end VectorNorm

/-! ## Vertices and facets of the building -/

namespace NormClass

variable {F : Type v} [NormedField F] {V : Type w} [AddCommGroup V] [Module F V]

/-- The Goldman–Iwahori distance on norm classes, in multiplicative form. -/
def distRatio : NormClass F V → NormClass F V → ℝ≥0∞ :=
  Quotient.lift₂ VectorNorm.distRatio fun _ _ _ _ h h' => (VectorNorm.Homothetic.distRatio_eq h h').symm

@[simp]
theorem distRatio_mk (ν μ : VectorNorm F V) :
    distRatio (⟦ν⟧ : NormClass F V) ⟦μ⟧ = VectorNorm.distRatio ν μ := rfl

theorem distRatio_comm (x y : NormClass F V) : distRatio x y = distRatio y x :=
  Quotient.inductionOn₂ x y VectorNorm.distRatio_comm

theorem one_le_distRatio [Nontrivial V] (x y : NormClass F V) : 1 ≤ distRatio x y :=
  Quotient.inductionOn₂ x y VectorNorm.one_le_distRatio

theorem distRatio_self [Nontrivial V] (x : NormClass F V) : distRatio x x = 1 :=
  Quotient.inductionOn x VectorNorm.distRatio_self

/-- Vertices of the building: classes of lattice norms. -/
def IsVertex (x : NormClass F V) : Prop := ∃ ν : VectorNorm F V, ⟦ν⟧ = x ∧ ν.IsLatticeNorm

/-- Facets of the building: the sets of vertices of chains of lattices. -/
def IsFacet (S : Set (NormClass F V)) : Prop :=
  ∃ (k : ℕ) (ν : Fin (k + 1) → VectorNorm F V), VectorNorm.IsLatticeChain ν ∧
    S = range fun i => (⟦ν i⟧ : NormClass F V)

theorem IsFacet.isVertex {S : Set (NormClass F V)} (hS : IsFacet S) {x : NormClass F V}
    (hx : x ∈ S) : IsVertex x := by
  obtain ⟨k, ν, hν, rfl⟩ := hS
  obtain ⟨i, rfl⟩ := hx
  exact ⟨ν i, rfl, hν.isLatticeNorm i⟩

/-- A vertex is a facet. -/
theorem isFacet_singleton {x : NormClass F V} (hx : IsVertex x) : IsFacet {x} := by
  obtain ⟨ν, rfl, hν⟩ := hx
  refine ⟨0, fun _ => ν, ⟨fun _ => hν, fun _ _ _ _ => le_rfl, fun t ht y => ?_⟩, ?_⟩
  · exact mul_le_of_le_one_left (ν.nonneg y) ht.le
  · ext y
    simp

/-- The closed star of a vertex `e` in the first barycentric subdivision: the points for which
`e` is a nearest vertex. -/
def vertexStar (e : NormClass F V) : Set (NormClass F V) :=
  {x | ∀ e', IsVertex e' → distRatio x e ≤ distRatio x e'}

/-- Harris's open neighbourhood `B(e, ε)` of the star of a vertex `e`. -/
def vertexNbhd (e : NormClass F V) (ε : ℝ) : Set (NormClass F V) :=
  {x | ∃ y ∈ vertexStar e, distRatio x y < ENNReal.ofReal (Real.exp ε)}

/-- A vertex lies in its own star. -/
theorem self_mem_vertexStar [Nontrivial V] (e : NormClass F V) : e ∈ vertexStar e :=
  fun e' _ => (distRatio_self e).symm ▸ one_le_distRatio e e'

/-- The star of a vertex lies in each of its neighbourhoods. -/
theorem vertexStar_subset_vertexNbhd [Nontrivial V] (e : NormClass F V) {ε : ℝ} (hε : 0 < ε) :
    vertexStar e ⊆ vertexNbhd e ε := by
  intro x hx
  refine ⟨x, hx, ?_⟩
  rw [distRatio_self, ← ENNReal.ofReal_one]
  exact (ENNReal.ofReal_lt_ofReal_iff (Real.exp_pos ε)).2 (Real.one_lt_exp_iff.2 hε)

/-- Harris's `B(f, ε)` for a facet `f`: the intersection of the `B(e, ε)` over its vertices. -/
def facetNbhd (S : Set (NormClass F V)) (ε : ℝ) : Set (NormClass F V) :=
  ⋂ e ∈ S, vertexNbhd e ε

end NormClass

/-! ## Invariance under `GL_n(F)` -/

namespace VectorNorm

variable {F : Type v} [NormedField F] {n : Type w} [Fintype n] [DecidableEq n]

/-- Right multiplication by an invertible matrix, as a permutation of row vectors. -/
def vecMulEquiv (γ : Matrix.GeneralLinearGroup n F) : (n → F) ≃ (n → F) where
  toFun a := Matrix.vecMul a (γ : Matrix n n F)
  invFun a := Matrix.vecMul a ((γ⁻¹ : Matrix.GeneralLinearGroup n F) : Matrix n n F)
  left_inv a := by
    change Matrix.vecMul (Matrix.vecMul a _) _ = a
    rw [Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.vecMul_one]
  right_inv a := by
    change Matrix.vecMul (Matrix.vecMul a _) _ = a
    rw [Matrix.vecMul_vecMul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.vecMul_one]

theorem ratioSup_smul (γ : Matrix.GeneralLinearGroup n F) (ν μ : VectorNorm F (n → F)) :
    ratioSup (γ • ν) (γ • μ) = ratioSup ν μ :=
  (vecMulEquiv γ).iSup_comp (g := fun a => ENNReal.ofReal (ν a / μ a))

theorem distRatio_smul (γ : Matrix.GeneralLinearGroup n F) (ν μ : VectorNorm F (n → F)) :
    distRatio (γ • ν) (γ • μ) = distRatio ν μ := by
  rw [distRatio, ratioSup_smul, ratioSup_smul, distRatio]

theorem IsLatticeNorm.smul {ν : VectorNorm F (n → F)} (h : ν.IsLatticeNorm)
    (γ : Matrix.GeneralLinearGroup n F) : (γ • ν).IsLatticeNorm := fun _ => h _

theorem IsLatticeChain.smul {k : ℕ} {ν : Fin (k + 1) → VectorNorm F (n → F)}
    (h : IsLatticeChain ν) (γ : Matrix.GeneralLinearGroup n F) :
    IsLatticeChain fun i => γ • ν i :=
  ⟨fun i => (h.isLatticeNorm i).smul γ, fun i j hij _ => h.mono i j hij _,
    fun t ht _ => h.bounded t ht _⟩

end VectorNorm

namespace NormClass

variable {F : Type v} [NormedField F] {n : Type w} [Fintype n] [DecidableEq n]

theorem distRatio_smul (γ : Matrix.GeneralLinearGroup n F) (x y : NormClass F (n → F)) :
    distRatio (γ • x) (γ • y) = distRatio x y :=
  Quotient.inductionOn₂ x y fun ν μ => VectorNorm.distRatio_smul γ ν μ

theorem IsVertex.smul {x : NormClass F (n → F)} (hx : IsVertex x)
    (γ : Matrix.GeneralLinearGroup n F) : IsVertex (γ • x) := by
  obtain ⟨ν, rfl, hν⟩ := hx
  exact ⟨γ • ν, rfl, hν.smul γ⟩

theorem isVertex_smul_iff (γ : Matrix.GeneralLinearGroup n F) (x : NormClass F (n → F)) :
    IsVertex (γ • x) ↔ IsVertex x :=
  ⟨fun h => by simpa using h.smul γ⁻¹, fun h => h.smul γ⟩

theorem IsFacet.smul {S : Set (NormClass F (n → F))} (hS : IsFacet S)
    (γ : Matrix.GeneralLinearGroup n F) : IsFacet (γ • S) := by
  obtain ⟨k, ν, hν, rfl⟩ := hS
  refine ⟨k, fun i => γ • ν i, hν.smul γ, ?_⟩
  rw [Set.smul_set_range]
  rfl

theorem smul_mem_vertexStar_iff (γ : Matrix.GeneralLinearGroup n F) (e x : NormClass F (n → F)) :
    γ • x ∈ vertexStar (γ • e) ↔ x ∈ vertexStar e := by
  constructor
  · intro h e' he'
    have := h (γ • e') (he'.smul γ)
    rwa [distRatio_smul, distRatio_smul] at this
  · intro h e' he'
    have := h (γ⁻¹ • e') ((isVertex_smul_iff γ⁻¹ e').2 he')
    rwa [← distRatio_smul γ, ← distRatio_smul γ x, smul_inv_smul] at this

theorem smul_mem_vertexNbhd_iff (γ : Matrix.GeneralLinearGroup n F) (e x : NormClass F (n → F))
    (ε : ℝ) : γ • x ∈ vertexNbhd (γ • e) ε ↔ x ∈ vertexNbhd e ε := by
  constructor
  · rintro ⟨y, hy, hxy⟩
    refine ⟨γ⁻¹ • y, ?_, ?_⟩
    · rw [← smul_mem_vertexStar_iff γ, smul_inv_smul]
      exact hy
    · rwa [← distRatio_smul γ, smul_inv_smul]
  · rintro ⟨y, hy, hxy⟩
    exact ⟨γ • y, (smul_mem_vertexStar_iff γ e y).2 hy, by rwa [distRatio_smul]⟩

theorem smul_mem_facetNbhd_iff (γ : Matrix.GeneralLinearGroup n F) (S : Set (NormClass F (n → F)))
    (x : NormClass F (n → F)) (ε : ℝ) : γ • x ∈ facetNbhd (γ • S) ε ↔ x ∈ facetNbhd S ε := by
  simp only [facetNbhd, mem_iInter]
  constructor
  · intro h e he
    exact (smul_mem_vertexNbhd_iff γ e x ε).1 (h (γ • e) (smul_mem_smul_set he))
  · intro h e he
    obtain ⟨e', he', rfl⟩ := he
    exact (smul_mem_vertexNbhd_iff γ e' x ε).2 (h e' he')

end NormClass

/-! ## Harris's domains `U(e)` of Drinfeld's upper half space -/

namespace DrinfeldUpperHalfSpace

variable {F : Type v} [NontriviallyNormedField F]
  (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [NormedAlgebra F K] {d : ℕ}

/-- Harris's subset `U(f) = Res⁻¹(B(f, ε))` of `Ω` for a set of vertices `f` of the
building. -/
def facetDomain (S : Set (NormClass F (Fin (d + 1) → F))) (ε : ℝ) : Set (Omega F K d) :=
  reduction K ⁻¹' NormClass.facetNbhd S ε

/-- The stabilizer `S(f)` of a set of vertices in `GL_{d+1}(F)`. -/
abbrev facetStabilizer (S : Set (NormClass F (Fin (d + 1) → F))) :
    Subgroup (Matrix.GeneralLinearGroup (Fin (d + 1)) F) :=
  MulAction.stabilizer _ S

variable [ProperSpace F] [NeZero d]

/-- `γ U(f) = U(γ f)`. -/
theorem actionMap_mem_facetDomain_iff (γ : Matrix.GeneralLinearGroup (Fin (d + 1)) F)
    (S : Set (NormClass F (Fin (d + 1) → F))) (ε : ℝ) (z : Omega F K d) :
    actionMap K γ z ∈ facetDomain K (γ • S) ε ↔ z ∈ facetDomain K S ε := by
  rw [facetDomain, mem_preimage, reduction_actionMap]
  exact NormClass.smul_mem_facetNbhd_iff γ S _ ε

/-- The stabilizer of `f` preserves `U(f)`. -/
theorem actionMap_mem_facetDomain_of_mem_stabilizer {γ : Matrix.GeneralLinearGroup (Fin (d + 1)) F}
    {S : Set (NormClass F (Fin (d + 1) → F))} (hγ : γ ∈ facetStabilizer S) (ε : ℝ)
    (z : Omega F K d) : actionMap K γ z ∈ facetDomain K S ε ↔ z ∈ facetDomain K S ε := by
  have h := actionMap_mem_facetDomain_iff K γ S ε z
  rwa [MulAction.mem_stabilizer_iff.1 hγ] at h

end DrinfeldUpperHalfSpace

end Langlands.Analytic
