import Langlands.Theta.DualPair.Unitary.WeylElement
import Langlands.Theta.DualPair.TensorInvariants
import Langlands.Group.BigCellHom
import Langlands.Representation.Smooth.OpenStabilizer
import Mathlib.Topology.LocallyConstant.Algebra

/-!
# The Leray splitting of `U(ν, ν)` and its Weil representation

GKT §11.2 (Theorem 11.6, p. 318; Corollary 11.7, p. 325) and §12.4 (Proposition 12.27 (1), p. 372;
Proposition 12.29, p. 375) for the unitary dual pair in Case `3₊` with `W` split, proved directly
by generators and relations. Let `F` be a nonarchimedean local field of characteristic zero,
`E / F` a quadratic extension with conjugation `c`, `Q` an invertible Hermitian `α × α` matrix over
`E`, `ψ` a non-trivial unitary character of `F`, and `χ` a continuous unitary character of `Eˣ`
whose restriction to `Fˣ` is `η^{|α|}`, `η = LocalClassField.normResidueSign F E` the quadratic
character of `E / F` (the condition (11.2) on Leray splitting data, GKT p. 317).

`IsLerayWeil c ψ χ Q μ κ ω`: the representation `ω` of `U(ν, ν)` on Schwartz–Bruhat functions on
`M_{α×ν}(E)` acts on the Siegel parabolic by `siegelParabolicOp` and at the Weyl element by `κ`
times `hermitianFourier` (for a Haar measure `μ`): the formulas of Proposition 12.27 (1).

- `exists_isLerayWeil`: such `κ` and `ω` exist. The operators of the Siegel parabolic form a
  representation of it; `κ` is chosen so that the braid relation holds exactly (from the Gauss
  integral of the Hermitian quadratic character); the relations of the big cell then hold, and
  `Group.exists_monoidHom_of_bigCell_relations` extends the operators to `U(ν, ν)`, every finite set
  having a translate in the big cell (`UnitaryGroup.exists_mul_isInBigCell`). The book proves
  Theorem 11.6 differently, by the explicit Leray cocycle (Theorem 5.2).
- `IsLerayWeil.isSmooth`: `ω` is smooth (the stabilizer of a vector contains neighbourhoods of `1`
  in the Siegel parabolic and in its conjugate by the Weyl element, hence is open:
  `UnitaryGroup.isOpen_of_eventually_mem_siegelParabolic`).
- `IsLerayWeil.lintegral_enorm_sq`: `ω` preserves the `L²` norm for every Haar measure (the
  operators of the Siegel parabolic do, and `|κ|² C = 1` for the constant `C` of Fourier
  inversion, because the square of the Weyl element is in the Siegel parabolic).
- `IsLerayWeil.normalizes`: `ω` normalizes the Schrödinger representation `hermitianSchrodinger`
  along `UnitaryGroup.heisenbergAction`: `ω(g) ρ(w, t) ω(g)⁻¹ = ρ(w g⁻¹, t)` (relation (2.2) of
  GKT p. 47).
- `IsLerayWeil.siegelLevi_apply`: the Levi element `diag(a, c(a)⁻ᵀ)` acts by
  `φ ↦ χ(det a) |N_{E/F} det a|_F^{|α|/2} φ(· a)`.

So `ω` is a splitting over `U(ν, ν)` of the metaplectic cover, in the Schrödinger model. The
normalization is that of S. S. Kudla, *Splitting metaplectic covers of dual reductive pairs*,
Israel J. Math. 87 (1994), §3, Theorem 3.1, p. 378 (the function `β_V`, built in the unitary case
from a character of `Eˣ` whose restriction to `Fˣ` is `ε_{E/F}^m`), Corollary 3.3, p. 380 (the
splitting), and §5, pp. 399–400 (the operators `ω_V(g) = β_V(g) r(g)` of the Schrödinger model).
-/

noncomputable section

open MeasureTheory Matrix ValuativeRel Filter
open scoped Topology ENNReal NNReal

namespace Langlands.Theta

open Langlands.UnitaryGroup Langlands.HarmonicAnalysis

namespace Unitary.Internal

end Unitary.Internal

open Unitary.Internal

section IsLerayWeilDef

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {E : Type} [Field E] [Algebra F E] (c : E →ₐ[F] E)
  {α ν : Type} [Fintype α] [DecidableEq α] [Fintype ν] [DecidableEq ν]

/-- `ω` is the Weil representation of `U(ν, ν)` for the Leray splitting with data `(χ, ψ)` in the
Schrödinger model, in the form of GKT Proposition 12.27 (1) with the values of Proposition 12.29:
it acts on the Siegel parabolic by the explicit operators `siegelParabolicOp` (the first two
formulas of 12.27 (1), with `β(m(a) n(b)) = χ(det a)`), and the Weyl element acts by `κ` times the
Fourier transform of the Hermitian pairing for the Haar measure `μ` (the third formula; `κ` absorbs
`β(w)` and the normalization of `μ`). -/
structure IsLerayWeil [TopologicalSpace E] [MeasurableSpace (Matrix α ν E)] (ψ : AddChar F ℂ)
    (χ : Eˣ →* Circle) (Q : Matrix α α E) (μ : Measure (Matrix α ν E)) (κ : ℂ)
    (ω : Representation ℂ (ofForm c (hyperbolicForm ν E)) (SchwartzBruhat (Matrix α ν E))) :
    Prop where
  apply_of_mem_siegelParabolic : ∀ p ∈ siegelParabolic c ν, ∀ φ : SchwartzBruhat (Matrix α ν E),
    (ω p φ : Matrix α ν E → ℂ) =
      siegelParabolicOp c ψ χ Q ((p : GL (ν ⊕ ν) E) : Matrix (ν ⊕ ν) (ν ⊕ ν) E) φ
  weylElement_apply : ∀ φ : SchwartzBruhat (Matrix α ν E),
    (ω (weylElement c ν) φ : Matrix α ν E → ℂ) = κ • hermitianFourier c ψ Q μ φ

end IsLerayWeilDef

namespace Unitary.Internal

namespace WeylCellRel

variable {F : Type} [Field F] {E : Type} [Field E] [Algebra F E] (c : E →ₐ[F] E)
  {ν : Type} [Fintype ν] [DecidableEq ν]

theorem mat_mul (p q : ofForm c (hyperbolicForm ν E)) : mat c (p * q) = mat c p * mat c q := rfl

theorem mat_weyl_inv : mat c (weylElement c ν)⁻¹ = -hyperbolicForm ν E := rfl

theorem mat_unip_inv (b : Matrix ν ν E) (hb : (b.map c)ᵀ = b) : mat c
    (siegelUnipotent c b hb)⁻¹ = fromBlocks 1 (-b) 0 1 := rfl

theorem mat_weyl : mat c (weylElement c ν) = fromBlocks 0 1 (-1) 0 := hyperbolicForm_eq_fromBlocks

theorem mat_levi (hc : Function.Involutive c) (a : GL ν E) :
    mat c (siegelLevi c hc a) = fromBlocks (a : Matrix ν ν E) 0 0
        (((a⁻¹ : GL ν E) : Matrix ν ν E).map c)ᵀ := rfl

theorem mat_unip (b : Matrix ν ν E) (hb : (b.map c)ᵀ = b) : mat c
    (siegelUnipotent c b hb) = fromBlocks 1 b 0 1 := rfl

theorem splitUnitaryElementMatrix_bigCell_product (b : Matrix ν ν E) (hb : (b.map c)ᵀ = b)
    (hb0 : b.det ≠ 0) (hb' : ((-b⁻¹).map c)ᵀ = -b⁻¹) :
    mat c (weylElement c ν * siegelUnipotent c b hb * weylElement c ν * (siegelUnipotent c
        (-b⁻¹) hb')⁻¹ * (weylElement c ν)⁻¹) =
      fromBlocks (-b⁻¹) 1 0 (-b) := by
  have h1 : b * b⁻¹ = 1 := mul_nonsing_inv b (isUnit_iff_ne_zero.mpr hb0)
  rw [mat_mul, mat_mul, mat_mul, mat_mul, mat_weyl_inv, mat_unip_inv, mat_unip, mat_weyl]
  simp only [hyperbolicForm_eq_fromBlocks, fromBlocks_multiply, fromBlocks_neg]
  simp [h1]

theorem conj_levi_mem (hc : Function.Involutive c) (a : GL ν E) :
    weylElement c ν * siegelLevi c hc a * (weylElement c ν)⁻¹ ∈ siegelParabolic c ν := by
  rw [mem_sieg, mat_mul, mat_mul, mat_weyl_inv, mat_weyl, mat_levi]
  simp [hyperbolicForm_eq_fromBlocks, fromBlocks_multiply, fromBlocks_neg]

theorem herm_neg_inv (b : Matrix ν ν E) (hb : (b.map c)ᵀ = b) (hb0 : b.det ≠ 0) :
    ((-b⁻¹).map c)ᵀ = -b⁻¹ := by
  have h1 : ((b⁻¹).map c)ᵀ * b = 1 := by
    have h3 : ((b⁻¹).map c)ᵀ * (b.map c)ᵀ = 1 := by
      rw [← transpose_mul, ← Matrix.map_mul (f := c),
          mul_nonsing_inv b (isUnit_iff_ne_zero.mpr hb0),
        Matrix.map_one _ (map_zero c) (map_one c), transpose_one]
    rwa [hb] at h3
  have h2 : ((b⁻¹).map c)ᵀ = b⁻¹ := (Matrix.inv_eq_left_inv h1).symm
  rw [Matrix.map_neg _ (map_neg c), transpose_neg, h2]

theorem lower_left (hc : Function.Involutive c) (a : GL ν E) (b : Matrix ν ν E) (hb :
    (b.map c)ᵀ = b) :
    (mat c (weylElement c ν *
        (siegelLevi c hc a * siegelUnipotent c b hb) * weylElement c ν)).toBlocks₂₁ =
        (a : Matrix ν ν E) * b := by
  rw [mat_mul, mat_mul, mat_mul, mat_weyl, mat_levi, mat_unip]
  simp [fromBlocks_multiply]

end WeylCellRel

theorem WeylCellRel.gauss_const_ne_zero : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E]
    [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E)
    (_ : IsQuadraticInvolution c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν]
    [DecidableEq ν] (Q : Matrix α α E) (_ : IsHerm c Q) (ψ : AddChar F ℂ) (_ : Continuous ψ) (_ :
    ∀ t,
    ‖ψ t‖ = 1) (_ : ψ ≠ 1) (χ : Eˣ →* Circle) (_ : Continuous χ) (_ : ResEtaPow (R := F) ⊥ χ
    (Fintype.card α)) [MeasurableSpace (Matrix α ν E)] [BorelSpace (Matrix α ν E)] (μ : Measure
    (Matrix α ν E)) [μ.IsAddHaarMeasure] (γ₀ : ℂ), (∀ b : Matrix ν ν E,
    (b.map c)ᵀ = b → b.det ≠ 0 → HasGaussIntegral μ (fun x => ψ (2⁻¹ * pr c Q x (x * b)))
    (γ₀ * splittingScalar F χ (Fintype.card α) b.det⁻¹)) → γ₀ ≠ 0 := by
  intro F _ _ _ _ _ E _ _ _ _ c δ hE α _ _ ν _ _ Q hQ ψ hψ hψ1 hψne χ hχ hres _ _ μ _ γ₀ hγ hγ0
  have hfd : FiniteDimensional F E := hE.finite
  have : FiniteDimensional F E := hE.finite
  have : IsModuleTopology F (Matrix α ν E) := isModuleTopology_matrix F (E := E) α ν
  have := IsModuleTopology.isTopologicalAddGroup F (Matrix α ν E)
  have := t2Space_of_finiteDimensional F (Matrix α ν E)
  have := locallyCompactSpace_of_finiteDimensional F (Matrix α ν E)
  have := secondCountableTopology_of_finiteDimensional F (Matrix α ν E)
  have := compactOpenExhaustion_of_finiteDimensional F (Matrix α ν E)
  have : FiniteDimensional F (Matrix α ν E) := inferInstance
  obtain ⟨β, hβ, hsymm, hnd, -, -⟩ := pr_alg F E c δ hE α ν Q hQ
  have hpair := isSelfDualBicharacter_of_symm (V := Matrix α ν E) hψ hψ1 hψne β hsymm hnd
  have hfou : ∀ f, hermitianFourier c ψ Q μ f = bicharacterFourier μ (fun x y => ψ (β x y)) f := by
    intro f
    have hfe : (fun x y => ψ (β x y)) = (fun x y => ψ (pr c Q x y)) := by funext x y; rw [hβ]
    rw [hfe]; rfl
  obtain ⟨C, hC, hinv⟩ := exists_pos_bicharacterFourier_bicharacterFourier μ hpair
  have inj : ∀ g ∈ schwartzBruhatSubmodule (Matrix α ν E),
      hermitianFourier c ψ Q μ g = 0 → g = 0 := by
    intro g hg h0
    funext x
    have h1 := hinv g hg (-x)
    rw [← hfou g, h0, neg_neg] at h1
    have h2 : bicharacterFourier μ (fun x y => ψ (β x y)) (0 : Matrix α ν E → ℂ) (-x) = 0 := by
        simp [bicharacterFourier]
    rw [h2] at h1
    exact (mul_eq_zero.mp h1.symm).resolve_left (by exact_mod_cast hC.ne')
  obtain ⟨L, hLc, hLo, -⟩ :=
    CompactOpenExhaustion.exists_subset (X := Matrix α ν E) Set.univ Filter.univ_mem
  have hLcl : IsClopen (L : Set (Matrix α ν E)) :=
    ⟨AddSubgroup.isClosed_of_isOpen L hLo, hLo⟩
  set φ : Matrix α ν E → ℂ := (L : Set (Matrix α ν E)).indicator 1 with hφd
  have hφ : φ ∈ schwartzBruhatSubmodule (Matrix α ν E) := by
    refine ⟨?_, HasCompactSupport.intro hLc fun x hx => Set.indicator_of_notMem hx _⟩
    have := (LocallyConstant.indicator (1 : LocallyConstant
        (Matrix α ν E) ℂ) hLcl).isLocallyConstant
    convert this using 1
    funext y
    exact (LocallyConstant.indicator_apply (1 : LocallyConstant (Matrix α ν E) ℂ) hLcl y).symm
  have hφ0 : φ 0 = 1 := by simp [hφd]
  have hfφ : hermitianFourier c ψ Q μ φ ∈ schwartzBruhatSubmodule (Matrix α ν E) := by
    rw [hfou]; exact bicharacterFourier_mem μ hpair hφ
  have h1 : ((1 : Matrix ν ν E).map c)ᵀ = 1 := by
    rw [Matrix.map_one _ (map_zero c) (map_one c), transpose_one]
  have hu : siegelUnipotent c 1 h1 ∈ siegelParabolic c ν := by
      rw [mem_sieg, WeylCellRel.mat_unip]; simp
  have hg := parFun_mem F E c δ hE α ν Q hQ ψ hψ hψ1 hψne χ hχ hres
      (siegelUnipotent c 1 h1) hu _ hfφ
  obtain ⟨sc1, scmul, -⟩ := sc_basic F E c δ hE (Fintype.card α) χ hres
  have sc_ne : ∀ z : E, z ≠ 0 → splittingScalar F χ (Fintype.card α) z ≠ 0 := fun z hz h => by
    have h' := scmul z z⁻¹
    rw [mul_inv_cancel₀ hz, sc1, h, zero_mul] at h'
    exact one_ne_zero h'
  have br := braid_relation F E c δ hE α ν Q hQ ψ hψ hψ1 hψne χ hχ hres μ 1 _ h1 (by simp)
    (hγ 1 h1 (by simp)) φ hφ
  rw [hγ0, zero_mul, zero_smul] at br
  have hs : splittingScalar F χ (Fintype.card α) (-(1 : Matrix ν ν E)⁻¹).det ≠ 0 := sc_ne _ (by simp
      [det_neg])
  have hX := (smul_eq_zero.mp br).resolve_left hs
  have hpar0 := inj _ hg hX
  apply one_ne_zero (α := ℂ)
  rw [← hφ0]
  have hF0 : hermitianFourier c ψ Q μ φ = 0 := by
    funext x
    have h2 := congrFun hpar0 x
    have hψ0 : ∀ t, ψ t ≠ 0 := by
      intro t h4; have := hψ1 t; rw [h4, norm_zero] at this; exact zero_ne_one this
    simpa [siegelParabolicOp, WeylCellRel.mat_unip, sc1, hψ0] using h2
  rw [inj φ hφ hF0]; rfl

theorem weyl_cell_relation : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E]
    [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E)
    (_ : IsQuadraticInvolution c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν]
    [DecidableEq ν] (Q : Matrix α α E) (_ : IsHerm c Q) (ψ : AddChar F ℂ) (_ : Continuous ψ) (_ :
    ∀ t,
    ‖ψ t‖ = 1) (_ : ψ ≠ 1) (χ : Eˣ →* Circle) (_ : Continuous χ) (_ : ResEtaPow (R := F) ⊥ χ
    (Fintype.card α)) [MeasurableSpace (Matrix α ν E)] [BorelSpace (Matrix α ν E)] (μ : Measure
    (Matrix α ν E)) [μ.IsAddHaarMeasure], ∃ κ : ℂ, κ ≠ 0 ∧ ∀ p ∈ siegelParabolic c ν,
    IsInBigCell c (weylElement c ν * p * weylElement c ν) → ∃ p₁ ∈ siegelParabolic c ν,
    ∃ p₂ ∈ siegelParabolic c ν,
    weylElement c ν * p * weylElement c ν = p₁ * weylElement c ν * p₂ ∧
    ∀ φ ∈ schwartzBruhatSubmodule (Matrix α ν E),
    κ • hermitianFourier c ψ Q μ (siegelParabolicOp c ψ χ Q (mat c p)
    (κ • hermitianFourier c ψ Q μ φ)) = siegelParabolicOp c ψ χ Q (mat c p₁)
    (κ • hermitianFourier c ψ Q μ (siegelParabolicOp c ψ χ Q (mat c p₂) φ)) := by
  intro F _ _ _ _ _ E _ _ _ _ c δ hE α _ _ ν _ _ Q hQ ψ hψ hψ1 hψne χ hχ hres _ _ μ _
  obtain ⟨γ₀, hγ⟩ := GaussMain.hasGauss_herm F E c δ hE α ν Q hQ ψ hψ hψ1 hψne χ hχ hres μ
  have hγ0 : γ₀ ≠ 0 :=
    WeylCellRel.gauss_const_ne_zero F E c δ hE α ν Q hQ ψ hψ hψ1 hψne χ hχ hres μ γ₀ hγ
  obtain ⟨sc1, scmul, -⟩ := sc_basic F E c δ hE (Fintype.card α) χ hres
  have sc_ne : ∀ z : E, z ≠ 0 → splittingScalar F χ (Fintype.card α) z ≠ 0 := fun z hz h => by
    have h' := scmul z z⁻¹
    rw [mul_inv_cancel₀ hz, sc1, h, zero_mul] at h'
    exact one_ne_zero h'
  have hs1 : splittingScalar F χ (Fintype.card α) (-1 : Matrix ν ν E).det ≠ 0 := sc_ne _ (by simp
      [det_neg])
  refine ⟨splittingScalar F χ (Fintype.card α) (-1 : Matrix ν ν E).det / γ₀, div_ne_zero hs1 hγ0,
      ?_⟩
  intro p hp hcell
  obtain ⟨-, -, a, b, hb, rfl⟩ := exists_eq_siegelLevi_mul_siegelUnipotent c hE.involutive p hp
  have hb0 : b.det ≠ 0 := by
    have h := (isInBigCell_iff_det_ne_zero c _).mp hcell
    change (mat c _).toBlocks₂₁.det ≠ 0 at h
    rw [WeylCellRel.lower_left, det_mul] at h
    exact right_ne_zero_of_mul h
  have hb' := WeylCellRel.herm_neg_inv c b hb hb0
  have hunip : ∀ (b' : Matrix ν ν E) (h' : (b'.map c)ᵀ = b'),
      siegelUnipotent c b' h' ∈ siegelParabolic c ν := by
    intro b' h'; rw [mem_sieg, WeylCellRel.mat_unip]; simp
  have hlevi : siegelLevi c hE.involutive a ∈ siegelParabolic c ν := by
      rw [mem_sieg, WeylCellRel.mat_levi]; simp
  obtain ⟨q, hqd⟩ : ∃ q,
      q = weylElement c ν * siegelLevi c hE.involutive a * (weylElement c ν)⁻¹ := ⟨_, rfl⟩
  obtain ⟨p₀, hp0d⟩ : ∃ p₀,
      p₀ = weylElement c ν * siegelUnipotent c b hb * weylElement c ν * (siegelUnipotent c
      (-b⁻¹) hb')⁻¹ * (weylElement c ν)⁻¹ :=
    ⟨_, rfl⟩
  have hq : q ∈ siegelParabolic c ν := hqd ▸ WeylCellRel.conj_levi_mem c hE.involutive a
  have hp0m : mat c p₀ = fromBlocks (-b⁻¹) 1 0
      (-b) := hp0d ▸ WeylCellRel.splitUnitaryElementMatrix_bigCell_product c b hb hb0 hb'
  have hp0 : p₀ ∈ siegelParabolic c ν := by rw [mem_sieg, hp0m]; simp
  refine ⟨q * p₀, mul_mem hq hp0, siegelUnipotent c (-b⁻¹) hb', hunip _ _, by
      rw [hqd, hp0d]; group, ?_⟩
  intro φ hφ
  obtain ⟨-, pm⟩ := parFun_sieg_mul F E c δ hE α ν Q hQ ψ hψ hψ1 hψne χ hχ hres
  have fl := fou_parFun_levi F E c δ hE α ν Q hQ ψ hψ hψ1 hψne χ hχ hres μ
      (siegelLevi c hE.involutive a) hlevi q hq
    (by rw [hqd]; group)
  have br := braid_relation F E c δ hE α ν Q hQ ψ hψ hψ1 hψne χ hχ hres μ b _ hb hb0
      (hγ b hb hb0) φ hφ
  rw [← WeylCellRel.mat_unip c b hb, ← WeylCellRel.mat_unip c (-b⁻¹) hb', ← hp0m] at br
  have pf_smul : ∀ (g : Matrix (ν ⊕ ν) (ν ⊕ ν) E) (k : ℂ) (f : Matrix α ν E → ℂ),
      siegelParabolicOp c ψ χ Q g (k • f) = k • siegelParabolicOp c ψ χ Q g f := by
    intro g k f; funext x; simp only [siegelParabolicOp, Pi.smul_apply, smul_eq_mul]; ring
  have fou_smul : ∀ (k : ℂ) (f : Matrix α ν E → ℂ),
      hermitianFourier c ψ Q μ (k • f) = k • hermitianFourier c ψ Q μ f := by
    intro k f; funext x; simp only [hermitianFourier, bicharacterFourier, Pi.smul_apply,
        smul_eq_mul]
    rw [← integral_const_mul]; congr 1; funext y; ring
  have e : (-b⁻¹ : Matrix ν ν E).det = (-1 : Matrix ν ν E).det * b.det⁻¹ := by
    rw [← neg_one_mul, det_mul, det_nonsing_inv, Ring.inverse_eq_inv']
  have hκγ : splittingScalar F χ (Fintype.card α) (-1 : Matrix ν ν E).det / γ₀ *
      (γ₀ * splittingScalar F χ (Fintype.card α) b.det⁻¹) =
      splittingScalar F χ (Fintype.card α) (-b⁻¹).det := by
    rw [e, scmul]; field_simp
  have hs : splittingScalar F χ (Fintype.card α) (-b⁻¹).det ≠ 0 := sc_ne _ (by
    rw [e]; exact mul_ne_zero (by simp [det_neg]) (inv_ne_zero hb0))
  have hγne : γ₀ * splittingScalar F χ (Fintype.card α) b.det⁻¹ ≠ 0 := by
    intro h; rw [h, mul_zero] at hκγ; exact hs hκγ.symm
  set κ := splittingScalar F χ (Fintype.card α) (-1 : Matrix ν ν E).det / γ₀ with hκ
  have key : κ • hermitianFourier c ψ Q μ (siegelParabolicOp c ψ χ Q (mat c
      (siegelUnipotent c b hb)) (hermitianFourier c ψ Q μ φ)) =
      siegelParabolicOp c ψ χ Q (mat c p₀) (hermitianFourier c ψ Q μ (siegelParabolicOp c ψ χ Q
          (mat c (siegelUnipotent c (-b⁻¹) hb')) φ)) := by
    apply smul_right_injective _ hγne
    simp only
    rw [smul_smul, mul_comm, hκγ, br]
  rw [pf_smul, fou_smul, pm _ hlevi _ (hunip _ _), fl, ← pf_smul, key, pf_smul, pm _ hq _ hp0]



namespace Exist

theorem exists_isLerayWeil : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F]
    [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E]
    [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (_ : IsQuadraticInvolution c δ) (α : Type)
    [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (Q : Matrix α α E)
    (_ : IsHerm c Q) (ψ : AddChar F ℂ) (_ : Continuous ψ) (_ : ∀ t,
    ‖ψ t‖ = 1) (_ : ψ ≠ 1) (χ : Eˣ →* Circle) (_ : Continuous χ) (_ : ResEtaPow (R := F) ⊥ χ
    (Fintype.card α)) [MeasurableSpace (Matrix α ν E)] [BorelSpace (Matrix α ν E)] (μ : Measure
    (Matrix α ν E)) [μ.IsAddHaarMeasure],
    ∃ (κ : ℂ) (ω : Representation ℂ (ofForm c (hyperbolicForm ν E)) (schwartzBruhatSubmodule
    (Matrix α ν E))), IsLerayWeil c ψ χ Q μ κ ω := by
  intro F _ _ _ _ _ E _ _ _ _ c δ hE α _ _ ν _ _ Q hQ ψ hψ hψn hψ1 χ hχ hη _ _ μ _
  have hFD : FiniteDimensional F E := hE.finite
  have : FiniteDimensional F E := hE.finite
  have : IsModuleTopology F (Matrix α ν E) := isModuleTopology_matrix F (E := E) α ν
  have := IsModuleTopology.isTopologicalAddGroup F (Matrix α ν E)
  have := t2Space_of_finiteDimensional F (Matrix α ν E)
  have := locallyCompactSpace_of_finiteDimensional F (Matrix α ν E)
  have := secondCountableTopology_of_finiteDimensional F (Matrix α ν E)
  have := compactOpenExhaustion_of_finiteDimensional F (Matrix α ν E)
  obtain ⟨β, hβ, hβs, hβn, -, -⟩ := pr_alg F E c δ hE α ν Q hQ
  have hpair : IsSelfDualBicharacter (fun x y : Matrix α ν E => ψ (pr c Q x y)) := by
    have h := isSelfDualBicharacter_of_symm (V := Matrix α ν E) hψ hψn hψ1 β hβs hβn
    simpa only [hβ] using h
  have hfm : ∀ φ ∈ schwartzBruhatSubmodule (Matrix α ν E),
      hermitianFourier c ψ Q μ φ ∈ schwartzBruhatSubmodule (Matrix α ν E) := fun φ hφ =>
    bicharacterFourier_mem μ hpair hφ
  have hpm := parFun_mem F E c δ hE α ν Q hQ ψ hψ hψn hψ1 χ hχ hη
  obtain ⟨hp1, hpmul⟩ := parFun_sieg_mul F E c δ hE α ν Q hQ ψ hψ hψn hψ1 χ hχ hη
  obtain ⟨κ, hκ, hrel⟩ := weyl_cell_relation F E c δ hE α ν Q hQ ψ hψ hψn hψ1 χ hχ hη μ
  obtain ⟨C, hC, hff⟩ := exists_pos_bicharacterFourier_bicharacterFourier μ hpair

  let parL : siegelParabolic c ν → Module.End ℂ (schwartzBruhatSubmodule (Matrix α ν E)) := fun p =>
    { toFun := fun φ => ⟨siegelParabolicOp c ψ χ Q (mat c p) φ, hpm p p.2 φ φ.2⟩
      map_add' := fun φ φ' => Subtype.ext (funext fun x => by
        simp only [siegelParabolicOp, Submodule.coe_add, Pi.add_apply]; ring)
      map_smul' := fun z φ => Subtype.ext (funext fun x => by
        simp only [siegelParabolicOp, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul,
            RingHom.id_apply]; ring) }
  let ρ₀ : siegelParabolic c ν →* Module.End ℂ (schwartzBruhatSubmodule (Matrix α ν E)) :=
    { toFun := parL
      map_one' := LinearMap.ext fun φ => Subtype.ext (hp1 φ)
      map_mul' := fun p q => LinearMap.ext fun φ => Subtype.ext (hpmul p p.2 q q.2 φ) }

  have hint : ∀ φ : Matrix α ν E → ℂ, φ ∈ schwartzBruhatSubmodule (Matrix α ν E) → ∀ x,
      Integrable (fun y => ψ (pr c Q x y) * φ y) μ := by
    intro φ hφ x
    have hlc : IsLocallyConstant (fun y => ψ (pr c Q x y) * φ y) :=
      (hpair.isLocallyConstant.comp_continuous (continuous_const.prodMk continuous_id)).mul hφ.1
    exact hlc.continuous.integrable_of_hasCompactSupport hφ.2.mul_left
  have fou_smul : ∀ (k : ℂ) (f : Matrix α ν E → ℂ) x,
      hermitianFourier c ψ Q μ (k • f) x = k * hermitianFourier c ψ Q μ f x := by
    intro k f x
    simp only [hermitianFourier, bicharacterFourier, Pi.smul_apply, smul_eq_mul]
    rw [← integral_const_mul]
    congr 1; funext y; ring
  let Fo : Module.End ℂ (schwartzBruhatSubmodule (Matrix α ν E)) :=
    { toFun := fun φ => ⟨hermitianFourier c ψ Q μ φ, hfm φ φ.2⟩
      map_add' := fun φ φ' => Subtype.ext (funext fun x => by
        simp only [hermitianFourier, bicharacterFourier, Submodule.coe_add, Pi.add_apply, mul_add]
        exact integral_add (hint _ φ.2 x) (hint _ φ'.2 x))
      map_smul' := fun z φ => Subtype.ext (funext fun x => by
        simp only [Submodule.coe_smul, RingHom.id_apply, Pi.smul_apply, smul_eq_mul]
        exact fou_smul z _ x) }
  have hne : (κ ^ 2 * (C : ℂ)) ≠ 0 := mul_ne_zero (pow_ne_zero _ hκ) (by exact_mod_cast hC.ne')
  have key : ∀ φ : schwartzBruhatSubmodule (Matrix α ν E),
      (((κ • Fo) ((κ • Fo) φ) : schwartzBruhatSubmodule
          (Matrix α ν E)) : Matrix α ν E → ℂ) = fun x => (κ ^ 2 * (C : ℂ)) * (φ : Matrix α ν E → ℂ)
          (-x) := by
    intro φ
    funext x
    show κ * hermitianFourier c ψ Q μ (κ • hermitianFourier c ψ Q μ φ) x = _
    rw [fou_smul]
    have h := hff φ φ.2 x
    change hermitianFourier c ψ Q μ (hermitianFourier c ψ Q μ φ) x = _ at h
    rw [h]
    ring
  have hW : IsUnit (κ • Fo) := by
    rw [Module.End.isUnit_iff]
    constructor
    · intro a b hab
      have h2 := congrArg (fun φ => (((κ • Fo) φ : schwartzBruhatSubmodule
          (Matrix α ν E)) : Matrix α ν E → ℂ)) hab
      simp only [key] at h2
      apply Subtype.ext
      funext x
      have h3 := congrFun h2 (-x)
      simp only [neg_neg] at h3
      exact mul_left_cancel₀ hne h3
    · intro φ
      have hr : (fun x => (φ : Matrix α ν E → ℂ) (-x)) ∈ schwartzBruhatSubmodule (Matrix α ν E) :=
        ⟨φ.2.1.comp_continuous continuous_neg, φ.2.2.comp_homeomorph (Homeomorph.neg _)⟩
      refine ⟨(κ ^ 2 * (C : ℂ))⁻¹ • (κ • Fo) ⟨_, hr⟩, Subtype.ext (funext fun x => ?_)⟩
      rw [map_smul, Submodule.coe_smul, Pi.smul_apply, key]
      simp only [neg_neg, smul_eq_mul]
      exact inv_mul_cancel_left₀ hne _
  obtain ⟨Φ, hΦp,
      hΦw⟩ := Group.exists_monoidHom_of_bigCell_relations (H := (Module.End ℂ
      (schwartzBruhatSubmodule (Matrix α ν E)))ˣ) (siegelParabolic c ν)
    (weylElement c ν) ρ₀.toHomUnits hW.unit
    (by
      intro p q hpq
      apply Units.ext
      apply LinearMap.ext
      intro φ
      apply Subtype.ext
      funext x
      have h := fou_parFun_levi F E c δ hE α ν Q hQ ψ hψ hψn hψ1 χ hχ hη μ p p.2 q q.2 hpq φ
      show κ * hermitianFourier c ψ Q μ (siegelParabolicOp c ψ χ Q (mat c p) φ) x =
        siegelParabolicOp c ψ χ Q (mat c q) (κ • hermitianFourier c ψ Q μ φ) x
      rw [h]
      simp only [siegelParabolicOp, Pi.smul_apply, smul_eq_mul]
      ring)
    (by
      rintro p ⟨p₁, p₂, h⟩
      obtain ⟨q₁, hq₁, q₂, hq₂, he, hop⟩ := hrel p p.2 ⟨p₁, p₁.2, p₂, p₂.2, h⟩
      refine ⟨⟨q₁, hq₁⟩, ⟨q₂, hq₂⟩, he, ?_⟩
      apply Units.ext
      apply LinearMap.ext
      intro φ
      apply Subtype.ext
      exact hop φ φ.2)
    (by
      intro s
      obtain ⟨u,
          hu⟩ :=
          (have : Infinite F :=
          Infinite.of_injective Nat.cast Nat.cast_injective; exists_mul_isInBigCell hE s)
      refine ⟨u, fun g hg => ?_⟩
      obtain ⟨p, hp, q, hq, h⟩ := hu g hg
      exact ⟨⟨p, hp⟩, ⟨q, hq⟩, h⟩)
  refine ⟨κ, (Units.coeHom _).comp Φ, ⟨fun p hp φ => ?_, fun φ => ?_⟩⟩
  · have h := hΦp ⟨p, hp⟩
    change ((Φ ((⟨p,
        hp⟩ : siegelParabolic c ν) : ofForm c (hyperbolicForm ν E)) : Module.End ℂ
        (schwartzBruhatSubmodule (Matrix α ν E))) φ :
      Matrix α ν E → ℂ) = _
    rw [h]
    rfl
  · change ((Φ (weylElement c ν) : Module.End ℂ (schwartzBruhatSubmodule
      (Matrix α ν E))) φ : Matrix α ν E → ℂ) = _
    rw [hΦw, IsUnit.unit_spec]
    rfl

end Exist




theorem weil_heis_intertwine : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E]
    [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E)
    (_ : IsQuadraticInvolution c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν]
    [DecidableEq ν] (Q : Matrix α α E) (_ : IsHerm c Q) (ψ : AddChar F ℂ) (hψ : Continuous ψ) (_ :
    ∀ t,
    ‖ψ t‖ = 1) (_ : ψ ≠ 1) (χ : Eˣ →* Circle) (_ : Continuous χ) (_ : ResEtaPow (R := F) ⊥ χ
    (Fintype.card α)) [MeasurableSpace (Matrix α ν E)] [BorelSpace (Matrix α ν E)] (μ : Measure
    (Matrix α ν E)) [μ.IsAddHaarMeasure] (κ : ℂ) (ω : Representation ℂ (ofForm c
    (hyperbolicForm ν E)) (schwartzBruhatSubmodule (Matrix α ν E))),
    IsLerayWeil c ψ χ Q μ κ ω → ∀ (g : ofForm c (hyperbolicForm ν E)) (w : Matrix α (ν ⊕ ν) E),
    Heisenberg₂ c hψ Q w * ω g = ω g * Heisenberg₂ c hψ Q (w * ((g : GL (ν ⊕ ν) E) : Matrix (ν ⊕ ν)
    (ν ⊕ ν) E)) := by
  intro F _ _ _ _ _ E _ _ _ _ c δ hE α _ _ ν _ _ Q hQ ψ hψ hψ1 hψne χ hχ hη _ _ μ _ κ ω hK
  let U : Subgroup (ofForm c (hyperbolicForm ν E)) :=
    { carrier := {g | ∀ w : Matrix α (ν ⊕ ν) E,
        Heisenberg₂ c hψ Q w * ω g = ω g * Heisenberg₂ c hψ Q (w * mat c g)}
      one_mem' := by
        intro w
        have h1 : mat c (1 : ofForm c (hyperbolicForm ν E)) = 1 := rfl
        rw [map_one, h1, Matrix.mul_one, mul_one, one_mul]
      mul_mem' := by
        intro g h hg hh w
        have hm : mat c (g * h) = mat c g * mat c h := rfl
        rw [map_mul, ← mul_assoc, hg, mul_assoc, hh, ← mul_assoc, hm, Matrix.mul_assoc]
      inv_mem' := by
        intro g hg w
        have h1 : mat c g⁻¹ * mat c g = 1 := by
          change (((g⁻¹ * g : ofForm c (hyperbolicForm ν E)) : GL (ν ⊕ ν) E) : Matrix (ν ⊕ ν)
              (ν ⊕ ν) E) = 1
          rw [inv_mul_cancel]; rfl
        have h2 := hg (w * mat c g⁻¹)
        rw [Matrix.mul_assoc, h1, Matrix.mul_one] at h2
        have h3 : ω g⁻¹ * ω g = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
        have h4 : ω g * ω g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
        show Heisenberg₂ c hψ Q w * ω g⁻¹ = ω g⁻¹ * Heisenberg₂ c hψ Q (w * mat c g⁻¹)
        calc Heisenberg₂ c hψ Q w * ω g⁻¹ = ω g⁻¹ * (ω g * Heisenberg₂ c hψ Q w) * ω g⁻¹ := by
              simp only [← mul_assoc, h3, one_mul]
          _ = ω g⁻¹ * (Heisenberg₂ c hψ Q (w * mat c g⁻¹) * ω g) * ω g⁻¹ := by rw [h2]
          _ = ω g⁻¹ * Heisenberg₂ c hψ Q (w * mat c g⁻¹) := by simp only [mul_assoc, h4, mul_one] }
  have hsieg : siegelParabolic c ν ≤ U := by
    intro p hp w
    refine LinearMap.ext fun φ => Subtype.ext ?_
    simp only [Module.End.mul_apply, heis_apply, hK.apply_of_mem_siegelParabolic p hp]
    exact heisFun_parFun F E c δ hE α ν Q hQ ψ hψ hψ1 hψne χ hχ hη p hp w φ
  have hweyl : weylElement c ν ∈ U := by
    intro w
    refine LinearMap.ext fun φ => Subtype.ext ?_
    simp only [Module.End.mul_apply, heis_apply, hK.weylElement_apply]
    have hs : ∀ f : Matrix α ν E → ℂ, heisFun c ψ Q w (κ • f) = κ • heisFun c ψ Q w f := by
      intro f; funext x; simp only [heisFun, Pi.smul_apply, smul_eq_mul]; ring
    rw [hs, heisFun_fou F E c δ hE α ν Q hQ ψ μ w φ]
    rfl
  have hU :=
      (have : Infinite F :=
      Infinite.of_injective Nat.cast Nat.cast_injective;
      eq_top_of_siegelParabolic_le_of_weylElement_mem hE hsieg hweyl)
  intro g w
  have hg : g ∈ U := hU ▸ Subgroup.mem_top g
  exact hg w




theorem weil_representation_preserves_L2 : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E]
    [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E)
    (_ : IsQuadraticInvolution c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν]
    [DecidableEq ν] (Q : Matrix α α E) (_ : IsHerm c Q) (ψ : AddChar F ℂ) (_ : Continuous ψ) (_ :
    ∀ t,
    ‖ψ t‖ = 1) (_ : ψ ≠ 1) (χ : Eˣ →* Circle) (_ : Continuous χ) (_ : ResEtaPow (R := F) ⊥ χ
    (Fintype.card α)) [MeasurableSpace (Matrix α ν E)] [BorelSpace (Matrix α ν E)] (μ : Measure
    (Matrix α ν E)) [μ.IsAddHaarMeasure] (κ : ℂ) (ω : Representation ℂ (ofForm c
    (hyperbolicForm ν E)) (schwartzBruhatSubmodule (Matrix α ν E))),
    IsLerayWeil c ψ χ Q μ κ ω → ∀ (μ' : Measure (Matrix α ν E)) [μ'.IsAddHaarMeasure] (g : ofForm c
    (hyperbolicForm ν E)) (φ : schwartzBruhatSubmodule (Matrix α ν E)), ∫⁻ x,
    ‖(ω g φ : Matrix α ν E → ℂ) x‖ₑ ^ 2 ∂μ' = ∫⁻ x, ‖(φ : Matrix α ν E → ℂ) x‖ₑ ^ 2 ∂μ' := by
  intro F _ _ _ _ _ E _ _ _ _ c δ hE α _ _ ν _ _ Q hQ ψ hψ hψ1 hψne χ hχ hres _ _ μ _ κ ω hKW μ' _ g
      φ
  have hfd : FiniteDimensional F E := hE.finite
  have htr : IsTopologicalRing E := hE.isTopologicalRing
  have hinv : ContinuousInv₀ E := hE.continuousInv₀
  have ht2 : T2Space E := hE.t2Space
  have hc : Continuous c := hE.continuous_conj
  have hn : Continuous (Algebra.norm F : E → F) := hE.continuous_norm
  have htrc : Continuous (Algebra.trace F E) := hE.continuous_trace
  have : FiniteDimensional F E := hE.finite
  have : IsModuleTopology F (Matrix α ν E) := isModuleTopology_matrix F (E := E) α ν
  have := IsModuleTopology.isTopologicalAddGroup F (Matrix α ν E)
  have := t2Space_of_finiteDimensional F (Matrix α ν E)
  have := locallyCompactSpace_of_finiteDimensional F (Matrix α ν E)
  have := secondCountableTopology_of_finiteDimensional F (Matrix α ν E)
  have := compactOpenExhaustion_of_finiteDimensional F (Matrix α ν E)
  let N : schwartzBruhatSubmodule (Matrix α ν E) → ℝ≥0∞ := fun f => ∫⁻ x,
      ‖(f : Matrix α ν E → ℂ) x‖ₑ ^ 2 ∂μ
  let U : Subgroup (ofForm c (hyperbolicForm ν E)) :=
    { carrier := {g | ∀ φ, N (ω g φ) = N φ}
      one_mem' := by intro φ; simp
      mul_mem' := by
        intro g h hg hh φ
        show N (ω (g * h) φ) = N φ
        rw [map_mul, Module.End.mul_apply, hg, hh]
      inv_mem' := by
        intro g hg φ
        have := hg (ω g⁻¹ φ)
        rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
            Module.End.one_apply] at this
        exact this.symm }
  have hsieg : siegelParabolic c ν ≤ U := by
    intro p hp φ
    show N (ω p φ) = N φ
    simp only [N]
    rw [hKW.apply_of_mem_siegelParabolic p hp φ]
    exact parFun_lintegral_sq F E c δ hE α ν Q hQ ψ hψ hψ1 hψne χ hχ hres μ p hp φ
  obtain ⟨β, hβ, hβs, hβn, -, -⟩ := pr_alg F E c δ hE α ν Q hQ
  have hpair : IsSelfDualBicharacter (fun x y : Matrix α ν E => ψ (pr c Q x y)) := by
    have := isSelfDualBicharacter_of_symm (V := Matrix α ν E) hψ hψ1 hψne β hβs hβn
    simpa only [hβ] using this
  obtain ⟨C, hC, hfi⟩ := exists_pos_bicharacterFourier_bicharacterFourier μ hpair
  have hpl := fun φ (hφ : φ ∈ schwartzBruhatSubmodule (Matrix α ν E)) =>
    lintegral_enorm_bicharacterFourier_sq μ hpair C hC hfi hφ
  have hw : ∀ φ : schwartzBruhatSubmodule (Matrix α ν E),
      N (ω (weylElement c ν) φ) = (‖κ‖ₑ ^ 2 * ENNReal.ofReal C) * N φ := by
    intro φ
    simp only [N]
    rw [hKW.weylElement_apply φ]
    simp only [Pi.smul_apply, smul_eq_mul, enorm_mul, mul_pow]
    rw [lintegral_const_mul' _ _ (by simp), hermitianFourier, hpl _ φ.2, mul_assoc]
  have hww : weylElement c ν * weylElement c ν ∈ siegelParabolic c ν := by
    rw [mem_sieg]
    show ((hyperbolicForm ν E) * (hyperbolicForm ν E)).toBlocks₂₁ = 0
    rw [hyperbolicForm_mul_self]
    ext i j
    simp [toBlocks₂₁]
  obtain ⟨L, hLc, hLo, -⟩ :=
    CompactOpenExhaustion.exists_superset (X := Matrix α ν E) ∅ isCompact_empty
  have hmem : (L : Set (Matrix α ν E)).indicator (1 : Matrix α ν E → ℂ) ∈ schwartzBruhatSubmodule
      (Matrix α ν E) := by
    refine ⟨?_, ?_⟩
    · have hcl : IsClopen (L : Set (Matrix α ν E)) := ⟨AddSubgroup.isClosed_of_isOpen L hLo, hLo⟩
      exact (LocallyConstant.charFn ℂ hcl).isLocallyConstant
    · exact HasCompactSupport.intro hLc (fun x hx => Set.indicator_of_notMem hx _)
  set φ₀ : schwartzBruhatSubmodule (Matrix α ν E) := ⟨_, hmem⟩ with hφ₀
  have hN0 : N φ₀ = μ L := by
    simp only [N, hφ₀]
    have e : (fun x => ‖(L : Set (Matrix α ν E)).indicator (1 : Matrix α ν E → ℂ) x‖ₑ ^ 2) =
        (L : Set (Matrix α ν E)).indicator 1 := by
      funext x
      by_cases hx : x ∈ (L : Set (Matrix α ν E)) <;> simp [hx]
    rw [e, lintegral_indicator_one hLo.measurableSet]
  have hpos : μ L ≠ 0 := (hLo.measure_pos μ ⟨0, L.zero_mem⟩).ne'
  have hfin : μ L ≠ ∞ := hLc.measure_lt_top.ne
  set k : ℝ≥0∞ := ‖κ‖ₑ ^ 2 * ENNReal.ofReal C with hk
  have hkk : k * k = 1 := by
    have h1 : N (ω (weylElement c ν * weylElement c ν) φ₀) = N φ₀ := hsieg hww φ₀
    rw [map_mul, Module.End.mul_apply, hw, hw, ← mul_assoc, hN0] at h1
    have h2 := congrArg (· / μ L) h1
    simpa [ENNReal.mul_div_cancel_right hpos hfin, ENNReal.div_self hpos hfin] using h2
  have hk1 : k = 1 := by
    rcases lt_trichotomy k 1 with h | h | h
    · have : k * k ≤ k * 1 := by gcongr
      rw [hkk, mul_one] at this
      exact absurd this (not_le.mpr h)
    · exact h
    · have : 1 * k ≤ k * k := by gcongr
      rw [hkk, one_mul] at this
      exact absurd this (not_le.mpr h)
  have hwU : weylElement c ν ∈ U := by
    intro φ
    show N (ω (weylElement c ν) φ) = N φ
    rw [hw, hk1, one_mul]
  have htop : U = ⊤ :=
      (have : Infinite F :=
      Infinite.of_injective Nat.cast Nat.cast_injective;
      eq_top_of_siegelParabolic_le_of_weylElement_mem hE hsieg hwU)
  have hgU : g ∈ U := htop ▸ Subgroup.mem_top g
  have hμ' : μ' = Measure.addHaarScalarFactor μ' μ • μ := Measure.isAddLeftInvariant_eq_smul μ' μ
  rw [hμ', lintegral_smul_measure, lintegral_smul_measure]
  exact congrArg _ (hgU φ)



theorem isSmooth_of_isLerayWeil : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F]
    [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E]
    [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (_ : IsQuadraticInvolution c δ) (α : Type)
    [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (Q : Matrix α α E)
    (_ : IsHerm c Q) (ψ : AddChar F ℂ) (_ : Continuous ψ) (_ : ∀ t,
    ‖ψ t‖ = 1) (_ : ψ ≠ 1) (χ : Eˣ →* Circle) (_ : Continuous χ) (_ : ResEtaPow (R := F) ⊥ χ
    (Fintype.card α)) [MeasurableSpace (Matrix α ν E)] [BorelSpace (Matrix α ν E)] (μ : Measure
    (Matrix α ν E)) [μ.IsAddHaarMeasure] (κ : ℂ) (ω : Representation ℂ (ofForm c
    (hyperbolicForm ν E)) (schwartzBruhatSubmodule (Matrix α ν E))),
    IsLerayWeil c ψ χ Q μ κ ω → IsSmooth ω := by
  intro F _ _ _ _ _ E _ _ _ _ c δ hE α _ _ ν _ _ Q hQ ψ hψ hψ1 hψne χ hχ hη _ _ μ _ κ ω hKW
  have htr : IsTopologicalRing E := hE.isTopologicalRing
  have hinv : ContinuousInv₀ E := hE.continuousInv₀
  have ht2 : T2Space E := hE.t2Space
  rw [isSmooth_iff_forall_isOpen]
  intro v
  let U : Subgroup (ofForm c (hyperbolicForm ν E)) :=
    { carrier := {g | ω g v = v}
      one_mem' := by simp
      mul_mem' := by
        intro a b ha hb
        simp only [Set.mem_ofPred_eq] at ha hb ⊢
        rw [map_mul, Module.End.mul_apply, hb, ha]
      inv_mem' := by
        intro a ha
        simp only [Set.mem_ofPred_eq] at ha ⊢
        conv_lhs => rw [← ha]
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
  have key : ∀ u : schwartzBruhatSubmodule (Matrix α ν E),
      ∀ᶠ g in nhds (1 : ofForm c (hyperbolicForm ν E)), g ∈ siegelParabolic c ν → ω g u = u := by
    intro u
    filter_upwards [parFun_fixed_near_one F E c δ hE α ν Q hQ ψ hψ hψ1 hψne χ hχ hη
        (u : Matrix α ν E → ℂ) u.2] with g hg hs
    apply Subtype.ext
    rw [hKW.apply_of_mem_siegelParabolic g hs u]
    exact hg hs
  have hU : IsOpen (U : Set (ofForm c (hyperbolicForm ν E))) := by
    refine isOpen_of_eventually_mem_siegelParabolic c (U := U) (key v) ?_
    filter_upwards [key (ω (weylElement c ν) v)] with g hg hs
    change ω ((weylElement c ν)⁻¹ * g * weylElement c ν) v = v
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply,
        hg hs, ← Module.End.mul_apply, ← map_mul,
      inv_mul_cancel, map_one, Module.End.one_apply]
  exact hU




end Unitary.Internal

open Unitary.Internal

/-! ### The Leray splitting of `U(ν, ν)` -/

section LeraySplitting

variable {F : Type} [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {E : Type} [Field E] [Algebra F E] [TopologicalSpace E]
  [IsModuleTopology F E] [Algebra.IsQuadraticExtension F E]
  {c : E →ₐ[F] E} {δ : E} {α ν : Type} [Fintype α] [DecidableEq α] [Fintype ν] [DecidableEq ν]
  {Q : Matrix α α E} {ψ : UnitaryAdditiveCharacter F} {χ : Eˣ →* Circle}

omit [TopologicalSpace E] [IsModuleTopology F E] [DecidableEq α] in
theorem Unitary.Internal.resEtaPow_of_normResidueSign
    (hres : ∀ a : Fˣ, (χ (Units.map (algebraMap F E : F →* E) a) : ℂ) =
      ((LocalClassField.normResidueSign F E a : ℤ) : ℂ) ^ Fintype.card α) :
    ResEtaPow (R := F) ⊥ χ (Fintype.card α) := by
  classical
  intro a
  rw [hres a, bot_sup_eq, LocalClassField.normResidueSign_pow_eq_ite]

/-- **The Leray splitting of `U(ν, ν)`** (GKT Theorem 11.6 and Corollary 11.7 in Case `3₊` with
`W` split, proved by generators and relations): for every Haar measure `μ` on
`M_{α×ν}(E)` there are a scalar `κ` and a representation `ω` of `U(ν, ν)` on the Schwartz–Bruhat
functions which acts by the explicit operators on the Siegel parabolic and by `κ` times the
Fourier transform at the Weyl element. -/
theorem exists_isLerayWeil (hE : IsQuadraticInvolution c δ) (hQ : Matrix.IsHermitianFor c Q)
    (hQu : IsUnit Q.det) (hχ : Continuous χ)
    (hres : ∀ a : Fˣ, (χ (Units.map (algebraMap F E : F →* E) a) : ℂ) =
      ((LocalClassField.normResidueSign F E a : ℤ) : ℂ) ^ Fintype.card α)
    [MeasurableSpace (Matrix α ν E)] [BorelSpace (Matrix α ν E)] (μ : Measure (Matrix α ν E))
    [μ.IsAddHaarMeasure] :
    ∃ (κ : ℂ) (ω : Representation ℂ (ofForm c (hyperbolicForm ν E)) (SchwartzBruhat
        (Matrix α ν E))),
      IsLerayWeil c ψ.complex χ Q μ κ ω :=
  Exist.exists_isLerayWeil F E c δ hE α ν Q ⟨hQ, hQu⟩ ψ.complex ψ.continuous_complex ψ.norm_complex
    ψ.complex_ne_one χ hχ (resEtaPow_of_normResidueSign hres) μ

namespace IsLerayWeil

variable [MeasurableSpace (Matrix α ν E)] [BorelSpace (Matrix α ν E)] {μ : Measure (Matrix α ν E)}
  [μ.IsAddHaarMeasure] {κ : ℂ}
  {ω : Representation ℂ (ofForm c (hyperbolicForm ν E)) (SchwartzBruhat (Matrix α ν E))}

/-- The Weil representation of the Leray splitting is smooth (GKT Proposition 13.16 for this
pair). -/
theorem isSmooth (hE : IsQuadraticInvolution c δ) (hQ : Matrix.IsHermitianFor c Q)
    (hQu : IsUnit Q.det) (hχ : Continuous χ)
    (hres : ∀ a : Fˣ, (χ (Units.map (algebraMap F E : F →* E) a) : ℂ) =
      ((LocalClassField.normResidueSign F E a : ℤ) : ℂ) ^ Fintype.card α)
    (h : IsLerayWeil c ψ.complex χ Q μ κ ω) : IsSmooth ω :=
  isSmooth_of_isLerayWeil F E c δ hE α ν Q ⟨hQ, hQu⟩ ψ.complex ψ.continuous_complex ψ.norm_complex
    ψ.complex_ne_one χ hχ (resEtaPow_of_normResidueSign hres) μ κ ω h

/-- The Weil representation of the Leray splitting preserves the `L²` norm for every Haar
measure. -/
theorem lintegral_enorm_sq (hE : IsQuadraticInvolution c δ) (hQ : Matrix.IsHermitianFor c Q)
    (hQu : IsUnit Q.det) (hχ : Continuous χ)
    (hres : ∀ a : Fˣ, (χ (Units.map (algebraMap F E : F →* E) a) : ℂ) =
      ((LocalClassField.normResidueSign F E a : ℤ) : ℂ) ^ Fintype.card α)
    (h : IsLerayWeil c ψ.complex χ Q μ κ ω) (μ' : Measure (Matrix α ν E)) [μ'.IsAddHaarMeasure]
    (g : ofForm c (hyperbolicForm ν E)) (φ : SchwartzBruhat (Matrix α ν E)) :
    ∫⁻ x, ‖(ω g φ : Matrix α ν E → ℂ) x‖ₑ ^ 2 ∂μ' = ∫⁻ x, ‖(φ : Matrix α ν E → ℂ) x‖ₑ ^ 2 ∂μ' :=
  weil_representation_preserves_L2 F E c δ hE α ν Q ⟨hQ, hQu⟩ ψ.complex ψ.continuous_complex
    ψ.norm_complex ψ.complex_ne_one χ hχ (resEtaPow_of_normResidueSign hres) μ κ ω h μ' g φ

omit [Algebra.IsQuadraticExtension F E] in
omit [CharZero F] [MeasurableSpace (Matrix α ν E)] [BorelSpace (Matrix α ν E)] in
theorem Unitary.Internal.hermitianSchrodinger_eq_heisenberg [Invertible (2 : F)]
    (k : HeisenbergGroup (HeisenbergGroup.polarizedForm (hermitianPairing (ν := ν) c Q)))
    (φ : SchwartzBruhat (Matrix α ν E)) :
    hermitianSchrodinger c ν Q ψ k φ =
      ψ.complex k.cen • Heisenberg₂ c ψ.continuous_complex Q (fromCols k.vec.1 k.vec.2) φ := by
  apply Subtype.ext
  rw [hermitianSchrodinger_apply, HeisenbergGroup.schrodinger_apply, Submodule.coe_smul,
    heis_apply, schrodingerFun_hermitian, toCols₁_fromCols, toCols₂_fromCols]

/-- **The representation normalizes the Schrödinger representation**: for `g ∈ U(ν, ν)`,
`ω(g) ∘ ρ(h) = ρ(g · h) ∘ ω(g)`, where `U(ν, ν)` acts on the Heisenberg group of `M_{α×2ν}(E)`
through `w ↦ w g⁻¹`. -/
theorem normalizes [Invertible (2 : F)] (hE : IsQuadraticInvolution c δ)
    (hQ : Matrix.IsHermitianFor c Q) (hQu : IsUnit Q.det) (hχ : Continuous χ)
    (hres : ∀ a : Fˣ, (χ (Units.map (algebraMap F E : F →* E) a) : ℂ) =
      ((LocalClassField.normResidueSign F E a : ℤ) : ℂ) ^ Fintype.card α)
    (h : IsLerayWeil c ψ.complex χ Q μ κ ω) :
    HeisenbergGroup.Normalizes (hermitianSchrodinger c ν Q ψ)
      (UnitaryGroup.heisenbergAction c hE.involutive hQ) ω := by
  intro g k
  refine LinearMap.ext fun φ => ?_
  simp only [LinearMap.comp_apply, Unitary.Internal.hermitianSchrodinger_eq_heisenberg, map_smul,
    UnitaryGroup.heisenbergAction_apply]
  congr 1
  set w' : Matrix α (ν ⊕ ν) E :=
    fromCols (UnitaryGroup.rightMulInvEquiv c g k.vec).1 (UnitaryGroup.rightMulInvEquiv c g k.vec).2
  have hw : w' * ((g : GL (ν ⊕ ν) E) : Matrix (ν ⊕ ν) (ν ⊕ ν) E) = fromCols k.vec.1 k.vec.2 := by
    simp only [w', UnitaryGroup.rightMulInvEquiv_apply, fromCols_toCols, Matrix.mul_assoc,
      UnitaryGroup.val_inv_mul_val, Matrix.mul_one]
  have key := LinearMap.congr_fun (weil_heis_intertwine F E c δ hE α ν Q ⟨hQ, hQu⟩ ψ.complex
    ψ.continuous_complex ψ.norm_complex ψ.complex_ne_one χ hχ (resEtaPow_of_normResidueSign hres)
    μ κ ω h g w') φ
  rw [Module.End.mul_apply, Module.End.mul_apply, hw] at key
  exact key.symm

omit [BorelSpace (Matrix α ν E)] [μ.IsAddHaarMeasure] in
omit [DecidableEq α] in
/-- **The Levi formula** (GKT Proposition 12.27 (1) with Proposition 12.29, `β(m(a)) = χ(det a)`):
`siegelLevi a = diag(a, c(a)⁻ᵀ)` acts by
`φ ↦ χ(det a) |N_{E/F} det a|_F^{|α|/2} φ(· a)`. -/
theorem siegelLevi_apply (hE : IsQuadraticInvolution c δ)
    (hres : ∀ a : Fˣ, (χ (Units.map (algebraMap F E : F →* E) a) : ℂ) =
      ((LocalClassField.normResidueSign F E a : ℤ) : ℂ) ^ Fintype.card α)
    (h : IsLerayWeil c ψ.complex χ Q μ κ ω) (a : GL ν E) (φ : SchwartzBruhat (Matrix α ν E))
    (x : Matrix α ν E) :
    (ω (siegelLevi c hE.involutive a) φ : Matrix α ν E → ℂ) x =
      (χ (Matrix.GeneralLinearGroup.det a) : ℂ) *
        (((distribHaarChar F (Units.map (Algebra.norm F : E →* F)
          (Matrix.GeneralLinearGroup.det a)) : ℝ) ^ ((Fintype.card α : ℝ) / 2) : ℝ) : ℂ) *
        (φ : Matrix α ν E → ℂ) (x * (a : Matrix ν ν E)) := by
  rw [h.apply_of_mem_siegelParabolic _ (siegelLevi_mem c hE.involutive a) φ]
  have h0 : ∀ y : Matrix α ν E, pr c Q y 0 = 0 := fun y => by
    simp [pr, hermitianSymplecticForm, hermitianTensor]
  obtain ⟨-, -, hsc,
      -⟩ := sc_basic F E c δ hE (Fintype.card α) χ (resEtaPow_of_normResidueSign hres)
  have hd := hsc (Matrix.GeneralLinearGroup.det a)
  rw [Matrix.GeneralLinearGroup.val_det_apply] at hd
  simp only [siegelParabolicOp, siegelLevi_val, toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂,
    Matrix.mul_zero, h0, mul_zero, AddChar.map_zero_eq_one, one_mul, hd]

end IsLerayWeil

end LeraySplitting

end Langlands.Theta

/-! ### Deprecated aliases -/

namespace Langlands.Theta

@[deprecated IsLerayWeil (since := "2026-11-23")]
alias IsKudlaWeil := IsLerayWeil

@[deprecated IsLerayWeil.apply_of_mem_siegelParabolic (since := "2026-11-23")]
alias IsKudlaWeil.apply_of_mem_siegelParabolic := IsLerayWeil.apply_of_mem_siegelParabolic

@[deprecated IsLerayWeil.weylElement_apply (since := "2026-11-23")]
alias IsKudlaWeil.weylElement_apply := IsLerayWeil.weylElement_apply

@[deprecated IsLerayWeil.mk (since := "2026-11-23")]
alias IsKudlaWeil.mk := IsLerayWeil.mk

@[deprecated exists_isLerayWeil (since := "2026-11-23")]
alias exists_isKudlaWeil := exists_isLerayWeil

@[deprecated IsLerayWeil.isSmooth (since := "2026-11-23")]
alias IsKudlaWeil.isSmooth := IsLerayWeil.isSmooth

@[deprecated IsLerayWeil.lintegral_enorm_sq (since := "2026-11-23")]
alias IsKudlaWeil.lintegral_enorm_sq := IsLerayWeil.lintegral_enorm_sq

@[deprecated IsLerayWeil.normalizes (since := "2026-11-23")]
alias IsKudlaWeil.normalizes := IsLerayWeil.normalizes

@[deprecated IsLerayWeil.siegelLevi_apply (since := "2026-11-23")]
alias IsKudlaWeil.siegelLevi_apply := IsLerayWeil.siegelLevi_apply

end Langlands.Theta
