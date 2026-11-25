import Langlands.Group.Unitary.Hyperbolic
import Langlands.Group.Classical.Bruhat

/-!
# `U(ν, ν)` and `U(Q)` as isometry groups of `ε`-Hermitian spaces

The matrix groups of `Langlands.Group.Unitary.Basic` and `Langlands.Group.Unitary.Hyperbolic`
identified with the isometry groups of `Langlands.LinearAlgebra.EpsilonHermitian.Basic`, and the
Siegel parabolic, its Levi factor and unipotent radical, and the Weyl elements of
`Langlands.Group.Unitary.Hyperbolic` with those of `Langlands.Group.Classical.SiegelParabolic`
(GKT §4.4.1, the Weyl elements `w_S` of (4.8)).

Let `c` be an involutive `F`-algebra automorphism of a field `E` (`ringInvo c hc`, the involution
as a `RingInvo`).

* `hyperbolicHermitianForm c hc ν`: the skew-Hermitian form `h(u, v) = u J c(v)ᵀ` on the row
  vectors `E^{ν ⊕ ν}`, `J = hyperbolicForm ν E = [[0, 1], [-1, 0]]`, with the standard basis
  `hyperbolicStandardBasis c hc ν`: `eᵢ = (0, εᵢ)`, `eᵢ* = -(εᵢ, 0)`.
* `toIsometryGroup c hc : U(ν, ν) ≃* U(W)`, `g ↦ (w ↦ w g⁻¹)`.
* `toIsometryGroup_mem_siegelParabolic_iff`: the Library's Siegel parabolic (lower left block
  zero) is the stabilizer `P(X)` of `X = span {eᵢ} = {(0, y)}`.
* `toIsometryGroup_siegelLevi`: `diag(a, c(a)⁻ᵀ)` is `m(a')` for the automorphism `a'` of `X`
  with matrix `c(a)` in the basis `(eᵢ)`; `exists_toIsometryGroup_siegelUnipotent`:
  `[[1, b], [0, 1]]` is `n(b')` with `b'(eⱼ*) = ∑ₖ b_{jk} eₖ`; conversely the image of `g` lies
  in `M(X)` (resp. `N(X)`) iff `g` is a Library Levi (resp. unipotent) element
  (`toIsometryGroup_mem_siegelLevi_iff`, `toIsometryGroup_mem_siegelUnipotent_iff`).
* `partialWeylElement c S = [[1 - e_S, e_S], [-e_S, 1 - e_S]]`;
  `toIsometryGroup_partialWeylElement`: it is the Weyl element `w_S` of the standard basis, and
  `weylElement c ν = w_ν` (`toIsometryGroup_weylElement`).
* `det_restrictLagrangianFst`: for `p` in the Siegel parabolic, `det(p|_X) = det (p⁻¹)₂₂`.
* `blockEmbedding c σ : U(ν₁, ν₁) × U(ν₂, ν₂) →* U(ν, ν)` for `σ : ν₁ ⊕ ν₂ ≃ ν` (block diagonal
  matrices `blockMatrix σ A B`), mapping `P₁ × P₂` into `P`; `partialWeylElement_eq_blockEmbedding`:
  `w_S` is the Weyl element of `U(S, S)` embedded along `S ⊕ Sᶜ ≃ ν`.
* `hermitianFormOf c hc Q hQ`: the Hermitian form `(u, v) ↦ uᵀ Q c(v)` on the column vectors
  `E^α`, and `toIsometryGroupOfForm c hc hQ : U(Q) →* U(V)`, `h ↦ (v ↦ h v)`.
-/

noncomputable section

open Matrix

namespace Langlands

namespace UnitaryGroup

open EpsilonHermitianForm

variable {F : Type*} [Field F] {E : Type*} [Field E] [Algebra F E] (c : E →ₐ[F] E)
  (hc : Function.Involutive c) {ν : Type*} [Fintype ν] [DecidableEq ν]

/-- The involution `c` of `E` as a `RingInvo`. -/
def ringInvo : _root_.RingInvo E :=
  RingInvo.mk' ((RingEquiv.toOpposite E).toRingHom.comp c.toRingHom) fun r => hc r

@[simp] theorem conj_ringInvo (a : E) : RingInvo.conj (ringInvo c hc) a = c a := rfl

variable (ν) in
/-- **The hyperbolic skew-Hermitian space** `W = E^{ν ⊕ ν}` of row vectors with
`h(u, v) = u J c(v)ᵀ`, `J = hyperbolicForm ν E`. -/
def hyperbolicHermitianForm : EpsilonHermitianForm (ringInvo c hc) (-1) (ν ⊕ ν → E) where
  toFun u v := u ⬝ᵥ (hyperbolicForm ν E *ᵥ fun j => c (v j))
  map_add_left' x y z := add_dotProduct x y _
  map_smul_left' a x y := smul_dotProduct a x _
  conj_swap' x y := by
    simp only [conj_ringInvo, dotProduct, mulVec, map_sum, map_mul, hc _, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have hJ : c (hyperbolicForm ν E i j) = -hyperbolicForm ν E j i := by
      rcases i with i | i <;> rcases j with j | j <;>
        simp [hyperbolicForm_eq_fromBlocks, one_apply, eq_comm]
    rw [hJ]
    simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one]
    ring

theorem hyperbolicHermitianForm_apply (u v : ν ⊕ ν → E) :
    hyperbolicHermitianForm c hc ν u v = u ⬝ᵥ (hyperbolicForm ν E *ᵥ fun j => c (v j)) := rfl

theorem hyperbolicHermitianForm_single (a b : ν ⊕ ν) :
    hyperbolicHermitianForm c hc ν (Pi.single a 1) (Pi.single b 1) = hyperbolicForm ν E a b := by
  simp [hyperbolicHermitianForm_apply, mulVec, dotProduct, Pi.single_apply]

/-- `h(u M, v M) = u (M J c(M)ᵀ) c(v)ᵀ`. -/
theorem hyperbolicHermitianForm_vecMul (M : Matrix (ν ⊕ ν) (ν ⊕ ν) E) (u v : ν ⊕ ν → E) :
    hyperbolicHermitianForm c hc ν (u ᵥ* M) (v ᵥ* M) =
      u ⬝ᵥ ((M * hyperbolicForm ν E * (M.map c)ᵀ) *ᵥ fun j => c (v j)) := by
  have e : (fun j => c ((v ᵥ* M) j)) = (M.map c)ᵀ *ᵥ fun j => c (v j) := by
    ext j
    simp [vecMul, mulVec, dotProduct, map_sum, mul_comm]
  rw [hyperbolicHermitianForm_apply, e, mulVec_mulVec, ← dotProduct_mulVec, mulVec_mulVec,
    Matrix.mul_assoc]

/-- The matrix entries of `M J c(M)ᵀ` are the values of the form on the rows of `M`. -/
theorem mul_hyperbolicForm_mul_apply (M : Matrix (ν ⊕ ν) (ν ⊕ ν) E) (a b : ν ⊕ ν) :
    (M * hyperbolicForm ν E * (M.map c)ᵀ) a b =
      hyperbolicHermitianForm c hc ν (Pi.single a 1 ᵥ* M) (Pi.single b 1 ᵥ* M) := by
  rw [hyperbolicHermitianForm_vecMul]
  have e : (fun j => c ((Pi.single b (1 : E) : ν ⊕ ν → E) j)) = Pi.single b 1 := by
    ext j; by_cases h : j = b <;> simp [h]
  rw [e, mulVec_single_one, single_one_dotProduct]
  rfl

variable (ν) in
/-- The basis `eᵢ = (0, εᵢ)`, `eᵢ* = -(εᵢ, 0)` of `E^{ν ⊕ ν}` (indexed by `inl i ↦ eᵢ`,
`inr i ↦ eᵢ*`). -/
def hyperbolicBasis : Module.Basis (ν ⊕ ν) E (ν ⊕ ν → E) :=
  ((Pi.basisFun E (ν ⊕ ν)).reindex (Equiv.sumComm ν ν)).unitsSMul (Sum.elim 1 (-1))

@[simp] theorem hyperbolicBasis_inl (i : ν) :
    hyperbolicBasis (E := E) ν (.inl i) = Pi.single (.inr i) 1 := by
  simp [hyperbolicBasis, Module.Basis.unitsSMul_apply]

@[simp] theorem hyperbolicBasis_inr (i : ν) :
    hyperbolicBasis (E := E) ν (.inr i) = -Pi.single (.inl i) 1 := by
  simp [hyperbolicBasis, Module.Basis.unitsSMul_apply]

variable (ν) in
/-- **The standard basis of the hyperbolic skew-Hermitian space** (GKT Definition 4.8):
`eᵢ = (0, εᵢ)`, `eᵢ* = -(εᵢ, 0)`, with `h(eᵢ, eⱼ*) = δᵢⱼ`; `X = span {eᵢ}` is the Lagrangian of
the row vectors `(0, y)`. -/
def hyperbolicStandardBasis : (hyperbolicHermitianForm c hc ν).StandardBasis ν where
  basis := hyperbolicBasis ν
  apply_inl_inl i j := by
    rw [hyperbolicBasis_inl, hyperbolicBasis_inl, hyperbolicHermitianForm_single,
      hyperbolicForm_eq_fromBlocks, fromBlocks_apply₂₂, Matrix.zero_apply]
  apply_inr_inr i j := by
    rw [hyperbolicBasis_inr, hyperbolicBasis_inr, map_neg_left, map_neg_right, neg_neg,
      hyperbolicHermitianForm_single, hyperbolicForm_eq_fromBlocks, fromBlocks_apply₁₁,
      Matrix.zero_apply]
  apply_inl_inr i j := by
    rw [hyperbolicBasis_inl, hyperbolicBasis_inr, map_neg_right, hyperbolicHermitianForm_single,
      hyperbolicForm_eq_fromBlocks, fromBlocks_apply₂₁]
    by_cases h : i = j <;> simp [one_apply, h]

@[simp] theorem hyperbolicStandardBasis_basis :
    (hyperbolicStandardBasis c hc ν).basis = hyperbolicBasis ν := rfl

@[simp] theorem hyperbolicStandardBasis_fst (i : ν) :
    (hyperbolicStandardBasis c hc ν).fst i = Pi.single (.inr i) 1 :=
  hyperbolicBasis_inl i

@[simp] theorem hyperbolicStandardBasis_snd (i : ν) :
    (hyperbolicStandardBasis c hc ν).snd i = -Pi.single (.inl i) 1 :=
  hyperbolicBasis_inr i

/-- The matrix of an element of `U(ν, ν)`. -/
private abbrev matOf (g : ofForm c (hyperbolicForm ν E)) : Matrix (ν ⊕ ν) (ν ⊕ ν) E :=
  ((g : GL (ν ⊕ ν) E) : Matrix (ν ⊕ ν) (ν ⊕ ν) E)

private theorem matOf_inv_mul (g : ofForm c (hyperbolicForm ν E)) :
    matOf c g⁻¹ * matOf c g = 1 := by
  rw [matOf, matOf, Subgroup.coe_inv, Units.inv_mul]

private theorem matOf_mul_inv (g : ofForm c (hyperbolicForm ν E)) :
    matOf c g * matOf c g⁻¹ = 1 := by
  rw [matOf, matOf, Subgroup.coe_inv, Units.mul_inv]

/-- The linear automorphism `w ↦ w g⁻¹` of the row vectors. -/
def rowMulInvEquiv (g : ofForm c (hyperbolicForm ν E)) : (ν ⊕ ν → E) ≃ₗ[E] (ν ⊕ ν → E) where
  toFun w := w ᵥ* matOf c g⁻¹
  invFun w := w ᵥ* matOf c g
  map_add' w w' := add_vecMul _ w w'
  map_smul' a w := smul_vecMul a w _
  left_inv w := by simp only [vecMul_vecMul, matOf_inv_mul, vecMul_one]
  right_inv w := by simp only [vecMul_vecMul, matOf_mul_inv, vecMul_one]

theorem rowMulInvEquiv_apply (g : ofForm c (hyperbolicForm ν E)) (w : ν ⊕ ν → E) :
    rowMulInvEquiv c g w = w ᵥ* ((g⁻¹ : ofForm c (hyperbolicForm ν E)) : GL (ν ⊕ ν) E) := rfl

theorem rowMulInvEquiv_mem (g : ofForm c (hyperbolicForm ν E)) :
    rowMulInvEquiv c g ∈ (hyperbolicHermitianForm c hc ν).isometryGroup := by
  intro u v
  change hyperbolicHermitianForm c hc ν (u ᵥ* matOf c g⁻¹) (v ᵥ* matOf c g⁻¹) = _
  rw [hyperbolicHermitianForm_vecMul,
    (mem_ofForm_hyperbolicForm_iff c ((g⁻¹ : ofForm c (hyperbolicForm ν E)) : GL (ν ⊕ ν) E)).1
      (g⁻¹).2]
  rfl

/-- `U(ν, ν)` acting on the row vectors by `w ↦ w g⁻¹`, into the isometry group of the hyperbolic
skew-Hermitian space. -/
def toIsometryGroupHom :
    ofForm c (hyperbolicForm ν E) →* (hyperbolicHermitianForm c hc ν).isometryGroup where
  toFun g := ⟨rowMulInvEquiv c g, rowMulInvEquiv_mem c hc g⟩
  map_one' := Subtype.ext <| LinearEquiv.ext fun w => by
    change w ᵥ* matOf c 1⁻¹ = w
    rw [inv_one]; exact vecMul_one w
  map_mul' g g' := Subtype.ext <| LinearEquiv.ext fun w => by
    change w ᵥ* matOf c (g * g')⁻¹ = (w ᵥ* matOf c g'⁻¹) ᵥ* matOf c g⁻¹
    rw [vecMul_vecMul, _root_.mul_inv_rev]; rfl

theorem toIsometryGroupHom_bijective : Function.Bijective (toIsometryGroupHom c hc (ν := ν)) := by
  constructor
  · rw [injective_iff_map_eq_one]
    intro g hg
    have h1 : ∀ w, w ᵥ* matOf c g⁻¹ = w := fun w =>
      congrArg (fun k : (hyperbolicHermitianForm c hc ν).isometryGroup =>
        (k : (ν ⊕ ν → E) ≃ₗ[E] (ν ⊕ ν → E)) w) hg
    have h2 : matOf c g⁻¹ = 1 := by
      ext a b
      have := congrFun (h1 (Pi.single a 1)) b
      rw [single_one_vecMul, show (matOf c g⁻¹).row a b = matOf c g⁻¹ a b from rfl] at this
      rw [this, one_apply, Pi.single_apply]; exact if_congr eq_comm rfl rfl
    have h3 : g⁻¹ = 1 := Subtype.ext (Units.ext h2)
    rw [← inv_inv g, h3, inv_one]
  · intro f
    set f₀ : (ν ⊕ ν → E) ≃ₗ[E] (ν ⊕ ν → E) := f.1
    set M : Matrix (ν ⊕ ν) (ν ⊕ ν) E := Matrix.of fun a b => f₀ (Pi.single a 1) b
    set N : Matrix (ν ⊕ ν) (ν ⊕ ν) E := Matrix.of fun a b => f₀.symm (Pi.single a 1) b
    have hM : ∀ w, f₀ w = w ᵥ* M := by
      have : f₀.toLinearMap = Matrix.vecMulLinear M := (Pi.basisFun E (ν ⊕ ν)).ext fun a => by
        ext b; simp [M]
      exact fun w => LinearMap.congr_fun this w
    have hN : ∀ w, f₀.symm w = w ᵥ* N := by
      have : f₀.symm.toLinearMap = Matrix.vecMulLinear N :=
        (Pi.basisFun E (ν ⊕ ν)).ext fun a => by
          ext b; simp [N]
      exact fun w => LinearMap.congr_fun this w
    have hMN : M * N = 1 := by
      ext a b
      have := congrFun (f₀.symm_apply_apply (Pi.single a 1)) b
      rw [hM, hN, vecMul_vecMul, single_one_vecMul,
        show (M * N).row a b = (M * N) a b from rfl] at this
      rw [this, one_apply, Pi.single_apply]; exact if_congr eq_comm rfl rfl
    have hNM : N * M = 1 := by
      ext a b
      have := congrFun (f₀.apply_symm_apply (Pi.single a 1)) b
      rw [hM, hN, vecMul_vecMul, single_one_vecMul,
        show (N * M).row a b = (N * M) a b from rfl] at this
      rw [this, one_apply, Pi.single_apply]; exact if_congr eq_comm rfl rfl
    set g : GL (ν ⊕ ν) E := ⟨N, M, hNM, hMN⟩
    have hg : g ∈ ofForm c (hyperbolicForm ν E) := by
      rw [mem_ofForm_hyperbolicForm_iff]
      ext a b
      change (N * hyperbolicForm ν E * (N.map c)ᵀ) a b = _
      rw [mul_hyperbolicForm_mul_apply c hc, ← hN, ← hN, ← hyperbolicHermitianForm_single c hc]
      exact (f⁻¹).2 _ _
    refine ⟨⟨g, hg⟩, Subtype.ext <| LinearEquiv.ext fun w => ?_⟩
    change w ᵥ* M = f₀ w
    rw [hM]

/-- **The Library's `U(ν, ν)` is the isometry group of the hyperbolic skew-Hermitian space**
`E^{ν ⊕ ν}`, acting on the row vectors by `w ↦ w g⁻¹`. -/
def toIsometryGroup :
    ofForm c (hyperbolicForm ν E) ≃* (hyperbolicHermitianForm c hc ν).isometryGroup :=
  MulEquiv.ofBijective (toIsometryGroupHom c hc) (toIsometryGroupHom_bijective c hc)

@[simp] theorem toIsometryGroup_apply (g : ofForm c (hyperbolicForm ν E)) (w : ν ⊕ ν → E) :
    ((toIsometryGroup c hc g : (hyperbolicHermitianForm c hc ν).isometryGroup) :
      (ν ⊕ ν → E) ≃ₗ[E] (ν ⊕ ν → E)) w =
        w ᵥ* ((g⁻¹ : ofForm c (hyperbolicForm ν E)) : GL (ν ⊕ ν) E) := rfl

/-! ### The Lagrangians `X = span {eᵢ}` and `Y = span {eᵢ*}` -/

theorem mem_lagrangianFst_iff {w : ν ⊕ ν → E} :
    w ∈ (hyperbolicStandardBasis c hc ν).lagrangianFst ↔ ∀ i, w (.inl i) = 0 := by
  constructor
  · intro hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      intro i; simp
    | zero => intro i; rfl
    | add x y _ _ hx hy => intro i; simp [hx i, hy i]
    | smul a x _ hx => intro i; simp [hx i]
  · intro hw
    have : w = ∑ i, w (.inr i) • (hyperbolicStandardBasis c hc ν).fst i := by
      ext k
      rcases k with k | k
      · simp [hw k]
      · simp [Pi.single_apply]
    rw [this]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem mem_lagrangianSnd_iff {w : ν ⊕ ν → E} :
    w ∈ (hyperbolicStandardBasis c hc ν).lagrangianSnd ↔ ∀ i, w (.inr i) = 0 := by
  constructor
  · intro hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      intro i; simp
    | zero => intro i; rfl
    | add x y _ _ hx hy => intro i; simp [hx i, hy i]
    | smul a x _ hx => intro i; simp [hx i]
  · intro hw
    have : w = ∑ i, (-w (.inl i)) • (hyperbolicStandardBasis c hc ν).snd i := by
      ext k
      rcases k with k | k
      · simp [Pi.single_apply]
      · simp [hw k]
    rw [this]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/-- `(x, y) M` for a block matrix `M`, read on the coordinates: its `inl`-part. -/
theorem vecMul_fromBlocks_inl {ι : Type*} [Fintype ι] (w : ι ⊕ ι → E) (A B C D : Matrix ι ι E)
    (j : ι) : (w ᵥ* fromBlocks A B C D) (.inl j) =
      ((fun i => w (.inl i)) ᵥ* A + (fun i => w (.inr i)) ᵥ* C) j := by
  simp [vecMul, dotProduct, Fintype.sum_sum_type]

theorem vecMul_fromBlocks_inr {ι : Type*} [Fintype ι] (w : ι ⊕ ι → E) (A B C D : Matrix ι ι E)
    (j : ι) : (w ᵥ* fromBlocks A B C D) (.inr j) =
      ((fun i => w (.inl i)) ᵥ* B + (fun i => w (.inr i)) ᵥ* D) j := by
  simp [vecMul, dotProduct, Fintype.sum_sum_type]

private theorem matOf_eq_fromBlocks (g : ofForm c (hyperbolicForm ν E)) :
    matOf c g = fromBlocks (matOf c g).toBlocks₁₁ (matOf c g).toBlocks₁₂ (matOf c g).toBlocks₂₁
      (matOf c g).toBlocks₂₂ := (fromBlocks_toBlocks _).symm

/-- **The Library's Siegel parabolic is the stabilizer of `X = span {eᵢ}`** (GKT §4.4.1). -/
theorem toIsometryGroup_mem_siegelParabolic_iff {g : ofForm c (hyperbolicForm ν E)} :
    toIsometryGroup c hc g ∈ (hyperbolicHermitianForm c hc ν).siegelParabolic
      (hyperbolicStandardBasis c hc ν).lagrangianFst ↔ g ∈ siegelParabolic c ν := by
  have key : ∀ g : ofForm c (hyperbolicForm ν E), (matOf c g⁻¹).toBlocks₂₁ = 0 ↔
      ∀ w ∈ (hyperbolicStandardBasis c hc ν).lagrangianFst,
        ((toIsometryGroup c hc g : (hyperbolicHermitianForm c hc ν).isometryGroup) :
          (ν ⊕ ν → E) ≃ₗ[E] (ν ⊕ ν → E)) w ∈ (hyperbolicStandardBasis c hc ν).lagrangianFst := by
    intro g
    constructor
    · intro h0 w hw
      rw [mem_lagrangianFst_iff] at hw ⊢
      intro j
      rw [toIsometryGroup_apply, show (((g⁻¹ : ofForm c (hyperbolicForm ν E)) : GL (ν ⊕ ν) E) :
        Matrix (ν ⊕ ν) (ν ⊕ ν) E) = matOf c g⁻¹ from rfl, matOf_eq_fromBlocks c g⁻¹, h0,
        vecMul_fromBlocks_inl]
      have : (fun i => w (.inl i)) = 0 := funext hw
      simp [this]
    · intro H
      ext i j
      have := (mem_lagrangianFst_iff c hc).1 (H _ (Submodule.subset_span ⟨i, rfl⟩)) j
      rw [toIsometryGroup_apply, hyperbolicStandardBasis_fst, single_one_vecMul] at this
      exact this
  constructor
  · intro hg
    have h1 : g⁻¹ ∈ siegelParabolic c ν :=
      (key g).2 fun w hw => apply_mem_of_mem_siegelParabolic hg hw
    simpa using (siegelParabolic c ν).inv_mem h1
  · intro hg
    exact mem_siegelParabolic_of_le ((key g).1 ((siegelParabolic c ν).inv_mem hg))

/-! ### The Weyl elements `w_S` -/

variable (ν) in
/-- The diagonal matrix with entries `1` on `S` and `0` off `S`. -/
def idempotentOf (S : Finset ν) : Matrix ν ν E := diagonal fun i => if i ∈ S then 1 else 0

private theorem idem_mul_idem (S : Finset ν) :
    idempotentOf (E := E) ν S * idempotentOf ν S = idempotentOf ν S := by
  rw [idempotentOf, diagonal_mul_diagonal]; congr 1; funext i; split_ifs <;> simp

private theorem idem_mul_compl (S : Finset ν) :
    idempotentOf (E := E) ν S * (1 - idempotentOf ν S) = 0 := by
  rw [Matrix.mul_sub, Matrix.mul_one, idem_mul_idem, sub_self]

private theorem compl_mul_idem (S : Finset ν) :
    (1 - idempotentOf (E := E) ν S) * idempotentOf ν S = 0 := by
  rw [Matrix.sub_mul, Matrix.one_mul, idem_mul_idem, sub_self]

private theorem compl_mul_compl (S : Finset ν) :
    (1 - idempotentOf (E := E) ν S) * (1 - idempotentOf ν S) = 1 - idempotentOf ν S := by
  rw [Matrix.sub_mul, Matrix.one_mul, idem_mul_compl, sub_zero]

omit [Fintype ν] in
private theorem transpose_idem (S : Finset ν) :
    (idempotentOf (E := E) ν S)ᵀ = idempotentOf ν S := diagonal_transpose _

omit [Fintype ν] in
private theorem map_idem (S : Finset ν) :
    (idempotentOf (E := E) ν S).map c = idempotentOf ν S := by
  ext i j; by_cases h : i = j <;> simp [idempotentOf, h]

omit [Fintype ν] in
private theorem map_neg_idem (S : Finset ν) :
    (-idempotentOf (E := E) ν S).map c = -idempotentOf ν S := by
  ext i j; by_cases h : i = j <;> simp [idempotentOf, h]

omit [Fintype ν] in
private theorem map_compl (S : Finset ν) :
    (1 - idempotentOf (E := E) ν S).map c = 1 - idempotentOf ν S := by
  ext i j; by_cases h : i = j <;> simp [idempotentOf, h, one_apply]

/-- **The Weyl element `w_S`** of `U(ν, ν)` for `S ⊆ ν`: `[[1 - e_S, e_S], [-e_S, 1 - e_S]]`,
`e_S` the diagonal idempotent of `S`; it is `[[0, 1], [-1, 0]]` on the coordinates in `S` and the
identity on the others. -/
def partialWeylElement (S : Finset ν) : ofForm c (hyperbolicForm ν E) :=
  ⟨⟨fromBlocks (1 - idempotentOf ν S) (idempotentOf ν S) (-idempotentOf ν S)
      (1 - idempotentOf ν S),
    fromBlocks (1 - idempotentOf ν S) (-idempotentOf ν S) (idempotentOf ν S)
      (1 - idempotentOf ν S), by
      simp only [fromBlocks_multiply, compl_mul_compl, idem_mul_idem, idem_mul_compl,
        compl_mul_idem, Matrix.mul_neg, Matrix.neg_mul, neg_neg, neg_zero, add_zero]
      rw [sub_add_cancel, add_sub_cancel, ← fromBlocks_one], by
      simp only [fromBlocks_multiply, compl_mul_compl, idem_mul_idem, idem_mul_compl,
        compl_mul_idem, Matrix.mul_neg, Matrix.neg_mul, neg_neg, neg_zero, add_zero]
      rw [sub_add_cancel, add_sub_cancel, ← fromBlocks_one]⟩, by
    rw [mem_ofForm_hyperbolicForm_iff, hyperbolicForm_eq_fromBlocks]
    simp only [fromBlocks_map, fromBlocks_transpose, map_compl, map_neg_idem, map_idem,
      transpose_sub, transpose_neg, transpose_one, transpose_idem, fromBlocks_multiply,
      compl_mul_compl, idem_mul_idem, idem_mul_compl, compl_mul_idem, Matrix.mul_neg,
      Matrix.neg_mul, neg_neg, neg_zero, add_zero, zero_add, Matrix.mul_one, Matrix.mul_zero]
    rw [add_sub_cancel, ← neg_add, sub_add_cancel]⟩

theorem partialWeylElement_val (S : Finset ν) :
    ((partialWeylElement c S : GL (ν ⊕ ν) E) : Matrix (ν ⊕ ν) (ν ⊕ ν) E) =
      fromBlocks (1 - idempotentOf ν S) (idempotentOf ν S) (-idempotentOf ν S)
        (1 - idempotentOf ν S) := rfl

theorem partialWeylElement_inv_val (S : Finset ν) :
    (((partialWeylElement c S)⁻¹ : ofForm c (hyperbolicForm ν E)) : GL (ν ⊕ ν) E) =
      (fromBlocks (1 - idempotentOf ν S) (-idempotentOf ν S) (idempotentOf ν S)
        (1 - idempotentOf ν S) : Matrix (ν ⊕ ν) (ν ⊕ ν) E) := rfl

theorem partialWeylElement_univ :
    partialWeylElement c (Finset.univ : Finset ν) = weylElement c ν := by
  have h1 : idempotentOf (E := E) ν Finset.univ = 1 := by
    simp [idempotentOf]
  apply Subtype.ext
  apply Units.ext
  rw [partialWeylElement_val, weylElement_val, h1, hyperbolicForm_eq_fromBlocks, sub_self]

/-- **The Library's `w_S` is the Weyl element `w_S` of the standard basis** (GKT (4.8)): it maps
`eᵢ ↦ -eᵢ*`, `eᵢ* ↦ eᵢ` for `i ∈ S` and fixes the other basis vectors. -/
theorem toIsometryGroup_partialWeylElement (S : Finset ν) :
    toIsometryGroup c hc (partialWeylElement c S) =
      (hyperbolicStandardBasis c hc ν).weylElement S := by
  refine (hyperbolicStandardBasis c hc ν).isometryGroup_ext fun k => ?_
  rw [StandardBasis.weylElement_basis, toIsometryGroup_apply, partialWeylElement_inv_val]
  ext b
  rcases k with i | i <;> rcases b with b | b <;> by_cases hi : i ∈ S <;>
    rcases eq_or_ne b i with rfl | hb <;>
    simp [StandardBasis.weylImage, idempotentOf, one_apply, Pi.single_apply, vecMul, dotProduct,
      *, Ne.symm]

/-- **The Library's Weyl element is `w_ν`** of the standard basis (GKT (4.8), `S = ν`). -/
theorem toIsometryGroup_weylElement :
    toIsometryGroup c hc (weylElement c ν) =
      (hyperbolicStandardBasis c hc ν).weylElement Finset.univ := by
  rw [← partialWeylElement_univ, toIsometryGroup_partialWeylElement]

/-! ### The Siegel parabolic on `X`: the restriction `p|_X` -/

variable (ν) in
/-- The basis `(eᵢ)` of the Lagrangian `X = span {eᵢ}`. -/
def lagrangianFstBasis : Module.Basis ν E (hyperbolicStandardBasis c hc ν).lagrangianFst :=
  Module.Basis.span (show LinearIndependent E (hyperbolicStandardBasis c hc ν).fst from
    (hyperbolicStandardBasis c hc ν).basis.linearIndependent.comp _ Sum.inl_injective)

@[simp] theorem lagrangianFstBasis_apply (i : ν) :
    (lagrangianFstBasis c hc ν i : ν ⊕ ν → E) = Pi.single (.inr i) 1 :=
  (congrArg Subtype.val (Module.Basis.span_apply (show LinearIndependent E
    (hyperbolicStandardBasis c hc ν).fst from
      (hyperbolicStandardBasis c hc ν).basis.linearIndependent.comp _ Sum.inl_injective) i)).trans
    (hyperbolicStandardBasis_fst c hc i)

/-- The coordinates of `x ∈ X` in the basis `(eᵢ)` are its last `ν` entries. -/
theorem lagrangianFstBasis_repr (x : (hyperbolicStandardBasis c hc ν).lagrangianFst) (i : ν) :
    (lagrangianFstBasis c hc ν).repr x i = (x : ν ⊕ ν → E) (.inr i) := by
  have key : (lagrangianFstBasis c hc ν).coord i =
      (LinearMap.proj (.inr i)).comp (hyperbolicStandardBasis c hc ν).lagrangianFst.subtype :=
    (lagrangianFstBasis c hc ν).ext fun j => by
      rw [Module.Basis.coord_apply, Module.Basis.repr_self, LinearMap.comp_apply,
        Submodule.subtype_apply, lagrangianFstBasis_apply, LinearMap.proj_apply,
        Finsupp.single_apply]
      by_cases h : j = i <;> simp [h, Ne.symm]
  exact LinearMap.congr_fun key x

/-- The restriction `p|_X` of an element of the Siegel parabolic to `X`. -/
abbrev restrictLagrangianFst {p : ofForm c (hyperbolicForm ν E)} (hp : p ∈ siegelParabolic c ν) :
    (hyperbolicStandardBasis c hc ν).lagrangianFst ≃ₗ[E]
      (hyperbolicStandardBasis c hc ν).lagrangianFst :=
  restrictOfMemSiegelParabolic ((toIsometryGroup_mem_siegelParabolic_iff c hc).2 hp)

/-- **`p|_X` in the basis `(eᵢ)`**: its matrix is `((p⁻¹)₂₂)ᵀ` (`p` acts by
`(0, y) ↦ (0, y (p⁻¹)₂₂)`). -/
theorem toMatrix_restrictLagrangianFst {p : ofForm c (hyperbolicForm ν E)}
    (hp : p ∈ siegelParabolic c ν) :
    LinearMap.toMatrix (lagrangianFstBasis c hc ν) (lagrangianFstBasis c hc ν)
        (restrictLagrangianFst c hc hp).toLinearMap =
      ((((p⁻¹ : ofForm c (hyperbolicForm ν E)) : GL (ν ⊕ ν) E) :
        Matrix (ν ⊕ ν) (ν ⊕ ν) E).toBlocks₂₂)ᵀ := by
  ext i j
  rw [LinearMap.toMatrix_apply, lagrangianFstBasis_repr, LinearEquiv.coe_coe,
    restrictOfMemSiegelParabolic_apply, toIsometryGroup_apply, lagrangianFstBasis_apply,
    single_one_vecMul]
  rfl

/-- **`det(p|_X) = det (p⁻¹)₂₂`**, the Rao value of `p` (GKT (4.15), Corollary 4.36). -/
theorem det_restrictLagrangianFst {p : ofForm c (hyperbolicForm ν E)}
    (hp : p ∈ siegelParabolic c ν) :
    LinearMap.det (restrictLagrangianFst c hc hp).toLinearMap =
      ((((p⁻¹ : ofForm c (hyperbolicForm ν E)) : GL (ν ⊕ ν) E) :
        Matrix (ν ⊕ ν) (ν ⊕ ν) E).toBlocks₂₂).det := by
  rw [← LinearMap.det_toMatrix (lagrangianFstBasis c hc ν), toMatrix_restrictLagrangianFst,
    det_transpose]

/-! ### The Levi factor and the unipotent radical -/

/-- The Siegel Levi elements stabilize `Y = span {eᵢ*}`. -/
theorem toIsometryGroup_siegelLevi_mem (a : GL ν E) :
    toIsometryGroup c hc (siegelLevi c hc a) ∈ (hyperbolicHermitianForm c hc ν).siegelLevi
      (hyperbolicStandardBasis c hc ν).lagrangianFst
      (hyperbolicStandardBasis c hc ν).lagrangianSnd := by
  refine ⟨(toIsometryGroup_mem_siegelParabolic_iff c hc).2 (siegelLevi_mem c hc a),
    mem_siegelParabolic_of_le fun w hw => ?_⟩
  rw [mem_lagrangianSnd_iff] at hw ⊢
  intro j
  rw [toIsometryGroup_apply, show (((siegelLevi c hc a)⁻¹ : ofForm c (hyperbolicForm ν E)) :
      GL (ν ⊕ ν) E) = (fromBlocks ((a⁻¹ : GL ν E) : Matrix ν ν E) 0 0
        ((a : Matrix ν ν E).map c)ᵀ : Matrix (ν ⊕ ν) (ν ⊕ ν) E) from rfl,
    vecMul_fromBlocks_inr]
  have : (fun i => w (.inr i)) = 0 := funext hw
  simp [this]

/-- **The Library's Siegel Levi element `diag(a, c(a)⁻ᵀ)` is `m(a')`** (GKT §4.4.1), where `a'` is
the automorphism of `X = span {eᵢ}` with matrix `c(a)` in the basis `(eᵢ)`. -/
theorem toIsometryGroup_siegelLevi (a : GL ν E) :
    toIsometryGroup c hc (siegelLevi c hc a) =
      (hyperbolicHermitianForm c hc ν).siegelLeviOf
        (hyperbolicStandardBasis c hc ν).nondegenerate
        (hyperbolicStandardBasis c hc ν).isLagrangian_lagrangianFst
        (hyperbolicStandardBasis c hc ν).isLagrangian_lagrangianSnd
        (hyperbolicStandardBasis c hc ν).isCompl_lagrangianFst_lagrangianSnd
        (Matrix.toLinearEquiv (lagrangianFstBasis c hc ν) ((a : Matrix ν ν E).map c)
          (by
            rw [show ((a : Matrix ν ν E).map c).det = c (a : Matrix ν ν E).det from
              (RingHom.map_det c.toRingHom _).symm, ← Matrix.GeneralLinearGroup.val_det_apply]
            exact (Units.isUnit _).map c)) := by
  refine eq_siegelLeviOf _ _ _ _ _ (toIsometryGroup_siegelLevi_mem c hc a) fun x => ?_
  have hp := siegelLevi_mem c hc a
  have key : (restrictLagrangianFst c hc hp).toLinearMap =
      Matrix.toLin (lagrangianFstBasis c hc ν) (lagrangianFstBasis c hc ν)
        ((a : Matrix ν ν E).map c) := by
    apply (LinearMap.toMatrix (lagrangianFstBasis c hc ν) (lagrangianFstBasis c hc ν)).injective
    rw [LinearMap.toMatrix_toLin, toMatrix_restrictLagrangianFst]
    rfl
  exact congrArg Subtype.val (LinearMap.congr_fun key x)

/-- The Library's Siegel unipotent elements lie in `N(X)`. -/
theorem toIsometryGroup_siegelUnipotent_mem (b : Matrix ν ν E) (hb : (b.map c)ᵀ = b) :
    toIsometryGroup c hc (siegelUnipotent c b hb) ∈ (hyperbolicHermitianForm c hc ν).siegelUnipotent
      (hyperbolicStandardBasis c hc ν).lagrangianFst := by
  intro w
  rw [mem_lagrangianFst_iff]
  intro j
  rw [Pi.sub_apply, toIsometryGroup_apply, show (((siegelUnipotent c b hb)⁻¹ :
      ofForm c (hyperbolicForm ν E)) : GL (ν ⊕ ν) E) = (fromBlocks 1 (-b) 0 1 :
        Matrix (ν ⊕ ν) (ν ⊕ ν) E) from rfl, vecMul_fromBlocks_inl]
  simp

/-- **The Library's Siegel unipotent element `[[1, b], [0, 1]]` is `n(b')`** (GKT §4.4.1), where
`b' : Y → X` maps `eⱼ*` to `∑ₖ b_{jk} eₖ`. -/
theorem exists_toIsometryGroup_siegelUnipotent (b : Matrix ν ν E) (hb : (b.map c)ᵀ = b) :
    ∃ b' hb', toIsometryGroup c hc (siegelUnipotent c b hb) =
      (hyperbolicHermitianForm c hc ν).siegelUnipotentOf
        (hyperbolicStandardBasis c hc ν).nondegenerate
        (hyperbolicStandardBasis c hc ν).isLagrangian_lagrangianFst
        (hyperbolicStandardBasis c hc ν).isCompl_lagrangianFst_lagrangianSnd b' hb' ∧
      ∀ j, (b' ⟨_, (hyperbolicStandardBasis c hc ν).snd_mem_lagrangianSnd j⟩ : ν ⊕ ν → E) =
        ∑ k, b j k • (hyperbolicStandardBasis c hc ν).fst k := by
  obtain ⟨b', hb', h⟩ := exists_eq_siegelUnipotentOf (hyperbolicStandardBasis c hc ν).nondegenerate
    (hyperbolicStandardBasis c hc ν).isLagrangian_lagrangianFst
    (hyperbolicStandardBasis c hc ν).isCompl_lagrangianFst_lagrangianSnd
    (toIsometryGroup_siegelUnipotent_mem c hc b hb)
  refine ⟨b', hb', h, fun j => ?_⟩
  have e := siegelUnipotentOf_apply_right (hyperbolicStandardBasis c hc ν).nondegenerate
    (hyperbolicStandardBasis c hc ν).isLagrangian_lagrangianFst
    (hyperbolicStandardBasis c hc ν).isCompl_lagrangianFst_lagrangianSnd hb'
    ⟨_, (hyperbolicStandardBasis c hc ν).snd_mem_lagrangianSnd j⟩
  rw [← h, toIsometryGroup_apply] at e
  rw [eq_sub_of_add_eq' e.symm, show (((siegelUnipotent c b hb)⁻¹ :
      ofForm c (hyperbolicForm ν E)) : GL (ν ⊕ ν) E) = (fromBlocks 1 (-b) 0 1 :
        Matrix (ν ⊕ ν) (ν ⊕ ν) E) from rfl]
  ext k
  rcases k with k | k
  · simp [vecMul_fromBlocks_inl, Pi.single_apply]
  · simp [Pi.single_apply, vecMul, dotProduct]

theorem siegelLevi_one : siegelLevi c hc (1 : GL ν E) = 1 := by
  apply Subtype.ext; apply Units.ext
  rw [siegelLevi_val]
  simp [Matrix.map_one _ (map_zero c) (map_one c)]

theorem siegelUnipotent_zero (h0 : ((0 : Matrix ν ν E).map c)ᵀ = 0) :
    siegelUnipotent c (0 : Matrix ν ν E) h0 = 1 := by
  apply Subtype.ext; apply Units.ext
  rw [siegelUnipotent_val, fromBlocks_one]; rfl

/-- **The Library's Siegel unipotent elements are the unipotent radical `N(X)`**. -/
theorem toIsometryGroup_mem_siegelUnipotent_iff {g : ofForm c (hyperbolicForm ν E)} :
    toIsometryGroup c hc g ∈ (hyperbolicHermitianForm c hc ν).siegelUnipotent
      (hyperbolicStandardBasis c hc ν).lagrangianFst ↔
      ∃ (b : Matrix ν ν E) (hb : (b.map c)ᵀ = b), g = siegelUnipotent c b hb := by
  constructor
  · intro hg
    have hgP := (toIsometryGroup_mem_siegelParabolic_iff c hc).1
      (siegelUnipotent_le_siegelParabolic (hyperbolicStandardBasis c hc ν).nondegenerate
        (hyperbolicStandardBasis c hc ν).isLagrangian_lagrangianFst hg)
    obtain ⟨-, -, a, b, hb, rfl⟩ := exists_eq_siegelLevi_mul_siegelUnipotent c hc g hgP
    have hm : toIsometryGroup c hc (siegelLevi c hc a) ∈
        (hyperbolicHermitianForm c hc ν).siegelUnipotent
          (hyperbolicStandardBasis c hc ν).lagrangianFst := by
      have := Subgroup.mul_mem _ hg
        (Subgroup.inv_mem _ (toIsometryGroup_siegelUnipotent_mem c hc b hb))
      rwa [← map_inv, ← map_mul, mul_inv_cancel_right] at this
    have ha : a = 1 := by
      have hfix : ∀ i, ((toIsometryGroup c hc (siegelLevi c hc a) :
          (hyperbolicHermitianForm c hc ν).isometryGroup) : (ν ⊕ ν → E) ≃ₗ[E] (ν ⊕ ν → E))
            (Pi.single (.inr i) 1) = Pi.single (.inr i) 1 := fun i =>
        apply_eq_of_mem_siegelUnipotent (hyperbolicStandardBasis c hc ν).nondegenerate
          (hyperbolicStandardBasis c hc ν).isLagrangian_lagrangianFst hm
          (by
            rw [← hyperbolicStandardBasis_fst c hc]
            exact (hyperbolicStandardBasis c hc ν).fst_mem_lagrangianFst i)
      have hM : ((a : Matrix ν ν E).map c)ᵀ = 1 := by
        ext i j
        have := congrFun (hfix i) (.inr j)
        rw [toIsometryGroup_apply, show (((siegelLevi c hc a)⁻¹ : ofForm c (hyperbolicForm ν E)) :
            GL (ν ⊕ ν) E) = (fromBlocks ((a⁻¹ : GL ν E) : Matrix ν ν E) 0 0
              ((a : Matrix ν ν E).map c)ᵀ : Matrix (ν ⊕ ν) (ν ⊕ ν) E) from rfl,
          single_one_vecMul] at this
        simpa [one_apply, Pi.single_apply, eq_comm] using this
      have hM' : (a : Matrix ν ν E) = 1 := by
        have h2 := congrArg (fun M : Matrix ν ν E => (Mᵀ).map c) hM
        simp only [transpose_transpose, Matrix.map_map, transpose_one,
          Matrix.map_one _ (map_zero c) (map_one c)] at h2
        rw [show (⇑c ∘ ⇑c) = id from funext hc, Matrix.map_id] at h2
        exact h2
      exact Units.ext hM'
    subst ha
    exact ⟨b, hb, by rw [siegelLevi_one, one_mul]⟩
  · rintro ⟨b, hb, rfl⟩
    exact toIsometryGroup_siegelUnipotent_mem c hc b hb

/-- **The Library's Siegel Levi elements are the Levi subgroup `M(X) = P(X) ∩ P(Y)`**. -/
theorem toIsometryGroup_mem_siegelLevi_iff {g : ofForm c (hyperbolicForm ν E)} :
    toIsometryGroup c hc g ∈ (hyperbolicHermitianForm c hc ν).siegelLevi
      (hyperbolicStandardBasis c hc ν).lagrangianFst
      (hyperbolicStandardBasis c hc ν).lagrangianSnd ↔ ∃ a : GL ν E, g = siegelLevi c hc a := by
  constructor
  · intro hg
    obtain ⟨-, -, a, b, hb, rfl⟩ := exists_eq_siegelLevi_mul_siegelUnipotent c hc g
      ((toIsometryGroup_mem_siegelParabolic_iff c hc).1 hg.1)
    have hn : toIsometryGroup c hc (siegelUnipotent c b hb) ∈
        (hyperbolicHermitianForm c hc ν).siegelParabolic
          (hyperbolicStandardBasis c hc ν).lagrangianSnd := by
      have := Subgroup.mul_mem _
        (Subgroup.inv_mem _ (toIsometryGroup_siegelLevi_mem c hc a).2) hg.2
      rwa [← map_inv, ← map_mul, inv_mul_cancel_left] at this
    have hb0 : b = 0 := by
      ext j k
      have := (mem_lagrangianSnd_iff c hc).1 (apply_mem_of_mem_siegelParabolic hn
        ((hyperbolicStandardBasis c hc ν).snd_mem_lagrangianSnd j)) k
      rw [toIsometryGroup_apply, show (((siegelUnipotent c b hb)⁻¹ :
          ofForm c (hyperbolicForm ν E)) : GL (ν ⊕ ν) E) = (fromBlocks 1 (-b) 0 1 :
            Matrix (ν ⊕ ν) (ν ⊕ ν) E) from rfl, hyperbolicStandardBasis_snd,
        vecMul_fromBlocks_inr] at this
      simpa [Pi.single_apply, vecMul, dotProduct] using this
    subst hb0
    exact ⟨a, by rw [siegelUnipotent_zero, mul_one]⟩
  · rintro ⟨a, rfl⟩
    exact toIsometryGroup_siegelLevi_mem c hc a

/-! ### Block embeddings -/

section Block

variable {ν₁ : Type*} [Fintype ν₁] [DecidableEq ν₁] {ν₂ : Type*} [Fintype ν₂] [DecidableEq ν₂]
  (σ : ν₁ ⊕ ν₂ ≃ ν)

/-- The coordinates `ν ⊕ ν ≃ (ν₁ ⊕ ν₁) ⊕ (ν₂ ⊕ ν₂)` of `σ : ν₁ ⊕ ν₂ ≃ ν`. -/
def blockIndexEquiv : ν ⊕ ν ≃ (ν₁ ⊕ ν₁) ⊕ (ν₂ ⊕ ν₂) :=
  (Equiv.sumCongr σ.symm σ.symm).trans (Equiv.sumSumSumComm ν₁ ν₂ ν₁ ν₂)

/-- The block diagonal matrix `diag(A, B)` written in the coordinates `ν ⊕ ν`. -/
def blockMatrix (A : Matrix (ν₁ ⊕ ν₁) (ν₁ ⊕ ν₁) E) (B : Matrix (ν₂ ⊕ ν₂) (ν₂ ⊕ ν₂) E) :
    Matrix (ν ⊕ ν) (ν ⊕ ν) E :=
  (fromBlocks A 0 0 B).submatrix (blockIndexEquiv σ) (blockIndexEquiv σ)

omit [DecidableEq ν] [DecidableEq ν₁] [DecidableEq ν₂] in
theorem blockMatrix_mul (A A' : Matrix (ν₁ ⊕ ν₁) (ν₁ ⊕ ν₁) E)
    (B B' : Matrix (ν₂ ⊕ ν₂) (ν₂ ⊕ ν₂) E) :
    blockMatrix σ A B * blockMatrix σ A' B' = blockMatrix σ (A * A') (B * B') := by
  rw [blockMatrix, blockMatrix, submatrix_mul_equiv, fromBlocks_multiply]
  simp [blockMatrix]

omit [Fintype ν] [Fintype ν₁] [Fintype ν₂] in
theorem blockMatrix_one : blockMatrix σ (1 : Matrix (ν₁ ⊕ ν₁) (ν₁ ⊕ ν₁) E) 1 = 1 := by
  rw [blockMatrix, fromBlocks_one, submatrix_one_equiv]

omit [Fintype ν] [DecidableEq ν] [Fintype ν₁] [DecidableEq ν₁] [Fintype ν₂] [DecidableEq ν₂] in
theorem transpose_blockMatrix (A : Matrix (ν₁ ⊕ ν₁) (ν₁ ⊕ ν₁) E)
    (B : Matrix (ν₂ ⊕ ν₂) (ν₂ ⊕ ν₂) E) :
    (blockMatrix σ A B)ᵀ = blockMatrix σ Aᵀ Bᵀ := by
  simp only [blockMatrix, transpose_submatrix, fromBlocks_transpose, transpose_zero]

omit [Fintype ν] [DecidableEq ν] [Fintype ν₁] [DecidableEq ν₁] [Fintype ν₂] [DecidableEq ν₂] in
theorem map_blockMatrix (A : Matrix (ν₁ ⊕ ν₁) (ν₁ ⊕ ν₁) E)
    (B : Matrix (ν₂ ⊕ ν₂) (ν₂ ⊕ ν₂) E) :
    (blockMatrix σ A B).map c = blockMatrix σ (A.map c) (B.map c) := by
  simp only [blockMatrix, ← submatrix_map, fromBlocks_map, Matrix.map_zero _ (map_zero c)]

omit [Fintype ν] [Fintype ν₁] [Fintype ν₂] in
theorem blockMatrix_hyperbolicForm :
    blockMatrix σ (hyperbolicForm ν₁ E) (hyperbolicForm ν₂ E) = hyperbolicForm ν E := by
  ext (i | i) (k | k) <;>
    rcases hi : σ.symm i with i₁ | i₂ <;> rcases hk : σ.symm k with k₁ | k₂ <;>
    simp [blockMatrix, blockIndexEquiv, hi, hk, hyperbolicForm_eq_fromBlocks, one_apply,
      ← σ.symm.injective.eq_iff]

omit [Fintype ν] [DecidableEq ν] [Fintype ν₁] [DecidableEq ν₁] [Fintype ν₂] [DecidableEq ν₂] in
theorem toBlocks₂₁_blockMatrix (A : Matrix (ν₁ ⊕ ν₁) (ν₁ ⊕ ν₁) E)
    (B : Matrix (ν₂ ⊕ ν₂) (ν₂ ⊕ ν₂) E) :
    (blockMatrix σ A B).toBlocks₂₁ =
      (fromBlocks A.toBlocks₂₁ 0 0 B.toBlocks₂₁).submatrix σ.symm σ.symm := by
  ext k l
  rcases hk : σ.symm k with k₁ | k₂ <;> rcases hl : σ.symm l with l₁ | l₂ <;>
    simp [blockMatrix, blockIndexEquiv, toBlocks₂₁, hk, hl]

omit [Fintype ν] [DecidableEq ν] [Fintype ν₁] [DecidableEq ν₁] [Fintype ν₂] [DecidableEq ν₂] in
theorem toBlocks₂₂_blockMatrix (A : Matrix (ν₁ ⊕ ν₁) (ν₁ ⊕ ν₁) E)
    (B : Matrix (ν₂ ⊕ ν₂) (ν₂ ⊕ ν₂) E) :
    (blockMatrix σ A B).toBlocks₂₂ =
      (fromBlocks A.toBlocks₂₂ 0 0 B.toBlocks₂₂).submatrix σ.symm σ.symm := by
  ext k l
  rcases hk : σ.symm k with k₁ | k₂ <;> rcases hl : σ.symm l with l₁ | l₂ <;>
    simp [blockMatrix, blockIndexEquiv, toBlocks₂₂, hk, hl]

omit [Fintype ν] [Fintype ν₁] [Fintype ν₂] in
theorem det_toBlocks₂₂_blockMatrix [Fintype ν] [Fintype ν₁] [Fintype ν₂]
    (A : Matrix (ν₁ ⊕ ν₁) (ν₁ ⊕ ν₁) E) (B : Matrix (ν₂ ⊕ ν₂) (ν₂ ⊕ ν₂) E) :
    (blockMatrix σ A B).toBlocks₂₂.det = A.toBlocks₂₂.det * B.toBlocks₂₂.det := by
  rw [toBlocks₂₂_blockMatrix, det_submatrix_equiv_self, det_fromBlocks_zero₂₁]

/-- **The block embedding** `U(ν₁, ν₁) × U(ν₂, ν₂) → U(ν, ν)` along `σ : ν₁ ⊕ ν₂ ≃ ν`:
`(h₁, h₂) ↦ diag(h₁, h₂)` in the coordinates of `ν` (the book's
`U(W₁) × U(W₂) ⊆ U(W₁ ⊕ W₂)` for the hyperbolic spaces). -/
def blockEmbedding :
    ofForm c (hyperbolicForm ν₁ E) × ofForm c (hyperbolicForm ν₂ E) →*
      ofForm c (hyperbolicForm ν E) where
  toFun h := ⟨⟨blockMatrix σ ((h.1 : GL (ν₁ ⊕ ν₁) E) : Matrix (ν₁ ⊕ ν₁) (ν₁ ⊕ ν₁) E)
      ((h.2 : GL (ν₂ ⊕ ν₂) E) : Matrix (ν₂ ⊕ ν₂) (ν₂ ⊕ ν₂) E),
    blockMatrix σ (((h.1⁻¹ : ofForm c (hyperbolicForm ν₁ E)) : GL (ν₁ ⊕ ν₁) E) :
        Matrix (ν₁ ⊕ ν₁) (ν₁ ⊕ ν₁) E)
      (((h.2⁻¹ : ofForm c (hyperbolicForm ν₂ E)) : GL (ν₂ ⊕ ν₂) E) :
        Matrix (ν₂ ⊕ ν₂) (ν₂ ⊕ ν₂) E), by
      rw [blockMatrix_mul, Subgroup.coe_inv, Subgroup.coe_inv, Units.mul_inv, Units.mul_inv,
        blockMatrix_one], by
      rw [blockMatrix_mul, Subgroup.coe_inv, Subgroup.coe_inv, Units.inv_mul, Units.inv_mul,
        blockMatrix_one]⟩, by
    change (blockMatrix σ _ _)ᵀ * hyperbolicForm ν E * (blockMatrix σ _ _).map c =
      hyperbolicForm ν E
    rw [← blockMatrix_hyperbolicForm σ, transpose_blockMatrix, map_blockMatrix, blockMatrix_mul,
      blockMatrix_mul, show (((h.1 : GL (ν₁ ⊕ ν₁) E) : Matrix (ν₁ ⊕ ν₁) (ν₁ ⊕ ν₁) E))ᵀ *
        hyperbolicForm ν₁ E * ((h.1 : GL (ν₁ ⊕ ν₁) E) : Matrix (ν₁ ⊕ ν₁) (ν₁ ⊕ ν₁) E).map c =
          hyperbolicForm ν₁ E from h.1.2,
      show (((h.2 : GL (ν₂ ⊕ ν₂) E) : Matrix (ν₂ ⊕ ν₂) (ν₂ ⊕ ν₂) E))ᵀ *
        hyperbolicForm ν₂ E * ((h.2 : GL (ν₂ ⊕ ν₂) E) : Matrix (ν₂ ⊕ ν₂) (ν₂ ⊕ ν₂) E).map c =
          hyperbolicForm ν₂ E from h.2.2]⟩
  map_one' := Subtype.ext <| Units.ext <| blockMatrix_one σ
  map_mul' g h := Subtype.ext <| Units.ext <| (blockMatrix_mul σ _ _ _ _).symm

theorem blockEmbedding_val
    (h : ofForm c (hyperbolicForm ν₁ E) × ofForm c (hyperbolicForm ν₂ E)) :
    ((blockEmbedding c σ h : GL (ν ⊕ ν) E) : Matrix (ν ⊕ ν) (ν ⊕ ν) E) =
      blockMatrix σ ((h.1 : GL (ν₁ ⊕ ν₁) E) : Matrix (ν₁ ⊕ ν₁) (ν₁ ⊕ ν₁) E)
        ((h.2 : GL (ν₂ ⊕ ν₂) E) : Matrix (ν₂ ⊕ ν₂) (ν₂ ⊕ ν₂) E) := rfl

/-- The block embedding maps `P₁ × P₂` into the Siegel parabolic. -/
theorem blockEmbedding_mem_siegelParabolic
    {h : ofForm c (hyperbolicForm ν₁ E) × ofForm c (hyperbolicForm ν₂ E)}
    (h₁ : h.1 ∈ siegelParabolic c ν₁) (h₂ : h.2 ∈ siegelParabolic c ν₂) :
    blockEmbedding c σ h ∈ siegelParabolic c ν := by
  rw [mem_siegelParabolic, blockEmbedding_val, toBlocks₂₁_blockMatrix,
    (mem_siegelParabolic c).1 h₁, (mem_siegelParabolic c).1 h₂, fromBlocks_zero, submatrix_zero]
  rfl

/-- **`w_S` is the Weyl element of `U(S, S)` embedded in `U(ν, ν)`**. -/
theorem partialWeylElement_eq_blockEmbedding (S : Finset ν) :
    partialWeylElement c S = blockEmbedding c (Equiv.sumCompl (· ∈ S)) (weylElement c _, 1) := by
  apply Subtype.ext
  apply Units.ext
  rw [partialWeylElement_val, blockEmbedding_val, weylElement_val]
  ext (i | i) (k | k) <;> by_cases hi : i ∈ S <;> by_cases hk : k ∈ S <;> by_cases hik : i = k <;>
    simp [blockMatrix, blockIndexEquiv, idempotentOf, hyperbolicForm_eq_fromBlocks, diagonal,
      one_apply, Equiv.sumCompl_symm_apply_of_pos, Equiv.sumCompl_symm_apply_of_neg, *]

end Block

/-! ### The Hermitian space of a Hermitian matrix -/

section Hermitian

variable {α : Type*} [Fintype α] [DecidableEq α] {Q : Matrix α α E}

variable (Q) in
/-- **The Hermitian space `V = (E^α, Q)`** of column vectors, `(u, v) ↦ uᵀ Q c(v)`. -/
def hermitianFormOf (hQ : Matrix.IsHermitianFor c Q) :
    EpsilonHermitianForm (ringInvo c hc) 1 (α → E) where
  toFun u v := u ⬝ᵥ (Q *ᵥ fun j => c (v j))
  map_add_left' x y z := add_dotProduct x y _
  map_smul_left' a x y := smul_dotProduct a x _
  conj_swap' x y := by
    simp only [conj_ringInvo, dotProduct, mulVec, map_sum, map_mul, hc _, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hQ j i]
    simp only [Units.val_one, Int.cast_one]
    ring

omit [DecidableEq α] in
theorem hermitianFormOf_apply (hQ : Matrix.IsHermitianFor c Q) (u v : α → E) :
    hermitianFormOf c hc Q hQ u v = u ⬝ᵥ (Q *ᵥ fun j => c (v j)) := rfl

/-- The linear automorphism `v ↦ h v` of the column vectors, for `h ∈ U(Q)`. -/
def mulVecEquiv (h : ofForm c Q) : (α → E) ≃ₗ[E] (α → E) where
  toFun v := ((h : GL α E) : Matrix α α E) *ᵥ v
  invFun v := (((h⁻¹ : ofForm c Q) : GL α E) : Matrix α α E) *ᵥ v
  map_add' v v' := mulVec_add _ v v'
  map_smul' a v := mulVec_smul _ a v
  left_inv v := by
    simp only [mulVec_mulVec, Subgroup.coe_inv, Units.inv_mul, one_mulVec]
  right_inv v := by
    simp only [mulVec_mulVec, Subgroup.coe_inv, Units.mul_inv, one_mulVec]

/-- **`U(Q)` in the isometry group of `V = (E^α, Q)`**: `h` acts by `v ↦ h v`. -/
def toIsometryGroupOfForm (hQ : Matrix.IsHermitianFor c Q) :
    ofForm c Q →* (hermitianFormOf c hc Q hQ).isometryGroup where
  toFun h := ⟨mulVecEquiv c h, fun u v => by
    change (((h : GL α E) : Matrix α α E) *ᵥ u) ⬝ᵥ
      (Q *ᵥ fun j => c ((((h : GL α E) : Matrix α α E) *ᵥ v) j)) = u ⬝ᵥ (Q *ᵥ fun j => c (v j))
    have hh : ((h : GL α E) : Matrix α α E)ᵀ * Q * ((h : GL α E) : Matrix α α E).map c = Q := h.2
    have e : (fun j => c ((((h : GL α E) : Matrix α α E) *ᵥ v) j)) =
        ((h : GL α E) : Matrix α α E).map c *ᵥ fun j => c (v j) := by
      ext j; simp [mulVec, dotProduct, map_sum]
    rw [e, mulVec_mulVec, ← vecMul_transpose, ← dotProduct_mulVec, mulVec_mulVec,
      ← Matrix.mul_assoc, hh]⟩
  map_one' := Subtype.ext <| LinearEquiv.ext fun v => one_mulVec v
  map_mul' h h' := Subtype.ext <| LinearEquiv.ext fun v => (mulVec_mulVec _ _ _).symm

@[simp] theorem toIsometryGroupOfForm_apply (hQ : Matrix.IsHermitianFor c Q) (h : ofForm c Q)
    (v : α → E) :
    ((toIsometryGroupOfForm c hc hQ h : (hermitianFormOf c hc Q hQ).isometryGroup) :
      (α → E) ≃ₗ[E] (α → E)) v = ((h : GL α E) : Matrix α α E) *ᵥ v := rfl

theorem toIsometryGroupOfForm_injective (hQ : Matrix.IsHermitianFor c Q) :
    Function.Injective (toIsometryGroupOfForm c hc hQ) := by
  rw [injective_iff_map_eq_one]
  intro h hh
  have h1 : ∀ v, ((h : GL α E) : Matrix α α E) *ᵥ v = v := fun v =>
    congrArg (fun k : (hermitianFormOf c hc Q hQ).isometryGroup =>
      (k : (α → E) ≃ₗ[E] (α → E)) v) hh
  refine Subtype.ext (Units.ext ?_)
  ext a b
  have := congrFun (h1 (Pi.single b 1)) a
  rw [mulVec_single_one] at this
  rw [show ((h : GL α E) : Matrix α α E) a b = (((h : GL α E) : Matrix α α E).col b) a from rfl,
    this, Subgroup.coe_one, Units.val_one, one_apply, Pi.single_apply]

end Hermitian

end UnitaryGroup

end Langlands
