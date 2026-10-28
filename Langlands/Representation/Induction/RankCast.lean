import Langlands.Group.GL.RankReindex
import Langlands.Group.GL.SingleBlock
import Langlands.Representation.Induction.BlockFactors

/-!
# Normalized product induction along an equality of total ranks

A continuous group isomorphism `φ : G ≃* H` carrying a subgroup `P` exactly onto `Q`,
and matching the inducing representations, identifies smooth induction from `Q`, pulled
back along `φ`, with smooth induction from `P`: a function is precomposed with `φ`, and
the inverse precomposes with `φ.symm`. For a block shape `B` of total rank `m` and
`h : m = n`, the entry-preserving reindex `GL_m ≃* GL_n` along `finCongr h` carries the
standard parabolic of `B` exactly onto that of `B.rankCast h` and matches their Levi
projections, which transports normalized product induction along `h`.
-/

noncomputable section

namespace Langlands.Induction

universe uR uG uH uV

variable {R : Type uR} {G : Type uG} {H : Type uH} {V : Type uV}
variable [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
variable [AddCommGroup V] [Module R V]
variable {P : Subgroup G} {Q : Subgroup H} {σ : Representation R P V}
  {τ : Representation R Q V}

omit [IsTopologicalGroup G] [IsTopologicalGroup H] in
/-- Precomposition `x ↦ f (φ x)` with a continuous homomorphism carrying `P` into `Q`
and matching the inducing representations carries smooth `Q`-covariant functions on `H`
to smooth `P`-covariant functions on `G`. -/
def comapSmoothFunction (φ : G →* H) (hφ : Continuous φ) (hPQ : ∀ p : P, φ p ∈ Q)
    (hστ : ∀ p : P, τ ⟨φ p, hPQ p⟩ = σ p) (f : SmoothFunctions Q τ) :
    SmoothFunctions P σ :=
  ⟨⟨fun x => eval Q τ f (φ x), by
    intro p x
    change eval Q τ f (φ ((p : G) * x)) = σ p (eval Q τ f (φ x))
    rw [map_mul, ← hστ p]
    exact f.1.2 ⟨φ p, hPQ p⟩ (φ x)⟩, by
    obtain ⟨K, hK⟩ := f.property
    refine ⟨K.comap φ hφ, ?_⟩
    intro k
    apply Subtype.ext
    funext x
    change eval Q τ f (φ (x * (k : G))) = eval Q τ f (φ x)
    rw [map_mul]
    exact congrArg (fun ψ : EquivariantFunctions Q τ => ψ.1 (φ x)) (hK ⟨φ k, k.2⟩)⟩

omit [IsTopologicalGroup G] [IsTopologicalGroup H] in
@[simp]
theorem comapSmoothFunction_eval (φ : G →* H) (hφ : Continuous φ) (hPQ : ∀ p : P, φ p ∈ Q)
    (hστ : ∀ p : P, τ ⟨φ p, hPQ p⟩ = σ p) (f : SmoothFunctions Q τ) (x : G) :
    eval P σ (comapSmoothFunction φ hφ hPQ hστ f) x = eval Q τ f (φ x) := rfl

omit [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace H]
  [IsTopologicalGroup H] in
/-- The inverse of an isomorphism carrying `P` exactly onto `Q` carries `Q` into `P`. -/
private theorem symm_mem_of_mem_iff (φ : G ≃* H) (hPQ : ∀ g : G, φ g ∈ Q ↔ g ∈ P)
    (q : Q) : φ.symm q ∈ P := by
  rw [← hPQ, MulEquiv.apply_symm_apply]
  exact q.2

omit [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace H]
  [IsTopologicalGroup H] in
/-- The inverse of an isomorphism matching the inducing representations matches them. -/
private theorem symm_rep_eq (φ : G ≃* H) (hPQ : ∀ g : G, φ g ∈ Q ↔ g ∈ P)
    (hστ : ∀ p : P, τ ⟨φ p, (hPQ p).2 p.2⟩ = σ p) (q : Q) :
    σ ⟨φ.symm q, symm_mem_of_mem_iff φ hPQ q⟩ = τ q := by
  rw [← hστ]
  congr 1
  apply Subtype.ext
  exact MulEquiv.apply_symm_apply φ q

/-- A continuous group isomorphism `φ : G ≃* H` with continuous inverse, carrying `P`
exactly onto `Q` and matching the inducing representations, identifies smooth induction
from `Q` pulled back along `φ` with smooth induction from `P`. The forward map
precomposes with `φ` and the inverse precomposes with `φ.symm`. -/
def comapSmoothInducedEquiv (φ : G ≃* H) (hφ : Continuous φ) (hφ' : Continuous φ.symm)
    (hPQ : ∀ g : G, φ g ∈ Q ↔ g ∈ P) (hστ : ∀ p : P, τ ⟨φ p, (hPQ p).2 p.2⟩ = σ p) :
    Representation.Equiv ((smoothInduced Q τ).comp φ.toMonoidHom) (smoothInduced P σ) where
  toFun := comapSmoothFunction φ.toMonoidHom hφ (fun p => (hPQ p).2 p.2) hστ
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun := comapSmoothFunction φ.symm.toMonoidHom hφ' (symm_mem_of_mem_iff φ hPQ)
    (symm_rep_eq φ hPQ hστ)
  left_inv f := by
    apply Subtype.ext
    apply Subtype.ext
    funext y
    change eval Q τ f (φ (φ.symm y)) = eval Q τ f y
    rw [MulEquiv.apply_symm_apply]
  right_inv f := by
    apply Subtype.ext
    apply Subtype.ext
    funext x
    change eval P σ f (φ.symm (φ x)) = eval P σ f x
    rw [MulEquiv.symm_apply_apply]
  isIntertwining' g := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    apply Subtype.ext
    funext x
    change eval Q τ f (φ x * φ g) = eval Q τ f (φ (x * g))
    rw [map_mul]

@[simp]
theorem comapSmoothInducedEquiv_eval (φ : G ≃* H) (hφ : Continuous φ)
    (hφ' : Continuous φ.symm) (hPQ : ∀ g : G, φ g ∈ Q ↔ g ∈ P)
    (hστ : ∀ p : P, τ ⟨φ p, (hPQ p).2 p.2⟩ = σ p) (f : SmoothFunctions Q τ) (x : G) :
    eval P σ (comapSmoothInducedEquiv φ hφ hφ' hPQ hστ f) x = eval Q τ f (φ x) := rfl

@[simp]
theorem comapSmoothInducedEquiv_symm_eval (φ : G ≃* H) (hφ : Continuous φ)
    (hφ' : Continuous φ.symm) (hPQ : ∀ g : G, φ g ∈ Q ↔ g ∈ P)
    (hστ : ∀ p : P, τ ⟨φ p, (hPQ p).2 p.2⟩ = σ p) (f : SmoothFunctions P σ) (y : H) :
    eval Q τ ((comapSmoothInducedEquiv φ hφ hφ' hPQ hστ).symm f) y =
      eval P σ f (φ.symm y) := rfl

end Langlands.Induction

namespace Langlands.GeneralLinear.BlockShape

universe u

variable {R : Type u} [CommRing R] {m n : ℕ}

/-- The block shape cast along `rfl` is the original shape. -/
@[simp]
theorem rankCast_rfl (B : BlockShape n) : B.rankCast rfl = B := rfl

/-- The entry-preserving reindex carries the standard parabolic of `B` exactly onto the
standard parabolic of `B.rankCast h`. -/
theorem reindex_mem_rankCast_parabolic_iff (B : BlockShape m) (h : m = n)
    (g : GeneralLinear m R) :
    reindex (R := R) (finCongr h) g ∈ (B.rankCast h).parabolic R ↔ g ∈ B.parabolic R := by
  subst h
  rfl

/-- The entry-preserving reindex is compatible with the Levi projections of `B` and
`B.rankCast h`, whose Levi groups agree. -/
theorem rankCast_leviProjection_reindex (B : BlockShape m) (h : m = n) (p : B.parabolic R) :
    (B.rankCast h).leviProjection R
        ⟨reindex (R := R) (finCongr h) p,
          (B.reindex_mem_rankCast_parabolic_iff h (p : GeneralLinear m R)).2 p.2⟩ =
      B.leviProjection R p := by
  subst h
  rfl

end Langlands.GeneralLinear.BlockShape

namespace Langlands.PadicField.TopologicalData

open GeneralLinear

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
variable (T : F.TopologicalData) {m n : ℕ} (B : GeneralLinear.BlockShape m) (h : m = n)
variable {V : Fin B.length → Type uV} [instV : ∀ i, AddCommGroup (V i)]
  [modV : ∀ i, Module ℂ (V i)]

/-- The positive half modulus of `B.rankCast h` at the reindexed parabolic element is the
positive half modulus of `B`. -/
theorem parabolicHalfModulus_rankCast_reindex (q : B.parabolic F.Carrier) :
    T.parabolicHalfModulus (B.rankCast h)
        ⟨reindex (R := F.Carrier) (finCongr h) q,
          (B.reindex_mem_rankCast_parabolic_iff h (q : GeneralLinear m F.Carrier)).2 q.2⟩ =
      T.parabolicHalfModulus B q := by
  subst h
  rfl

/-- The inducing representations of `B.rankCast h` and `B` agree along the reindex. The
Levi group of `B.rankCast h` is that of `B`, so the block tensor of `σ` over `B` is
composed with the Levi projection of `B.rankCast h`. -/
theorem rankCast_inducing_reindex
    (σ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F.Carrier) (V i))
    (q : B.parabolic F.Carrier) :
    twist (T.parabolicHalfModulus (B.rankCast h))
        ((B.blockTensor σ).comp ((B.rankCast h).leviProjection F.Carrier))
        ⟨reindex (R := F.Carrier) (finCongr h) q,
          (B.reindex_mem_rankCast_parabolic_iff h (q : GeneralLinear m F.Carrier)).2 q.2⟩ =
      twist (T.parabolicHalfModulus B) ((B.blockTensor σ).comp (B.leviProjection F.Carrier))
        q := by
  subst h
  rfl

/-- Normalized product induction transported along the equality of total ranks `h : m = n`:
the normalized product of `σ` over `B.rankCast h`, pulled back along the entry-preserving
reindex `GL_m ≃* GL_n`, is equivalent to the normalized product of `σ` over `B`. The factor
family `σ` and its carrier instances are those of `B`, since `B.rankCast h` has the same
blocks. The forward map precomposes a function on `GL_n` with the reindex, and the inverse
precomposes a function on `GL_m` with the inverse reindex. -/
def normalizedProductInducedRankCastEquiv
    (σ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F.Carrier) (V i)) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup m
    letI := T.generalLinearTopologicalGroup n
    Representation.Equiv
      ((@normalizedProductInduced p _ F T n (B.rankCast h) V instV modV σ).comp
        (reindex (R := F.Carrier) (finCongr h)).toMonoidHom)
      (T.normalizedProductInduced B σ) :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup m
  letI := T.generalLinearTopologicalGroup n
  Induction.comapSmoothInducedEquiv (V := PiTensorProduct ℂ V)
    (reindex (R := F.Carrier) (finCongr h)) (continuous_reindex_finCongr h) (continuous_reindex_finCongr_symm h)
    (B.reindex_mem_rankCast_parabolic_iff h) (T.rankCast_inducing_reindex B h σ)

/-- The forward transport precomposes with the entry-preserving reindex. -/
@[simp]
theorem normalizedProductInducedRankCastEquiv_eval
    (σ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F.Carrier) (V i))
    (f : letI := T.topology
      letI := T.generalLinearTopologicalGroup n
      Induction.SmoothFunctions ((B.rankCast h).parabolic F.Carrier)
        (twist (T.parabolicHalfModulus (B.rankCast h))
          ((B.blockTensor σ).comp ((B.rankCast h).leviProjection F.Carrier))))
    (x : GeneralLinear m F.Carrier) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup m
    letI := T.generalLinearTopologicalGroup n
    Induction.eval (B.parabolic F.Carrier)
        (twist (T.parabolicHalfModulus B) ((B.blockTensor σ).comp (B.leviProjection F.Carrier)))
        (T.normalizedProductInducedRankCastEquiv B h σ f) x =
      Induction.eval ((B.rankCast h).parabolic F.Carrier)
        (twist (T.parabolicHalfModulus (B.rankCast h))
          ((B.blockTensor σ).comp ((B.rankCast h).leviProjection F.Carrier)))
        f (reindex (R := F.Carrier) (finCongr h) x) := rfl

/-- The inverse transport precomposes with the inverse entry-preserving reindex. -/
@[simp]
theorem normalizedProductInducedRankCastEquiv_symm_eval
    (σ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F.Carrier) (V i))
    (f : letI := T.topology
      letI := T.generalLinearTopologicalGroup m
      Induction.SmoothFunctions (B.parabolic F.Carrier)
        (twist (T.parabolicHalfModulus B) ((B.blockTensor σ).comp (B.leviProjection F.Carrier))))
    (y : GeneralLinear n F.Carrier) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup m
    letI := T.generalLinearTopologicalGroup n
    Induction.eval ((B.rankCast h).parabolic F.Carrier)
        (twist (T.parabolicHalfModulus (B.rankCast h))
          ((B.blockTensor σ).comp ((B.rankCast h).leviProjection F.Carrier)))
        ((T.normalizedProductInducedRankCastEquiv B h σ).symm f) y =
      Induction.eval (B.parabolic F.Carrier)
        (twist (T.parabolicHalfModulus B) ((B.blockTensor σ).comp (B.leviProjection F.Carrier)))
        f ((reindex (R := F.Carrier) (finCongr h)).symm y) := rfl

end Langlands.PadicField.TopologicalData
