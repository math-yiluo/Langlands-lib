import Langlands.Shimura.ProPLevels
import Langlands.Shimura.Unitary.HarrisDivisionLevels

/-!
# Harris's pro-`p` levels `H_p`

Harris 1999, §4, p.310: "we fix a compact open subgroup `K_p ⊂ GJ_p` contained in a fixed maximal
compact subgroup `C_p`. [...] Let `H_p` be an open normal pro-`p` subgroup of `C_p` contained in
`K_p`, and let `H(m) = K^{ℓ,p} × K_ℓ(m) × H_p`." Here `K(m)^p = K^{ℓ,p} × K_ℓ(m)` (p.309).

For an algebra with involution `σ` over a number field `K`, finite over `K`, and a finite place
`w` of `K`, the local points `σ.Points K_w` are totally disconnected, and the points `(g, c)` with
`‖ρ(g) - 1‖ ≤ 1/2` and `‖c - 1‖ ≤ 1/2` (`ρ` the left regular representation with the operator
norm) form an open subgroup which is topologically `p`-torsion when `w` divides `p`. So every
compact open level `C` and open subgroup `L` admit Harris's `H_p` (`AlgebraInvolution.proPLevel`).
Over `ℚ`, `H(m) = K(m)^p × H_p` is the level of `σ(A_f)` assembled from `H_p` and a level
`K(m)^p` of `σ(A_f^p)` (`AlgebraInvolution.harrisProPAdelicLevel`, through
`AlgebraInvolution.localAdelicLevel`).
-/

noncomputable section

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped TensorProduct

set_option autoImplicit false

universe v z

namespace Langlands.Shimura

open Global CompactOpenLevel

/-- If `p` lies in the prime of `w`, then `‖p‖ < 1` in `K_w` with the norm of its valuation. -/
theorem norm_natCast_adicCompletion_lt_one {K : Type v} [Field K] [NumberField K]
    (w : HeightOneSpectrum (𝓞 K)) {p : ℕ} (hp : (p : 𝓞 K) ∈ w.asIdeal) :
    letI := completionNormedField w
    ‖(p : w.adicCompletion K)‖ < 1 := by
  let := completionNormedField w
  rw [Valued.toNormedField.norm_lt_one_iff]
  have h1 : ∀ n : ℕ, ((n : K) : w.adicCompletion K) = (n : w.adicCompletion K) := by
    intro n
    induction n with
    | zero => simp only [Nat.cast_zero, adicCompletion.coe_zero]
    | succ n ih => simp only [Nat.cast_succ, adicCompletion.coe_add, adicCompletion.coe_one, ih]
  have h2 : (p : K) = algebraMap (𝓞 K) K (p : 𝓞 K) := (map_natCast _ _).symm
  rw [← h1 p, valuedAdicCompletion_eq_valuation', h2, valuation_lt_one_iff_mem]
  exact hp

namespace AlgebraInvolution

section Local

variable {K : Type v} [Field K] [NumberField K] {A : Type z} [Ring A] [Algebra K A]
  [Module.Finite K A] (σ : AlgebraInvolution K A) (w : HeightOneSpectrum (𝓞 K))

/-- The local points `σ.Points K_w` are totally disconnected. -/
instance totallyDisconnectedSpace_points :
    TotallyDisconnectedSpace (σ.Points (w.adicCompletion K)) := by
  let := completionNormedField w
  let : TopologicalSpace (w.adicCompletion K ⊗[K] A) :=
    moduleTopology (w.adicCompletion K) (w.adicCompletion K ⊗[K] A)
  have : IsModuleTopology (w.adicCompletion K) (w.adicCompletion K ⊗[K] A) := ⟨rfl⟩
  have := totallyDisconnectedSpace_units (w.adicCompletion K) (w.adicCompletion K ⊗[K] A)
  have : TotallyDisconnectedSpace (w.adicCompletion K)ˣ :=
    totallyDisconnectedSpace_of_continuous_injective Units.continuous_val Units.val_injective
  exact inferInstanceAs (TotallyDisconnectedSpace (σ.baseChange (w.adicCompletion K)).similitudes)

/-- The principal points of `σ.Points K_w`: the points `(g, c)` with `‖ρ(g) - 1‖ ≤ 1/2` and
`‖c - 1‖ ≤ 1/2`, for the left regular representation `ρ` of `K_w ⊗[K] A` with the operator norm
and the norm of the valuation of `K_w`. -/
def principalPoints : Subgroup (σ.Points (w.adicCompletion K)) :=
  letI := completionNormedField w
  ((regularPrincipalUnits (w.adicCompletion K) (w.adicCompletion K ⊗[K] A) (1 / 2)
      (by norm_num) (by norm_num)).prod
    (principalUnits (S := w.adicCompletion K) norm_one.le (1 / 2) (by norm_num)
      (by norm_num))).comap
    (σ.baseChange (w.adicCompletion K)).similitudes.subtype

theorem mem_principalPoints (g : σ.Points (w.adicCompletion K)) :
    g ∈ σ.principalPoints w ↔
      letI := completionNormedField w
      ‖regularRepresentation (w.adicCompletion K) (w.adicCompletion K ⊗[K] A)
          ((σ.baseChange (w.adicCompletion K)).underlyingUnit g : w.adicCompletion K ⊗[K] A) -
        1‖ ≤ 1 / 2 ∧
        ‖((Points.multiplier σ (w.adicCompletion K) g : (w.adicCompletion K)ˣ) :
            w.adicCompletion K) - 1‖ ≤ 1 / 2 :=
  Iff.rfl

theorem isOpen_principalPoints :
    IsOpen (σ.principalPoints w : Set (σ.Points (w.adicCompletion K))) := by
  let := completionNormedField w
  let : TopologicalSpace (w.adicCompletion K ⊗[K] A) :=
    moduleTopology (w.adicCompletion K) (w.adicCompletion K ⊗[K] A)
  have : IsModuleTopology (w.adicCompletion K) (w.adicCompletion K ⊗[K] A) := ⟨rfl⟩
  exact ((isOpen_regularPrincipalUnits (w.adicCompletion K) (w.adicCompletion K ⊗[K] A)
    (by norm_num) (by norm_num)).prod
      (isOpen_principalUnits (S := w.adicCompletion K) norm_one.le (by norm_num)
        (by norm_num))).preimage continuous_subtype_val

/-- If `w` divides `p`, the principal points are topologically `p`-torsion. -/
theorem isTopologicallyPTorsion_principalPoints {p : ℕ} (hp : (p : 𝓞 K) ∈ w.asIdeal) :
    IsTopologicallyPTorsion p (σ.principalPoints w) := by
  let := completionNormedField w
  let : TopologicalSpace (w.adicCompletion K ⊗[K] A) :=
    moduleTopology (w.adicCompletion K) (w.adicCompletion K ⊗[K] A)
  have : IsModuleTopology (w.adicCompletion K) (w.adicCompletion K ⊗[K] A) := ⟨rfl⟩
  exact ((isTopologicallyPTorsion_regularPrincipalUnits (w.adicCompletion K)
    (w.adicCompletion K ⊗[K] A) (norm_natCast_adicCompletion_lt_one w hp) _ _ _).prod
      (isTopologicallyPTorsion_principalUnits (S := w.adicCompletion K) norm_one.le
        (norm_natCast_adicCompletion_lt_one w hp) _ _ _)).comap _ Topology.IsInducing.subtypeVal

/-- Harris's `H_p` (1999, p.310): for a prime `p` divisible by `w`, a compact open level `C` of
`σ.Points K_w` and an open subgroup `L`, the normal core in `C` of `L ⊓ principalPoints` is an
open subgroup of `L`, normal in `C` and pro-`p`. -/
def proPLevel {p : ℕ} (hp : p.Prime) (hpw : (p : 𝓞 K) ∈ w.asIdeal)
    (C : CompactOpenLevel (σ.Points (w.adicCompletion K)))
    {L : Subgroup (σ.Points (w.adicCompletion K))}
    (hL : IsOpen (L : Set (σ.Points (w.adicCompletion K)))) :
    NormalProPLevel p C L :=
  NormalProPLevel.ofNormalCore hp C hL (σ.isOpen_principalPoints w)
    (σ.isTopologicallyPTorsion_principalPoints w hpw)

theorem nonempty_normalProPLevel {p : ℕ} (hp : p.Prime) (hpw : (p : 𝓞 K) ∈ w.asIdeal)
    (C : CompactOpenLevel (σ.Points (w.adicCompletion K)))
    {L : Subgroup (σ.Points (w.adicCompletion K))}
    (hL : IsOpen (L : Set (σ.Points (w.adicCompletion K)))) :
    Nonempty (NormalProPLevel p C L) :=
  ⟨σ.proPLevel w hp hpw C hL⟩

end Local

section Adelic

variable {A : Type z} [Ring A] [Algebra ℚ A] [Module.Finite ℚ A] (σ : AlgebraInvolution ℚ A)
  (p : ℕ) (hp : p.Prime) (v : {v : Global.FinitePlace ℚ // (p : 𝓞 ℚ) ∈ v.asIdeal})

/-- The level `L_p × L^p` of `σ(A_f)`: the inverse image, under the published splitting
`σ(A_f) ≃ₜ* σ(Π_{w ∣ p} ℚ_w) × σ(A_f^p)`, of the product of a level `L_p` of `σ(ℚ_v)` and a
level `L^p` of `σ(A_f^p)`. -/
def localAdelicLevel (Lp : CompactOpenLevel (σ.Points (FiniteCompletion ℚ v.1)))
    (L' : CompactOpenLevel (σ.PrimeToPoints p)) : CompactOpenLevel σ.FiniteAdelicPoints :=
  transport (σ.finiteAdelicPointsSplit p hp.ne_zero).symm
    (prod (transport (σ.dividingPrimePointsEquiv p hp v).symm Lp) L')

/-- A finite adelic point lies in `L_p × L^p` exactly when its local image at `v` lies in `L_p`
and its prime-to-`p` component lies in `L^p`. -/
theorem mem_localAdelicLevel (Lp : CompactOpenLevel (σ.Points (FiniteCompletion ℚ v.1)))
    (L' : CompactOpenLevel (σ.PrimeToPoints p)) (g : σ.FiniteAdelicPoints) :
    g ∈ (σ.localAdelicLevel p hp v Lp L').subgroup ↔
      σ.finiteLocalMap v.1 g ∈ Lp.subgroup ∧
        (σ.finiteAdelicPointsSplit p hp.ne_zero g).2 ∈ L'.subgroup := by
  change σ.dividingLocalMap p v (σ.finiteAdelicPointsSplit p hp.ne_zero g).1 ∈ Lp.subgroup ∧
      (σ.finiteAdelicPointsSplit p hp.ne_zero g).2 ∈ L'.subgroup ↔ _
  rw [dividingLocalMap_finiteAdelicPointsSplit]

theorem localAdelicLevel_mono {Lp Mp : CompactOpenLevel (σ.Points (FiniteCompletion ℚ v.1))}
    (h : Lp.subgroup ≤ Mp.subgroup) (L' : CompactOpenLevel (σ.PrimeToPoints p)) :
    (σ.localAdelicLevel p hp v Lp L').subgroup ≤ (σ.localAdelicLevel p hp v Mp L').subgroup :=
  fun g hg => (σ.mem_localAdelicLevel p hp v Mp L' g).mpr
    ⟨h ((σ.mem_localAdelicLevel p hp v Lp L' g).mp hg).1,
      ((σ.mem_localAdelicLevel p hp v Lp L' g).mp hg).2⟩

/-- Harris's `H_p` (1999, p.310) for compact open levels `K_p` and `C_p` of `σ(ℚ_v)`: an open
subgroup of `K_p`, normal in `C_p` and pro-`p`. -/
def harrisProPLevel (Kp Cp : CompactOpenLevel (σ.Points (FiniteCompletion ℚ v.1))) :
    NormalProPLevel p Cp Kp.subgroup :=
  σ.proPLevel v.1 hp v.2 Cp Kp.openSubgroup.isOpen

/-- Harris's `H(m) = K(m)^p × H_p` (1999, p.310): the level of `σ(A_f)` assembled from
`H_p = harrisProPLevel K_p C_p` and a level `K(m)^p` of `σ(A_f^p)`. -/
def harrisProPAdelicLevel (Kp Cp : CompactOpenLevel (σ.Points (FiniteCompletion ℚ v.1)))
    (Km : CompactOpenLevel (σ.PrimeToPoints p)) : CompactOpenLevel σ.FiniteAdelicPoints :=
  σ.localAdelicLevel p hp v (σ.harrisProPLevel p hp v Kp Cp).level Km

/-- `H(m) ⊆ K(m) = K(m)^p × K_p`. -/
theorem harrisProPAdelicLevel_le (Kp Cp : CompactOpenLevel (σ.Points (FiniteCompletion ℚ v.1)))
    (Km : CompactOpenLevel (σ.PrimeToPoints p)) :
    (σ.harrisProPAdelicLevel p hp v Kp Cp Km).subgroup ≤
      (σ.localAdelicLevel p hp v Kp Km).subgroup :=
  σ.localAdelicLevel_mono p hp v (σ.harrisProPLevel p hp v Kp Cp).le Km

end Adelic

end AlgebraInvolution

end Langlands.Shimura
