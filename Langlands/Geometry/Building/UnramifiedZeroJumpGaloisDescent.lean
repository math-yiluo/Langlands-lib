import Langlands.Geometry.Building.RootGroupLinearization
import Langlands.Geometry.Building.UnramifiedFixedPointRootDescent
import Langlands.Geometry.Building.RootFunctionFieldRestriction
import Langlands.Geometry.Building.RootJumpLiftNonMultipliable
import Langlands.Geometry.Building.MaximalUnramifiedValuation
import Langlands.GroupScheme.FilteredTraceDescent
import Langlands.GroupScheme.GaloisStableSubringTrace
import Langlands.GroupScheme.UnramifiedIntegralCosetDescent
import Langlands.GroupScheme.Torus.RootSupportBaseChange

/-! # Galois descent of root filtration jumps through semilinear root coordinates

Let `K/k` be a field extension, `S` a split torus of a `k`-group `G`, `α` a root of `(G, S)`
and `ψ` a family of root functions of `(G_K, S_K)`. Assume that `ψ_{α_K}` is ultrametric on
`U = U_{α_K}(K)`, invariant under the coefficient action of `Aut(K/k)`, and invariant under
conjugation by the points of `S_K` at which every character has valuation one. Assume further
`RootGroupLinearization iS α v`: semilinear coordinates on `U` and on `U₂ = U_{2α_K}(K)`
that torus points of valuation one scale by squares.

* `exists_fixed_jump_of_rootGroupLinearization`: if a jump `u` of `ψ_{α_K}` at `r` is fixed
  by the kernel of a map `res` from `Aut(K/k)` onto a finite group, and a ring `R` with unit
  values of valuation one supplies dual families and trace-one elements in every stable
  subring containing the squares of units, then there is an `Aut(K/k)`-fixed jump.
* `isRootFiltrationJump_fieldRestrict_of_fixed`: over a Galois extension, a fixed jump
  descends to a jump of `α` for `fieldRestrict ψ`.
* `isRootFiltrationJump_fieldRestrict_of_not_lt`: if `ψ_{α_K}(1) ≤ r`, the identity is a jump
  of `α` for `fieldRestrict ψ`.
* `MaximalUnramified.isRootFiltrationJump_fieldRestrict_of_linearization`: for `K = F^ur`,
  the finite level is a finite Galois subextension `E` of `K/F` over which `u` is defined;
  the ring is the ring of integers of `E`.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison

namespace Langlands.Geometry.Building

section Generic

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}

local notation "b" => algebraBaseMap k K
local notation "S_K" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange b) S
local notation "G_K" => CategoryTheory.Functor.obj (GroupScheme.baseChange b) G
local notation "j_K" => CategoryTheory.Functor.map (GroupScheme.baseChange b)
local notation "a_K" a => characterLattice.baseChange b S a

/-- An ultrametric root function is bounded on its root group by its value at `1`. -/
theorem rootFunction_le_one_of_min_le (iS : S.toGrp ⟶ G) (α : characterLattice S)
    (ψ : RootFunctionFamily S_K G_K)
    (hmin : ∀ g ∈ rootGroupPoints (j_K iS) (a_K α), ∀ h ∈ rootGroupPoints (j_K iS) (a_K α),
      min (ψ (a_K α) g) (ψ (a_K α) h) ≤ ψ (a_K α) (g * h⁻¹))
    {g : rationalPoints G_K} (hg : g ∈ rootGroupPoints (j_K iS) (a_K α)) :
    ψ (a_K α) g ≤ ψ (a_K α) 1 := by
  have h := hmin g hg g hg
  rwa [min_self, mul_inv_cancel] at h

variable [IsAffineHom G.X.hom]

/-- The base change of an affine group scheme along `Spec K ⟶ Spec k` is affine. -/
local instance zeroJumpGaloisDescent_isAffineHom_baseChange :
    IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k K)).obj G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom (algebraBaseMap k K))
  infer_instance

/-- **The degenerate case.** If `ψ_{α_K}(1) ≤ r` and `ψ_{α_K}` is ultrametric on `U_{α_K}(K)`,
then a jump of `α_K` at `r` for `ψ` gives a jump of `α` at `r` for `fieldRestrict ψ`: the
identity lies in the filtration, and no point of `U_α(k)` has value `> r`. -/
theorem isRootFiltrationJump_fieldRestrict_of_not_lt (iS : S.toGrp ⟶ G) (α : characterLattice S)
    (ψ : RootFunctionFamily S_K G_K)
    (hmin : ∀ g ∈ rootGroupPoints (j_K iS) (a_K α), ∀ h ∈ rootGroupPoints (j_K iS) (a_K α),
      min (ψ (a_K α) g) (ψ (a_K α) h) ≤ ψ (a_K α) (g * h⁻¹))
    (r : ℝ) (hjump : IsRootFiltrationJump (j_K iS) ψ (a_K α) r)
    (h1 : ¬ (r : WithTop ℝ) < ψ (a_K α) 1) :
    IsRootFiltrationJump iS (RootFunctionFamily.fieldRestrict (k := k) (K := K) ψ) α r := by
  obtain ⟨u, huF, -⟩ := Set.not_subset.mp hjump
  obtain ⟨huU, hur⟩ := mem_rootFiltration.mp huF
  have hr1 : (r : WithTop ℝ) ≤ ψ (a_K α) 1 :=
    hur.trans (rootFunction_le_one_of_min_le iS α ψ hmin huU)
  intro hsub
  have h1mem : (1 : rationalPoints G) ∈
      rootFiltration iS (RootFunctionFamily.fieldRestrict (k := k) (K := K) ψ) α r := by
    refine mem_rootFiltration.mpr ⟨Subgroup.one_mem _, ?_⟩
    rw [RootFunctionFamily.fieldRestrict_apply, map_one]
    exact hr1
  obtain ⟨y, hy, w, -, -⟩ := Set.mem_mul.mp (hsub h1mem)
  obtain ⟨hyU, hyr⟩ := hy
  rw [RootFunctionFamily.fieldRestrict_apply] at hyr
  exact h1 (hyr.trans_le (rootFunction_le_one_of_min_le iS α ψ hmin
    (rationalExtend_mem_rootGroupPoints iS α hyU)))

/-- Scalar extension maps `U_{2α}(k)` into `U_{2α_K}(K)`, with the convention that these
groups are trivial when `2α`, resp. `2α_K`, is not a root. -/
theorem rationalExtend_mem_doubleRootGroupPoints [LocallyOfFiniteType G.X.hom]
    (iS : S.toGrp ⟶ G) (hS : IsSplitTorus S.toGrp) (α : characterLattice S)
    {w : rationalPoints G} (hw : w ∈ doubleRootGroupPoints iS α) :
    rationalExtend k K G w ∈ doubleRootGroupPoints (j_K iS) (a_K α) := by
  classical
  unfold doubleRootGroupPoints at hw ⊢
  by_cases h2 : 2 • α ∈ relativeRoots iS
  · rw [ite_eq_left h2] at hw
    have h2K : 2 • (a_K α) ∈ relativeRoots (j_K iS) := by
      rw [← map_nsmul]
      exact (mem_roots_baseChange_iff (K := K) G S hS iS (2 • α)).mpr h2
    rw [ite_eq_left h2K, ← map_nsmul]
    exact rationalExtend_mem_rootGroupPoints iS (2 • α) hw
  · rw [ite_eq_right h2, Subgroup.mem_bot] at hw
    rw [hw, map_one]
    exact Subgroup.one_mem _

/-- **Descent of a fixed jump.** Over a Galois extension `K/k`, an `Aut(K/k)`-fixed point
`h ∈ U_{α_K}(K)` with `r ≤ ψ_{α_K}(h)` and `h ∉ {g ∈ U_{α_K}(K) | r < ψ_{α_K}(g)} · U_{2α_K}(K)`
is the extension of a point of `U_α(k)`, which witnesses a jump of `α` at `r` for
`fieldRestrict ψ`. -/
theorem isRootFiltrationJump_fieldRestrict_of_fixed [IsGalois k K] [Smooth G.X.hom]
    (iS : S.toGrp ⟶ G) (hS : IsSplitTorus S.toGrp) {α : characterLattice S}
    (hα : α ∈ relativeRoots iS) (ψ : RootFunctionFamily S_K G_K) (r : ℝ)
    {h : rationalPoints G_K} (hU : h ∈ rootGroupPoints (j_K iS) (a_K α))
    (hr : (r : WithTop ℝ) ≤ ψ (a_K α) h)
    (hfix : ∀ σ : K ≃ₐ[k] K, rationalConjugate k K G σ h = h)
    (hne : h ∉ {g | g ∈ rootGroupPoints (j_K iS) (a_K α) ∧ (r : WithTop ℝ) < ψ (a_K α) g} *
      (doubleRootGroupPoints (j_K iS) (a_K α) : Set (rationalPoints G_K))) :
    IsRootFiltrationJump iS (RootFunctionFamily.fieldRestrict (k := k) (K := K) ψ) α r := by
  obtain ⟨h₀, h₀U, rfl⟩ := exists_mem_rootGroupPoints_of_fixed_of_isGalois k K iS hS α
    (mem_relativeRoots.mp hα).1 hfix hU
  intro hsub
  obtain ⟨y, hy, w, hw, hyw⟩ := Set.mem_mul.mp (hsub (mem_rootFiltration.mpr ⟨h₀U, hr⟩))
  obtain ⟨hyU, hyr⟩ := hy
  apply hne
  refine Set.mem_mul.mpr ⟨rationalExtend k K G y,
    ⟨rationalExtend_mem_rootGroupPoints iS α hyU, hyr⟩, rationalExtend k K G w,
    rationalExtend_mem_doubleRootGroupPoints iS hS α hw, ?_⟩
  rw [← hyw, map_mul]

/-- **Fixed jumps from semilinear root coordinates.** Let `ψ_{α_K}` be ultrametric on
`U = U_{α_K}(K)`, invariant under `Aut(K/k)`, and invariant under conjugation by the points of
`S_K` at which every character has valuation one, and let `RootGroupLinearization iS α v` hold.
Let `res : Aut(K/k) →* Γ` onto a finite group have a section `s`, and let `Γ` act on a ring `R`
through `ρ`, compatibly with `incl : R →+* K`, where units of `R` have valuation one. Assume that
every `Γ`-stable subring of `R` containing all squares of units contains a dual family and a
trace-one element. If `r < ψ_{α_K}(1)` and `u ∈ U` with `r ≤ ψ_{α_K}(u)` is fixed by the kernel
of `res` and lies outside `{g ∈ U | r < ψ_{α_K}(g)} · U_{2α_K}(K)`, then some `Aut(K/k)`-fixed
`h ∈ U` has the same two properties. -/
theorem exists_fixed_jump_of_rootGroupLinearization (iS : S.toGrp ⟶ G) (α : characterLattice S)
    {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation K Γ₀)
    (hlin : RootGroupLinearization iS α v)
    (ψ : RootFunctionFamily S_K G_K)
    (hmin : ∀ g ∈ rootGroupPoints (j_K iS) (a_K α), ∀ h ∈ rootGroupPoints (j_K iS) (a_K α),
      min (ψ (a_K α) g) (ψ (a_K α) h) ≤ ψ (a_K α) (g * h⁻¹))
    (hgal : ∀ σ : K ≃ₐ[k] K, ∀ g ∈ rootGroupPoints (j_K iS) (a_K α),
      ψ (a_K α) (rationalConjugate k K G σ g) = ψ (a_K α) g)
    (htor : ∀ t ∈ characterValuationKernel v (S_K).toGrp, ∀ g ∈ rootGroupPoints (j_K iS) (a_K α),
      ψ (a_K α) (rationalPoints.map (j_K iS) t * g * (rationalPoints.map (j_K iS) t)⁻¹) =
        ψ (a_K α) g)
    {Γ : Type*} [Group Γ] [Fintype Γ] [DecidableEq Γ]
    (res : (K ≃ₐ[k] K) →* Γ) (s : Γ → (K ≃ₐ[k] K)) (hs : ∀ gm, res (s gm) = gm)
    {R R₀ : Type*} [CommRing R] [CommRing R₀] [Algebra R₀ R]
    (ρ : Γ →* (R ≃ₐ[R₀] R)) (incl : R →+* K)
    (hincl : ∀ (σ : K ≃ₐ[k] K) (x : R), incl (ρ (res σ) x) = σ (incl x))
    (hunit : ∀ x : R, IsUnit x → v (incl x) = 1)
    (hdual : ∀ P : Subring R, (∀ gm, ∀ x ∈ P, ρ gm x ∈ P) → (∀ x : R, IsUnit x → x ^ 2 ∈ P) →
      ∃ (N : ℕ) (a c : Fin N → R), (∀ j, a j ∈ P) ∧ (∀ j, c j ∈ P) ∧
        ∀ gm : Γ, ∑ j, a j * ρ gm (c j) = if gm = 1 then 1 else 0)
    (htrace : ∀ P : Subring R, (∀ gm, ∀ x ∈ P, ρ gm x ∈ P) → (∀ x : R, IsUnit x → x ^ 2 ∈ P) →
      ∃ θ ∈ P, ∑ gm : Γ, ρ gm θ = 1)
    (r : ℝ) (hr1 : (r : WithTop ℝ) < ψ (a_K α) 1)
    (u : rationalPoints G_K) (huU : u ∈ rootGroupPoints (j_K iS) (a_K α))
    (hur : (r : WithTop ℝ) ≤ ψ (a_K α) u)
    (hufix : ∀ σ : K ≃ₐ[k] K, res σ = 1 → rationalConjugate k K G σ u = u)
    (hu : u ∉ {g | g ∈ rootGroupPoints (j_K iS) (a_K α) ∧ (r : WithTop ℝ) < ψ (a_K α) g} *
      (doubleRootGroupPoints (j_K iS) (a_K α) : Set (rationalPoints G_K))) :
    ∃ h ∈ rootGroupPoints (j_K iS) (a_K α), (r : WithTop ℝ) ≤ ψ (a_K α) h ∧
      (∀ σ : K ≃ₐ[k] K, rationalConjugate k K G σ h = h) ∧
      h ∉ {g | g ∈ rootGroupPoints (j_K iS) (a_K α) ∧ (r : WithTop ℝ) < ψ (a_K α) g} *
        (doubleRootGroupPoints (j_K iS) (a_K α) : Set (rationalPoints G_K)) := by
  obtain ⟨n, m, d, q, e, hd, hq_mul, hq_ker, he_mul, he_inj, hU, hq_act, he_act, hscale⟩ := hlin
  let act : (K ≃ₐ[k] K) →* MulAut (rationalPoints G_K) :=
    { toFun := fun σ => rationalConjugate k K G σ
      map_one' := MulEquiv.ext (rationalConjugate_one k K G)
      map_mul' := fun σ τ => MulEquiv.ext (rationalConjugate_mul k K G σ τ) }
  -- elements of the kernel of `res` fix the image of `R`
  have hker : ∀ σ : K ≃ₐ[k] K, res σ = 1 → ∀ x : R, σ (incl x) = incl x := by
    intro σ hσ x
    rw [← hincl, hσ, map_one, AlgEquiv.one_apply]
  -- torus points attached to units of valuation one
  have htorus : ∀ c : Kˣ, v (c : K) = 1 → (∀ σ : K ≃ₐ[k] K, res σ = 1 → σ (c : K) = c) →
      ∃ τ : rationalPoints G_K, (∀ σ, res σ = 1 → act σ τ = τ) ∧
        ∀ g ∈ rootGroupPoints (j_K iS) (a_K α),
          τ * g * τ⁻¹ ∈ rootGroupPoints (j_K iS) (a_K α) ∧
          ψ (a_K α) (τ * g * τ⁻¹) = ψ (a_K α) g ∧ q (τ * g * τ⁻¹) = (c : K) ^ d • q g ∧
          (g ∈ doubleRootGroupPoints (j_K iS) (a_K α) →
            e (τ * g * τ⁻¹) = (c : K) ^ 2 • e g) := by
    intro c hc hcfix
    obtain ⟨t, ht, htfix, htU, htU₂⟩ := hscale c hc
    refine ⟨rationalPoints.map (j_K iS) t, fun σ hσ => htfix σ (hcfix σ hσ), fun g hg => ?_⟩
    obtain ⟨hgU, hgq⟩ := htU g hg
    exact ⟨hgU, htor t ht g hg, hgq, fun hg₂ => htU₂ g hg₂⟩
  have hsq_q : ∀ x : R, IsUnit x → ∃ τ : rationalPoints G_K, (∀ σ, res σ = 1 → act σ τ = τ) ∧
      ∀ g ∈ rootGroupPoints (j_K iS) (a_K α),
        τ * g * τ⁻¹ ∈ rootGroupPoints (j_K iS) (a_K α) ∧
        ψ (a_K α) (τ * g * τ⁻¹) = ψ (a_K α) g ∧ q (τ * g * τ⁻¹) = incl (x ^ 2) • q g := by
    intro x hx
    have hxv : v (incl x) = 1 := hunit x hx
    have hc₀ : ((hx.map incl).unit : K) = incl x := IsUnit.unit_spec _
    rcases hd with rfl | rfl
    · obtain ⟨τ, hτ, hτU⟩ := htorus ((hx.map incl).unit ^ 2)
        (by rw [Units.val_pow_eq_pow_val, map_pow, hc₀, hxv, one_pow])
        (fun σ hσ => by rw [Units.val_pow_eq_pow_val, map_pow, hc₀, hker σ hσ])
      refine ⟨τ, hτ, fun g hg => ?_⟩
      obtain ⟨h1, h2, h3, -⟩ := hτU g hg
      refine ⟨h1, h2, ?_⟩
      rw [h3, Units.val_pow_eq_pow_val, hc₀, pow_one, map_pow]
    · obtain ⟨τ, hτ, hτU⟩ := htorus (hx.map incl).unit (by rw [hc₀, hxv])
        (fun σ hσ => by rw [hc₀, hker σ hσ])
      refine ⟨τ, hτ, fun g hg => ?_⟩
      obtain ⟨h1, h2, h3, -⟩ := hτU g hg
      exact ⟨h1, h2, by rw [h3, hc₀, map_pow]⟩
  have hsq_e : ∀ x : R, IsUnit x → ∃ τ : rationalPoints G_K, (∀ σ, res σ = 1 → act σ τ = τ) ∧
      ∀ g ∈ rootGroupPoints (j_K iS) (a_K α), g ∈ doubleRootGroupPoints (j_K iS) (a_K α) →
        τ * g * τ⁻¹ ∈ rootGroupPoints (j_K iS) (a_K α) ∧
        τ * g * τ⁻¹ ∈ doubleRootGroupPoints (j_K iS) (a_K α) ∧
        ψ (a_K α) (τ * g * τ⁻¹) = ψ (a_K α) g ∧ e (τ * g * τ⁻¹) = incl (x ^ 2) • e g := by
    intro x hx
    have hc₀ : ((hx.map incl).unit : K) = incl x := IsUnit.unit_spec _
    obtain ⟨τ, hτ, hτU⟩ := htorus (hx.map incl).unit (by rw [hc₀]; exact hunit x hx)
      (fun σ hσ => by rw [hc₀, hker σ hσ])
    refine ⟨τ, hτ, fun g hg hg₂ => ?_⟩
    obtain ⟨h1, h2, h3, h4⟩ := hτU g hg
    refine ⟨h1, (hq_ker _ h1).mp ?_, h2, by rw [h4 hg₂, hc₀, map_pow]⟩
    rw [h3, (hq_ker g hg).mpr hg₂, smul_zero]
  -- the hypotheses in the form used by `FilteredTraceDescent`
  have hact : ∀ (σ : K ≃ₐ[k] K) (x : rationalPoints G_K), act σ x = rationalConjugate k K G σ x :=
    fun _ _ => rfl
  have hincl' : ∀ (σ : K ≃ₐ[k] K) (x : R), incl (ρ (res σ) x) = σ • incl x := hincl
  have hU' : ∀ σ : K ≃ₐ[k] K, ∀ x ∈ rootGroupPoints (j_K iS) (a_K α),
      act σ x ∈ rootGroupPoints (j_K iS) (a_K α) := fun σ x hx => by
    rw [hact]; exact hU σ x hx
  have hq_act' : ∀ σ : K ≃ₐ[k] K, ∀ x ∈ rootGroupPoints (j_K iS) (a_K α),
      q (act σ x) = σ • q x := fun σ x hx => by
    rw [hact, hq_act σ x hx]; rfl
  have he_act' : ∀ σ : K ≃ₐ[k] K, ∀ x ∈ doubleRootGroupPoints (j_K iS) (a_K α),
      e (act σ x) = σ • e x := fun σ x hx => by
    rw [hact, he_act σ x hx]; rfl
  have hgal' : ∀ σ : K ≃ₐ[k] K, ∀ g ∈ rootGroupPoints (j_K iS) (a_K α),
      ψ (a_K α) (act σ g) = ψ (a_K α) g := fun σ g hg => by
    rw [hact]; exact hgal σ g hg
  have hufix' : ∀ σ : K ≃ₐ[k] K, res σ = 1 → act σ u = u := fun σ hσ => by
    rw [hact]; exact hufix σ hσ
  have k1 := FilteredTraceDescent.exists_fixed_not_mem_mul_of_subring (Λ := WithTop ℝ)
    act res s hs ρ incl hincl' hdual htrace (rootGroupPoints (j_K iS) (a_K α))
    (doubleRootGroupPoints (j_K iS) (a_K α)) hU' q e
  have k2 := k1 hq_mul hq_ker he_mul he_inj hq_act' he_act' (ψ (a_K α)) (r : WithTop ℝ)
  have k3 := k2 hmin hgal' hr1
  have k4 := k3 hsq_q hsq_e
  have k5 := k4 u huU hur hufix' hu
  obtain ⟨h, hhU, hhr, hhfix, hhne⟩ := k5
  exact ⟨h, hhU, hhr, fun σ => hhfix σ, hhne⟩

end Generic

namespace MaximalUnramified

open Langlands.LocalGalois Langlands.LocalGalois.Separable

section FiniteLevel

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

local instance zeroJumpGaloisDescentNormedField : NontriviallyNormedField F := localNormedField F
local instance zeroJumpGaloisDescentUltrametric : IsUltrametricDist F := localNormedField_ultrametric F
local instance zeroJumpGaloisDescentComplete : CompleteSpace F := localNormedField_complete F

/-- An element of the ring of integers of a finite subextension `E ⊆ F^ur` has valuation at
most one in `F^ur`. -/
theorem valuation_inclusion_integers_le_one (E : IntermediateField F (SeparableClosure F))
    [FiniteDimensional F E] (hE : E ≤ inertiaFixedField F)
    (x : LocalUnramified.integers F E) :
    valuation F (IntermediateField.inclusion hE (x : E)) ≤ 1 := by
  have hx : (x : E) ∈ extensionIntegers F E := (LocalUnramified.mem_integers_iff F E x).mp x.2
  have hsep := (integerInclusion F (SeparableClosure F) E ⟨x, hx⟩).2
  have hfix : IntermediateField.inclusion hE (x : E) ∈ fixedFieldIntegers F := hsep
  exact (mem_valuationSubring_iff F _).mpr hfix

/-- A unit of the ring of integers of a finite subextension `E ⊆ F^ur` has valuation one in
`F^ur`. -/
theorem valuation_inclusion_integers_eq_one (E : IntermediateField F (SeparableClosure F))
    [FiniteDimensional F E] (hE : E ≤ inertiaFixedField F)
    (x : LocalUnramified.integers F E) (hx : IsUnit x) :
    valuation F (IntermediateField.inclusion hE (x : E)) = 1 := by
  obtain ⟨y, hy⟩ := hx.exists_right_inv
  have h1 : IntermediateField.inclusion hE (x : E) * IntermediateField.inclusion hE (y : E) = 1 := by
    rw [← map_mul, ← map_one (IntermediateField.inclusion hE)]
    congr 1
    simpa using congrArg Subtype.val hy
  have hxy := congrArg (valuation F) h1
  rw [map_mul, map_one] at hxy
  refine le_antisymm (valuation_inclusion_integers_le_one F E hE x) ?_
  calc (1 : WithZero (Multiplicative ℤ)) = _ := hxy.symm
    _ ≤ valuation F (IntermediateField.inclusion hE (x : E)) :=
      mul_le_of_le_one_right' (valuation_inclusion_integers_le_one F E hE y)

/-- **A finite Galois level for a rational point.** A rational point `u` of `G_K`,
`K = F^ur`, is fixed by every `σ ∈ Aut(K/F)` that fixes a suitable finite Galois
subextension `E` of `K/F` pointwise. -/
theorem exists_finiteLevel_fixing (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (u : rationalPoints (baseChanged F (inertiaFixedField F) G)) :
    ∃ (E : IntermediateField F (SeparableClosure F)) (_ : FiniteDimensional F E)
      (_ : IsGalois F E) (hE : E ≤ inertiaFixedField F),
      ∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
        (∀ x : E, σ (IntermediateField.inclusion hE x) = IntermediateField.inclusion hE x) →
          rationalConjugate F (inertiaFixedField F) G σ u = u := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  obtain ⟨E, hfin, hgal, hE, xE, hxE⟩ :=
    GaloisPoint.exists_finiteUnramified_definition G (baseChangeCoeffEquiv F _ G u)
  refine ⟨E, hfin, hgal, hE, fun σ hσ => ?_⟩
  apply (baseChangeCoeffEquiv F _ G).injective
  rw [baseChangeCoeffEquiv_rationalConjugate, ← hxE]
  change Lie.affineMap G σ.toAlgHom (Lie.affineMap G (IntermediateField.inclusion hE) xE) =
    Lie.affineMap G (IntermediateField.inclusion hE) xE
  have hcomp : σ.toAlgHom.comp (IntermediateField.inclusion hE) =
      IntermediateField.inclusion hE := AlgHom.ext fun x => hσ x
  rw [← Lie.affineMap_comp, hcomp]

end FiniteLevel

section Main

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

local notation "Kur" => inertiaFixedField F

local notation "b" => algebraBaseMap F (inertiaFixedField F)
local notation "j_K" => CategoryTheory.Functor.map (GroupScheme.baseChange b)

set_option maxHeartbeats 1000000 in
/-- **Descent of root filtration jumps from `F^ur` to `F`, given root-group coordinates.**
Let `S` be a split torus of a smooth affine `F`-group `G`, `α` a root of `(G, S)`, and `ψ` a
family of root functions of `(G_K, S_K)`, `K = F^ur`, such that `ψ_{α_K}` is ultrametric on
`U_{α_K}(K)`, invariant under `Aut(K/F)`, and invariant under conjugation by the points of
`S_K` at which every character has valuation one. If `RootGroupLinearization iS α v` holds for
the normalized valuation `v` of `K`, then every jump of `α_K` at `r` for `ψ` gives a jump of
`α` at `r` for `fieldRestrict ψ`. -/
theorem isRootFiltrationJump_fieldRestrict_of_linearization
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] [Smooth G.X.hom]
    {S : CommGroupScheme (Spec (CommRingCat.of F))} (iS : S.toGrp ⟶ G)
    (hS : IsSplitTorus S.toGrp) {α : characterLattice S} (hα : α ∈ relativeRoots iS)
    (hlin : RootGroupLinearization iS α (valuation F))
    (ψ : RootFunctionFamily ((CommGroupScheme.baseChange b).obj S)
      ((GroupScheme.baseChange b).obj G))
    (hmin : ∀ g ∈ rootGroupPoints (j_K iS) (characterLattice.baseChange b S α),
      ∀ h ∈ rootGroupPoints (j_K iS) (characterLattice.baseChange b S α),
      min (ψ (characterLattice.baseChange b S α) g) (ψ (characterLattice.baseChange b S α) h) ≤
        ψ (characterLattice.baseChange b S α) (g * h⁻¹))
    (hgal : ∀ σ : Kur ≃ₐ[F] Kur, ∀ g ∈ rootGroupPoints (j_K iS) (characterLattice.baseChange b S α),
      ψ (characterLattice.baseChange b S α) (rationalConjugate F Kur G σ g) =
        ψ (characterLattice.baseChange b S α) g)
    (htor : ∀ t ∈ characterValuationKernel (valuation F)
        ((CommGroupScheme.baseChange b).obj S).toGrp,
      ∀ g ∈ rootGroupPoints (j_K iS) (characterLattice.baseChange b S α),
      ψ (characterLattice.baseChange b S α)
          (rationalPoints.map (j_K iS) t * g * (rationalPoints.map (j_K iS) t)⁻¹) =
        ψ (characterLattice.baseChange b S α) g)
    (r : ℝ) (hjump : IsRootFiltrationJump (j_K iS) ψ (characterLattice.baseChange b S α) r) :
    IsRootFiltrationJump iS (RootFunctionFamily.fieldRestrict (k := F) (K := Kur) ψ) α r := by
  classical
  by_cases h1 : (r : WithTop ℝ) < ψ (characterLattice.baseChange b S α) 1
  swap
  · exact isRootFiltrationJump_fieldRestrict_of_not_lt iS α ψ hmin r hjump h1
  obtain ⟨u, huF, hu⟩ := Set.not_subset.mp hjump
  obtain ⟨huU, hur⟩ := mem_rootFiltration.mp huF
  obtain ⟨E, hfin, hgalE, hE, hfixE⟩ := exists_finiteLevel_fixing F G u
  let : Algebra E Kur := (IntermediateField.inclusion hE).toRingHom.toAlgebra
  have : IsScalarTower F E Kur :=
    IsScalarTower.of_algebraMap_eq fun x => ((IntermediateField.inclusion hE).commutes x).symm
  let res : (Kur ≃ₐ[F] Kur) →* (E ≃ₐ[F] E) := AlgEquiv.restrictNormalHom E
  let s : (E ≃ₐ[F] E) → (Kur ≃ₐ[F] Kur) := fun gm => gm.liftNormal Kur
  have hs : ∀ gm, res (s gm) = gm := fun gm => gm.restrict_liftNormal Kur
  let incl : LocalUnramified.integers F E →+* Kur :=
    (IntermediateField.inclusion hE).toRingHom.comp
      (algebraMap (LocalUnramified.integers F E) E)
  have hincl : ∀ (σ : Kur ≃ₐ[F] Kur) (x : LocalUnramified.integers F E),
      incl (LocalUnramified.galoisAction F E (res σ) x) = σ (incl x) := by
    intro σ x
    change IntermediateField.inclusion hE
        ((LocalUnramified.galoisAction F E (res σ) x : LocalUnramified.integers F E) : E) =
      σ (IntermediateField.inclusion hE (x : E))
    rw [LocalUnramified.coe_galoisAction_apply]
    exact AlgEquiv.restrictNormal_commutes σ E (x : E)
  have hufix : ∀ σ : Kur ≃ₐ[F] Kur, res σ = 1 → rationalConjugate F Kur G σ u = u := by
    intro σ hσ
    apply hfixE σ
    intro x
    have h := AlgEquiv.restrictNormal_commutes σ E x
    change σ.restrictNormal E = 1 at hσ
    rw [hσ, AlgEquiv.one_apply] at h
    exact h.symm
  have hdual : ∀ P : Subring (LocalUnramified.integers F E),
      (∀ gm, ∀ x ∈ P, LocalUnramified.galoisAction F E gm x ∈ P) →
      (∀ x : LocalUnramified.integers F E, IsUnit x → x ^ 2 ∈ P) →
      ∃ (N : ℕ) (a c : Fin N → LocalUnramified.integers F E), (∀ j, a j ∈ P) ∧
        (∀ j, c j ∈ P) ∧ ∀ gm : E ≃ₐ[F] E,
          ∑ j, a j * LocalUnramified.galoisAction F E gm (c j) = if gm = 1 then 1 else 0 := by
    intro P hP hsq
    obtain ⟨N, a, c, ha, hc, hac⟩ := LocalUnramified.exists_dual_family_of_sq_mem F E hE P hP hsq
    exact ⟨N, a, c, ha, hc, fun gm => by convert hac gm⟩
  have htrace : ∀ P : Subring (LocalUnramified.integers F E),
      (∀ gm, ∀ x ∈ P, LocalUnramified.galoisAction F E gm x ∈ P) →
      (∀ x : LocalUnramified.integers F E, IsUnit x → x ^ 2 ∈ P) →
      ∃ θ ∈ P, ∑ gm : E ≃ₐ[F] E, LocalUnramified.galoisAction F E gm θ = 1 := by
    intro P hP hsq
    obtain ⟨θ, hθ, hθ1⟩ := LocalUnramified.exists_trace_eq_one_of_sq_mem F E hE P hP hsq
    exact ⟨θ, hθ, by convert hθ1⟩
  have hunit : ∀ x : LocalUnramified.integers F E, IsUnit x → valuation F (incl x) = 1 :=
    fun x hx => valuation_inclusion_integers_eq_one F E hE x hx
  have m0b := exists_fixed_jump_of_rootGroupLinearization (k := F) (K := Kur) iS α
    (valuation F) hlin
  have m0c := m0b ψ
  have m0d := m0c hmin
  have m0e := m0d hgal
  have m2 := m0e htor res s hs (LocalUnramified.galoisAction F E) incl hincl hunit
  have m3 := m2 hdual htrace r h1
  have m4 := m3 u huU hur hufix hu
  obtain ⟨h, hhU, hhr, hhfix, hhne⟩ := m4
  exact isRootFiltrationJump_fieldRestrict_of_fixed iS hS hα ψ r hhU hhr hhfix hhne

end Main

end MaximalUnramified

end Langlands.Geometry.Building
