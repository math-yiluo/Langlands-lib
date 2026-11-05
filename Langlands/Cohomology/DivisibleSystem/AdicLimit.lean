import Langlands.Cohomology.DivisibleSystem.ContinuousLimit
import Langlands.Cohomology.DivisibleSystem.ReductionLimit
import Langlands.Cohomology.DivisibleSystem.ReductionAdic
import Langlands.Cohomology.DivisibleSystem.HomSurjective

/-!
# The inverse limit of an `ℓ`-divisible system

Harris, *Galois properties of cohomological automorphic forms on GL(n)*, §2, p.304: an
`ℓ`-divisible system is a collection `{T_m}` with maps `i : T_{m'} → T_m` and
`j : T_m → T_{m-m'}` such that `T_m` is free over `ℤ/ℓ^mℤ`, `i` identifies `T_{m'}` with the
`ℓ^{m'}`-torsion in `T_m`, and "(2.1) `0 → T_{m'} → T_m → T_{m-m'} → 0` is exact"; p.306,
Lemma 2.8, passes to the inverse limit `lim C_m^•` of such a system of complexes. Milne,
*Étale Cohomology* (1980), Ch. V, §1, p.164, on the stalk `F_x = lim (F_n)_x` of an `l`-adic
sheaf: "the action is continuous when `F_x` is given the `l`-adic topology".

This module describes the inverse limit `L` of an `ℓ`-divisible system `T` (the published
`DivisibleSystem`), the vertex of a limit cone `c` over `T.tower`.

* Modules: the projections `L ⟶ T m` are surjective (`π_surjective`) with kernel `ℓ ^ m L`
  (`π_hom_apply_eq_zero_iff`, `π_hom_apply_eq_iff`, `ker_π`), `L` has no `ℓ`-torsion
  (`isSMulRegular_of_isLimit`), and `L` is `ℓ`-adically complete and Hausdorff
  (`isAdicComplete_of_isLimit`). On the way: the kernel of `j : T k ⟶ T p` is the
  `ℓ ^ (k - p)`-torsion of `T k` (`projection_hom_apply_eq_zero_iff`).
* Abelian categories: if each projection `L ⟶ T m` is a cokernel of multiplication by `ℓ ^ m`,
  the tower of reductions `L / ℓ ^ m L` is isomorphic to `T.tower` compatibly with the
  projections (`reductionTowerIso`, `reductionπ_reductionIso_hom`), and `L` is the inverse limit
  of its own reductions (`isLimitReductionConeOfIsLimit`). The cokernel condition follows from
  exactness and surjectivity (`isCokernelOfExact`), which can be checked after a faithful exact
  functor (`isCokernelOfMap`) and holds for modules (`isCokernelOfIsLimit`).
* Categories with a faithful exact functor to modules preserving limits over `ℕᵒᵖ`, such as
  `Rep R G` and `Action (ModuleCat R) G`: `isCokernelOfFaithful`,
  `reductionTowerIsoOfFaithful`, `isLimitReductionConeOfFaithful`, and multiplication by `ℓ`
  on `L` is a monomorphism (`mono_powSMul_one_of_faithful`). For representations:
  `rep_π_hom_apply_eq_zero_iff`, `rep_π_surjective`, `rep_isSMulRegular`,
  `rep_isAdicComplete`.
* Systems in `Action (ModuleCat R) G`, with the published inverse limit topology on
  `ContinuousLimit.ConeSpace c`: `ker_proj`, `isSMulRegular_coneSpace`,
  `isAdicComplete_coneSpace`, and `topology_eq_adicModuleTopology`: the inverse limit topology
  of the discrete levels is the `ℓ`-adic topology. So for smooth levels the action is jointly
  continuous for the `ℓ`-adic topology (`continuous_action_adicModuleTopology`).
* Harris's étale coefficients in degree zero, when the section maps of the projections are
  surjective: `lim_m H^0(X, 𝓛 / ℓ ^ m)` is the vertex of a limit cone over
  `harrisEtaleSectionsDivisibleSystem` (`harrisEtaleAdicCohomologyZeroCone`,
  `harrisEtaleAdicCohomologyZeroConeIsLimit`), has no `ℓ`-torsion, is `ℓ`-adically complete,
  and its reductions modulo `ℓ ^ m` are the modules of sections `Γ(X, 𝓛 / ℓ ^ m)`
  (`harrisEtaleAdicCohomologyZeroReductionIso`).

Harris states none of these properties of the limit; they are our reading of his passage to the
limit. The statements and proofs are ours.
-/

noncomputable section

namespace Langlands.Cohomology.DivisibleSystem

open CategoryTheory CategoryTheory.Limits Opposite

universe w u v u' v'

section Submodule

variable {R : Type u} [CommRing R] {M : Type w} [AddCommGroup M] [Module R M]

/-- The submodule `(ℓ) ^ m M` is the set of multiples `ℓ ^ m • y`. -/
lemma mem_span_pow_smul_top_iff (ℓ m : ℕ) (x : M) :
    x ∈ (Ideal.span {(ℓ : R)} ^ m • ⊤ : Submodule R M) ↔ ∃ y : M, ((ℓ : R) ^ m) • y = x := by
  rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists]
  simp only [Submodule.mem_top, true_and]

end Submodule

section ModuleCat

variable {R : Type u} [CommRing R] {ℓ : ℕ} (T : DivisibleSystem (ModuleCat.{w} R) ℓ)

/-- `ℓ ^ m` kills every element of `T m`. -/
lemma pow_smul_obj_eq_zero (m : ℕ) (x : T.obj m) : ((ℓ : R) ^ m) • x = 0 := by
  rw [← powSMul_moduleCat_hom_apply ℓ, T.powSMul_eq_zero m]
  rfl

/-- The projections of an `ℓ`-divisible system of modules are surjective. -/
lemma projection_surjective {p k : ℕ} (h : p ≤ k) : Function.Surjective (T.projection h).hom :=
  (ModuleCat.epi_iff_surjective _).1 (T.epi_projection h)

/-- Composition of projections, elementwise. -/
lemma projection_projection_apply {n p k : ℕ} (h₁ : n ≤ p) (h₂ : p ≤ k) (x : T.obj k) :
    (T.projection h₁).hom ((T.projection h₂).hom x) = (T.projection (h₁.trans h₂)).hom x := by
  rw [← ModuleCat.comp_apply, ← Functor.map_comp]
  rfl

/-- The kernel of the projection `T k ⟶ T p` is the `ℓ ^ (k - p)`-torsion of `T k`. -/
lemma projection_hom_apply_eq_zero_iff {p k : ℕ} (h : p ≤ k) (x : T.obj k) :
    (T.projection h).hom x = 0 ↔ ((ℓ : R) ^ (k - p)) • x = 0 := by
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · have hz : ∀ y : T.obj 0, y = 0 := fun y =>
      ModuleCat.subsingleton_of_isZero T.isZero_obj_zero |>.elim y 0
    simp only [Nat.sub_zero, hz, true_iff]
    exact T.pow_smul_obj_eq_zero k x
  obtain ⟨m', hm', rfl⟩ : ∃ m', m' < k ∧ p = k - m' := ⟨k - p, by omega, by omega⟩
  rw [Nat.sub_sub_self hm'.le]
  have hse := (ShortComplex.moduleCat_exact_iff _).1 (T.shortExact hm').exact
  have hte := (ShortComplex.moduleCat_exact_iff _).1 (T.torsion_exact hm')
  constructor
  · intro hx
    obtain ⟨z, rfl⟩ := hse x hx
    change ((ℓ : R) ^ m') • (T.inclusion hm').hom z = 0
    rw [← powSMul_moduleCat_hom_apply ℓ, ← ModuleCat.comp_apply, comp_powSMul,
      T.powSMul_eq_zero, zero_comp]
    rfl
  · intro hx
    obtain ⟨z, rfl⟩ := hte x (by
      change (powSMul ℓ m' (T.obj k)).hom x = 0
      rw [powSMul_moduleCat_hom_apply]
      exact hx)
    change (T.inclusion hm' ≫ T.projection (Nat.sub_le k m')).hom z = 0
    rw [T.inclusion_comp]
    rfl

/-- On `T k` with `k = a + b`, an element killed by `ℓ ^ b` is a multiple of `ℓ ^ a`. -/
lemma exists_pow_smul_eq_of_pow_smul_eq_zero {a b k : ℕ} (hk : k = a + b) (x : T.obj k)
    (hx : ((ℓ : R) ^ b) • x = 0) : ∃ y : T.obj k, ((ℓ : R) ^ a) • y = x := by
  subst hk
  obtain ⟨y, hy⟩ := (ShortComplex.moduleCat_exact_iff _).1 (T.flat a b) x (by
    change (powSMul ℓ b (T.obj (a + b))).hom x = 0
    rw [powSMul_moduleCat_hom_apply]
    exact hx)
  change (powSMul ℓ a (T.obj (a + b))).hom y = x at hy
  exact ⟨y, by rwa [powSMul_moduleCat_hom_apply] at hy⟩

variable {T} {c : Cone T.tower} (hc : IsLimit c)

/-- The projections of a cone commute with the transition maps, elementwise. -/
lemma projection_π_apply {p k : ℕ} (h : p ≤ k) (x : c.pt) :
    (T.projection h).hom ((c.π.app (op k)).hom x) = (c.π.app (op p)).hom x := by
  rw [← ModuleCat.comp_apply, c.w]

include hc in
/-- Two elements of the limit with the same projections are equal. -/
lemma ext_of_isLimit {x y : c.pt} (h : ∀ n : ℕ, (c.π.app (op n)).hom x = (c.π.app (op n)).hom y) :
    x = y :=
  Concrete.isLimit_ext T.tower hc x y fun j => by
    induction j using Opposite.rec with | op n => exact h n

include hc in
/-- A family of elements `s n ∈ T n` compatible with the projections `T (n + 1) ⟶ T n` comes
from an element of the limit. -/
lemma exists_π_apply_eq (s : ∀ n : ℕ, T.obj n)
    (hs : ∀ n, (T.projection (Nat.le_succ n)).hom (s (n + 1)) = s n) :
    ∃ y : c.pt, ∀ n, (c.π.app (op n)).hom y = s n := by
  have hc' := isLimitOfPreserves (CategoryTheory.forget (ModuleCat.{w} R)) hc
  have hmem : (fun j : ℕᵒᵖ => s j.unop) ∈
      (T.tower ⋙ CategoryTheory.forget (ModuleCat.{w} R)).sections :=
    mem_sections_of_map_succ (F := T.tower ⋙ CategoryTheory.forget (ModuleCat.{w} R)) s hs
  exact ⟨(Types.isLimitEquivSections hc').symm ⟨_, hmem⟩, fun n =>
    Types.isLimitEquivSections_symm_apply hc' ⟨_, hmem⟩ (op n)⟩

include hc in
/-- The projections from the limit of an `ℓ`-divisible system of modules are surjective. -/
lemma π_surjective (m : ℕ) : Function.Surjective (c.π.app (op m)).hom :=
  concrete_surjective_π_app_of_surjective_map hc (fun _ => T.projection_surjective _) m

include hc in
/-- The kernel of the projection from the limit to `T m` is `ℓ ^ m` times the limit. -/
theorem π_hom_apply_eq_zero_iff (m : ℕ) (x : c.pt) :
    (c.π.app (op m)).hom x = 0 ↔ ∃ y : c.pt, ((ℓ : R) ^ m) • y = x := by
  constructor
  · intro hx
    -- `x (n + m)` is a multiple `ℓ ^ m • w n`.
    have hw : ∀ n : ℕ, ∃ w : T.obj (n + m), ((ℓ : R) ^ m) • w = (c.π.app (op (n + m))).hom x :=
      fun n => T.exists_pow_smul_eq_of_pow_smul_eq_zero (Nat.add_comm n m) _ (by
        have := (T.projection_hom_apply_eq_zero_iff (Nat.le_add_left m n)
          ((c.π.app (op (n + m))).hom x)).1 (by rw [projection_π_apply, hx])
        rwa [Nat.add_sub_cancel] at this)
    choose w hw using hw
    let s : ∀ n : ℕ, T.obj n := fun n => (T.projection (Nat.le_add_right n m)).hom (w n)
    -- The class `s n` does not depend on the choice of `w n`.
    have huniq : ∀ (n : ℕ) (v : T.obj (n + m)),
        ((ℓ : R) ^ m) • v = (c.π.app (op (n + m))).hom x →
          (T.projection (Nat.le_add_right n m)).hom v = s n := by
      intro n v hv
      rw [← sub_eq_zero, ← map_sub, T.projection_hom_apply_eq_zero_iff, Nat.add_sub_cancel_left,
        smul_sub, hv, hw, sub_self]
    have hs : ∀ n, (T.projection (Nat.le_succ n)).hom (s (n + 1)) = s n := by
      intro n
      have hle : n + m ≤ n + 1 + m := by omega
      have hv : ((ℓ : R) ^ m) • (T.projection hle).hom (w (n + 1)) =
          (c.π.app (op (n + m))).hom x := by
        rw [← map_smul, hw, projection_π_apply]
      rw [← huniq n _ hv, projection_projection_apply, projection_projection_apply]
    obtain ⟨y, hy⟩ := exists_π_apply_eq hc s hs
    refine ⟨y, ext_of_isLimit hc fun n => ?_⟩
    rw [map_smul, hy]
    show ((ℓ : R) ^ m) • (T.projection (Nat.le_add_right n m)).hom (w n) = _
    rw [← map_smul, hw, projection_π_apply]
  · rintro ⟨y, rfl⟩
    rw [map_smul]
    exact T.pow_smul_obj_eq_zero m _

include hc in
/-- Two elements of the limit have the same image in `T m` exactly when they are congruent
modulo `(ℓ) ^ m`. -/
theorem π_hom_apply_eq_iff (m : ℕ) (x y : c.pt) :
    (c.π.app (op m)).hom x = (c.π.app (op m)).hom y ↔
      x ≡ y [SMOD (Ideal.span {(ℓ : R)} ^ m • ⊤ : Submodule R c.pt)] := by
  rw [SModEq.sub_mem, mem_span_pow_smul_top_iff, ← sub_eq_zero, ← map_sub,
    π_hom_apply_eq_zero_iff hc]

include hc in
/-- The kernel of the projection from the limit to `T m` is the submodule `(ℓ) ^ m` of the
limit. -/
theorem ker_π (m : ℕ) :
    LinearMap.ker (c.π.app (op m)).hom = (Ideal.span {(ℓ : R)} ^ m • ⊤ : Submodule R c.pt) := by
  ext x
  rw [LinearMap.mem_ker, π_hom_apply_eq_zero_iff hc, mem_span_pow_smul_top_iff]
  exact Iff.rfl

include hc in
/-- The limit of an `ℓ`-divisible system of modules has no `ℓ`-torsion. -/
theorem isSMulRegular_of_isLimit : IsSMulRegular c.pt (ℓ : R) := by
  intro x y hxy
  have h0 : (ℓ : R) • (x - y) = 0 := by
    rw [smul_sub]
    exact sub_eq_zero.2 hxy
  refine sub_eq_zero.1 (ext_of_isLimit hc fun n => ?_)
  rw [map_zero, ← projection_π_apply (Nat.le_succ n),
    T.projection_hom_apply_eq_zero_iff, show n.succ - n = 1 by omega, pow_one, ← map_smul, h0,
    map_zero]

include hc in
/-- The limit of an `ℓ`-divisible system of modules is complete and Hausdorff for the `ℓ`-adic
topology. -/
theorem isAdicComplete_of_isLimit : IsAdicComplete (Ideal.span {(ℓ : R)}) c.pt := by
  rw [isAdicComplete_iff]
  refine ⟨⟨fun x hx => ext_of_isLimit hc fun n => ?_⟩, ⟨fun f hf => ?_⟩⟩
  · rw [map_zero]
    exact ((π_hom_apply_eq_iff hc n x 0).2 (hx n)).trans (map_zero _)
  · let s : ∀ n : ℕ, T.obj n := fun n => (c.π.app (op n)).hom (f n)
    have hs : ∀ n, (T.projection (Nat.le_succ n)).hom (s (n + 1)) = s n := fun n => by
      rw [projection_π_apply]
      exact ((π_hom_apply_eq_iff hc n _ _).2 (hf (Nat.le_succ n))).symm
    obtain ⟨y, hy⟩ := exists_π_apply_eq hc s hs
    exact ⟨y, fun n => (π_hom_apply_eq_iff hc n _ _).1 (hy n).symm⟩

end ModuleCat

section Abelian

variable {C : Type u'} [Category.{v'} C] [Abelian C] {ℓ : ℕ} {T : DivisibleSystem C ℓ}
  (c : Cone T.tower)

/-- Multiplication by `ℓ ^ m` on the vertex of a cone over `T`, followed by the projection to
`T m`, is zero. -/
@[reassoc (attr := simp)]
lemma powSMul_comp_π (m : ℕ) : powSMul ℓ m c.pt ≫ c.π.app (op m) = 0 := by
  rw [← comp_powSMul, T.powSMul_eq_zero, comp_zero]

/-- If the projection `c.pt ⟶ T m` is a cokernel of multiplication by `ℓ ^ m` for every `m`,
the reduction `c.pt / ℓ ^ m c.pt` is isomorphic to `T m`. -/
def reductionIso
    (hcok : ∀ m : ℕ, IsColimit (CokernelCofork.ofπ (c.π.app (op m)) (powSMul_comp_π c m)))
    (m : ℕ) : (reductionTower ℓ c.pt).obj (op m) ≅ T.obj m :=
  (reductionπIsCokernel ℓ c.pt m).coconePointUniqueUpToIso (hcok m)

/-- `reductionIso` carries the projection `c.pt ⟶ c.pt / ℓ ^ m c.pt` to the projection
`c.pt ⟶ T m`. -/
@[reassoc (attr := simp)]
lemma reductionπ_reductionIso_hom
    (hcok : ∀ m : ℕ, IsColimit (CokernelCofork.ofπ (c.π.app (op m)) (powSMul_comp_π c m)))
    (m : ℕ) : reductionπ ℓ c.pt m ≫ (reductionIso c hcok m).hom = c.π.app (op m) :=
  (reductionπIsCokernel ℓ c.pt m).comp_coconePointUniqueUpToIso_hom (hcok m)
    WalkingParallelPair.one

/-- If the projection `c.pt ⟶ T m` is a cokernel of multiplication by `ℓ ^ m` for every `m`,
the tower of `T` is isomorphic to the tower of reductions `c.pt / ℓ ^ m c.pt`. -/
def reductionTowerIso
    (hcok : ∀ m : ℕ, IsColimit (CokernelCofork.ofπ (c.π.app (op m)) (powSMul_comp_π c m))) :
    reductionTower ℓ c.pt ≅ T.tower :=
  NatIso.ofComponents (fun m => reductionIso c hcok m.unop) (by
    intro m n f
    induction m using Opposite.rec with | op m =>
    induction n using Opposite.rec with | op n =>
    change (reductionTower ℓ c.pt).map f ≫ (reductionIso c hcok n).hom =
      (reductionIso c hcok m).hom ≫ T.tower.map f
    rw [← cancel_epi (reductionπ ℓ c.pt m), reductionπ_map_assoc, reductionπ_reductionIso_hom,
      reductionπ_reductionIso_hom_assoc, c.w])

/-- The components of `reductionTowerIso` are the isomorphisms `reductionIso`. -/
lemma reductionTowerIso_hom_app
    (hcok : ∀ m : ℕ, IsColimit (CokernelCofork.ofπ (c.π.app (op m)) (powSMul_comp_π c m)))
    (m : ℕ) : (reductionTowerIso c hcok).hom.app (op m) = (reductionIso c hcok m).hom :=
  rfl

/-- If `c` is a limit cone and each projection `c.pt ⟶ T m` is a cokernel of multiplication
by `ℓ ^ m`, then `c.pt` is the inverse limit of its own reductions `c.pt / ℓ ^ m c.pt`. -/
def isLimitReductionConeOfIsLimit (hc : IsLimit c)
    (hcok : ∀ m : ℕ, IsColimit (CokernelCofork.ofπ (c.π.app (op m)) (powSMul_comp_π c m))) :
    IsLimit (reductionCone ℓ c.pt) :=
  (IsLimit.postcomposeHomEquiv (reductionTowerIso c hcok) _)
    (hc.ofIsoLimit (Cone.ext (Iso.refl _) fun j => by
      induction j using Opposite.rec with | op m =>
      exact ((Category.id_comp _).trans (reductionπ_reductionIso_hom c hcok m)).symm))

/-- The projection `c.pt ⟶ T m` is a cokernel of multiplication by `ℓ ^ m` when the sequence
`c.pt ⟶ c.pt ⟶ T m` is exact and the projection is an epimorphism. -/
def isCokernelOfExact (m : ℕ)
    (hex : (ShortComplex.mk (powSMul ℓ m c.pt) (c.π.app (op m)) (powSMul_comp_π c m)).Exact)
    (hepi : Epi (c.π.app (op m))) :
    IsColimit (CokernelCofork.ofπ (c.π.app (op m)) (powSMul_comp_π c m)) :=
  hex.gIsCokernel

variable {D : Type*} [Category D] [Abelian D] (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]
  [PreservesFiniteColimits F] [F.Faithful]

include F in
/-- Exactness of `c.pt ⟶ c.pt ⟶ T m` can be checked after a faithful exact functor. -/
lemma exact_of_map (m : ℕ)
    (h : (ShortComplex.mk (powSMul ℓ m (F.mapCone c).pt) ((F.mapCone c).π.app (op m))
      (powSMul_comp_π (T := T.map F) (F.mapCone c) m)).Exact) :
    (ShortComplex.mk (powSMul ℓ m c.pt) (c.π.app (op m)) (powSMul_comp_π c m)).Exact := by
  rw [← ShortComplex.exact_map_iff_of_faithful _ F]
  exact shortComplex_exact_congr (map_powSMul F ℓ m c.pt).symm rfl h

include F in
/-- If `F` carries `c` to a cone whose projections are cokernels of the powers of `ℓ`, so are
the projections of `c`. -/
def isCokernelOfMap
    (h : ∀ m : ℕ, (ShortComplex.mk (powSMul ℓ m (F.mapCone c).pt) ((F.mapCone c).π.app (op m))
      (powSMul_comp_π (T := T.map F) (F.mapCone c) m)).Exact)
    (hepi : ∀ m : ℕ, Epi ((F.mapCone c).π.app (op m))) (m : ℕ) :
    IsColimit (CokernelCofork.ofπ (c.π.app (op m)) (powSMul_comp_π c m)) :=
  isCokernelOfExact c m (exact_of_map c F m (h m)) (F.epi_of_epi_map (hepi m))

end Abelian

section ModuleCatCokernel

variable {R : Type u} [CommRing R] {ℓ : ℕ} {T : DivisibleSystem (ModuleCat.{w} R) ℓ}
  {c : Cone T.tower} (hc : IsLimit c)

include hc in
/-- For a limit cone over an `ℓ`-divisible system of modules, `c.pt ⟶ c.pt ⟶ T m` is exact. -/
lemma exact_powSMul_π (m : ℕ) :
    (ShortComplex.mk (powSMul ℓ m c.pt) (c.π.app (op m)) (powSMul_comp_π c m)).Exact := by
  rw [ShortComplex.moduleCat_exact_iff]
  intro x hx
  obtain ⟨y, hy⟩ := (π_hom_apply_eq_zero_iff hc m x).1 hx
  exact ⟨y, (powSMul_moduleCat_hom_apply ℓ c.pt m y).trans hy⟩

include hc in
/-- For a limit cone over an `ℓ`-divisible system of modules, the projections are
epimorphisms. -/
lemma epi_π (m : ℕ) : Epi (c.π.app (op m)) :=
  (ModuleCat.epi_iff_surjective _).2 (π_surjective hc m)

/-- For a limit cone over an `ℓ`-divisible system of modules, `c.pt ⟶ T m` is a cokernel of
multiplication by `ℓ ^ m`. -/
def isCokernelOfIsLimit (m : ℕ) :
    IsColimit (CokernelCofork.ofπ (c.π.app (op m)) (powSMul_comp_π c m)) :=
  isCokernelOfExact c m (exact_powSMul_π hc m) (epi_π hc m)

end ModuleCatCokernel

section Faithful

variable {C : Type u'} [Category.{v'} C] [Abelian C] {R : Type u} [CommRing R] {ℓ : ℕ}
  {T : DivisibleSystem C ℓ} {c : Cone T.tower} (hc : IsLimit c)
  (F : C ⥤ ModuleCat.{w} R) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [F.Faithful] [PreservesLimitsOfShape ℕᵒᵖ F]

/-- If a faithful exact functor `F` to modules preserves the limit `c`, each projection
`c.pt ⟶ T m` is a cokernel of multiplication by `ℓ ^ m`. -/
def isCokernelOfFaithful (m : ℕ) :
    IsColimit (CokernelCofork.ofπ (c.π.app (op m)) (powSMul_comp_π c m)) :=
  isCokernelOfMap c F
    (fun m => exact_powSMul_π (T := T.map F) (c := F.mapCone c) (isLimitOfPreserves F hc) m)
    (fun m => epi_π (T := T.map F) (c := F.mapCone c) (isLimitOfPreserves F hc) m) m

/-- The tower of `T` is isomorphic to the tower of reductions `lim T / ℓ ^ m lim T`. -/
def reductionTowerIsoOfFaithful : reductionTower ℓ c.pt ≅ T.tower :=
  reductionTowerIso c (isCokernelOfFaithful hc F)

/-- The inverse limit of `T` is the inverse limit of its own reductions. -/
def isLimitReductionConeOfFaithful : IsLimit (reductionCone ℓ c.pt) :=
  isLimitReductionConeOfIsLimit c hc (isCokernelOfFaithful hc F)

include hc F in
/-- Multiplication by `ℓ` on the inverse limit of `T` is a monomorphism. -/
lemma mono_powSMul_one_of_faithful : Mono (powSMul ℓ 1 c.pt) := by
  refine F.mono_of_mono_map ?_
  rw [map_powSMul, ModuleCat.mono_iff_injective]
  intro x y hxy
  rw [powSMul_moduleCat_hom_apply, powSMul_moduleCat_hom_apply, pow_one] at hxy
  exact isSMulRegular_of_isLimit (T := T.map F) (c := F.mapCone c) (isLimitOfPreserves F hc) hxy

end Faithful

section Rep

variable {R : Type u} [CommRing R] {G : Type v} [Monoid G]

/-- The forgetful functor from representations to modules preserves limits indexed by `ℕᵒᵖ`. -/
instance rep_forget₂_preservesLimitsOfShape_nat :
    PreservesLimitsOfShape ℕᵒᵖ (forget₂ (Rep.{w} R G) (ModuleCat.{w} R)) :=
  have : PreservesLimitsOfSize.{0, 0} (forget₂ (Rep.{w} R G) (ModuleCat.{w} R)) :=
    preservesSmallestLimits_of_preservesLimits _
  inferInstance

variable {ℓ : ℕ} {T : DivisibleSystem (Rep.{w} R G) ℓ} {c : Cone T.tower} (hc : IsLimit c)

include hc in
/-- For an `ℓ`-divisible system of representations, the kernel of the projection from the
inverse limit to `T m` is `ℓ ^ m` times the inverse limit. -/
theorem rep_π_hom_apply_eq_zero_iff (m : ℕ) (x : c.pt) :
    (c.π.app (op m)).hom x = 0 ↔ ∃ y : c.pt, ((ℓ : R) ^ m) • y = x :=
  π_hom_apply_eq_zero_iff (T := T.map (forget₂ (Rep.{w} R G) (ModuleCat.{w} R)))
    (isLimitOfPreserves (forget₂ (Rep.{w} R G) (ModuleCat.{w} R)) hc) m x

include hc in
/-- The projections from the inverse limit of an `ℓ`-divisible system of representations are
surjective. -/
theorem rep_π_surjective (m : ℕ) : Function.Surjective (c.π.app (op m)).hom :=
  π_surjective (T := T.map (forget₂ (Rep.{w} R G) (ModuleCat.{w} R)))
    (isLimitOfPreserves (forget₂ (Rep.{w} R G) (ModuleCat.{w} R)) hc) m

include hc in
/-- The inverse limit of an `ℓ`-divisible system of representations has no `ℓ`-torsion. -/
theorem rep_isSMulRegular : IsSMulRegular c.pt (ℓ : R) :=
  isSMulRegular_of_isLimit (T := T.map (forget₂ (Rep.{w} R G) (ModuleCat.{w} R)))
    (isLimitOfPreserves (forget₂ (Rep.{w} R G) (ModuleCat.{w} R)) hc)

include hc in
/-- The inverse limit of an `ℓ`-divisible system of representations is `ℓ`-adically complete
and Hausdorff. -/
theorem rep_isAdicComplete : IsAdicComplete (Ideal.span {(ℓ : R)}) c.pt :=
  isAdicComplete_of_isLimit (T := T.map (forget₂ (Rep.{w} R G) (ModuleCat.{w} R)))
    (isLimitOfPreserves (forget₂ (Rep.{w} R G) (ModuleCat.{w} R)) hc)

end Rep

section Action

open ContinuousLimit Filter Topology

variable {R : Type u} [CommRing R] {G : Type v} [Group G] {ℓ : ℕ}
  {T : DivisibleSystem (Action (ModuleCat.{u} R) G) ℓ} {c : Cone T.tower} (hc : IsLimit c)

include hc in
/-- For an `ℓ`-divisible system of representations, the kernel of the projection from the
inverse limit to level `m` is the submodule `(ℓ) ^ m` of the inverse limit. -/
theorem ker_proj (m : ℕ) :
    LinearMap.ker (proj c (op m)) =
      (Ideal.span {(ℓ : R)} ^ m • ⊤ : Submodule R (ConeSpace c)) :=
  ker_π (T := T.map (Action.forget (ModuleCat.{u} R) G))
    (isLimitOfPreserves (Action.forget (ModuleCat.{u} R) G) hc) m

include hc in
/-- The inverse limit of an `ℓ`-divisible system of representations has no `ℓ`-torsion. -/
theorem isSMulRegular_coneSpace : IsSMulRegular (ConeSpace c) (ℓ : R) :=
  isSMulRegular_of_isLimit (T := T.map (Action.forget (ModuleCat.{u} R) G))
    (isLimitOfPreserves (Action.forget (ModuleCat.{u} R) G) hc)

include hc in
/-- The inverse limit of an `ℓ`-divisible system of representations is `ℓ`-adically complete
and Hausdorff. -/
theorem isAdicComplete_coneSpace : IsAdicComplete (Ideal.span {(ℓ : R)}) (ConeSpace c) :=
  isAdicComplete_of_isLimit (T := T.map (Action.forget (ModuleCat.{u} R) G))
    (isLimitOfPreserves (Action.forget (ModuleCat.{u} R) G) hc)

include hc in
/-- The inverse limit topology of the discrete levels on the inverse limit of an `ℓ`-divisible
system of representations is the `ℓ`-adic topology. -/
theorem topology_eq_adicModuleTopology :
    (inferInstance : TopologicalSpace (ConeSpace c)) =
      (Ideal.span {(ℓ : R)}).adicModuleTopology (ConeSpace c) := by
  let I := Ideal.span {(ℓ : R)}
  let _ : TopologicalSpace R := I.adicTopology
  let B := I.ringFilterBasis.moduleFilterBasis (I.adic_module_basis (ConeSpace c))
  refine IsTopologicalAddGroup.ext inferInstance B.toAddGroupFilterBasis.isTopologicalAddGroup ?_
  have e : ∀ j : ℕᵒᵖ, @nhds (ConeSpace c) (TopologicalSpace.induced (proj c j) ⊥) 0 =
      𝓟 ((I ^ j.unop • ⊤ : Submodule R (ConeSpace c)) : Set (ConeSpace c)) := by
    intro j
    induction j using Opposite.rec with | op m =>
    let _ : TopologicalSpace (T.tower.obj (op m)).V := ⊥
    have : DiscreteTopology (T.tower.obj (op m)).V := ⟨rfl⟩
    rw [nhds_induced, nhds_discrete, map_zero, comap_pure]
    congr 1
    ext x
    rw [Set.mem_preimage, Set.mem_singleton_iff, SetLike.mem_coe, ← ker_proj hc m,
      LinearMap.mem_ker]
  have h₁ : (@nhds (ConeSpace c) (⨅ j, TopologicalSpace.induced (proj c j) ⊥) 0).HasBasis
      (fun _ : ℕᵒᵖ => True)
      fun j => ((I ^ j.unop • ⊤ : Submodule R (ConeSpace c)) : Set (ConeSpace c)) := by
    rw [nhds_iInf]
    simp only [e]
    refine hasBasis_iInf_principal fun i j => ⟨op (max i.unop j.unop), ?_, ?_⟩
    · exact SetLike.coe_subset_coe.2
        (Submodule.smul_mono_left (Ideal.pow_le_pow_right (le_max_left _ _)))
    · exact SetLike.coe_subset_coe.2
        (Submodule.smul_mono_left (Ideal.pow_le_pow_right (le_max_right _ _)))
  have h₂ : (@nhds (ConeSpace c) (I.adicModuleTopology (ConeSpace c)) 0).HasBasis
      (fun _ : ℕᵒᵖ => True)
      fun j => ((I ^ j.unop • ⊤ : Submodule R (ConeSpace c)) : Set (ConeSpace c)) :=
    B.toAddGroupFilterBasis.nhds_zero_hasBasis.to_hasBasis
      (fun V hV => by
        obtain ⟨i, rfl⟩ := hV
        exact ⟨op i, trivial, subset_rfl⟩)
      (fun j _ => ⟨_, ⟨j.unop, rfl⟩, subset_rfl⟩)
  exact h₁.eq_of_same_basis h₂

include hc in
/-- If every level is a smooth representation, the action on the inverse limit of an
`ℓ`-divisible system of representations is jointly continuous for the `ℓ`-adic topology. -/
theorem continuous_action_adicModuleTopology [TopologicalSpace G] [ContinuousMul G]
    (hT : ∀ j, IsSmooth ((Rep.ActionToRep R G).obj (T.tower.obj j)).ρ) :
    letI := (Ideal.span {(ℓ : R)}).adicModuleTopology (ConeSpace c)
    Continuous fun p : G × ConeSpace c => act c p.1 p.2 := by
  rw [← topology_eq_adicModuleTopology hc]
  exact ContinuousLimit.continuous_action c hT

end Action

section Harris

open Langlands.Global Langlands.Shimura Langlands.Shimura.Coefficients EtaleAdicCohomology

variable (ℓ : ℕ) [NeZero ℓ]
variable {A : Type u} [Ring A] [Algebra ℚ A] [Module.Finite ℚ A]
variable {L : Type u} [Field L] [NumberField L]
variable {W : Type u} [AddCommGroup W] [Module L W] [Module.Finite L W]
variable {σ : AlgebraInvolution ℚ A} (ρ : (σ.baseChange L).AlgebraicRepresentation W)
variable (p : FinitePlace ℚ) (U : CompactOpenLevel σ.FiniteAdelicPoints)
variable (X : AlgebraicGeometry.Scheme.{u})
variable (Y : EquivariantDiagram (harrisCongruenceGroups ρ p U ℓ) X.Etale)
variable (hY : ∀ n, IsFiniteGeometricTorsor X (Y.action n))
variable (hΓ : ∀ {m' m : ℕ} (h : m' ≤ m),
  Epi ((Langlands.Geometry.EtaleDerivedSections.sections X (HarrisCoefficientIntegers L p)).map
    ((harrisEtaleDivisibleSystem ℓ ρ p U X Y hY).projection h)))

/-- Harris's degree-zero cohomology `H^0(X, 𝓛̃) = lim_m H^0(X, 𝓛 / ℓ ^ m)`, with its
projections to the modules of sections `Γ(X, 𝓛 / ℓ ^ m)`, is a limit cone over the inverse
system of the `ℓ`-divisible system `harrisEtaleSectionsDivisibleSystem`. -/
def harrisEtaleAdicCohomologyZeroCone :
    Cone (harrisEtaleSectionsDivisibleSystem ℓ ρ p U X Y hY hΓ).tower :=
  (limit.cone _).extend (harrisEtaleAdicCohomologyZeroDivisibleIso ℓ ρ p U X Y hY hΓ).hom

/-- `harrisEtaleAdicCohomologyZeroCone` is a limit cone. -/
def harrisEtaleAdicCohomologyZeroConeIsLimit :
    IsLimit (harrisEtaleAdicCohomologyZeroCone ℓ ρ p U X Y hY hΓ) :=
  (limit.isLimit _).extendIso _

include hΓ in
/-- When the section maps of the projections are surjective, Harris's degree-zero `ℓ`-adic
cohomology has no `ℓ`-torsion. -/
theorem isSMulRegular_harrisEtaleAdicCohomology_zero :
    IsSMulRegular (harrisEtaleAdicCohomology ℓ ρ p U X Y hY 0)
      (ℓ : HarrisCoefficientIntegers L p) :=
  isSMulRegular_of_isLimit (harrisEtaleAdicCohomologyZeroConeIsLimit ℓ ρ p U X Y hY hΓ)

include hΓ in
/-- When the section maps of the projections are surjective, Harris's degree-zero `ℓ`-adic
cohomology is `ℓ`-adically complete and Hausdorff. -/
theorem isAdicComplete_harrisEtaleAdicCohomology_zero :
    IsAdicComplete (Ideal.span {(ℓ : HarrisCoefficientIntegers L p)})
      (harrisEtaleAdicCohomology ℓ ρ p U X Y hY 0) :=
  isAdicComplete_of_isLimit (harrisEtaleAdicCohomologyZeroConeIsLimit ℓ ρ p U X Y hY hΓ)

/-- When the section maps of the projections are surjective, the reductions
`H^0(X, 𝓛̃) / ℓ ^ m H^0(X, 𝓛̃)` of Harris's degree-zero `ℓ`-adic cohomology are the modules of
sections `Γ(X, 𝓛 / ℓ ^ m)`, compatibly with the transition maps. -/
def harrisEtaleAdicCohomologyZeroReductionIso :
    reductionTower ℓ (harrisEtaleAdicCohomology ℓ ρ p U X Y hY 0) ≅
      harrisEtaleSectionsSystem ρ p U ℓ X Y hY :=
  reductionTowerIso (harrisEtaleAdicCohomologyZeroCone ℓ ρ p U X Y hY hΓ)
    (isCokernelOfIsLimit (harrisEtaleAdicCohomologyZeroConeIsLimit ℓ ρ p U X Y hY hΓ))

end Harris


end Langlands.Cohomology.DivisibleSystem
