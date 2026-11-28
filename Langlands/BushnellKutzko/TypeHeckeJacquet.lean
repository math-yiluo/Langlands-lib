import Langlands.BushnellKutzko.PositiveDepthTypeHeckeInjectivityStatement
import Langlands.BushnellKutzko.RepresentationIntertwining
import Langlands.Representation.Compact.ProjectionProof
import Langlands.Representation.Jacquet.Coinvariants
import Langlands.Representation.Smooth.Transfer.PullbackProof

/-! # Nonzero Jacquet modules from injective Hecke operators -/

noncomputable section

namespace Langlands.BushnellKutzko.TypeHeckeJacquet

open Langlands.Compact

universe uG uV uW uH

section OrbitMean

variable {H : Type uH} [Group H] {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- A linear map taking the constant value `w` on the finite orbit of `v` takes the value `w`
at the orbit mean of `v`. -/
theorem map_orbitMean_of_forall_eq (τ : Representation ℂ H V) (f : V →ₗ[ℂ] W) (v : V) (w : W)
    [Finite (orbit τ v)] (hf : ∀ h : H, f (τ h v) = w) : f (orbitMean τ v) = w := by
  classical
  let := Fintype.ofFinite (orbit τ v)
  have hx (x : orbit τ v) : f x.val = w := by
    obtain ⟨h, hh⟩ := x.property
    exact (congrArg f hh).symm.trans (hf h)
  have hc : (Fintype.card (orbit τ v) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [orbitMean_eq_finiteMean]
  change f ((Fintype.card (orbit τ v) : ℂ)⁻¹ • ∑ x : orbit τ v, x.val) = w
  rw [map_smul, map_sum]
  simp only [hx, Finset.sum_const, Finset.card_univ,
    ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hc, one_smul]

/-- Orbit means depend only on the orbit. -/
theorem orbitMean_eq_of_orbit_eq {H' : Type*} [Group H'] (τ : Representation ℂ H V)
    (τ' : Representation ℂ H' V) {v v' : V} (h : orbit τ v = orbit τ' v') :
    orbitMean τ v = orbitMean τ' v' := by
  unfold orbitMean
  rw [h]

theorem orbit_apply (τ : Representation ℂ H V) (h : H) (v : V) :
    orbit τ (τ h v) = orbit τ v := by
  ext x
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨k * h, by simp [map_mul, Module.End.mul_apply]⟩
  · rintro ⟨k, rfl⟩
    refine ⟨k * h⁻¹, ?_⟩
    simp only [map_mul, Module.End.mul_apply]
    rw [← Module.End.mul_apply (τ h⁻¹), ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

theorem orbitMean_apply (τ : Representation ℂ H V) (h : H) (v : V) :
    orbitMean τ (τ h v) = orbitMean τ v :=
  orbitMean_eq_of_orbit_eq τ τ (orbit_apply τ h v)

/-- The orbit mean as a linear map, when every orbit is finite. -/
def orbitMeanLinear (τ : Representation ℂ H V) (hfin : ∀ v, Finite (orbit τ v)) :
    V →ₗ[ℂ] V where
  toFun := orbitMean τ
  map_add' v w := by
    let := hfin v
    let := hfin w
    let := hfin (v + w)
    exact orbitMean_add τ v w
  map_smul' c v := by
    let := hfin v
    let := hfin (c • v)
    exact orbitMean_smul τ c v

theorem orbitMeanLinear_apply (τ : Representation ℂ H V) (hfin : ∀ v, Finite (orbit τ v))
    (v : V) : orbitMeanLinear τ hfin v = orbitMean τ v := rfl

/-- Restricting to a subgroup gives a subset of the orbit. -/
theorem orbit_comp_subset (τ : Representation ℂ H V) (N : Subgroup H) (v : V) :
    orbit (τ.comp N.subtype) v ⊆ orbit τ v := by
  rintro x ⟨n, rfl⟩
  exact ⟨n.val, rfl⟩

theorem finite_orbit_comp (τ : Representation ℂ H V) (N : Subgroup H) (v : V)
    [Finite (orbit τ v)] : Finite (orbit (τ.comp N.subtype) v) :=
  Set.Finite.subset (Set.toFinite (orbit τ v)) (orbit_comp_subset τ N v)

/-- Averaging over a group absorbs a preceding average over a subgroup. -/
theorem orbitMean_orbitMean_comp (τ : Representation ℂ H V) (hfin : ∀ v, Finite (orbit τ v))
    (N : Subgroup H) (v : V) :
    orbitMean τ (orbitMean (τ.comp N.subtype) v) = orbitMean τ v := by
  let := hfin v
  let := finite_orbit_comp τ N v
  exact map_orbitMean_of_forall_eq (τ.comp N.subtype) (orbitMeanLinear τ hfin) v _
    (fun n => orbitMean_apply τ n.val v)

/-- Averaging over a subgroup `K` absorbs a preceding average over a subgroup `N ≤ K`. -/
theorem orbitMean_orbitMean_of_le (τ : Representation ℂ H V) {N K : Subgroup H} (hNK : N ≤ K)
    (hfin : ∀ v, Finite (orbit (τ.comp K.subtype) v)) (v : V)
    [Finite (orbit (τ.comp N.subtype) v)] :
    orbitMean (τ.comp K.subtype) (orbitMean (τ.comp N.subtype) v) =
      orbitMean (τ.comp K.subtype) v :=
  map_orbitMean_of_forall_eq (τ.comp N.subtype) (orbitMeanLinear (τ.comp K.subtype) hfin) v _
    (fun n => orbitMean_apply (τ.comp K.subtype) ⟨n.val, hNK n.property⟩ v)

/-- A finite orbit stays finite after restriction along a homomorphism. -/
theorem finite_orbit_comp_hom {H' : Type*} [Group H'] (τ : Representation ℂ H V) (φ : H' →* H)
    (v : V) [Finite (orbit τ v)] : Finite (orbit (τ.comp φ) v) :=
  Set.Finite.subset (Set.toFinite (orbit τ v)) (by rintro x ⟨h, rfl⟩; exact ⟨φ h, rfl⟩)

/-- In a compact topological group, smooth vectors have finite orbits. -/
theorem finite_orbit_of_isSmooth [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H]
    (τ : Representation ℂ H V) (hτ : IsSmooth τ) (v : V) : Finite (orbit τ v) := by
  let : MulAction H V := representationAction τ
  obtain ⟨O, hO⟩ := hτ v
  have hle : O.toSubgroup ≤ MulAction.stabilizer H v := fun k hk => hO ⟨k, hk⟩
  have hopen : IsOpen (MulAction.stabilizer H v : Set H) :=
    Subgroup.isOpen_mono hle O.isOpen
  let : Finite (H ⧸ MulAction.stabilizer H v) := Subgroup.quotient_finite_of_isOpen _ hopen
  exact Finite.of_equiv (H ⧸ MulAction.stabilizer H v)
    (MulAction.orbitEquivQuotientStabilizer H v).symm

end OrbitMean

section Conjugation

variable {G : Type uG} [Group G] {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Averaging over a conjugate subgroup: if `K = g K' g⁻¹`, the `K`-mean of `π(g) v` is
`π(g)` applied to the `K'`-mean of `v`. -/
theorem orbitMean_conj (π : Representation ℂ G V) {K K' : Subgroup G} (g : G)
    (hK : ∀ k, k ∈ K ↔ g⁻¹ * k * g ∈ K') (v : V) [Finite (orbit (π.comp K'.subtype) v)] :
    orbitMean (π.comp K.subtype) (π g v) = π g (orbitMean (π.comp K'.subtype) v) := by
  let φ : K' →* K :=
    { toFun := fun k => ⟨g * k * g⁻¹, (hK _).mpr (by simp [mul_assoc])⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp [mul_assoc]) }
  have hf : ∀ (k : K') (w : V), π g ((π.comp K'.subtype) k w) =
      ((π.comp K.subtype).comp φ) k (π g w) := by
    intro k w
    change π g (π k w) = π (g * k * g⁻¹) (π g w)
    simp only [map_mul, Module.End.mul_apply]
    rw [← Module.End.mul_apply (π g⁻¹), ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have horb : orbit ((π.comp K.subtype).comp φ) (π g v) = orbit (π.comp K.subtype) (π g v) := by
    ext x
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨φ k, rfl⟩
    · rintro ⟨k, rfl⟩
      refine ⟨⟨g⁻¹ * k * g, (hK k).mp k.property⟩, ?_⟩
      change π (g * (g⁻¹ * k * g) * g⁻¹) (π g v) = π k (π g v)
      congr 2
      group
  let := finite_orbit_comp_hom (π.comp K'.subtype) (MonoidHom.id _) v
  have hfin : Finite (orbit ((π.comp K.subtype).comp φ) (π g v)) := by
    let f : orbit (π.comp K'.subtype) v → orbit ((π.comp K.subtype).comp φ) (π g v) :=
      fun x => ⟨π g x.val, by
        obtain ⟨k, hk⟩ := x.property
        exact ⟨k, by rw [← hk]; exact (hf k v).symm⟩⟩
    refine Finite.of_surjective f ?_
    rintro ⟨y, k, rfl⟩
    exact ⟨⟨(π.comp K'.subtype) k v, k, rfl⟩, Subtype.ext (hf k v)⟩
  have h := orbitMean_map (π.comp K'.subtype) ((π.comp K.subtype).comp φ) (π g) hf v
  rw [h]
  exact orbitMean_eq_of_orbit_eq _ _ horb.symm

end Conjugation

section LinHom

variable {H : Type uH} [Group H] [TopologicalSpace H]
  {V : Type uV} [AddCommGroup V] [Module ℂ V] {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- The action `j ↦ σ(j) ∘ (-) ∘ ρ(j)⁻¹` on linear maps out of a finite-dimensional smooth
representation into a smooth representation is smooth. -/
theorem isSmooth_linHom (ρ : Representation ℂ H W) (σ : Representation ℂ H V)
    [FiniteDimensional ℂ W] (hρ : IsSmooth ρ) (hσ : IsSmooth σ) :
    IsSmooth (Representation.linHom ρ σ) := by
  intro ψ
  let b := Module.finBasis ℂ W
  choose O hO using fun i => hρ (b i)
  choose O' hO' using fun i => hσ (ψ (b i))
  let K : Subgroup H := ⨅ i, (O i).toSubgroup ⊓ (O' i).toSubgroup
  have hK : IsOpen (K : Set H) := by
    simp only [K, Subgroup.coe_iInf, Subgroup.coe_inf]
    exact isOpen_iInter_of_finite fun i => (O i).isOpen.inter (O' i).isOpen
  refine ⟨⟨K, hK⟩, ?_⟩
  intro k
  have hk : ∀ i, (k : H) ∈ (O i).toSubgroup ⊓ (O' i).toSubgroup :=
    Subgroup.mem_iInf.mp k.property
  change Representation.linHom ρ σ k ψ = ψ
  rw [Representation.linHom_apply]
  refine b.ext fun i => ?_
  have h1 : ρ (k : H)⁻¹ (b i) = b i := hO i ⟨_, (O i).inv_mem (hk i).1⟩
  have h2 : σ (k : H) (ψ (b i)) = ψ (b i) := hO' i ⟨_, (hk i).2⟩
  simp only [LinearMap.comp_apply, h1, h2]

end LinHom

section Main

variable {G : Type uG} [Group G]

/-- An Iwahori factorization `J = (J ∩ U)(J ∩ M)(J ∩ U⁻)` together with an element `ζ` that
commutes with `J ∩ M`, sends `U` into `U` under `x ↦ ζ x ζ⁻¹` (only this inclusion is
required, not `ζ U ζ⁻¹ = U`), contracts `J ∩ U` under `x ↦ ζ x ζ⁻¹`, contracts `J ∩ U⁻` under
`x ↦ ζ⁻¹ x ζ`, and carries every element of `U` into `J` after conjugation by a power. -/
structure IsHeckeContraction (J U M Ubar : Subgroup G) (ζ : G) : Prop where
  factor : ∀ j ∈ J, ∃ u ∈ J ⊓ U, ∃ m ∈ J ⊓ M, ∃ l ∈ J ⊓ Ubar, j = u * m * l
  commute : ∀ m ∈ J ⊓ M, ζ * m = m * ζ
  normalize : ∀ x ∈ U, ζ * x * ζ⁻¹ ∈ U
  upper : ∀ u ∈ J ⊓ U, ζ * u * ζ⁻¹ ∈ J
  lower : ∀ l ∈ J ⊓ Ubar, ζ⁻¹ * l * ζ ∈ J ⊓ Ubar
  exhaust : ∀ x ∈ U, ∃ r : ℕ, ζ ^ r * x * (ζ ^ r)⁻¹ ∈ J

namespace IsHeckeContraction

variable {J U M Ubar : Subgroup G} {ζ : G}

theorem upper_pow (h : IsHeckeContraction J U M Ubar ζ) (s : ℕ) :
    ∀ u ∈ J ⊓ U, ζ ^ s * u * (ζ ^ s)⁻¹ ∈ J ⊓ U := by
  induction s with
  | zero => intro u hu; simpa using hu
  | succ s ih =>
    intro u hu
    have e : ζ ^ (s + 1) * u * (ζ ^ (s + 1))⁻¹ = ζ * (ζ ^ s * u * (ζ ^ s)⁻¹) * ζ⁻¹ := by group
    rw [e]
    exact ⟨h.upper _ (ih u hu), h.normalize _ (ih u hu).2⟩

theorem lower_pow (h : IsHeckeContraction J U M Ubar ζ) (s : ℕ) :
    ∀ l ∈ J ⊓ Ubar, (ζ ^ s)⁻¹ * l * ζ ^ s ∈ J ⊓ Ubar := by
  induction s with
  | zero => intro l hl; simpa using hl
  | succ s ih =>
    intro l hl
    have e : (ζ ^ (s + 1))⁻¹ * l * ζ ^ (s + 1) = ζ⁻¹ * ((ζ ^ s)⁻¹ * l * ζ ^ s) * ζ := by group
    rw [e]
    exact h.lower _ (ih l hl)

theorem commute_pow (h : IsHeckeContraction J U M Ubar ζ) (s : ℕ) :
    ∀ m ∈ J ⊓ M, ζ ^ s * m = m * ζ ^ s := by
  intro m hm
  exact ((Commute.pow_left (h.commute m hm) s))

theorem eventually_mem (h : IsHeckeContraction J U M Ubar ζ) (x : G) (hx : x ∈ U) :
    ∃ r : ℕ, ∀ s : ℕ, r ≤ s → ζ ^ s * x * (ζ ^ s)⁻¹ ∈ J ⊓ U := by
  obtain ⟨r, hr⟩ := h.exhaust x hx
  have hU : ∀ t : ℕ, ∀ y ∈ U, ζ ^ t * y * (ζ ^ t)⁻¹ ∈ U := by
    intro t
    induction t with
    | zero => intro y hy; simpa using hy
    | succ t ih =>
      intro y hy
      have e : ζ ^ (t + 1) * y * (ζ ^ (t + 1))⁻¹ = ζ * (ζ ^ t * y * (ζ ^ t)⁻¹) * ζ⁻¹ := by group
      rw [e]
      exact h.normalize _ (ih y hy)
  refine ⟨r, fun s hs => ?_⟩
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hs
  have e : ζ ^ (r + t) * x * (ζ ^ (r + t))⁻¹ = ζ ^ t * (ζ ^ r * x * (ζ ^ r)⁻¹) * (ζ ^ t)⁻¹ := by
    group
  rw [e]
  exact h.upper_pow t _ ⟨hr, hU r x hx⟩

end IsHeckeContraction

end Main

section MainTheorem

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V] {W : Type uW} [AddCommGroup W] [Module ℂ W]

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- For `d ∈ J ∩ x J x⁻¹`, the map `π(x) ∘ Φ ∘ Θ` is fixed by `d` under `ψ ↦ π(d) ∘ ψ ∘ ρ(d)⁻¹`. -/
theorem linHom_heckeMap_eq {J : Subgroup G} (π : Representation ℂ G V) (ρ : Representation ℂ J W)
    (x : G) (Θ : intertwiningSpace ρ ρ x) (Φ : ρ.IntertwiningMap (π.comp J.subtype)) (d : J)
    (hd : x⁻¹ * d * x ∈ J) :
    Representation.linHom ρ (π.comp J.subtype) d (π x ∘ₗ Φ.toLinearMap ∘ₗ Θ.toLinearMap) =
      π x ∘ₗ Φ.toLinearMap ∘ₗ Θ.toLinearMap := by
  rw [Representation.linHom_apply]
  ext w
  let h : J := ⟨x⁻¹ * d * x, hd⟩
  have hk : ((h⁻¹ : J) : G) ∈ intertwiningDomain J J x := by
    rw [mem_intertwiningDomain]
    refine ⟨?_, (h⁻¹).property⟩
    have e : x * ((h⁻¹ : J) : G) * x⁻¹ = (d : G)⁻¹ := by
      simp only [h, InvMemClass.coe_inv, mul_inv_rev, inv_inv]
      group
    rw [e]
    exact J.inv_mem d.property
  have hΘ := Representation.IntertwiningMap.isIntertwining _ _ Θ
    (⟨((h⁻¹ : J) : G), hk⟩ : intertwiningDomain J J x) w
  have e1 : (intertwiningDomainConj J J x ⟨((h⁻¹ : J) : G), hk⟩ : J) = d⁻¹ := by
    apply Subtype.ext
    simp only [coe_intertwiningDomainConj, h, InvMemClass.coe_inv, mul_inv_rev, inv_inv]
    group
  simp only [MonoidHom.coe_comp, Function.comp_apply, e1] at hΘ
  simp only [LinearMap.comp_apply, Representation.IntertwiningMap.toLinearMap_apply]
  rw [hΘ]
  change π d (π x (Φ (ρ (intertwiningDomainIncl J J x ⟨((h⁻¹ : J) : G), hk⟩) (Θ w)))) = _
  rw [Φ.isIntertwining]
  simp only [MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype,
    coe_intertwiningDomainIncl]
  rw [← Module.End.mul_apply (π x), ← map_mul, ← Module.End.mul_apply (π (d : G)), ← map_mul]
  congr 2
  simp only [h, InvMemClass.coe_inv, mul_inv_rev, inv_inv]
  group

/-- **Nonzero Jacquet modules from injective Hecke operators.** Let `J` be a compact open
subgroup of `G`, `ρ` a smooth finite-dimensional representation of `J`, and `ζ` an element
satisfying `IsHeckeContraction J U M Ubar ζ` such that `ρ` is trivial on
`ζ^{r₀} (J ∩ U) ζ^{-r₀}` for some `r₀`. Suppose that for every `r` some intertwiner
`Θ ∈ I_{ζ^r}(ρ)` has an injective Hecke operator on `Hom_J(ρ, π)`. If `π` is smooth and contains
`ρ`, then the Jacquet module of `π` along `U` is nonzero. -/
theorem not_subsingleton_coinvariants_of_heckeInjective
    (π : Representation ℂ G V) (hπ : IsSmooth π)
    {J : Subgroup G} (hJo : IsOpen (J : Set G)) (hJc : IsCompact (J : Set G))
    (ρ : Representation ℂ J W) [FiniteDimensional ℂ W] (hρ : IsSmooth ρ)
    {U M Ubar : Subgroup G} {ζ : G} (h : IsHeckeContraction J U M Ubar ζ)
    (hshrink : ∃ r₀ : ℕ, ∀ j : J, (∃ u ∈ J ⊓ U, (j : G) = ζ ^ r₀ * u * (ζ ^ r₀)⁻¹) → ρ j = 1)
    (hHecke : ∀ r : ℕ, ∃ Θ : intertwiningSpace ρ ρ (ζ ^ r),
      ∀ Φ : ρ.IntertwiningMap (π.comp J.subtype),
        typeHeckeMean ρ π (ζ ^ r) Θ.toLinearMap Φ.toLinearMap = 0 → Φ = 0)
    (Φ : ρ.IntertwiningMap (π.comp J.subtype)) (hΦ : Φ ≠ 0) :
    ¬ Subsingleton (Jacquet.Coinvariants π U) := by
  intro hsub
  classical
  let JO : OpenSubgroup G := ⟨J, hJo⟩
  have hfinJ : ∀ (K : Subgroup G), K ≤ J → ∀ v : V, Finite (orbit (π.comp K.subtype) v) := by
    intro K hKJ v
    let := Compact.finite_orbit_of_smooth π hπ JO hJc v
    exact Set.Finite.subset (Set.toFinite (orbit (π.comp JO.toSubgroup.subtype) v))
      (by rintro x ⟨k, rfl⟩; exact ⟨⟨k.val, hKJ k.property⟩, rfl⟩)
  set JU : Subgroup G := J ⊓ U with hJUdef
  have hJU : JU ≤ J := inf_le_left
  let A : V →ₗ[ℂ] V := orbitMeanLinear (π.comp JU.subtype) (hfinJ JU hJU)
  have hA : ∀ v, A v = orbitMean (π.comp JU.subtype) v := fun _ => rfl
  -- Vanishing on relations.
  have hvanish : ∀ v ∈ Jacquet.relations π U, ∃ s₀ : ℕ, ∀ s, s₀ ≤ s → A (π (ζ ^ s) v) = 0 := by
    intro v hv
    rw [Jacquet.relations_eq_span] at hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨⟨n, w⟩, rfl⟩ := hx
      obtain ⟨r, hr⟩ := h.eventually_mem n n.property
      refine ⟨r, fun s hs => ?_⟩
      rw [map_sub, map_sub, sub_eq_zero]
      have hmem := hr s hs
      calc A (π (ζ ^ s) (π n w)) = A (π (ζ ^ s * n * (ζ ^ s)⁻¹) (π (ζ ^ s) w)) := by
            congr 1
            simp only [← Module.End.mul_apply, ← map_mul]
            congr 2
            group
        _ = A (π (ζ ^ s) w) := by
            rw [hA, hA]
            exact orbitMean_apply (π.comp JU.subtype) ⟨_, hmem⟩ _
    | zero => exact ⟨0, fun s _ => by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨rx, hx⟩ := hx
      obtain ⟨ry, hy⟩ := hy
      exact ⟨max rx ry, fun s hs => by
        rw [map_add, map_add, hx s (le_trans (le_max_left _ _) hs),
          hy s (le_trans (le_max_right _ _) hs), add_zero]⟩
    | smul c x _ hx =>
      obtain ⟨r, hr⟩ := hx
      exact ⟨r, fun s hs => by rw [map_smul, map_smul, hr s hs, smul_zero]⟩
  -- Uniformity over the image of `Φ`.
  have huniform : ∃ s₀ : ℕ, ∀ w : W, A (π (ζ ^ s₀) (Φ w)) = 0 := by
    let b := Module.finBasis ℂ W
    have hb : ∀ i, ∃ s₀ : ℕ, ∀ s, s₀ ≤ s → A (π (ζ ^ s) (Φ (b i))) = 0 := fun i =>
      hvanish _ ((Jacquet.mk_eq_zero π U _).mp (Subsingleton.elim _ _))
    choose r hr using hb
    refine ⟨Finset.univ.sup r, fun w => ?_⟩
    have hz : (A ∘ₗ π (ζ ^ Finset.univ.sup r) ∘ₗ Φ.toLinearMap) = 0 := by
      refine b.ext fun i => ?_
      exact hr i _ (Finset.le_sup (Finset.mem_univ i))
    exact LinearMap.congr_fun hz w
  obtain ⟨s₀, hs₀⟩ := huniform
  obtain ⟨r₀, hr₀⟩ := hshrink
  obtain ⟨Θ, hΘ⟩ := hHecke (r₀ + s₀)
  apply hΦ
  apply hΘ
  -- The Hecke mean vanishes.
  set φ : W →ₗ[ℂ] V := π (ζ ^ (r₀ + s₀)) ∘ₗ Φ.toLinearMap ∘ₗ Θ.toLinearMap with hφdef
  let R := Representation.linHom ρ (π.comp J.subtype)
  have hπJ : IsSmooth (π.comp J.subtype) := isSmooth_comp J.subtype continuous_subtype_val hπ
  have hR : IsSmooth R := isSmooth_linHom ρ (π.comp J.subtype) hρ hπJ
  let : CompactSpace J := isCompact_iff_compactSpace.mp hJc
  have hfinR : ∀ ψ, Finite (orbit R ψ) := finite_orbit_of_isSmooth R hR
  let JU' : Subgroup J := U.subgroupOf J
  -- Step 1: the `J`-orbit of `φ` is its `J ∩ U`-orbit.
  have hfix : ∀ d : J, (ζ ^ (r₀ + s₀))⁻¹ * d * ζ ^ (r₀ + s₀) ∈ J → R d φ = φ := fun d hd =>
    linHom_heckeMap_eq π ρ (ζ ^ (r₀ + s₀)) Θ Φ d hd
  have horb : orbit R φ = orbit (R.comp JU'.subtype) φ := by
    refine Set.Subset.antisymm ?_ (orbit_comp_subset R JU' φ)
    rintro _ ⟨j, rfl⟩
    obtain ⟨u, hu, m, hm, l, hl, hj⟩ := h.factor j j.property
    let uJ : J := ⟨u, hu.1⟩
    let mlJ : J := ⟨m * l, J.mul_mem hm.1 hl.1⟩
    have hj' : j = uJ * mlJ := Subtype.ext (by simp [uJ, mlJ, hj, mul_assoc])
    have hml : (ζ ^ (r₀ + s₀))⁻¹ * (mlJ : G) * ζ ^ (r₀ + s₀) ∈ J := by
      have e : (ζ ^ (r₀ + s₀))⁻¹ * (m * l) * ζ ^ (r₀ + s₀) =
          m * ((ζ ^ (r₀ + s₀))⁻¹ * l * ζ ^ (r₀ + s₀)) := by
        have hc := h.commute_pow (r₀ + s₀) m hm
        calc (ζ ^ (r₀ + s₀))⁻¹ * (m * l) * ζ ^ (r₀ + s₀)
            = (ζ ^ (r₀ + s₀))⁻¹ * m * ζ ^ (r₀ + s₀) *
                ((ζ ^ (r₀ + s₀))⁻¹ * l * ζ ^ (r₀ + s₀)) := by group
          _ = m * ((ζ ^ (r₀ + s₀))⁻¹ * l * ζ ^ (r₀ + s₀)) := by
              rw [mul_assoc (ζ ^ (r₀ + s₀))⁻¹ m, ← hc]
              group
      change (ζ ^ (r₀ + s₀))⁻¹ * (m * l) * ζ ^ (r₀ + s₀) ∈ J
      rw [e]
      exact J.mul_mem hm.1 (h.lower_pow (r₀ + s₀) l hl).1
    refine ⟨⟨uJ, hu.2⟩, ?_⟩
    change R uJ φ = R j φ
    rw [hj', map_mul, Module.End.mul_apply, hfix mlJ hml]
  -- Step 2: average first over the conjugate `ζ^{r₀} (J ∩ U) ζ^{-r₀}`.
  let K : Subgroup G := JU.map (MulAut.conj (ζ ^ r₀)).toMonoidHom
  have hK : ∀ k, k ∈ K ↔ (ζ ^ r₀)⁻¹ * k * ζ ^ r₀ ∈ JU := by
    intro k
    constructor
    · rintro ⟨u, hu, rfl⟩
      change (ζ ^ r₀)⁻¹ * (ζ ^ r₀ * u * (ζ ^ r₀)⁻¹) * ζ ^ r₀ ∈ JU
      have e : (ζ ^ r₀)⁻¹ * (ζ ^ r₀ * u * (ζ ^ r₀)⁻¹) * ζ ^ r₀ = u := by group
      rw [e]
      exact hu
    · intro hk
      refine ⟨(ζ ^ r₀)⁻¹ * k * ζ ^ r₀, hk, ?_⟩
      change ζ ^ r₀ * ((ζ ^ r₀)⁻¹ * k * ζ ^ r₀) * (ζ ^ r₀)⁻¹ = k
      group
  have hKJU : ∀ k ∈ K, k ∈ JU := by
    rintro _ ⟨u, hu, rfl⟩
    exact h.upper_pow r₀ u hu
  let N0 : Subgroup J := K.subgroupOf J
  have hN0 : N0 ≤ JU' := fun j hj => (hKJU _ hj).2
  have hfinJU' : ∀ ψ, Finite (orbit (R.comp JU'.subtype) ψ) := fun ψ =>
    let := hfinR ψ
    finite_orbit_comp R JU' ψ
  let := hfinR φ
  let := finite_orbit_comp R N0 φ
  have hstep2 := orbitMean_orbitMean_of_le R hN0 hfinJU' φ
  -- Step 3: the average over the conjugate vanishes.
  have hstep3 : orbitMean (R.comp N0.subtype) φ = 0 := by
    ext w
    let ev : (W →ₗ[ℂ] V) →ₗ[ℂ] V := LinearMap.applyₗ w
    let σ' : Representation ℂ N0 V := (π.comp J.subtype).comp N0.subtype
    have hev : ∀ (n : N0) (ψ : W →ₗ[ℂ] V), ev ((R.comp N0.subtype) n ψ) = σ' n (ev ψ) := by
      intro n ψ
      have hn : ρ (n⁻¹ : N0) = 1 := by
        refine hr₀ _ ?_
        obtain ⟨u, hu, hu'⟩ := (n⁻¹ : N0).property
        exact ⟨u, hu, hu'.symm⟩
      change (R n ψ) w = π n (ψ w)
      rw [Representation.linHom_apply]
      change π n (ψ (ρ (n : J)⁻¹ w)) = π n (ψ w)
      have : ρ ((n : J)⁻¹) = 1 := hn
      rw [this, Module.End.one_apply]
    let : Finite (orbit σ' (ev φ)) := by
      let := hfinJ K (fun k hk => (hKJU k hk).1) (ev φ)
      refine Set.Finite.subset (Set.toFinite (orbit (π.comp K.subtype) (ev φ))) ?_
      rintro _ ⟨n, rfl⟩
      exact ⟨⟨(n : J), n.property⟩, rfl⟩
    have hmap := orbitMean_map (R.comp N0.subtype) σ' ev hev φ
    change ev (orbitMean (R.comp N0.subtype) φ) = 0
    rw [hmap]
    have horbK : orbit σ' (ev φ) = orbit (π.comp K.subtype) (ev φ) := by
      ext y
      constructor
      · rintro ⟨n, rfl⟩
        exact ⟨⟨(n : J), n.property⟩, rfl⟩
      · rintro ⟨k, rfl⟩
        exact ⟨⟨⟨k, (hKJU k k.property).1⟩, k.property⟩, rfl⟩
    rw [orbitMean_eq_of_orbit_eq _ _ horbK]
    have hφw : ev φ = π (ζ ^ r₀) (π (ζ ^ s₀) (Φ (Θ w))) := by
      change π (ζ ^ (r₀ + s₀)) (Φ (Θ w)) = _
      rw [show π (ζ ^ (r₀ + s₀)) = π (ζ ^ r₀) * π (ζ ^ s₀) by rw [pow_add, map_mul],
        Module.End.mul_apply]
    rw [hφw]
    let := hfinJ JU hJU (π (ζ ^ s₀) (Φ (Θ w)))
    rw [orbitMean_conj π (ζ ^ r₀) hK, ← hA, hs₀, map_zero]
  change orbitMean R φ = 0
  rw [orbitMean_eq_of_orbit_eq R (R.comp JU'.subtype) horb, ← hstep2, hstep3]
  exact orbitMean_id _ 0 (fun _ => map_zero _)

end MainTheorem

end Langlands.BushnellKutzko.TypeHeckeJacquet
