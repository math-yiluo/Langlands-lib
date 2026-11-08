import Langlands.Automorphic.Contragredient
import Langlands.Automorphic.OperatorUnitaryForm
import Langlands.Automorphic.OperatorCompactCompatibility
import Langlands.Representation.Unitary.Completion
import Langlands.Global.FiniteAdelicGL.StandardIntegralCompact
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Langlands.Representation.Smooth.Transfer.SubquotientProof

/-!
# A unitary criterion for contragredient realizations

Let `ρ` be a smooth representation of a topological group `G` and `κ` a representation
of a group `K` on the same complex vector space, commuting with `ρ`, with every vector
`κ`-finite. Joint admissibility asks that for every open subgroup `L` of `G` and every
representation `σ` of `K` on `Fin m → ℂ`, the `K`-equivariant linear maps from `σ` into
the `L`-fixed vectors form a finite-dimensional space.

If a positive definite form is invariant under `ρ` and `κ`, the pair is jointly
admissible, and every open subgroup of `G` contains a compact open subgroup, then every
`ρ`-smooth and `κ`-finite linear functional is the inner product with a vector.

For actual automorphic realizations this gives: if `S` carries a unitary form, is
jointly admissible, and `T` is related to `S` by a conjugate-linear bijection commuting
with the finite, compact and real Lie operators, then `T` realizes the contragredient
of `S`.
-/

noncomputable section

universe uG uK uV u

namespace Langlands

open FiniteVectors

section JointAdmissibility

variable {G : Type uG} [Group G] {K : Type uK} [Group K]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

private theorem mem_fixedVectors_iff' {ρ : Representation ℂ G V} {L : Subgroup G} {v : V} :
    v ∈ fixedVectors ρ L ↔ ∀ d ∈ L, ρ d v = v :=
  ⟨fun h d hd => h ⟨d, hd⟩, fun h d => h d d.2⟩

/-- The `K`-equivariant linear maps from a representation `σ` of `K` on `Fin m → ℂ` into
the vectors fixed by the subgroup `L` under `ρ`. -/
def jointMultiplicitySpace (ρ : Representation ℂ G V) (κ : Representation ℂ K V)
    (L : Subgroup G) {m : ℕ} (σ : Representation ℂ K (Fin m → ℂ)) :
    Submodule ℂ ((Fin m → ℂ) →ₗ[ℂ] V) where
  carrier := {φ | (∀ v, φ v ∈ fixedVectors ρ L) ∧ ∀ k v, φ (σ k v) = κ k (φ v)}
  add_mem' := by
    rintro φ ψ ⟨hφ, hφ'⟩ ⟨hψ, hψ'⟩
    refine ⟨fun v => (fixedVectors ρ L).add_mem (hφ v) (hψ v), fun k v => ?_⟩
    simp only [LinearMap.add_apply, map_add, hφ', hψ']
  zero_mem' := ⟨fun _ => (fixedVectors ρ L).zero_mem, fun k v => by simp⟩
  smul_mem' := by
    rintro a φ ⟨hφ, hφ'⟩
    refine ⟨fun v => (fixedVectors ρ L).smul_mem a (hφ v), fun k v => ?_⟩
    simp only [LinearMap.smul_apply, map_smul, hφ']

theorem mem_jointMultiplicitySpace (ρ : Representation ℂ G V) (κ : Representation ℂ K V)
    (L : Subgroup G) {m : ℕ} (σ : Representation ℂ K (Fin m → ℂ))
    (φ : (Fin m → ℂ) →ₗ[ℂ] V) :
    φ ∈ jointMultiplicitySpace ρ κ L σ ↔
      (∀ v, φ v ∈ fixedVectors ρ L) ∧ ∀ k v, φ (σ k v) = κ k (φ v) :=
  Iff.rfl

/-- Joint admissibility: every multiplicity space of a finite-dimensional representation
of `K` in the vectors fixed by an open subgroup of `G` is finite-dimensional. -/
def IsJointlyAdmissible [TopologicalSpace G] (ρ : Representation ℂ G V)
    (κ : Representation ℂ K V) : Prop :=
  ∀ (L : OpenSubgroup G) (m : ℕ) (σ : Representation ℂ K (Fin m → ℂ)),
    FiniteDimensional ℂ (jointMultiplicitySpace ρ κ L.toSubgroup σ)

/-- Transport of a representation along a conjugate-linear equivalence. -/
def conjugateTransport {E : Type*} [AddCommGroup E] [Module ℂ E]
    {W : Type*} [AddCommGroup W] [Module ℂ W] (γ : E ≃ₛₗ[starRingEnd ℂ] W)
    (σ : Representation ℂ K E) : Representation ℂ K W where
  toFun k := (γ.toLinearMap.comp ((σ k).comp γ.symm.toLinearMap) : W →ₗ[ℂ] W)
  map_one' := by
    ext w
    simp
  map_mul' k k' := by
    ext w
    simp

theorem conjugateTransport_apply {E : Type*} [AddCommGroup E] [Module ℂ E]
    {W : Type*} [AddCommGroup W] [Module ℂ W] (γ : E ≃ₛₗ[starRingEnd ℂ] W)
    (σ : Representation ℂ K E) (k : K) (w : W) :
    conjugateTransport γ σ k w = γ (σ k (γ.symm w)) :=
  rfl

end JointAdmissibility

namespace InvariantPositiveForm

section Riesz

variable {G : Type uG} [Group G] {K : Type uK} [Group K]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {ρ : Representation ℂ G V} (b : InvariantPositiveForm ρ)

theorem inner_add_left' (v w x : V) : b.inner (v + w) x = b.inner v x + b.inner w x :=
  b.add_left v w x

theorem inner_smul_left' (c : ℂ) (v w : V) :
    b.inner (c • v) w = starRingEnd ℂ c * b.inner v w :=
  b.smul_left v w c

theorem inner_add_right' (v w x : V) : b.inner v (w + x) = b.inner v w + b.inner v x := by
  simp only [← inner_toNormedCarrier, map_add, inner_add_right]

theorem inner_smul_right' (c : ℂ) (v w : V) : b.inner v (c • w) = c * b.inner v w := by
  simp only [← inner_toNormedCarrier, map_smul, inner_smul_right]

/-- Two vectors of a subspace with the same inner products against it are equal. -/
theorem eq_of_inner_eq {U : Submodule ℂ V} {g g' : V} (hg : g ∈ U) (hg' : g' ∈ U)
    (h : ∀ u ∈ U, b.inner g u = b.inner g' u) : g = g' := by
  have h₀ := h (g - g') (U.sub_mem hg hg')
  apply sub_eq_zero.mp
  apply b.definite
  have e₁ : b.inner (g - g') (g - g') = inner ℂ (b.toNormedCarrier g - b.toNormedCarrier g')
      (b.toNormedCarrier (g - g')) := by
    rw [← map_sub]
    rfl
  have e₂ : b.inner g (g - g') =
      inner ℂ (b.toNormedCarrier g) (b.toNormedCarrier (g - g')) := rfl
  have e₃ : b.inner g' (g - g') =
      inner ℂ (b.toNormedCarrier g') (b.toNormedCarrier (g - g')) := rfl
  change b.inner (g - g') (g - g') = 0
  rw [e₁, inner_sub_left, ← e₂, ← e₃, h₀, sub_self]

/-- Riesz representation on a finite-dimensional subspace. -/
theorem exists_inner_eq (U : Submodule ℂ V) (hU : FiniteDimensional ℂ U)
    (l : Module.Dual ℂ V) : ∃ g ∈ U, ∀ u ∈ U, b.inner g u = l u := by
  let ι : V ≃ₗ[ℂ] b.NormedCarrier := b.toNormedCarrier
  let U' : Submodule ℂ b.NormedCarrier := U.map ι.toLinearMap
  have hU' : FiniteDimensional ℂ U' := Module.Finite.map U ι.toLinearMap
  have : CompleteSpace U' := FiniteDimensional.complete ℂ U'
  let μ : StrongDual ℂ U' :=
    LinearMap.toContinuousLinearMap ((l.comp ι.symm.toLinearMap).comp U'.subtype)
  let g' : U' := (InnerProductSpace.toDual ℂ U').symm μ
  have hg' : ι (ι.symm (g' : b.NormedCarrier)) = (g' : b.NormedCarrier) :=
    ι.apply_symm_apply _
  refine ⟨ι.symm g', ?_, fun u hu => ?_⟩
  · obtain ⟨v, hv, hv'⟩ := Submodule.mem_map.mp g'.2
    rw [← hv']
    simpa using hv
  · have hu' : ι u ∈ U' := Submodule.mem_map_of_mem hu
    have h := InnerProductSpace.toDual_symm_apply (𝕜 := ℂ) (E := U') (x := ⟨ι u, hu'⟩)
      (y := μ)
    rw [← inner_toNormedCarrier]
    change inner ℂ (ι (ι.symm (g' : b.NormedCarrier))) (ι u) = l u
    rw [hg']
    rw [Submodule.coe_inner] at h
    change inner ℂ (g' : b.NormedCarrier) (ι u) = l u at h
    rw [h]

/-- The Riesz representative of a functional in a finite-dimensional subspace. -/
def rieszVector (U : Submodule ℂ V) (hU : FiniteDimensional ℂ U) (l : Module.Dual ℂ V) : V :=
  (b.exists_inner_eq U hU l).choose

theorem rieszVector_mem (U : Submodule ℂ V) (hU : FiniteDimensional ℂ U)
    (l : Module.Dual ℂ V) : b.rieszVector U hU l ∈ U :=
  (b.exists_inner_eq U hU l).choose_spec.1

theorem inner_rieszVector (U : Submodule ℂ V) (hU : FiniteDimensional ℂ U)
    (l : Module.Dual ℂ V) {u : V} (hu : u ∈ U) : b.inner (b.rieszVector U hU l) u = l u :=
  (b.exists_inner_eq U hU l).choose_spec.2 u hu

theorem eq_rieszVector (U : Submodule ℂ V) (hU : FiniteDimensional ℂ U)
    (l : Module.Dual ℂ V) {g : V} (hg : g ∈ U) (h : ∀ u ∈ U, b.inner g u = l u) :
    g = b.rieszVector U hU l :=
  b.eq_of_inner_eq hg (b.rieszVector_mem U hU l) fun u hu =>
    (h u hu).trans (b.inner_rieszVector U hU l hu).symm

theorem rieszVector_add (U : Submodule ℂ V) (hU : FiniteDimensional ℂ U)
    (l l' : Module.Dual ℂ V) :
    b.rieszVector U hU (l + l') = b.rieszVector U hU l + b.rieszVector U hU l' := by
  symm
  refine b.eq_rieszVector U hU _
    (U.add_mem (b.rieszVector_mem U hU l) (b.rieszVector_mem U hU l')) fun u hu => ?_
  rw [b.inner_add_left', b.inner_rieszVector U hU l hu, b.inner_rieszVector U hU l' hu]
  rfl

theorem rieszVector_smul (U : Submodule ℂ V) (hU : FiniteDimensional ℂ U) (c : ℂ)
    (l : Module.Dual ℂ V) :
    b.rieszVector U hU (c • l) = starRingEnd ℂ c • b.rieszVector U hU l := by
  symm
  refine b.eq_rieszVector U hU _ (U.smul_mem _ (b.rieszVector_mem U hU l)) fun u hu => ?_
  rw [b.inner_smul_left', b.inner_rieszVector U hU l hu, Complex.conj_conj]
  rfl

/-- The conjugate-linear Riesz map of a finite-dimensional subspace. -/
def rieszMap (U : Submodule ℂ V) (hU : FiniteDimensional ℂ U) :
    Module.Dual ℂ V →ₛₗ[starRingEnd ℂ] V where
  toFun := b.rieszVector U hU
  map_add' := b.rieszVector_add U hU
  map_smul' := b.rieszVector_smul U hU

theorem rieszMap_apply (U : Submodule ℂ V) (hU : FiniteDimensional ℂ U)
    (l : Module.Dual ℂ V) : b.rieszMap U hU l = b.rieszVector U hU l :=
  rfl

/-- On a subspace stable under an operator group preserving the form, the Riesz map
intertwines the dual action with the action. -/
theorem rieszVector_dual {κ : Representation ℂ K V}
    (hκ : ∀ k v w, b.inner (κ k v) (κ k w) = b.inner v w)
    (U : Submodule ℂ V) (hU : FiniteDimensional ℂ U) (hUκ : ∀ k, ∀ u ∈ U, κ k u ∈ U)
    (k : K) (l : Module.Dual ℂ V) :
    b.rieszVector U hU (κ.dual k l) = κ k (b.rieszVector U hU l) := by
  symm
  refine b.eq_rieszVector U hU _ (hUκ k _ (b.rieszVector_mem U hU l)) fun u hu => ?_
  have h₁ := hκ k⁻¹ (κ k (b.rieszVector U hU l)) u
  rw [Representation.inv_self_apply] at h₁
  rw [← h₁, b.inner_rieszVector U hU l (hUκ k⁻¹ u hu)]
  rfl

end Riesz

section ConjugatePairing

variable {G : Type uG} [Group G] {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type u} [AddCommGroup W] [Module ℂ W] {ρ : Representation ℂ G V}
  (b : InvariantPositiveForm ρ) (c : V ≃ₛₗ[starRingEnd ℂ] W)

/-- The bilinear pairing `B y x = ⟪c⁻¹ x, y⟫` of a positive form with a conjugate-linear
bijection. -/
def conjPairing : V →ₗ[ℂ] W →ₗ[ℂ] ℂ :=
  LinearMap.mk₂ ℂ (fun y x => b.inner (c.symm x) y)
    (fun _ _ _ => b.inner_add_right' _ _ _)
    (fun _ _ _ => b.inner_smul_right' _ _ _)
    (fun y x₁ x₂ => by
      simp only [map_add]
      exact b.inner_add_left' _ _ _)
    (fun a y x => by
      simp only [LinearEquiv.map_smulₛₗ]
      rw [b.inner_smul_left', Complex.conj_conj]
      rfl)

@[simp] theorem conjPairing_apply (y : V) (x : W) :
    b.conjPairing c y x = b.inner (c.symm x) y :=
  rfl

/-- Commutation of an equivalence with operators transfers to its inverse. -/
theorem symm_comm {A : V → V} {A' : W → W} (h : ∀ f, A' (c f) = c (A f)) (x : W) :
    c.symm (A' x) = A (c.symm x) := by
  rw [← c.apply_symm_apply x, h, c.symm_apply_apply, c.symm_apply_apply]

/-- Invariance of the pairing under operators preserving the form and commuting with `c`. -/
theorem conjPairing_invariant {H : Type uK} [Group H] {α : Representation ℂ H V}
    {β : Representation ℂ H W} (hα : ∀ h v w, b.inner (α h v) (α h w) = b.inner v w)
    (hc : ∀ h f, β h (c f) = c (α h f)) (h : H) (y : V) (x : W) :
    b.conjPairing c (α h y) (β h x) = b.conjPairing c y x := by
  rw [conjPairing_apply, conjPairing_apply, symm_comm c (hc h)]
  exact hα h _ _

/-- Infinitesimal invariance of the pairing under skew operators commuting with `c`. -/
theorem conjPairing_skew {D : V → V} {D' : W → W}
    (hD : ∀ v w, b.inner (D v) w + b.inner v (D w) = 0) (hc : ∀ f, D' (c f) = c (D f))
    (y : V) (x : W) : b.conjPairing c (D y) x + b.conjPairing c y (D' x) = 0 := by
  rw [conjPairing_apply, conjPairing_apply, symm_comm c hc, add_comm]
  exact hD _ _

theorem conjPairing_flip_injective : Function.Injective (b.conjPairing c).flip := by
  intro x₁ x₂ h
  apply c.symm.injective
  exact b.eq_of_inner_eq (U := ⊤) trivial trivial fun u _ => LinearMap.congr_fun h u

/-- The partial map intertwines an invariant action with the dual action. -/
theorem conjPairing_flip_dual {H : Type uK} [Group H] {α : Representation ℂ H V}
    {β : Representation ℂ H W} (hα : ∀ h v w, b.inner (α h v) (α h w) = b.inner v w)
    (hc : ∀ h f, β h (c f) = c (α h f)) (h : H) (x : W) :
    (b.conjPairing c).flip (β h x) = α.dual h ((b.conjPairing c).flip x) := by
  ext y
  have h₁ := b.conjPairing_invariant c hα hc h⁻¹ y (β h x)
  rw [Representation.inv_self_apply] at h₁
  rw [Representation.dual_apply, LinearMap.flip_apply, ← h₁]
  rfl

/-- The partial map as an intertwiner into the dual. -/
def conjPairingIntertwining {H : Type uK} [Group H] {α : Representation ℂ H V}
    {β : Representation ℂ H W} (hα : ∀ h v w, b.inner (α h v) (α h w) = b.inner v w)
    (hc : ∀ h f, β h (c f) = c (α h f)) : β.IntertwiningMap α.dual where
  toLinearMap := (b.conjPairing c).flip
  isIntertwining' h := LinearMap.ext fun x => b.conjPairing_flip_dual c hα hc h x

end ConjugatePairing

section Contragredient

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {K : Type uK} [Group K] {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {ρ : Representation ℂ G V} {κ : Representation ℂ K V} (b : InvariantPositiveForm ρ)

/-- Under joint admissibility, every smooth and compact-finite linear functional is the
inner product with a vector. -/
theorem exists_inner_eq_of_contragredient
    (hb : ∀ k v w, b.inner (κ k v) (κ k w) = b.inner v w)
    (hcomm : ∀ d k v, ρ d (κ k v) = κ k (ρ d v))
    (hsmooth : IsSmooth ρ) (hfin : ∀ v, IsFiniteVector κ v)
    (hcpt : ∀ L : OpenSubgroup G, ∃ L₀ : OpenSubgroup G, L₀ ≤ L ∧ IsCompact (L₀ : Set G))
    (hA : IsJointlyAdmissible ρ κ) {l : Module.Dual ℂ V}
    (hl : IsSmoothVector ρ.dual l) (hl' : IsFiniteVector κ.dual l) :
    ∃ g : V, ∀ y, b.inner g y = l y := by
  classical
  obtain ⟨L, hL⟩ := hl
  obtain ⟨L₀, hL₀L, hL₀c⟩ := hcpt L
  set L0 : Subgroup G := L₀.toSubgroup with hL0
  -- the functional is invariant under the compact open subgroup
  have hlinv : ∀ d ∈ L0, ∀ y, l (ρ d y) = l y := by
    intro d hd y
    have h := (mem_fixedVectors_iff'.mp hL) d⁻¹ (L.inv_mem (hL₀L hd))
    have h' : l (ρ d⁻¹⁻¹ y) = l y := LinearMap.congr_fun h y
    rwa [inv_inv] at h'
  -- the compact orbit of the functional and conjugate coordinates on it
  set Λ : Submodule ℂ (Module.Dual ℂ V) := orbitSpan κ.dual l with hΛ
  have hΛfin : FiniteDimensional ℂ Λ := hl'
  set m := Module.finrank ℂ Λ
  let e := Module.finBasis ℂ Λ
  let γ : Λ ≃ₛₗ[starRingEnd ℂ] (Fin m → ℂ) :=
    e.equivFun.trans (starLinearEquiv ℂ (A := Fin m → ℂ))
  let σ : Representation ℂ K Λ := (orbitSubrepresentation κ.dual l).toRepresentation
  let ρ' : Representation ℂ K (Fin m → ℂ) := conjugateTransport γ σ
  -- every Riesz map on an admissible subspace is a multiplicity map
  have key : ∀ (U : Submodule ℂ V) (hU : FiniteDimensional ℂ U),
      (∀ k, ∀ u ∈ U, κ k u ∈ U) → U ≤ fixedVectors ρ L0 →
      ∃ φ ∈ jointMultiplicitySpace ρ κ L0 ρ',
        ∀ μ : Λ, φ (γ μ) = b.rieszVector U hU (μ : Module.Dual ℂ V) := by
    intro U hU hUκ hUL
    let φ : (Fin m → ℂ) →ₗ[ℂ] V :=
      ((b.rieszMap U hU).comp Λ.subtype).comp γ.symm.toLinearMap
    refine ⟨φ, ⟨fun v => hUL (b.rieszVector_mem U hU _), fun k v => ?_⟩, fun μ => ?_⟩
    · change b.rieszVector U hU ((γ.symm (γ (σ k (γ.symm v))) : Λ) : Module.Dual ℂ V) =
        κ k (b.rieszVector U hU ((γ.symm v : Λ) : Module.Dual ℂ V))
      rw [γ.symm_apply_apply]
      exact b.rieszVector_dual hb U hU hUκ k _
    · change b.rieszVector U hU ((γ.symm (γ μ) : Λ) : Module.Dual ℂ V) = _
      rw [γ.symm_apply_apply]
  -- the span of all multiplicity images
  set M := jointMultiplicitySpace ρ κ L0 ρ' with hM
  have hMfin : FiniteDimensional ℂ M := hA L₀ m ρ'
  let bf := Pi.basisFun ℂ (Fin m)
  set W : Submodule ℂ V := ⨆ i : Fin m, M.map (LinearMap.applyₗ (bf i)) with hWdef
  have hW : FiniteDimensional ℂ W := by
    have : ∀ i : Fin m, FiniteDimensional ℂ (M.map (LinearMap.applyₗ (bf i))) :=
      fun i => Module.Finite.map M _
    exact Submodule.finiteDimensional_iSup _
  have hMW : ∀ φ ∈ M, ∀ v, φ v ∈ W := by
    intro φ hφ v
    rw [← bf.sum_repr v, map_sum]
    refine W.sum_mem fun i _ => ?_
    rw [map_smul]
    refine W.smul_mem _ ?_
    exact Submodule.mem_iSup_of_mem i (Submodule.mem_map_of_mem (f := LinearMap.applyₗ (bf i)) hφ)
  have hWfix : W ≤ fixedVectors ρ L0 := by
    refine iSup_le fun i => ?_
    rintro _ ⟨φ, hφ, rfl⟩
    exact hφ.1 _
  have hWκ : ∀ k, ∀ w ∈ W, κ k w ∈ W := by
    intro k w hw
    refine Submodule.iSup_induction _ (motive := fun w => κ k w ∈ W) hw ?_ ?_ ?_
    · rintro i _ ⟨φ, hφ, rfl⟩
      change κ k (φ (bf i)) ∈ W
      rw [← hφ.2]
      exact hMW φ hφ _
    · simp
    · intro x y hx hy
      rw [map_add]
      exact W.add_mem hx hy
  refine ⟨b.rieszVector W hW l, fun y => ?_⟩
  -- the finite orbit of `y` under the compact open subgroup
  obtain ⟨Ly, hLy⟩ := hsmooth y
  have : CompactSpace L0 := isCompact_iff_compactSpace.mp hL₀c
  let H : Subgroup L0 := Ly.toSubgroup.subgroupOf L0
  have : Finite (L0 ⧸ H) :=
    Subgroup.quotient_finite_of_isOpen H (Subgroup.subgroupOf_isOpen _ _ Ly.isOpen)
  let O : L0 ⧸ H → V := fun q => ρ ((Quotient.out q : L0) : G) y
  have hO : ∀ d : L0, ρ (d : G) y = O (d : L0 ⧸ H) := by
    intro d
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul H d
    have hy : ρ ((h : L0) : G) y = y :=
      (mem_fixedVectors_iff'.mp hLy) _ (Subgroup.mem_subgroupOf.mp h.2)
    simp only [O, hh, Subgroup.coe_mul, map_mul, Module.End.mul_apply, hy]
  let Uy : Submodule ℂ V :=
    Submodule.span ℂ (Set.range fun p : K × L0 => κ p.1 (ρ (p.2 : G) y))
  have hUy : FiniteDimensional ℂ Uy := by
    have : ∀ q : L0 ⧸ H, FiniteDimensional ℂ (orbitSpan κ (O q)) := fun q => hfin (O q)
    refine Submodule.finiteDimensional_of_le (S₂ := ⨆ q : L0 ⧸ H, orbitSpan κ (O q)) ?_
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨⟨k, d⟩, rfl⟩
    change κ k (ρ (d : G) y) ∈ _
    rw [hO d]
    exact Submodule.mem_iSup_of_mem _ (action_mem_orbitSpan κ k _)
  have hUyκ : ∀ k, ∀ u ∈ Uy, κ k u ∈ Uy := by
    intro k u hu
    have hle : Uy ≤ Uy.comap (κ k) := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨⟨k', d⟩, rfl⟩
      change κ k (κ k' (ρ (d : G) y)) ∈ Uy
      rw [← Module.End.mul_apply, ← map_mul]
      exact Submodule.subset_span ⟨(k * k', d), rfl⟩
    exact hle hu
  have hUyρ : ∀ d ∈ L0, ∀ u ∈ Uy, ρ d u ∈ Uy := by
    intro d hd u hu
    have hle : Uy ≤ Uy.comap (ρ d) := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨⟨k', d'⟩, rfl⟩
      change ρ d (κ k' (ρ (d' : G) y)) ∈ Uy
      rw [hcomm, ← Module.End.mul_apply (ρ d), ← map_mul]
      exact Submodule.subset_span ⟨(k', ⟨d, hd⟩ * d'), rfl⟩
    exact hle hu
  have hyUy : y ∈ Uy :=
    Submodule.subset_span ⟨((1 : K), (1 : L0)), by simp⟩
  -- a finite-dimensional subspace stable under both groups containing `y` and `W`
  let U : Submodule ℂ V := Uy ⊔ W
  have hU : FiniteDimensional ℂ U := Submodule.finiteDimensional_sup _ _
  have hUκ : ∀ k, ∀ u ∈ U, κ k u ∈ U := by
    intro k u hu
    obtain ⟨a, ha, w, hw, rfl⟩ := Submodule.mem_sup.mp hu
    rw [map_add]
    exact Submodule.add_mem_sup (hUyκ k a ha) (hWκ k w hw)
  have hUρ : ∀ d ∈ L0, ∀ u ∈ U, ρ d u ∈ U := by
    intro d hd u hu
    obtain ⟨a, ha, w, hw, rfl⟩ := Submodule.mem_sup.mp hu
    rw [map_add, (mem_fixedVectors_iff'.mp (hWfix hw)) d hd]
    exact Submodule.add_mem_sup (hUyρ d hd a ha) hw
  set g' := b.rieszVector U hU l with hg'def
  -- the Riesz vector in `U` is fixed by the compact open subgroup
  have hg'fix : ∀ d ∈ L0, ρ d g' = g' := by
    intro d hd
    refine b.eq_rieszVector U hU l (hUρ d hd _ (b.rieszVector_mem U hU l)) fun u hu => ?_
    have h₁ := b.invariant d g' (ρ d⁻¹ u)
    rw [Representation.self_inv_apply] at h₁
    rw [h₁, b.inner_rieszVector U hU l (hUρ d⁻¹ (L0.inv_mem hd) u hu),
      hlinv d⁻¹ (L0.inv_mem hd)]
  -- hence it is the Riesz vector of the fixed part, which lies in `W`
  let U'' : Submodule ℂ V := U ⊓ fixedVectors ρ L0
  have hU'' : FiniteDimensional ℂ U'' := Submodule.finiteDimensional_inf_left _ _
  have hU''κ : ∀ k, ∀ u ∈ U'', κ k u ∈ U'' := by
    rintro k u ⟨hu, hu'⟩
    refine ⟨hUκ k u hu, mem_fixedVectors_iff'.mpr fun d hd => ?_⟩
    rw [hcomm, (mem_fixedVectors_iff'.mp hu') d hd]
  have hg'U'' : g' ∈ U'' :=
    ⟨b.rieszVector_mem U hU l, mem_fixedVectors_iff'.mpr hg'fix⟩
  have hg'eq : g' = b.rieszVector U'' hU'' l :=
    b.eq_rieszVector U'' hU'' l hg'U'' fun u hu => b.inner_rieszVector U hU l hu.1
  obtain ⟨φ, hφM, hφ⟩ := key U'' hU'' hU''κ inf_le_right
  have hlΛ : l ∈ Λ := self_mem_orbitSpan κ.dual l
  have hg'W : g' ∈ W := by
    have h := hφ ⟨l, hlΛ⟩
    rw [hg'eq]
    change b.rieszVector U'' hU'' l ∈ W
    rw [← show φ (γ ⟨l, hlΛ⟩) = b.rieszVector U'' hU'' l from h]
    exact hMW φ hφM _
  have hgg' : g' = b.rieszVector W hW l :=
    b.eq_rieszVector W hW l hg'W fun u hu =>
      b.inner_rieszVector U hU l (Submodule.mem_sup_right hu)
  rw [← hgg']
  exact b.inner_rieszVector U hU l (Submodule.mem_sup_left hyUy)

end Contragredient

end InvariantPositiveForm

namespace Automorphic

open Global

variable {F : Type u} [Field F] [NumberField F] {n : ℕ}

local instance criterionRationalAddCommGroup :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance criterionContinuousAddCommGroup :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance criterionSmoothAddCommGroup :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance criterionFormsAddCommGroup :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance criterionStableAddCommGroup :
    AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _

namespace OperatorRealization

local instance criterionSpaceAddCommGroup (S : OperatorRealization F n) :
    AddCommGroup S.Space :=
  Submodule.addCommGroup _

/-- Joint admissibility of an actual realization for its finite adelic action and the
action of the standard compact subgroup at infinity. -/
def IsJointlyAdmissible (S : OperatorRealization F n) : Prop :=
  Langlands.IsJointlyAdmissible S.finiteRepresentation S.compactRepresentation

/-- Every open subgroup of the finite adelic group contains a compact open subgroup. -/
theorem exists_compact_openSubgroup_le (L : OpenSubgroup (FiniteAdelicGL F n)) :
    ∃ L₀ : OpenSubgroup (FiniteAdelicGL F n), L₀ ≤ L ∧
      IsCompact (L₀ : Set (FiniteAdelicGL F n)) := by
  refine ⟨L ⊓ FiniteAdelicGL.standardIntegral F n, inf_le_left, ?_⟩
  exact (FiniteAdelicGL.isCompact_standardIntegral F n).of_isClosed_subset
    (OpenSubgroup.isClosed _) inf_le_right

variable {S T : OperatorRealization F n}

/-- A unitary form on a jointly admissible realization `S` makes every realization `T`
identified with `S` by a conjugate-linear bijection commuting with the finite, compact and
real Lie operators a contragredient of `S`, through the pairing `B y x = ⟪c⁻¹ x, y⟫`. -/
theorem isContragredientOf_of_unitaryForm (b : S.UnitaryForm) (hA : S.IsJointlyAdmissible)
    (c : S.Space ≃ₛₗ[starRingEnd ℂ] T.Space)
    (hfin : ∀ (d : FiniteAdelicGL F n) (f : S.Space),
      T.finiteRepresentation d (c f) = c (S.finiteRepresentation d f))
    (hcpt : ∀ (k : standardInfiniteCompact F n) (f : S.Space),
      T.compactRepresentation k (c f) = c (S.compactRepresentation k f))
    (hlie : ∀ (X : ArchimedeanGL.RealLieAlgebra F n) (f : S.Space),
      T.lieAction X (c f) = c (S.lieAction X f)) :
    T.IsContragredientOf S := by
  let b₀ := b.finiteForm
  let Mfin := b₀.conjPairingIntertwining c b₀.invariant hfin
  let Mcpt := b₀.conjPairingIntertwining c b.compact_invariant hcpt
  refine ⟨b₀.conjPairing c, ⟨b₀.conjPairing_invariant c b₀.invariant hfin,
    b₀.conjPairing_invariant c b.compact_invariant hcpt,
    fun X => b₀.conjPairing_skew c (b.real_skew X) (hlie X)⟩,
    fun x => ⟨Langlands.isSmoothVector_map Mfin (T.finiteRepresentation_isSmooth x),
      (T.compactRepresentation_isFiniteVector x).map Mcpt⟩,
    b₀.conjPairing_flip_injective c, fun l hl => ?_⟩
  obtain ⟨g, hg⟩ := b₀.exists_inner_eq_of_contragredient b.compact_invariant
    S.finiteRepresentation_compactRepresentation S.finiteRepresentation_isSmooth
    S.compactRepresentation_isFiniteVector exists_compact_openSubgroup_le hA hl.1 hl.2
  exact ⟨c g, LinearMap.ext fun y => (b₀.conjPairing_apply c y (c g)).trans
    ((congrArg (fun v => b₀.inner v y) (c.symm_apply_apply g)).trans (hg y))⟩

end OperatorRealization

end Automorphic

end Langlands
