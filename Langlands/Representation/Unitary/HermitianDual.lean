import Langlands.Representation.Unitary.Basic
import Langlands.Representation.Smooth.Contragredient.CompactDualityProof
import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# Hermitian identification of admissible representations with their smooth duals

An invariant positive form `b` sends a vector `v` to the functional
`w ↦ b(v, w)`. This map is conjugate-linear, injective and equivariant for the
smooth contragredient. When compact open subgroups are cofinal and the
representation is admissible, it is also surjective onto the smooth dual.
No norm, topology, completion or finite-dimensionality is imposed on the carrier;
the finite-dimensional Riesz theorem is used only on compact-open fixed spaces.
-/

noncomputable section

namespace Langlands

universe uG uV uU

/-- Finite-dimensional Riesz representation for an algebraic inner-product core:
every linear functional is `x ↦ c(u, x)` for some vector `u`. -/
theorem InnerProductSpace.Core.exists_inner_eq_of_finiteDimensional
    {U : Type uU} [AddCommGroup U] [Module ℂ U] [FiniteDimensional ℂ U]
    (c : InnerProductSpace.Core ℂ U) (φ : Module.Dual ℂ U) :
    ∃ u : U, ∀ x : U, c.inner u x = φ x := by
  let _ : NormedAddCommGroup U :=
    @InnerProductSpace.Core.toNormedAddCommGroup ℂ U _ _ _ c
  let _ : InnerProductSpace ℂ U := InnerProductSpace.ofCore c.toCore
  have : CompleteSpace U := FiniteDimensional.complete ℂ U
  refine ⟨(InnerProductSpace.toDual ℂ U).symm (LinearMap.toContinuousLinearMap φ),
    fun x => ?_⟩
  exact InnerProductSpace.toDual_symm_apply

namespace InvariantPositiveForm

variable {G : Type uG} [Group G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}

/-- The algebraic functional `w ↦ b(v, w)`; it is linear because the form is
linear in its second variable. -/
def rightFunctional (b : InvariantPositiveForm ρ) (v : V) : Module.Dual ℂ V where
  toFun w := b.inner v w
  map_add' w x := by
    let := b.toInnerProductCore
    exact InnerProductSpace.Core.inner_add_right v w x
  map_smul' c w := by
    let := b.toInnerProductCore
    exact InnerProductSpace.Core.inner_smul_right v w

@[simp]
theorem rightFunctional_apply (b : InvariantPositiveForm ρ) (v w : V) :
    b.rightFunctional v w = b.inner v w := rfl

theorem rightFunctional_add (b : InvariantPositiveForm ρ) (v v' : V) :
    b.rightFunctional (v + v') = b.rightFunctional v + b.rightFunctional v' :=
  LinearMap.ext fun w => b.add_left v v' w

theorem rightFunctional_smul (b : InvariantPositiveForm ρ) (c : ℂ) (v : V) :
    b.rightFunctional (c • v) = starRingEnd ℂ c • b.rightFunctional v :=
  LinearMap.ext fun w => b.smul_left v w c

/-- The algebraic dual action `ℓ ↦ ℓ ∘ ρ(g⁻¹)` moves `b(v, -)` to `b(ρ(g)v, -)`. -/
theorem dual_rightFunctional (b : InvariantPositiveForm ρ) (g : G) (v : V) :
    ρ.dual g (b.rightFunctional v) = b.rightFunctional (ρ g v) := by
  apply LinearMap.ext
  intro w
  change b.inner v (ρ g⁻¹ w) = b.inner (ρ g v) w
  rw [← b.invariant g v (ρ g⁻¹ w), Representation.self_inv_apply]

variable [TopologicalSpace G] [IsTopologicalGroup G]

omit [IsTopologicalGroup G] in
/-- A functional `b(v, -)` with `v` smooth is smooth: the stabilizer of `v`
fixes it. -/
theorem rightFunctional_mem_smoothVectors (b : InvariantPositiveForm ρ)
    (hρ : IsSmooth ρ) (v : V) : b.rightFunctional v ∈ smoothVectors ρ.dual := by
  obtain ⟨K, hK⟩ := hρ v
  refine ⟨K, fun k => ?_⟩
  change ρ.dual k.val (b.rightFunctional v) = b.rightFunctional v
  rw [dual_rightFunctional]
  exact congrArg b.rightFunctional (hK k)

/-- The conjugate-linear map `v ↦ b(v, -)` into the smooth dual. -/
def toSmoothDual (b : InvariantPositiveForm ρ) (hρ : IsSmooth ρ) :
    V →ₗ⋆[ℂ] SmoothDual ρ where
  toFun v := ⟨b.rightFunctional v, b.rightFunctional_mem_smoothVectors hρ v⟩
  map_add' v v' := Subtype.ext (b.rightFunctional_add v v')
  map_smul' c v := Subtype.ext (b.rightFunctional_smul c v)

@[simp]
theorem smoothDualPairing_toSmoothDual (b : InvariantPositiveForm ρ)
    (hρ : IsSmooth ρ) (v w : V) :
    smoothDualPairing ρ (b.toSmoothDual hρ v) w = b.inner v w := rfl

/-- The map `v ↦ b(v, -)` intertwines the action with the smooth contragredient. -/
theorem toSmoothDual_apply_action (b : InvariantPositiveForm ρ) (hρ : IsSmooth ρ)
    (g : G) (v : V) :
    b.toSmoothDual hρ (ρ g v) = smoothContragredient ρ g (b.toSmoothDual hρ v) :=
  Subtype.ext (b.dual_rightFunctional g v).symm

/-- Positivity makes `v ↦ b(v, -)` injective. -/
theorem toSmoothDual_injective (b : InvariantPositiveForm ρ) (hρ : IsSmooth ρ) :
    Function.Injective (b.toSmoothDual hρ) := by
  refine (injective_iff_map_eq_zero (b.toSmoothDual hρ)).2 fun v hv => ?_
  apply b.definite v
  have h := congrArg (fun ℓ : SmoothDual ρ => smoothDualPairing ρ ℓ v) hv
  simpa using h

/-- With compact open subgroups cofinal, every smooth functional on an
admissible representation is `b(v, -)` for some vector `v`. -/
theorem toSmoothDual_surjective (b : InvariantPositiveForm ρ)
    (hcofinal : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G,
      IsCompact (L : Set G) ∧ L ≤ K)
    (hρ : IsAdmissible ρ) :
    Function.Surjective (b.toSmoothDual hρ.1) := by
  intro ℓ
  obtain ⟨H, hH⟩ := ℓ.property
  obtain ⟨K, hKc, hKH⟩ := hcofinal H
  let U := fixedVectors ρ K.toSubgroup
  let : FiniteDimensional ℂ U := hρ.2 K
  let cU : InnerProductSpace.Core ℂ U :=
    { inner := fun x y => b.inner x.val y.val
      conj_inner_symm := fun x y => b.conj_inner_symm x.val y.val
      re_inner_nonneg := fun x => b.re_inner_nonneg x.val
      add_left := fun x y z => b.add_left x.val y.val z.val
      smul_left := fun x y r => b.smul_left x.val y.val r
      definite := fun x hx => Subtype.ext (b.definite x.val hx) }
  obtain ⟨u, hu⟩ := InnerProductSpace.Core.exists_inner_eq_of_finiteDimensional cU
    (ℓ.val.comp U.subtype)
  have hEu : b.toSmoothDual hρ.1 u.val ∈
      fixedVectors (smoothContragredient ρ) K.toSubgroup := by
    intro k
    change smoothContragredient ρ k.val (b.toSmoothDual hρ.1 u.val) =
      b.toSmoothDual hρ.1 u.val
    rw [← toSmoothDual_apply_action]
    exact congrArg (b.toSmoothDual hρ.1) (u.property k)
  have hℓ : ℓ ∈ fixedVectors (smoothContragredient ρ) K.toSubgroup :=
    fun k => Subtype.ext (hH ⟨k.val, hKH k.property⟩)
  refine ⟨u.val, congrArg Subtype.val
    ((smoothDualFixedRestriction_bijective ρ hρ.1 K hKc).1
      (a₁ := ⟨_, hEu⟩) (a₂ := ⟨ℓ, hℓ⟩) ?_)⟩
  apply LinearMap.ext
  intro x
  exact hu x

/-- The equivariant conjugate-linear identification `v ↦ b(v, -)` of an
admissible representation with its smooth dual. -/
def smoothDualEquiv (b : InvariantPositiveForm ρ)
    (hcofinal : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G,
      IsCompact (L : Set G) ∧ L ≤ K)
    (hρ : IsAdmissible ρ) : V ≃ₗ⋆[ℂ] SmoothDual ρ :=
  LinearEquiv.ofBijective (b.toSmoothDual hρ.1)
    ⟨b.toSmoothDual_injective hρ.1, b.toSmoothDual_surjective hcofinal hρ⟩

@[simp]
theorem smoothDualEquiv_apply (b : InvariantPositiveForm ρ)
    (hcofinal : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G,
      IsCompact (L : Set G) ∧ L ≤ K)
    (hρ : IsAdmissible ρ) (v : V) :
    b.smoothDualEquiv hcofinal hρ v = b.toSmoothDual hρ.1 v := rfl

end InvariantPositiveForm

end Langlands
