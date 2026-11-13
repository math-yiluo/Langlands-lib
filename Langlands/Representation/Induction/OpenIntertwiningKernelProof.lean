import Langlands.Representation.Induction.OpenIntertwiningStatement

/-! # Intertwining kernels of compact induction from an open subgroup: proof

Proof of `CompactInductionKernelStatement` (Vignéras 1996, I.8.5, for `K = H` open). The
published Frobenius reciprocity `compactInductionHomEquiv` identifies a map
`T : c-Ind A ⟶ c-Ind B` with the `H`-map `v ↦ T (i_v)` from `A` to the restriction of
`c-Ind B`. Such `H`-maps `φ` correspond to intertwining kernels through
`Φ g v = (φ v) (g)`:

* `intertwinerKernel H φ` is the kernel of an `H`-map `φ`, and
  `isIntertwiningKernel_intertwinerKernel` proves it is an intertwining kernel;
* `kernelIntertwiner H hH hσ Φ hΦ` is the `H`-map `v ↦ (g ↦ Φ g v)` of an intertwining
  kernel `Φ`, built from `kernelFunction`;
* `intertwinerKernel_eq_iff` says that `kernelIntertwiner` is the only `H`-map with kernel
  `Φ`.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace Langlands.Induction

universe uR uG uV uW

section Kernel

variable {R : Type uR} {G : Type uG} {V : Type uV} {W : Type uW}
variable [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
variable (H : Subgroup G) {σ : Representation R H V} {τ : Representation R H W}

/-- Evaluation at a point `g` of `G`, as an `R`-linear map on compactly induced functions. -/
def evalLinearMap (τ : Representation R H W) (g : G) : CompactFunctions H τ →ₗ[R] W where
  toFun f := eval H τ f.1 g
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem evalLinearMap_apply (τ : Representation R H W) (g : G) (f : CompactFunctions H τ) :
    evalLinearMap H τ g f = eval H τ f.1 g :=
  rfl

/-- The kernel `Φ g v = (φ v) (g)` of an `H`-map `φ` from `σ` to the restriction to `H` of
the compact induction of `τ`. -/
def intertwinerKernel (φ : σ.IntertwiningMap ((compactInduced H τ).comp H.subtype)) (g : G) :
    V →ₗ[R] W :=
  evalLinearMap H τ g ∘ₗ φ.toLinearMap

theorem intertwinerKernel_apply (φ : σ.IntertwiningMap ((compactInduced H τ).comp H.subtype))
    (g : G) (v : V) : intertwinerKernel H φ g v = eval H τ (φ v).1 g :=
  rfl

/-- The kernel of an `H`-map into the restricted compact induction is an intertwining kernel:
left covariance of the values `φ v` and `H`-equivariance of `φ` give the covariance, and the
projected support of `φ v` is finite since `H` is open. -/
theorem isIntertwiningKernel_intertwinerKernel (hH : IsOpen (H : Set G))
    (φ : σ.IntertwiningMap ((compactInduced H τ).comp H.subtype)) :
    IsIntertwiningKernel H σ τ (intertwinerKernel H φ) := by
  refine ⟨fun h h' g => LinearMap.ext fun v => ?_, fun v => quotientSupport_finite H τ hH (φ v)⟩
  rw [LinearMap.comp_apply, LinearMap.comp_apply, intertwinerKernel_apply,
    intertwinerKernel_apply, φ.isIntertwining, mul_assoc]
  exact (φ v).1.1.2 h (g * (h' : G))

variable (hH : IsOpen (H : Set G))

/-- For an intertwining kernel `Φ` and a vector `v` of a smooth `σ`, the compactly induced
function `g ↦ Φ g v`. It is right invariant under the image in `G` of an open subgroup of `H`
fixing `v`, and its projected support is finite, hence compact. -/
def kernelFunction (hσ : IsSmooth σ) (Φ : G → V →ₗ[R] W) (hΦ : IsIntertwiningKernel H σ τ Φ)
    (v : V) : CompactFunctions H τ :=
  compactFunctionOf H τ (fun g => Φ g v)
    (by
      intro p x
      have h := LinearMap.congr_fun (hΦ.1 p 1 x) v
      simp only [OneMemClass.coe_one, mul_one, map_one, LinearMap.comp_apply,
        Module.End.one_apply] at h
      exact h)
    (openSubgroupMap H hH (Classical.choose (hσ v)))
    (by
      intro k x
      obtain ⟨k₀, hk₀, hk⟩ := Subgroup.mem_map.mp k.2
      have hfix : σ k₀ v = v := Classical.choose_spec (hσ v) ⟨k₀, hk₀⟩
      have h := LinearMap.congr_fun (hΦ.1 1 k₀ x) v
      simp only [OneMemClass.coe_one, one_mul, map_one, LinearMap.comp_apply,
        Module.End.one_apply, hfix] at h
      rw [← hk]
      exact h)
    (hΦ.2 v).isCompact

theorem eval_kernelFunction (hσ : IsSmooth σ) (Φ : G → V →ₗ[R] W)
    (hΦ : IsIntertwiningKernel H σ τ Φ) (v : V) (g : G) :
    eval H τ (kernelFunction H hH hσ Φ hΦ v).1 g = Φ g v :=
  rfl

/-- The `H`-map `v ↦ (g ↦ Φ g v)` from `σ` to the restriction to `H` of the compact induction
of `τ`, for an intertwining kernel `Φ`. -/
def kernelIntertwiner (hσ : IsSmooth σ) (Φ : G → V →ₗ[R] W)
    (hΦ : IsIntertwiningKernel H σ τ Φ) :
    σ.IntertwiningMap ((compactInduced H τ).comp H.subtype) where
  toFun := kernelFunction H hH hσ Φ hΦ
  map_add' v w := compactFunctions_ext H τ fun x => map_add (Φ x) v w
  map_smul' c v := compactFunctions_ext H τ fun x => map_smul (Φ x) c v
  isIntertwining' h := LinearMap.ext fun v => compactFunctions_ext H τ fun x => by
    have h' := LinearMap.congr_fun (hΦ.1 1 h x) v
    simp only [OneMemClass.coe_one, one_mul, map_one, LinearMap.comp_apply,
      Module.End.one_apply] at h'
    exact h'.symm

theorem kernelIntertwiner_apply (hσ : IsSmooth σ) (Φ : G → V →ₗ[R] W)
    (hΦ : IsIntertwiningKernel H σ τ Φ) (v : V) :
    kernelIntertwiner H hH hσ Φ hΦ v = kernelFunction H hH hσ Φ hΦ v :=
  rfl

/-- An `H`-map into the restricted compact induction has kernel `Φ` exactly when it is
`kernelIntertwiner H hH hσ Φ hΦ`. -/
theorem intertwinerKernel_eq_iff (hσ : IsSmooth σ) (Φ : G → V →ₗ[R] W)
    (hΦ : IsIntertwiningKernel H σ τ Φ)
    (φ : σ.IntertwiningMap ((compactInduced H τ).comp H.subtype)) :
    (∀ (g : G) (v : V), Φ g v = eval H τ (φ v).1 g) ↔ φ = kernelIntertwiner H hH hσ Φ hΦ := by
  constructor
  · intro hφ
    exact Representation.IntertwiningMap.ext (LinearMap.ext fun v =>
      compactFunctions_ext H τ fun g => (hφ g v).symm)
  · rintro rfl g v
    rfl

end Kernel

/-- **Vignéras I.8.5 for an open subgroup `K = H`.** Every map
`T : c-Ind A ⟶ c-Ind B` has the intertwining kernel `Φ g v = T (i_v) (g)`, and every
intertwining kernel arises in this way from exactly one map `T`. -/
theorem compactInductionKernel : CompactInductionKernelStatement.{uR, uG, uV} := by
  intro R _ G _ _ _ H hH A B
  let e := compactInductionHomEquiv.{uR, uG, uV} H hH A ((smoothCompactInduction R H).obj B)
  refine ⟨fun T => ⟨intertwinerKernel H (SmoothRep.hom (e T)),
    isIntertwiningKernel_intertwinerKernel H hH _, fun g v => rfl⟩, fun Φ hΦ => ?_⟩
  let φ := kernelIntertwiner H hH A.isSmooth Φ hΦ
  have key : ∀ T : (smoothCompactInduction R H).obj A ⟶ (smoothCompactInduction R H).obj B,
      (∀ (g : G) (v : A), Φ g v =
        eval H B.representation
          (SmoothRep.hom T (unitFunction H hH A.representation A.isSmooth v)).1 g) ↔
        e T = SmoothRep.ofHom φ := by
    intro T
    refine (intertwinerKernel_eq_iff H hH A.isSmooth Φ hΦ (SmoothRep.hom (e T))).trans ?_
    constructor
    · intro h
      exact congrArg SmoothRep.ofHom h
    · intro h
      exact congrArg SmoothRep.hom h
  refine ⟨e.symm (SmoothRep.ofHom φ), (key _).mpr (e.apply_symm_apply _), fun T hT => ?_⟩
  exact e.eq_symm_apply.mpr ((key T).mp hT)

end Langlands.Induction
