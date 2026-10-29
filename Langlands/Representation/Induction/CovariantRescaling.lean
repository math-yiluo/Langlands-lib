import Langlands.Representation.Induction.Definitions
import Langlands.Representation.Twist.RealPower
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Rescaling smooth induced functions by covariant scalars

A unit-valued function `c` on `G` with `c (q x) = χ q * c x` for `q ∈ P` and
right invariance under an open subgroup turns `P`-covariant functions for `σ`
into `P`-covariant functions for the twist of `σ` by `χ`. Conjugating smooth
induction from the twist by this linear equivalence gives a representation on
the untwisted function space.

For a height `G = P K` with `K` compact open and a positive character `N` of
`P` trivial on `P ∩ K`, the real powers of the height give a family `s ↦ π s`
on one function space. The member `π s` is equivalent to smooth induction of
`σ` twisted by `N ^ s`, agrees with untwisted right translation on `K`, has
matrix entries continuous in `s`, and pairs `π s` with `π (-s)` pointwise as
untwisted right translation does.
-/

noncomputable section

open scoped NNReal ComplexConjugate

namespace Langlands.Induction

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- A unit-valued function on `G`, left covariant under `P` by the character `χ`
and invariant under right translation by an open subgroup. -/
structure CovariantScalar (P : Subgroup G) (χ : P →* ℂˣ) where
  /-- The scalar function. -/
  toFun : G → ℂˣ
  /-- Left covariance under `P`. -/
  covariant : ∀ (q : P) (x : G), toFun ((q : G) * x) = χ q * toFun x
  /-- An open subgroup under which the function is right invariant. -/
  stabilizer : OpenSubgroup G
  /-- Right invariance under the stabilizer. -/
  invariant : ∀ (k : stabilizer) (x : G), toFun (x * (k : G)) = toFun x

variable {P : Subgroup G} {χ : P →* ℂˣ}

private def rescaleTo (c : CovariantScalar P χ) (σ : Representation ℂ P V)
    (f : SmoothFunctions P σ) : SmoothFunctions P (twist χ σ) := by
  let K := Classical.choose f.property
  have hK := Classical.choose_spec f.property
  refine smoothFunctionOf P _ (fun x => (c.toFun x : ℂ) • eval P σ f x) ?_
    (K ⊓ c.stabilizer) ?_
  · intro q x
    have hf : f.1.1 ((q : G) * x) = σ q (f.1.1 x) := f.1.property q x
    change (c.toFun ((q : G) * x) : ℂ) • f.1.1 ((q : G) * x) =
      (χ q : ℂ) • σ q ((c.toFun x : ℂ) • f.1.1 x)
    rw [hf, c.covariant]
    simp only [Units.val_mul, map_smul, mul_smul]
  · intro k x
    have hf := congrArg (fun F : EquivariantFunctions P σ => F.1 x)
      (hK ⟨(k : G), k.property.1⟩)
    change eval P σ f (x * (k : G)) = eval P σ f x at hf
    change (c.toFun (x * (k : G)) : ℂ) • eval P σ f (x * (k : G)) =
      (c.toFun x : ℂ) • eval P σ f x
    rw [hf, c.invariant ⟨(k : G), k.property.2⟩]

private def rescaleFrom (c : CovariantScalar P χ) (σ : Representation ℂ P V)
    (f : SmoothFunctions P (twist χ σ)) : SmoothFunctions P σ := by
  let K := Classical.choose f.property
  have hK := Classical.choose_spec f.property
  refine smoothFunctionOf P σ
    (fun x => ((c.toFun x)⁻¹ : ℂˣ) • eval P (twist χ σ) f x) ?_ (K ⊓ c.stabilizer) ?_
  · intro q x
    have hf := f.1.property q x
    change f.1.1 ((q : G) * x) = (χ q : ℂ) • σ q (f.1.1 x) at hf
    change ((c.toFun ((q : G) * x))⁻¹ : ℂˣ) • f.1.1 ((q : G) * x) =
      σ q (((c.toFun x)⁻¹ : ℂˣ) • f.1.1 x)
    simp only [Units.smul_def] at *
    rw [hf, map_smul, smul_smul, c.covariant]
    congr 1
    rw [← Units.val_mul, mul_inv_rev]
    simp [mul_assoc]
  · intro k x
    have hf := congrArg (fun F : EquivariantFunctions P (twist χ σ) => F.1 x)
      (hK ⟨(k : G), k.property.1⟩)
    change eval P _ f (x * (k : G)) = eval P _ f x at hf
    change ((c.toFun (x * (k : G)))⁻¹ : ℂˣ) • eval P _ f (x * (k : G)) =
      ((c.toFun x)⁻¹ : ℂˣ) • eval P _ f x
    rw [hf, c.invariant ⟨(k : G), k.property.2⟩]

/-- Multiplication by a covariant scalar, from covariant functions for `σ` to
covariant functions for the twist of `σ` by `χ`. -/
def rescaleEquiv (c : CovariantScalar P χ) (σ : Representation ℂ P V) :
    SmoothFunctions P σ ≃ₗ[ℂ] SmoothFunctions P (twist χ σ) where
  toFun := rescaleTo c σ
  map_add' f h := by
    apply Subtype.ext
    apply Subtype.ext
    funext x
    change (c.toFun x : ℂ) • (eval P σ f x + eval P σ h x) =
      (c.toFun x : ℂ) • eval P σ f x + (c.toFun x : ℂ) • eval P σ h x
    exact smul_add _ _ _
  map_smul' a f := by
    apply Subtype.ext
    apply Subtype.ext
    funext x
    change (c.toFun x : ℂ) • (a • eval P σ f x) = a • ((c.toFun x : ℂ) • eval P σ f x)
    exact smul_comm _ _ _
  invFun := rescaleFrom c σ
  left_inv f := by
    apply Subtype.ext
    apply Subtype.ext
    funext x
    change ((c.toFun x)⁻¹ : ℂˣ) • ((c.toFun x : ℂ) • eval P σ f x) = eval P σ f x
    simp [Units.smul_def, smul_smul]
  right_inv f := by
    apply Subtype.ext
    apply Subtype.ext
    funext x
    change (c.toFun x : ℂ) • (((c.toFun x)⁻¹ : ℂˣ) • eval P _ f x) = eval P _ f x
    simp [Units.smul_def, smul_smul]

omit [IsTopologicalGroup G] in
@[simp]
theorem rescaleEquiv_eval (c : CovariantScalar P χ) (σ : Representation ℂ P V)
    (f : SmoothFunctions P σ) (x : G) :
    eval P (twist χ σ) (rescaleEquiv c σ f) x = (c.toFun x : ℂ) • eval P σ f x := rfl

omit [IsTopologicalGroup G] in
@[simp]
theorem rescaleEquiv_symm_eval (c : CovariantScalar P χ) (σ : Representation ℂ P V)
    (f : SmoothFunctions P (twist χ σ)) (x : G) :
    eval P σ ((rescaleEquiv c σ).symm f) x =
      ((c.toFun x)⁻¹ : ℂˣ) • eval P (twist χ σ) f x := rfl

theorem eval_smoothInduced (σ : Representation ℂ P V) (g : G) (f : SmoothFunctions P σ)
    (x : G) : eval P σ (smoothInduced P σ g f) x = eval P σ f (x * g) := rfl

/-- Smooth induction from the twist of `σ` by `χ`, transported to the space of
covariant functions for `σ` by a covariant scalar. -/
def rescaledInduced (c : CovariantScalar P χ) (σ : Representation ℂ P V) :
    Representation ℂ G (SmoothFunctions P σ) where
  toFun g := (rescaleEquiv c σ).symm.toLinearMap ∘ₗ smoothInduced P (twist χ σ) g ∘ₗ
    (rescaleEquiv c σ).toLinearMap
  map_one' := by
    apply LinearMap.ext
    intro f
    simp
  map_mul' g h := by
    apply LinearMap.ext
    intro f
    simp [Module.End.mul_apply]

/-- The transported representation is equivalent to smooth induction from the
twist, by the rescaling map. -/
def rescaledInducedEquiv (c : CovariantScalar P χ) (σ : Representation ℂ P V) :
    (rescaledInduced c σ).Equiv (smoothInduced P (twist χ σ)) where
  toLinearEquiv := rescaleEquiv c σ
  isIntertwining' g := by
    apply LinearMap.ext
    intro f
    change rescaleEquiv c σ ((rescaleEquiv c σ).symm
      (smoothInduced P (twist χ σ) g (rescaleEquiv c σ f))) =
        smoothInduced P (twist χ σ) g (rescaleEquiv c σ f)
    exact (rescaleEquiv c σ).apply_symm_apply _

/-- Values of the transported action: `(c x)⁻¹ c (x g) f (x g)`. -/
theorem eval_rescaledInduced (c : CovariantScalar P χ) (σ : Representation ℂ P V)
    (g : G) (f : SmoothFunctions P σ) (x : G) :
    eval P σ (rescaledInduced c σ g f) x =
      (((c.toFun x)⁻¹ * c.toFun (x * g) : ℂˣ) : ℂ) • eval P σ f (x * g) := by
  change ((c.toFun x)⁻¹ : ℂˣ) • ((c.toFun (x * g) : ℂ) • eval P σ f (x * g)) = _
  rw [Units.smul_def, smul_smul, Units.val_mul]

/-- A factorization `G = P K` with `K` compact open, and a positive character
`N` of `P` trivial on `P ∩ K`. -/
structure IwasawaHeight (P : Subgroup G) where
  /-- The compact open subgroup of the factorization. -/
  compactSubgroup : OpenSubgroup G
  /-- Compactness of that subgroup. -/
  isCompact : IsCompact (compactSubgroup : Set G)
  /-- Every element factors as an element of `P` times an element of `K`. -/
  factor : ∀ g : G, ∃ (q : P) (k : compactSubgroup), g = (q : G) * (k : G)
  /-- The positive character of `P`. -/
  modulus : P →* ℝ≥0ˣ
  /-- The character is trivial on `P ∩ K`. -/
  modulus_eq_one : ∀ q : P, (q : G) ∈ compactSubgroup → modulus q = 1

/-- The real power `r ↦ r ^ s` from positive reals to complex units. -/
def positivePower (s : ℝ) : ℝ≥0ˣ →* ℂˣ :=
  positiveUnitsToComplex.comp (Units.map (NNReal.rpowMonoidHom s))

@[simp]
theorem coe_positivePower (s : ℝ) (r : ℝ≥0ˣ) :
    (positivePower s r : ℂ) = ((((r : ℝ≥0) : ℝ) ^ s : ℝ) : ℂ) := rfl

omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem positivePower_comp (N : P →* ℝ≥0ˣ) (s : ℝ) :
    (positivePower s).comp N = realPowerCharacter N s := rfl

namespace IwasawaHeight

variable (H : IwasawaHeight P)

/-- The height `N q` of `x = q k`, for the chosen factorization. -/
def height (x : G) : ℝ≥0ˣ :=
  H.modulus (Classical.choose (H.factor x))

omit [IsTopologicalGroup G] in
/-- The height of `q k` is `N q`, independently of the chosen factorization. -/
theorem height_mul_of_mem (q : P) {k : G} (hk : k ∈ H.compactSubgroup) :
    H.height ((q : G) * k) = H.modulus q := by
  let q' := Classical.choose (H.factor ((q : G) * k))
  obtain ⟨k', hk'⟩ := Classical.choose_spec (H.factor ((q : G) * k))
  change H.modulus q' = H.modulus q
  have hmem : ((q'⁻¹ * q : P) : G) ∈ H.compactSubgroup := by
    have heq : ((q'⁻¹ * q : P) : G) = (k' : G) * k⁻¹ := by
      push_cast
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← hk', mul_inv_cancel_right]
    rw [heq]
    exact H.compactSubgroup.mul_mem k'.property (H.compactSubgroup.inv_mem hk)
  have h1 := H.modulus_eq_one _ hmem
  rw [map_mul, map_inv, inv_mul_eq_one] at h1
  exact h1

omit [IsTopologicalGroup G] in
/-- Left covariance of the height. -/
theorem height_mul_left (q : P) (x : G) :
    H.height ((q : G) * x) = H.modulus q * H.height x := by
  obtain ⟨q', k', hx⟩ := H.factor x
  rw [hx, ← mul_assoc, ← Subgroup.coe_mul, H.height_mul_of_mem _ k'.property,
    H.height_mul_of_mem _ k'.property, map_mul]

omit [IsTopologicalGroup G] in
/-- Right invariance of the height under `K`. -/
theorem height_mul_right (x : G) {k : G} (hk : k ∈ H.compactSubgroup) :
    H.height (x * k) = H.height x := by
  obtain ⟨q', k', hx⟩ := H.factor x
  rw [hx, mul_assoc, H.height_mul_of_mem _ (H.compactSubgroup.mul_mem k'.property hk),
    H.height_mul_of_mem _ k'.property]

/-- The covariant scalar `x ↦ height x ^ s`, covariant for `N ^ s`. -/
def heightScalar (s : ℝ) : CovariantScalar P (realPowerCharacter H.modulus s) where
  toFun x := positivePower s (H.height x)
  covariant q x := by
    rw [H.height_mul_left, map_mul]
    rfl
  stabilizer := H.compactSubgroup
  invariant k x := by
    rw [H.height_mul_right x k.property]

/-- The family on the untwisted function space: smooth induction from `σ`
twisted by `N ^ s`, transported by the height power. -/
def family (σ : Representation ℂ P V) (s : ℝ) :
    Representation ℂ G (SmoothFunctions P σ) :=
  rescaledInduced (H.heightScalar s) σ

/-- Each member of the family is equivalent to smooth induction from the real
power twist `N ^ s ⊗ σ`. -/
def familyEquiv (σ : Representation ℂ P V) (s : ℝ) :
    (H.family σ s).Equiv (smoothInduced P (realPowerTwist H.modulus s σ)) :=
  rescaledInducedEquiv (H.heightScalar s) σ

/-- The ratio `height (x g) / height x`. -/
def ratio (g x : G) : ℝ≥0ˣ :=
  (H.height x)⁻¹ * H.height (x * g)

omit [IsTopologicalGroup G] in
theorem ratio_mul_left (g : G) (q : P) (x : G) :
    H.ratio g ((q : G) * x) = H.ratio g x := by
  simp only [ratio, mul_assoc, H.height_mul_left, mul_inv_rev]
  rw [inv_mul_cancel_left]

/-- Values of the family: `(height (x g) / height x) ^ s f (x g)`. -/
theorem eval_family (σ : Representation ℂ P V) (s : ℝ) (g : G)
    (f : SmoothFunctions P σ) (x : G) :
    eval P σ (H.family σ s g f) x =
      (positivePower s (H.ratio g x) : ℂ) • eval P σ f (x * g) := by
  rw [family, eval_rescaledInduced]
  congr 2
  simp [heightScalar, ratio, map_mul, map_inv]

/-- On `K` every member of the family is untwisted right translation. -/
theorem family_apply_of_mem (σ : Representation ℂ P V) (s : ℝ) {k : G}
    (hk : k ∈ H.compactSubgroup) : H.family σ s k = smoothInduced P σ k := by
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  apply Subtype.ext
  funext x
  change eval P σ (H.family σ s k f) x = eval P σ (smoothInduced P σ k f) x
  rw [H.eval_family, eval_smoothInduced, ratio, H.height_mul_right x hk, inv_mul_cancel,
    map_one, Units.val_one, one_smul]

/-- Members of the family agree on `K`. -/
theorem family_apply_eq_of_mem (σ : Representation ℂ P V) (s t : ℝ) {k : G}
    (hk : k ∈ H.compactSubgroup) : H.family σ s k = H.family σ t k := by
  rw [H.family_apply_of_mem σ s hk, H.family_apply_of_mem σ t hk]

/-- The pairing of the members at `s` and `-s` agrees pointwise with the
pairing of untwisted right translates. -/
theorem inner_eval_family_neg (b : InnerProductSpace.Core ℂ V) (σ : Representation ℂ P V)
    (s : ℝ) (g : G) (f h : SmoothFunctions P σ) (x : G) :
    b.inner (eval P σ (H.family σ s g f) x) (eval P σ (H.family σ (-s) g h) x) =
      b.inner (eval P σ f (x * g)) (eval P σ h (x * g)) := by
  rw [H.eval_family, H.eval_family, b.smul_left,
    InnerProductSpace.Core.inner_smul_right, coe_positivePower, coe_positivePower,
    Complex.conj_ofReal, ← mul_assoc, ← Complex.ofReal_mul,
    ← Real.rpow_add (by exact_mod_cast pos_iff_ne_zero.mpr (H.ratio g x).ne_zero),
    add_neg_cancel, Real.rpow_zero, Complex.ofReal_one, one_mul]

/-- The ratio is right invariant under the open subgroup `K ∩ g K g⁻¹`. -/
def ratioStabilizer (g : G) : OpenSubgroup G :=
  H.compactSubgroup ⊓ H.compactSubgroup.comap (MulAut.conj g⁻¹).toMonoidHom
    ((continuous_const.mul continuous_id).mul continuous_const)

theorem ratio_mul_right (g x : G) {k : G} (hk : k ∈ H.ratioStabilizer g) :
    H.ratio g (x * k) = H.ratio g x := by
  have hk1 : k ∈ H.compactSubgroup := hk.1
  have hk2 : g⁻¹ * k * g⁻¹⁻¹ ∈ H.compactSubgroup := hk.2
  rw [inv_inv] at hk2
  have heq : x * k * g = x * g * (g⁻¹ * k * g) := by group
  simp only [ratio]
  rw [heq, H.height_mul_right _ hk2, H.height_mul_right _ hk1]

theorem ratio_isLocallyConstant (g : G) : IsLocallyConstant (H.ratio g) := by
  apply (IsLocallyConstant.iff_exists_open _).mpr
  intro x
  refine ⟨(fun k => x * k) '' (H.ratioStabilizer g : Set G),
    isOpenMap_mul_left x _ (H.ratioStabilizer g).isOpen,
    ⟨1, (H.ratioStabilizer g).one_mem, mul_one x⟩, ?_⟩
  rintro _ ⟨k, hk, rfl⟩
  exact H.ratio_mul_right g x hk

/-- The ratio takes finitely many values. -/
theorem ratio_range_finite (g : G) : (Set.range (H.ratio g)).Finite := by
  have : CompactSpace H.compactSubgroup := isCompact_iff_compactSpace.mp H.isCompact
  have hfin := ((H.ratio_isLocallyConstant g).comp_continuous
    (continuous_subtype_val : Continuous (fun k : H.compactSubgroup => (k : G)))).range_finite
  apply hfin.subset
  rintro _ ⟨x, rfl⟩
  obtain ⟨q, k, hx⟩ := H.factor x
  exact ⟨k, by rw [Function.comp_apply, hx, H.ratio_mul_left]⟩

/-- Multiplication by a scalar function that is left `P`-invariant and right
invariant under an open subgroup. -/
def invariantMul (σ : Representation ℂ P V) (φ : G → ℂ)
    (hφ : ∀ (q : P) (x : G), φ ((q : G) * x) = φ x) (K' : OpenSubgroup G)
    (hK' : ∀ (k : K') (x : G), φ (x * (k : G)) = φ x) (f : SmoothFunctions P σ) :
    SmoothFunctions P σ := by
  let K := Classical.choose f.property
  have hK := Classical.choose_spec f.property
  refine smoothFunctionOf P σ (fun x => φ x • eval P σ f x) ?_ (K ⊓ K') ?_
  · intro q x
    have hf : f.1.1 ((q : G) * x) = σ q (f.1.1 x) := f.1.property q x
    change φ ((q : G) * x) • f.1.1 ((q : G) * x) = σ q (φ x • f.1.1 x)
    rw [hf, hφ, map_smul]
  · intro k x
    have hf := congrArg (fun F : EquivariantFunctions P σ => F.1 x)
      (hK ⟨(k : G), k.property.1⟩)
    change eval P σ f (x * (k : G)) = eval P σ f x at hf
    change φ (x * (k : G)) • eval P σ f (x * (k : G)) = φ x • eval P σ f x
    rw [hf, hK' ⟨(k : G), k.property.2⟩]

private def evalLinear (σ : Representation ℂ P V) (x : G) :
    SmoothFunctions P σ →ₗ[ℂ] V where
  toFun f := eval P σ f x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The family is a finite combination, with coefficients `r ^ s`, of fixed
vectors depending only on `g` and `f`. -/
theorem family_eq_sum (σ : Representation ℂ P V) (s : ℝ) (g : G)
    (f : SmoothFunctions P σ) :
    H.family σ s g f = ∑ r ∈ (H.ratio_range_finite g).toFinset,
      (positivePower s r : ℂ) • invariantMul σ
        (fun x => if H.ratio g x = r then 1 else 0)
        (fun q x => by rw [H.ratio_mul_left]) (H.ratioStabilizer g)
        (fun k x => by rw [H.ratio_mul_right g x k.property])
        (smoothInduced P σ g f) := by
  apply Subtype.ext
  apply Subtype.ext
  funext x
  change evalLinear σ x (H.family σ s g f) = evalLinear σ x (∑ r ∈ _, _)
  rw [map_sum]
  change eval P σ (H.family σ s g f) x = ∑ r ∈ _,
    (positivePower s r : ℂ) • ((if H.ratio g x = r then (1 : ℂ) else 0) •
      eval P σ (smoothInduced P σ g f) x)
  simp only [ite_smul, one_smul, zero_smul, smul_ite, smul_zero]
  rw [Finset.sum_ite_eq_of_mem _ _ _
      ((Set.Finite.mem_toFinset _).mpr (Set.mem_range_self x)),
    H.eval_family, eval_smoothInduced]

/-- Weak continuity: every scalar `ℓ (π s g f)` is continuous in `s`. -/
theorem continuous_family_apply (σ : Representation ℂ P V) (g : G)
    (f : SmoothFunctions P σ) (ℓ : Module.Dual ℂ (SmoothFunctions P σ)) :
    Continuous fun s : ℝ => ℓ (H.family σ s g f) := by
  simp_rw [H.family_eq_sum, map_sum, map_smul, smul_eq_mul, coe_positivePower]
  refine continuous_finsetSum _ fun r _ => ?_
  refine Continuous.mul ?_ continuous_const
  exact Complex.continuous_ofReal.comp (Real.continuous_const_rpow
    (by exact_mod_cast (r : ℝ≥0).coe_ne_zero.mpr r.ne_zero))

end IwasawaHeight

end Langlands.Induction
