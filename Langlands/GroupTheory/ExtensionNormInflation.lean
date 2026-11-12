import Langlands.GroupTheory.ExtensionAkizukiWitt

/-! # Inflation of factor-extension classes along a norm-compatible kernel map -/

noncomputable section

namespace Langlands.GroupExtensionPushout

universe u v

section NormInflation

variable {W : Type u} {G : Type v} {A : Type v} [Group W] [Group G] [CommGroup A]
  [MulDistribMulAction G A]
  {Q : Type v} {B : Type v} [Group Q] [CommGroup B] [MulDistribMulAction Q B]
  {q : W →* G} (π : G →* Q)

/-- The kernel of `q` as a subgroup of the kernel of `π ∘ q`. -/
def kernelInclusion : q.ker →* (π.comp q).ker :=
  Subgroup.inclusion (fun x (hx : x ∈ q.ker) => by
    rw [MonoidHom.mem_ker] at hx ⊢
    rw [MonoidHom.comp_apply, hx, map_one])

@[simp] theorem kernelInclusion_coe (x : q.ker) :
    ((kernelInclusion π x : (π.comp q).ker) : W) = x := rfl

variable (t : Section q) (σ : Section π)

/-- The element `t(γ) t(σ(π γ))⁻¹` of the kernel of `π ∘ q`, comparing the section `t`
with the lifted section `t ∘ σ ∘ π`. -/
def liftDifference (γ : G) : (π.comp q).ker :=
  ⟨t γ * (t (σ (π γ)))⁻¹, by
    rw [MonoidHom.mem_ker, map_mul, map_inv, MonoidHom.comp_apply, MonoidHom.comp_apply,
      Section.map_apply, Section.map_apply, Section.map_apply, mul_inv_cancel]⟩

/-- The factor set of `t` decomposed through the factor set of the lifted section. -/
theorem kernelInclusion_factorKernel (g g' : G) :
    kernelInclusion π (t.factorKernel g g') =
      liftDifference π t σ g *
        conjugateKernel (π.comp q) (t (σ (π g))) (liftDifference π t σ g') *
        (t.lift π σ).factorKernel (π g) (π g') * (liftDifference π t σ (g * g'))⁻¹ := by
  apply Subtype.ext
  change t g * t g' * (t (g * g'))⁻¹ =
    t g * (t (σ (π g)))⁻¹ * (t (σ (π g)) * (t g' * (t (σ (π g')))⁻¹) * (t (σ (π g)))⁻¹) *
      (t (σ (π g)) * t (σ (π g')) * (t (σ (π g * π g')))⁻¹) *
      (t (g * g') * (t (σ (π (g * g'))))⁻¹)⁻¹
  rw [map_mul π g g']
  group

variable (r : q.ker →* A)
  (hr : ∀ (x : W) (n : q.ker), r (conjugateKernel q x n) = q x • r n)

/-- **Inflation along a norm-compatible kernel map.** Let `π : G → Q` be surjective with
finite kernel `H`, and let the kernel map `r'` of `π ∘ q`, followed by an equivariant
`ι : B → A`, restrict on the kernel of `q` to the `H`-norm of `r`:
`ι (r' x) = ∏_{h ∈ H} h • r x`. Then inflating the factor-extension class of `π ∘ q`
gives `|H|` times the class of `q`. -/
theorem cohomologyClass_inflate_norm [Fintype π.ker] (hπ : Function.Surjective π)
    (ι : B →* A) (hι : ∀ g b, ι (π g • b) = g • ι b)
    (s : Section (π.comp q)) (r' : (π.comp q).ker →* B)
    (hr' : ∀ (x : W) (n : (π.comp q).ker),
      r' (conjugateKernel (π.comp q) x n) = (π.comp q) x • r' n)
    (hN : ∀ x : q.ker, ι (r' (kernelInclusion π x)) = ∏ h : π.ker, (h : G) • r x) :
    NormalizedTwoCocycle.cohomologyClass
        (NormalizedTwoCocycle.inflate π ι hι (s.cocycle r' hr')) =
      Fintype.card π.ker • NormalizedTwoCocycle.cohomologyClass (t.cocycle r hr) := by
  let σ := Section.ofSurjective hπ
  rw [NormalizedTwoCocycle.cohomologyClass_inflate_congr π ι hι
      (s.cohomologyClass_eq r' hr' (t.lift π σ)),
    ← NormalizedTwoCocycle.cohomologyClass_npow]
  have hrep : ∀ x : G, x⁻¹ * (fun y => y) x ∈ π.ker := by
    intro x
    rw [inv_mul_cancel]
    exact one_mem _
  let a := t.cocycle r hr
  let u : G → A := fun γ => ι (r' (liftDifference π t σ γ))
  let b := akizukiWittCochain π.ker a (fun y => y)
  apply NormalizedTwoCocycle.cohomologyClass_eq_of_cochain _ _ (fun γ => b γ / u γ)
  intro g g'
  have hid := akizukiWitt_identity π.ker a (fun y => y) hrep g g'
  simp only [mul_inv_cancel, NormalizedTwoCocycle.one_left, NormalizedTwoCocycle.one_right,
    inv_one, mul_one] at hid
  have hdec := congrArg (fun x => ι (r' x)) (kernelInclusion_factorKernel π t σ g g')
  simp only [map_mul, map_inv, hr', MonoidHom.comp_apply, Section.map_apply, hι] at hdec
  rw [hN] at hdec
  change ∏ h : π.ker, (h : G) • a (g, g') =
    u g * (g • u g') * ι (r' ((t.lift π σ).factorKernel (π g) (π g'))) * (u (g * g'))⁻¹ at hdec
  change ι (r' ((t.lift π σ).factorKernel (π g) (π g'))) * (b (g * g') / u (g * g')) =
    b g / u g * (g • (b g' / u g')) * a (g, g') ^ Fintype.card π.ker
  rw [hdec] at hid
  rw [smul_div']
  apply Additive.ofMul.injective
  have hid' := congrArg Additive.ofMul hid
  simp only [ofMul_mul, ofMul_div, ofMul_inv] at hid' ⊢
  rw [← sub_eq_zero] at hid' ⊢
  rw [← hid']
  abel

end NormInflation

end Langlands.GroupExtensionPushout
