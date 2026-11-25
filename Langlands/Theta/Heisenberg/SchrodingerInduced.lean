import Langlands.Theta.Heisenberg.InducedModel
import Langlands.Theta.Heisenberg.SchrodingerIrreducible

/-!
# The Schrödinger model as an induced model

GKT §1.2.2 (Theorem 1.13 and the restriction map (1.5), p. 25). For a pairing
`β : X →ₗ[F] Y →ₗ[F] F` of finite-dimensional spaces over a nonarchimedean local field, the
subspace `0 × Y` of `(X × Y, polarizedForm β)` is a Lagrangian (the book's `X`; the book's `Y` is
the Library's `X × 0`).

* `lagrangianRight`: the subgroup `0 × Y`; `schrodingerDatum`: `0 × Y` with the trivial extension
  `ψ_X (x, t) = ψ t` of `ψ`, an `InducingDatum` when `ψ ≠ 1` and `β` is non-degenerate on the left.
* `inducedFunction φ (x, y) = ψ(½ β(x, y)) φ(x)`: the function of the induced model whose
  restriction to `X × 0` is `φ` (the book's `f_φ`, proof of Theorem 1.13 and of Proposition 1.24).
* `restrictionEquiv`: **Theorem 1.13**, the restriction `R_{X,Y} : f ↦ (x ↦ f (x, 0))` is an
  isomorphism of representations from the induced model of `0 × Y` to the Schrödinger model
  `schrodingerSB`. Hence the induced model of `0 × Y` is smooth and irreducible
  (`isSmooth_schrodingerInducedSpace`, `isIrreducible_schrodingerInducedSpace`).
-/

noncomputable section

open Filter Topology
open scoped Pointwise

namespace Langlands.HeisenbergGroup

open Langlands.HarmonicAnalysis

universe u v w

section Algebra

variable {F : Type u} [Field F] {X : Type v} {Y : Type w} [AddCommGroup X] [Module F X]
  [AddCommGroup Y] [Module F Y]

variable (X Y) in
/-- The Lagrangian `0 × Y` of `polarizedForm β` (the book's `X` in the Schrödinger model). -/
def lagrangianRight : AddSubgroup (X × Y) :=
  (LinearMap.ker (LinearMap.fst F X Y)).toAddSubgroup

theorem mem_lagrangianRight {w : X × Y} : w ∈ lagrangianRight (F := F) X Y ↔ w.1 = 0 :=
  Iff.rfl

variable [Invertible (2 : F)] (β : X →ₗ[F] Y →ₗ[F] F) (ψ : AddChar F ℂ)

/-- **The function of the induced model with restriction `φ`** (GKT, proof of Theorem 1.13):
`(x, y) ↦ ψ(½ β(x, y)) φ(x)`. -/
def inducedFunction (φ : X → ℂ) : X × Y → ℂ := fun w => ψ (⅟2 * β w.1 w.2) * φ w.1

@[simp] theorem inducedFunction_apply (φ : X → ℂ) (w : X × Y) :
    inducedFunction β ψ φ w = ψ (⅟2 * β w.1 w.2) * φ w.1 := rfl

/-- The induced function of `φ` restricts to `φ` on `X × 0`. -/
@[simp] theorem inducedFunction_apply_zero (φ : X → ℂ) (x : X) :
    inducedFunction β ψ φ (x, 0) = φ x := by
  simp

/-- The Schrödinger representation is right translation on induced functions:
`(ρ(g) f_φ)|_{X} = f_{σ(g) φ}|_{X}` in the form of values. -/
theorem regular_inducedFunction (g : HeisenbergGroup (polarizedForm β)) (φ : X → ℂ) :
    regular (polarizedForm β) ψ g (inducedFunction β ψ φ) =
      inducedFunction β ψ (schrodinger ψ β g φ) := by
  have h2 : (⅟2 : F) + ⅟2 = 1 := by rw [← two_mul, mul_invOf_self]
  funext w
  simp only [regular_apply, LinearMap.smul_apply, Pi.smul_apply, regularFun_apply,
    inducedFunction_apply, schrodinger_apply, schrodingerFun_apply, smul_eq_mul,
    polarizedForm_apply, Prod.fst_add, Prod.snd_add]
  have e : ⅟2 * (β w.1 g.vec.2 - β g.vec.1 w.2) + ⅟2 * β (w.1 + g.vec.1) (w.2 + g.vec.2) =
      ⅟2 * β w.1 w.2 + (β w.1 g.vec.2 + ⅟2 * β g.vec.1 g.vec.2) := by
    simp only [map_add, LinearMap.add_apply]
    linear_combination (β w.1 g.vec.2) * h2
  calc ψ g.cen * (ψ (⅟2 * (β w.1 g.vec.2 - β g.vec.1 w.2)) *
        (ψ (⅟2 * β (w.1 + g.vec.1) (w.2 + g.vec.2)) * φ (w.1 + g.vec.1)))
      = ψ g.cen * (ψ (⅟2 * (β w.1 g.vec.2 - β g.vec.1 w.2) +
          ⅟2 * β (w.1 + g.vec.1) (w.2 + g.vec.2)) * φ (w.1 + g.vec.1)) := by
        rw [AddChar.map_add_eq_mul]; ring
    _ = _ := by rw [e, AddChar.map_add_eq_mul]; ring

end Algebra

section Local

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [Invertible (2 : F)]
  {X : Type v} [AddCommGroup X] [Module F X] [FiniteDimensional F X] [TopologicalSpace X]
  [IsModuleTopology F X] [IsTopologicalAddGroup X]
  {Y : Type w} [AddCommGroup Y] [Module F Y] [FiniteDimensional F Y] [TopologicalSpace Y]
  [IsModuleTopology F Y]
  {β : X →ₗ[F] Y →ₗ[F] F} {ψ : AddChar F ℂ}

omit [Invertible (2 : F)] [IsTopologicalAddGroup X] [FiniteDimensional F Y] in
/-- The pairing `β` is continuous on `X × Y` (the module topologies). -/
theorem continuous_pairing (β : X →ₗ[F] Y →ₗ[F] F) : Continuous fun p : X × Y => β p.1 p.2 :=
  IsModuleTopology.continuous_bilinear_of_finite_left β

omit [Invertible (2 : F)] [IsTopologicalAddGroup X] [FiniteDimensional F Y] in
/-- `z ↦ polarizedForm β z v` is continuous. -/
theorem continuous_polarizedForm_left (β : X →ₗ[F] Y →ₗ[F] F) (v : X × Y) :
    Continuous fun z => polarizedForm β z v := by
  simp only [polarizedForm_apply]
  exact ((continuous_pairing β).comp (continuous_fst.prodMk continuous_const)).sub
    ((continuous_pairing β).comp (continuous_const.prodMk continuous_snd))

variable (β) in
/-- **The Lagrangian `0 × Y` with the trivial extension of `ψ`** (GKT §1.2.2, p. 25:
`ψ_X(x, t) = ψ(t)`), an inducing datum for a non-trivial `ψ` and a pairing non-degenerate on the
left. -/
def schrodingerDatum (hψ1 : ψ ≠ 1) (hβl : ∀ x, (∀ y, β x y = 0) → x = 0) :
    InducingDatum (polarizedForm β) ψ where
  subgroup := lagrangianRight X Y
  isClosed := by
    have := t2Space_of_finiteDimensional F X
    exact isClosed_eq continuous_fst continuous_const
  charOrthogonal_eq := by
    ext w
    change w ∈ charOrthogonal (polarizedForm β) ψ
      ((LinearMap.ker (LinearMap.fst F X Y) : Submodule F (X × Y)) : Set (X × Y)) ↔ w.1 = 0
    rw [mem_charOrthogonal_submodule _ hψ1]
    constructor
    · intro h
      exact hβl _ fun y => by simpa using h (0, y) (by simp)
    · intro h l hl
      have hl' : l.1 = 0 := hl
      simp [polarizedForm_apply, h, hl']
  character _ := 1
  character_ne_zero _ _ := one_ne_zero
  character_mul a ha b hb := by
    have ha' : a.1 = 0 := ha
    have hb' : b.1 = 0 := hb
    simp [polarizedForm_apply, ha', hb']

variable (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) (hβl : ∀ x, (∀ y, β x y = 0) → x = 0)

omit [Invertible (2 : F)] in
include hψ in
/-- A continuous additive character of `F` is locally constant. -/
theorem isLocallyConstant_addChar : IsLocallyConstant ψ :=
  isLocallyConstant_of_continuous_addChar ψ hψ

/-- **The induced model of the Lagrangian `0 × Y`** (GKT Definition 1.6 with `A = X`). -/
def schrodingerInducedSpace : Subrepresentation (regular (polarizedForm β) ψ) :=
  have := IsModuleTopology.isTopologicalAddGroup F Y
  (schrodingerDatum β hψ1 hβl).inducedSpace (polarizedForm_isAlt β) (isLocallyConstant_addChar hψ)
    (continuous_polarizedForm_left β)

omit [IsTopologicalAddGroup X] [FiniteDimensional F Y] in
include hψ in
/-- The induced function of a Schwartz–Bruhat function lies in the induced model. -/
theorem inducedFunction_mem {φ : X → ℂ} (hφ : φ ∈ schwartzBruhatSubmodule X) :
    inducedFunction β ψ φ ∈ (schrodingerDatum β hψ1 hβl).inducedSubmodule := by
  have hψl := isLocallyConstant_addChar hψ
  refine ⟨fun a ha w => ?_, ?_, (fun x => (x, (0 : Y))) '' tsupport φ,
    hφ.2.image (continuous_id.prodMk continuous_const), fun w hw => ?_⟩
  · have ha' : a.1 = 0 := ha
    simp only [inducedFunction_apply, Prod.fst_add, Prod.snd_add, ha', zero_add,
      polarizedForm_apply, map_zero, LinearMap.zero_apply, sub_zero]
    change _ = 1 * _ * _
    rw [one_mul, ← mul_assoc, ← AddChar.map_add_eq_mul, map_add, ← mul_add, add_comm (β w.1 a.2)]
  · exact (hψl.comp_continuous (continuous_const.mul (continuous_pairing β))).mul
      (hφ.1.comp_continuous continuous_fst)
  · refine ⟨(0, w.2), (show ((0, w.2) : X × Y).1 = 0 from rfl), (w.1, 0),
      ⟨w.1, subset_tsupport _ (right_ne_zero_of_mul hw), rfl⟩, ?_⟩
    change (0 + w.1, w.2 + 0) = w
    simp

omit [FiniteDimensional F Y] [IsModuleTopology F Y] in
/-- The restriction of a function of the induced model is a Schwartz–Bruhat function. -/
theorem restriction_mem {f : X × Y → ℂ} (hf : f ∈ (schrodingerDatum β hψ1 hβl).inducedSubmodule) :
    (fun x => f (x, 0)) ∈ schwartzBruhatSubmodule X := by
  obtain ⟨-, hf2, K, hK, hfK⟩ := hf
  refine ⟨hf2.comp_continuous (continuous_id.prodMk continuous_const),
    HasCompactSupport.intro (hK.image continuous_fst) fun x hx => ?_⟩
  by_contra h
  obtain ⟨a, ha, k, hk, hak⟩ := hfK (x, 0) h
  have ha' : a.1 = 0 := ha
  refine hx ⟨k, hk, ?_⟩
  have := congrArg Prod.fst hak
  simpa [ha'] using this

omit [IsTopologicalAddGroup X] [FiniteDimensional F Y] [IsModuleTopology F Y] in
/-- A function of the induced model is the induced function of its restriction. -/
theorem inducedFunction_restriction {f : X × Y → ℂ}
    (hf : f ∈ (schrodingerDatum β hψ1 hβl).inducedSubmodule) :
    inducedFunction β ψ (fun x => f (x, 0)) = f := by
  funext w
  have h := hf.1 (0, w.2) (show ((0, w.2) : X × Y).1 = 0 from rfl) (w.1, 0)
  have e : ((0, w.2) : X × Y) + (w.1, 0) = w := by ext <;> simp
  rw [e] at h
  rw [h, inducedFunction_apply]
  change _ = 1 * _ * _
  simp [polarizedForm_apply]

/-- **GKT Theorem 1.13**: the restriction `R_{X,Y} : f ↦ (x ↦ f (x, 0))` is an isomorphism of
representations from the induced model of `0 × Y` (the book's `Ind_{H(X)}^{H(W)} ψ_X`) to the
Schrödinger model, with inverse `φ ↦ f_φ = inducedFunction β ψ φ`. -/
def restrictionEquiv :
    (schrodingerInducedSpace hψ hψ1 hβl).toRepresentation.Equiv
      (schrodingerSB hψ (fun _ => (continuous_pairing β).comp
        (continuous_id.prodMk continuous_const))) :=
  Representation.Equiv.mk
    { toFun := fun f => ⟨fun x => f.1 (x, 0), restriction_mem hψ1 hβl f.2⟩
      map_add' := fun f g => rfl
      map_smul' := fun c f => rfl
      invFun := fun φ => ⟨inducedFunction β ψ φ, inducedFunction_mem hψ hψ1 hβl φ.2⟩
      left_inv := fun f => Subtype.ext (inducedFunction_restriction hψ1 hβl f.2)
      right_inv := fun φ => Subtype.ext (funext fun x => inducedFunction_apply_zero β ψ _ x) }
    (fun g => LinearMap.ext fun f => Subtype.ext (funext fun x => by
      change regular (polarizedForm β) ψ g f.1 (x, 0) = schrodinger ψ β g (fun x => f.1 (x, 0)) x
      conv_lhs => rw [← inducedFunction_restriction hψ1 hβl f.2, regular_inducedFunction]
      exact inducedFunction_apply_zero β ψ _ x))

omit [FiniteDimensional F Y] in
@[simp] theorem restrictionEquiv_apply (f : (schrodingerInducedSpace hψ hψ1 hβl).toSubmodule)
    (x : X) : (restrictionEquiv hψ hψ1 hβl f : X → ℂ) x = f.1 (x, 0) := rfl

omit [FiniteDimensional F Y] in
@[simp] theorem restrictionEquiv_symm_apply
    (φ : SchwartzBruhat X) (w : X × Y) :
    ((restrictionEquiv hψ hψ1 hβl).symm φ).1 w = inducedFunction β ψ φ w := rfl

omit [Invertible (2 : F)] in
/-- Smoothness is carried back along an equivalence of representations. -/
theorem isSmooth_of_equiv {G : Type*} [Group G] [TopologicalSpace G] {V V' : Type*}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] {ρ : Representation ℂ G V}
    {ρ' : Representation ℂ G V'} (e : ρ.Equiv ρ') (h : IsSmooth ρ') : IsSmooth ρ := by
  intro v
  obtain ⟨K, hK⟩ := h (e v)
  refine ⟨K, fun k => ?_⟩
  have h1 : ρ' k (e v) = e v := hK k
  have h2 : e (ρ k v) = ρ' k (e v) := LinearMap.congr_fun (e.isIntertwining' k) v
  exact e.injective (h2.trans h1)

omit [Invertible (2 : F)] in
/-- Irreducibility is carried back along an equivalence of representations. -/
theorem isIrreducible_of_equiv {G : Type*} [Group G] {V V' : Type*}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] {ρ : Representation ℂ G V}
    {ρ' : Representation ℂ G V'} (e : ρ.Equiv ρ') (h : ρ'.IsIrreducible) : ρ.IsIrreducible := by
  rw [Representation.irreducible_iff_isSimpleModule_asModule] at h ⊢
  exact (LinearMap.isSimpleModule_iff_of_bijective
    (Representation.IntertwiningMap.equivLinearMapAsModule ρ ρ' e.toIntertwiningMap)
    e.bijective).2 h

/-- The induced model of `0 × Y` is smooth (GKT Theorem 1.13 with `isSmooth_schrodingerSB`). -/
theorem isSmooth_schrodingerInducedSpace :
    IsSmooth (schrodingerInducedSpace hψ hψ1 hβl).toRepresentation :=
  isSmooth_of_equiv (restrictionEquiv hψ hψ1 hβl) (isSmooth_schrodingerSB hψ _)

/-- **The induced model of `0 × Y` is irreducible** (GKT Proposition 1.12 for `A = X`, through
Theorem 1.13 and the irreducibility of the Schrödinger model). -/
theorem isIrreducible_schrodingerInducedSpace [β.IsPerfPair] :
    (schrodingerInducedSpace hψ hψ1 hβl).toRepresentation.IsIrreducible :=
  isIrreducible_of_equiv (restrictionEquiv hψ hψ1 hβl) (isIrreducible_schrodingerSB hψ hψ1 _)

end Local

end Langlands.HeisenbergGroup
