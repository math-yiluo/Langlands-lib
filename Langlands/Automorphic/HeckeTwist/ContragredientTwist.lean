import Langlands.Automorphic.Contragredient
import Langlands.Automorphic.HeckeTwist.OperatorTwist
import Langlands.Automorphic.HeckeTwist.Admissibility

/-! # Contragredients of Hecke twists

If `T` realizes the contragredient of the twist `S ⊗ (χ ∘ det)` of an operator realization
`S` by a Hecke character `χ`, then the twist `T ⊗ (χ ∘ det)` realizes the contragredient of
`S`. The pairing is `B(y, x) = B₀(e y, e'⁻¹ x)`, where `e` and `e'` are the multiplication
isomorphisms of the two twists: the determinant scalars of the two twists cancel.
-/

noncomputable section

universe u

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic

open Langlands.Global ContinuousRationalFunctions

variable {F : Type u} [Field F] [NumberField F] {n : ℕ}

local instance contragredientTwistRationalGroup (n : ℕ) :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance contragredientTwistContinuousGroup (n : ℕ) :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance contragredientTwistFiniteSmoothGroup (n : ℕ) :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance contragredientTwistFormGroup (n : ℕ) :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance contragredientTwistStableGroup (n : ℕ) :
    AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _

namespace OperatorRealization

local instance contragredientTwistSpaceGroup (S : OperatorRealization F n) :
    AddCommGroup S.Space := Submodule.addCommGroup _

section Generic

variable {V W : Type*} [AddCommMonoid V] [Module ℂ V] [AddCommMonoid W] [Module ℂ W]

/-- If `σ (e y) = c • e (ρ y)`, then `e⁻¹ (σ w) = c • ρ (e⁻¹ w)`. -/
theorem twist_symm_apply (e : V ≃ₗ[ℂ] W) (ρ : V →ₗ[ℂ] V) (σ : W →ₗ[ℂ] W) (c : ℂ)
    (h : ∀ y, σ (e y) = c • e (ρ y)) (w : W) : e.symm (σ w) = c • ρ (e.symm w) := by
  conv_lhs => rw [← e.apply_symm_apply w]
  rw [h, map_smul, e.symm_apply_apply]

/-- If `σ (e y) = c • e (ρ y)` with `c ≠ 0`, then `ρ (e⁻¹ w) = c⁻¹ • e⁻¹ (σ w)`. -/
theorem twist_apply_symm (e : V ≃ₗ[ℂ] W) (ρ : V →ₗ[ℂ] V) (σ : W →ₗ[ℂ] W) (c : ℂ)
    (hc : c ≠ 0) (h : ∀ y, σ (e y) = c • e (ρ y)) (w : W) :
    ρ (e.symm w) = c⁻¹ • e.symm (σ w) := by
  rw [twist_symm_apply e ρ σ c h w, inv_smul_smul₀ hc]

variable {V' W' : Type*} [AddCommMonoid V'] [Module ℂ V'] [AddCommMonoid W'] [Module ℂ W']

/-- Group invariance of a pairing transported along twisted isomorphisms: if `ρ'` and `σ'`
act on the twists through `ρ` and `σ` up to the same scalar `c`, and `B₀` is invariant under
`(ρ', σ)`, then `B₀ (e ·) (e'⁻¹ ·)` is invariant under `(ρ, σ')`. -/
theorem pairing_twisted_invariant (B₀ : W →ₗ[ℂ] V' →ₗ[ℂ] ℂ) (e : V ≃ₗ[ℂ] W)
    (e' : V' ≃ₗ[ℂ] W') (ρ : V →ₗ[ℂ] V) (ρ' : W →ₗ[ℂ] W) (σ : V' →ₗ[ℂ] V')
    (σ' : W' →ₗ[ℂ] W') (c : ℂ) (hρ : ∀ y, ρ' (e y) = c • e (ρ y))
    (hσ : ∀ z, σ' (e' z) = c • e' (σ z)) (hinv : ∀ w z, B₀ (ρ' w) (σ z) = B₀ w z)
    (y : V) (x : W') : B₀ (e (ρ y)) (e'.symm (σ' x)) = B₀ (e y) (e'.symm x) := by
  rw [twist_symm_apply e' σ σ' c hσ x, map_smul, ← LinearMap.map_smul₂, ← hρ, hinv]

/-- Lie invariance of a pairing transported along isomorphisms that shift both actions by the
same scalar `a`. -/
theorem pairing_shifted_invariant (B₀ : W →ₗ[ℂ] V' →ₗ[ℂ] ℂ) (e : V ≃ₗ[ℂ] W)
    (e' : V' ≃ₗ[ℂ] W') (ρ : V →ₗ[ℂ] V) (ρ' : W →ₗ[ℂ] W) (σ : V' →ₗ[ℂ] V')
    (σ' : W' →ₗ[ℂ] W') (a : ℂ) (hρ : ∀ y, ρ' (e y) = e (ρ y + a • y))
    (hσ : ∀ z, σ' (e' z) = e' (σ z + a • z)) (hinv : ∀ w z, B₀ (ρ' w) z + B₀ w (σ z) = 0)
    (y : V) (x : W') : B₀ (e (ρ y)) (e'.symm x) + B₀ (e y) (e'.symm (σ' x)) = 0 := by
  have hx : e'.symm (σ' x) = σ (e'.symm x) + a • e'.symm x := by
    conv_lhs => rw [← e'.apply_symm_apply x]
    rw [hσ, e'.symm_apply_apply]
  have h₀ := hinv (e y) (e'.symm x)
  rw [hρ, map_add, map_smul] at h₀
  rw [hx, map_add, map_smul]
  rw [LinearMap.map_add₂, LinearMap.map_smul₂] at h₀
  simp only [smul_eq_mul] at h₀ ⊢
  linear_combination h₀

/-- Pulling a pairing back along isomorphisms on both sides preserves injectivity of the
partial map. -/
theorem pairing_flip_injective (B₀ : W →ₗ[ℂ] V' →ₗ[ℂ] ℂ) (e : V ≃ₗ[ℂ] W)
    (e' : V' ≃ₗ[ℂ] W') (hinj : Function.Injective B₀.flip) :
    Function.Injective ((B₀ ∘ₗ e.toLinearMap).compl₂ e'.symm.toLinearMap).flip := by
  intro x₁ x₂ hx
  apply e'.symm.injective
  apply hinj
  apply LinearMap.ext
  intro w
  have hw := LinearMap.congr_fun hx (e.symm w)
  simpa using hw

/-- Pulling a pairing back along isomorphisms on both sides: surjectivity of the partial
map onto a class of functionals, transported along `e`. -/
theorem pairing_flip_surjective (B₀ : W →ₗ[ℂ] V' →ₗ[ℂ] ℂ) (e : V ≃ₗ[ℂ] W)
    (e' : V' ≃ₗ[ℂ] W') (l : Module.Dual ℂ V) (x₀ : V')
    (hx₀ : B₀.flip x₀ = l ∘ₗ e.symm.toLinearMap) :
    ((B₀ ∘ₗ e.toLinearMap).compl₂ e'.symm.toLinearMap).flip (e' x₀) = l := by
  apply LinearMap.ext
  intro y
  have h₁ := LinearMap.congr_fun hx₀ (e y)
  simpa using h₁

end Generic

section Functional

variable {S S₁ : OperatorRealization F n}

/-- Contragredient functionals pull back along a linear map `e : S → S₁` that intertwines
the finite actions up to scalars `c d` equal to `1` on an open subgroup, and the compact
actions up to nonzero scalars. -/
theorem isContragredientFunctional_comp_of_twisted (e : S.Space →ₗ[ℂ] S₁.Space)
    (c : FiniteAdelicGL F n → ℂ) (K₀ : OpenSubgroup (FiniteAdelicGL F n))
    (hK₀ : ∀ d ∈ K₀, c d = 1)
    (hd : ∀ (d : FiniteAdelicGL F n) (y : S.Space),
      S₁.finiteRepresentation d (e y) = c d • e (S.finiteRepresentation d y))
    (c' : standardInfiniteCompact F n → ℂ) (hc' : ∀ k, c' k ≠ 0)
    (hk : ∀ (k : standardInfiniteCompact F n) (y : S.Space),
      S₁.compactRepresentation k (e y) = c' k • e (S.compactRepresentation k y))
    {l : Module.Dual ℂ S₁.Space} (hl : S₁.IsContragredientFunctional l) :
    S.IsContragredientFunctional (l ∘ₗ e) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨K, hK⟩ := hl.1
    refine ⟨K ⊓ K₀, ?_⟩
    refine (Representation.mem_invariants _ _).mpr ?_
    rintro ⟨d, hdK⟩
    have hdK' : d ∈ K.toSubgroup ⊓ K₀.toSubgroup := hdK
    have hinv : d⁻¹ ∈ K₀ := K₀.toSubgroup.inv_mem (Subgroup.mem_inf.mp hdK').2
    have hc : c d⁻¹ = 1 := hK₀ _ hinv
    have hfix := (Representation.mem_invariants _ _).mp hK ⟨d, (Subgroup.mem_inf.mp hdK').1⟩
    apply LinearMap.ext
    intro y
    have h₁ : S₁.finiteRepresentation d⁻¹ (e y) = e (S.finiteRepresentation d⁻¹ y) :=
      (hd d⁻¹ y).trans ((congrArg (· • e (S.finiteRepresentation d⁻¹ y)) hc).trans
        (one_smul ℂ _))
    have h₂ : l (S₁.finiteRepresentation d⁻¹ (e y)) = l (e y) := LinearMap.congr_fun hfix (e y)
    exact (congrArg l h₁).symm.trans h₂
  · have hle : FiniteVectors.orbitSpan S.compactRepresentation.dual (l ∘ₗ e) ≤
        (FiniteVectors.orbitSpan S₁.compactRepresentation.dual l).map
          (Module.Dual.transpose (R := ℂ) e) := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨k, rfl⟩
      refine ⟨(c' k⁻¹)⁻¹ • S₁.compactRepresentation.dual k l,
        Submodule.smul_mem _ _ (FiniteVectors.action_mem_orbitSpan _ k l), ?_⟩
      apply LinearMap.ext
      intro y
      change (c' k⁻¹)⁻¹ • l (S₁.compactRepresentation k⁻¹ (e y)) =
        l (e (S.compactRepresentation k⁻¹ y))
      calc (c' k⁻¹)⁻¹ • l (S₁.compactRepresentation k⁻¹ (e y))
          = (c' k⁻¹)⁻¹ • l (c' k⁻¹ • e (S.compactRepresentation k⁻¹ y)) :=
            congrArg (fun w => (c' k⁻¹)⁻¹ • l w) (hk k⁻¹ y)
        _ = (c' k⁻¹)⁻¹ • (c' k⁻¹ • l (e (S.compactRepresentation k⁻¹ y))) :=
            congrArg ((c' k⁻¹)⁻¹ • ·) (l.map_smul _ _)
        _ = l (e (S.compactRepresentation k⁻¹ y)) := inv_smul_smul₀ (hc' _) _
    have : Module.Finite ℂ (FiniteVectors.orbitSpan S₁.compactRepresentation.dual l) := hl.2
    exact Submodule.finiteDimensional_of_le hle

end Functional

section Twist

variable (S : OperatorRealization F n) (χ : HeckeCharacter F)

/-- The finite determinant scalars of `χ` are `1` on an open subgroup. -/
def heckeDeterminantKernel : OpenSubgroup (FiniteAdelicGL F n) where
  toSubgroup := (χ.finiteAdelicDeterminant n).toMonoidHom.ker
  isOpen' := χ.finiteAdelicHeckeDeterminant_isOpen_ker n

theorem adelicDeterminant_ofFinite_eq_one {d : FiniteAdelicGL F n}
    (hd : d ∈ heckeDeterminantKernel (n := n) χ) :
    ((χ.adelicDeterminant n (AdelicGL.ofFinite F n d) : ℂˣ) : ℂ) = 1 := by
  have h : χ.finiteAdelicDeterminant n d = 1 := hd
  exact congrArg Units.val h

/-- The shift of an enveloping generator by `χ` adds a scalar. -/
theorem exists_heckeEnvelopingShift_generator (U : ArchimedeanGL.ComplexLieAlgebra F n) :
    ∃ a : ℂ, heckeEnvelopingShift n χ (ArchimedeanGL.envelopingGenerator F n U) =
      ArchimedeanGL.envelopingGenerator F n U +
        algebraMap ℂ (ArchimedeanGL.EnvelopingAlgebra F n) a :=
  ⟨_, ArchimedeanGL.envelopingShift_generator _ _ U⟩

/-- The scalar by which the character shift moves the enveloping generator of a real Lie
algebra element. -/
def heckeLieShift (X : ArchimedeanGL.RealLieAlgebra F n) : ℂ :=
  Classical.choose (exists_heckeEnvelopingShift_generator (n := n) χ
    (ArchimedeanGL.complexify F n X))

theorem heckeLieShift_spec (X : ArchimedeanGL.RealLieAlgebra F n) :
    heckeEnvelopingShift n χ
        (ArchimedeanGL.envelopingGenerator F n (ArchimedeanGL.complexify F n X)) =
      ArchimedeanGL.envelopingGenerator F n (ArchimedeanGL.complexify F n X) +
        algebraMap ℂ (ArchimedeanGL.EnvelopingAlgebra F n) (heckeLieShift χ X) :=
  Classical.choose_spec (exists_heckeEnvelopingShift_generator (n := n) χ
    (ArchimedeanGL.complexify F n X))

/-- The real Lie action on a twist is the real Lie action shifted by the scalar `a` that
the character shift adds to the enveloping generator. -/
theorem lieAction_heckeDeterminantTwistEquiv (X : ArchimedeanGL.RealLieAlgebra F n) {a : ℂ}
    (ha : heckeEnvelopingShift n χ
        (ArchimedeanGL.envelopingGenerator F n (ArchimedeanGL.complexify F n X)) =
      ArchimedeanGL.envelopingGenerator F n (ArchimedeanGL.complexify F n X) +
        algebraMap ℂ (ArchimedeanGL.EnvelopingAlgebra F n) a) (f : S.Space) :
    (S.heckeDeterminantTwist χ).lieAction X (S.heckeDeterminantTwistEquiv χ f) =
      S.heckeDeterminantTwistEquiv χ (S.lieAction X f + a • f) := by
  have h₁ : S.envelopingAction (heckeEnvelopingShift n χ
      (ArchimedeanGL.envelopingGenerator F n (ArchimedeanGL.complexify F n X))) f =
      S.lieAction X f + a • f :=
    calc S.envelopingAction (heckeEnvelopingShift n χ
          (ArchimedeanGL.envelopingGenerator F n (ArchimedeanGL.complexify F n X))) f
        = S.envelopingAction
            (ArchimedeanGL.envelopingGenerator F n (ArchimedeanGL.complexify F n X) +
              algebraMap ℂ (ArchimedeanGL.EnvelopingAlgebra F n) a) f :=
          congrArg (fun u => S.envelopingAction u f) ha
      _ = S.envelopingAction
            (ArchimedeanGL.envelopingGenerator F n (ArchimedeanGL.complexify F n X)) f +
          S.envelopingAction (algebraMap ℂ (ArchimedeanGL.EnvelopingAlgebra F n) a) f :=
          LinearMap.congr_fun (map_add S.envelopingAction _ _) f
      _ = S.lieAction X f + a • f :=
          congrArg (S.lieAction X f + ·)
            ((LinearMap.congr_fun (S.envelopingAction.commutes a) f).trans
              (Module.algebraMap_end_apply ℂ ℂ S.Space a f))
  exact (S.heckeDeterminantTwistEquiv_differential χ _ f).trans
    (congrArg (S.heckeDeterminantTwistEquiv χ) h₁)

end Twist

variable {S T : OperatorRealization F n} (χ : HeckeCharacter F)

/-- Contragredient functionals of a twist pull back to contragredient functionals. -/
theorem isContragredientFunctional_comp_heckeDeterminantTwistEquiv
    {l : Module.Dual ℂ (S.heckeDeterminantTwist χ).Space}
    (hl : (S.heckeDeterminantTwist χ).IsContragredientFunctional l) :
    S.IsContragredientFunctional
      (l ∘ₗ (S.heckeDeterminantTwistEquiv χ).toLinearEquiv.toLinearMap) :=
  isContragredientFunctional_comp_of_twisted _
    (fun d => ((χ.adelicDeterminant n (AdelicGL.ofFinite F n d) : ℂˣ) : ℂ))
    (heckeDeterminantKernel χ) (fun _ hd => adelicDeterminant_ofFinite_eq_one χ hd)
    (fun d y => S.heckeDeterminantTwistEquiv_finite χ d y)
    (fun k => ((χ.adelicDeterminant n (AdelicGL.ofInfinite F n k.val) : ℂˣ) : ℂ))
    (fun _k => Units.ne_zero _)
    (fun k y => S.heckeDeterminantTwistEquiv_compact χ k y) hl

/-- Contragredient functionals push forward to contragredient functionals of a twist. -/
theorem isContragredientFunctional_comp_heckeDeterminantTwistEquiv_symm
    {l : Module.Dual ℂ S.Space} (hl : S.IsContragredientFunctional l) :
    (S.heckeDeterminantTwist χ).IsContragredientFunctional
      (l ∘ₗ (S.heckeDeterminantTwistEquiv χ).toLinearEquiv.symm.toLinearMap) :=
  isContragredientFunctional_comp_of_twisted _
    (fun d => ((χ.adelicDeterminant n (AdelicGL.ofFinite F n d) : ℂˣ) : ℂ)⁻¹)
    (heckeDeterminantKernel χ)
    (fun _ hd => (congrArg (·⁻¹) (adelicDeterminant_ofFinite_eq_one χ hd)).trans inv_one)
    (fun d y => twist_apply_symm (S.heckeDeterminantTwistEquiv χ).toLinearEquiv
      (S.finiteRepresentation d) ((S.heckeDeterminantTwist χ).finiteRepresentation d) _
      (Units.ne_zero _) (fun f => S.heckeDeterminantTwistEquiv_finite χ d f) y)
    (fun k => ((χ.adelicDeterminant n (AdelicGL.ofInfinite F n k.val) : ℂˣ) : ℂ)⁻¹)
    (fun _k => inv_ne_zero (Units.ne_zero _))
    (fun k y => twist_apply_symm (S.heckeDeterminantTwistEquiv χ).toLinearEquiv
      (S.compactRepresentation k) ((S.heckeDeterminantTwist χ).compactRepresentation k) _
      (Units.ne_zero _) (fun f => S.heckeDeterminantTwistEquiv_compact χ k f) y) hl

section TwistPairing

variable (B₀ : (S.heckeDeterminantTwist χ).Space →ₗ[ℂ] T.Space →ₗ[ℂ] ℂ)

/-- The pairing `B(y, x) = B₀(e y, e'⁻¹ x)` between `S` and the twist of `T`. -/
def heckeTwistPairing : S.Space →ₗ[ℂ] (T.heckeDeterminantTwist χ).Space →ₗ[ℂ] ℂ :=
  (B₀ ∘ₗ (S.heckeDeterminantTwistEquiv χ).toLinearEquiv.toLinearMap).compl₂
    (T.heckeDeterminantTwistEquiv χ).toLinearEquiv.symm.toLinearMap

theorem heckeTwistPairing_finite
    (hd : ∀ (d : FiniteAdelicGL F n) (w : (S.heckeDeterminantTwist χ).Space) (z : T.Space),
      B₀ ((S.heckeDeterminantTwist χ).finiteRepresentation d w) (T.finiteRepresentation d z) =
        B₀ w z)
    (d : FiniteAdelicGL F n) (y : S.Space) (x : (T.heckeDeterminantTwist χ).Space) :
    heckeTwistPairing χ B₀ (S.finiteRepresentation d y)
        ((T.heckeDeterminantTwist χ).finiteRepresentation d x) =
      heckeTwistPairing χ B₀ y x :=
  pairing_twisted_invariant B₀ (S.heckeDeterminantTwistEquiv χ).toLinearEquiv
    (T.heckeDeterminantTwistEquiv χ).toLinearEquiv (S.finiteRepresentation d)
    ((S.heckeDeterminantTwist χ).finiteRepresentation d) (T.finiteRepresentation d)
    ((T.heckeDeterminantTwist χ).finiteRepresentation d) _
    (fun y => S.heckeDeterminantTwistEquiv_finite χ d y)
    (fun z => T.heckeDeterminantTwistEquiv_finite χ d z) (hd d) y x

theorem heckeTwistPairing_compact
    (hk : ∀ (k : standardInfiniteCompact F n) (w : (S.heckeDeterminantTwist χ).Space)
      (z : T.Space),
      B₀ ((S.heckeDeterminantTwist χ).compactRepresentation k w) (T.compactRepresentation k z) =
        B₀ w z)
    (k : standardInfiniteCompact F n) (y : S.Space) (x : (T.heckeDeterminantTwist χ).Space) :
    heckeTwistPairing χ B₀ (S.compactRepresentation k y)
        ((T.heckeDeterminantTwist χ).compactRepresentation k x) =
      heckeTwistPairing χ B₀ y x :=
  pairing_twisted_invariant B₀ (S.heckeDeterminantTwistEquiv χ).toLinearEquiv
    (T.heckeDeterminantTwistEquiv χ).toLinearEquiv (S.compactRepresentation k)
    ((S.heckeDeterminantTwist χ).compactRepresentation k) (T.compactRepresentation k)
    ((T.heckeDeterminantTwist χ).compactRepresentation k) _
    (fun y => S.heckeDeterminantTwistEquiv_compact χ k y)
    (fun z => T.heckeDeterminantTwistEquiv_compact χ k z) (hk k) y x

theorem heckeTwistPairing_lieAction
    (hX : ∀ (X : ArchimedeanGL.RealLieAlgebra F n) (w : (S.heckeDeterminantTwist χ).Space)
      (z : T.Space),
      B₀ ((S.heckeDeterminantTwist χ).lieAction X w) z + B₀ w (T.lieAction X z) = 0)
    (X : ArchimedeanGL.RealLieAlgebra F n) (y : S.Space)
    (x : (T.heckeDeterminantTwist χ).Space) :
    heckeTwistPairing χ B₀ (S.lieAction X y) x +
        heckeTwistPairing χ B₀ y ((T.heckeDeterminantTwist χ).lieAction X x) = 0 :=
  pairing_shifted_invariant B₀ (S.heckeDeterminantTwistEquiv χ).toLinearEquiv
    (T.heckeDeterminantTwistEquiv χ).toLinearEquiv (S.lieAction X)
    ((S.heckeDeterminantTwist χ).lieAction X) (T.lieAction X)
    ((T.heckeDeterminantTwist χ).lieAction X) (heckeLieShift χ X)
    (fun y => S.lieAction_heckeDeterminantTwistEquiv χ X (heckeLieShift_spec χ X) y)
    (fun z => T.lieAction_heckeDeterminantTwistEquiv χ X (heckeLieShift_spec χ X) z) (hX X) y x

theorem heckeTwistPairing_functional
    (hB : ∀ z : T.Space, (S.heckeDeterminantTwist χ).IsContragredientFunctional (B₀.flip z))
    (x : (T.heckeDeterminantTwist χ).Space) :
    S.IsContragredientFunctional ((heckeTwistPairing χ B₀).flip x) :=
  isContragredientFunctional_comp_heckeDeterminantTwistEquiv χ
    (hB ((T.heckeDeterminantTwistEquiv χ).toLinearEquiv.symm x))

theorem heckeTwistPairing_flip_injective (hinj : Function.Injective B₀.flip) :
    Function.Injective (heckeTwistPairing χ B₀).flip :=
  pairing_flip_injective B₀ _ _ hinj

theorem heckeTwistPairing_flip_surjective
    (hsurj : ∀ l : Module.Dual ℂ (S.heckeDeterminantTwist χ).Space,
      (S.heckeDeterminantTwist χ).IsContragredientFunctional l → ∃ z, B₀.flip z = l)
    (l : Module.Dual ℂ S.Space) (hl : S.IsContragredientFunctional l) :
    ∃ x, (heckeTwistPairing χ B₀).flip x = l := by
  obtain ⟨x₀, hx₀⟩ := hsurj _
    (isContragredientFunctional_comp_heckeDeterminantTwistEquiv_symm χ hl)
  exact ⟨_, pairing_flip_surjective B₀ (S.heckeDeterminantTwistEquiv χ).toLinearEquiv
    (T.heckeDeterminantTwistEquiv χ).toLinearEquiv l x₀ hx₀⟩

end TwistPairing

/-- **Contragredients of twists.** If `T` realizes the contragredient of the twist of `S`
by `χ ∘ det`, then the twist of `T` by `χ ∘ det` realizes the contragredient of `S`. -/
theorem IsContragredientOf.of_heckeDeterminantTwist
    (h : T.IsContragredientOf (S.heckeDeterminantTwist χ)) :
    (T.heckeDeterminantTwist χ).IsContragredientOf S := by
  obtain ⟨B₀, ⟨hd, hk, hX⟩, hB, hinj, hsurj⟩ := h
  exact ⟨heckeTwistPairing χ B₀,
    ⟨heckeTwistPairing_finite χ B₀ hd, heckeTwistPairing_compact χ B₀ hk,
      heckeTwistPairing_lieAction χ B₀ hX⟩,
    heckeTwistPairing_functional χ B₀ hB, heckeTwistPairing_flip_injective χ B₀ hinj,
    heckeTwistPairing_flip_surjective χ B₀ hsurj⟩

end OperatorRealization

end Langlands.Automorphic
