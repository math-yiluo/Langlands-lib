import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.FreeModule.Basic
import Langlands.Cohomology.DivisibleSystem.ScalarExtension
import Langlands.Shimura.DefiniteForms
import Langlands.Shimura.EquivariantFormsDoubleCoset

/-!
# Base change of Harris's forms `𝒜_f(GJ, ρ, K)`

Harris, *Galois properties of cohomological automorphic forms on GL(n)*, 1999, p.307, defines for
an `L`-algebra `L'` the space (3.2) `𝒜_f(GJ, ρ, K)(L')` of functions `f : GJ(𝔸^f)/K → W(L')`
with `f (γ g) = ρ(γ) f(g)` for rational `γ`, and states: "Obviously, for any `L`-algebra `L'`,
there is a canonical isomorphism (3.4) `𝒜_f(GJ, ρ, K)(L') = 𝒜_f(GJ, ρ, K)(L) ⊗_L L'`." This file
constructs this isomorphism when the double coset space `GJ(ℚ)\GJ(𝔸^f)/K` is finite.

## Main definitions

* `EquivariantForms.rationalForms ι K τ`: for groups `Γ`, `G`, a homomorphism `ι : Γ →* G`, a
  subgroup `K` of `G` and a representation `τ` of `Γ`, the functions `f : G → V` with
  `f (ι γ * g) = τ γ (f g)` and `f (g * k) = f g`.
* `EquivariantForms.rationalFormsBaseChangeEquiv`: for an `R`-algebra `S` that is free as an
  `R`-module and finitely many double cosets `ι Γ \ G / K`,
  `S ⊗[R] rationalForms ι K τ ≃ rationalForms ι K (baseChangeRepresentation S τ)`,
  `s ⊗ f ↦ (g ↦ s ⊗ f g)`. Injectivity and surjectivity are proved with the coordinates of
  `S ⊗[R] _` in a basis of `S` (`coordinateForm`).
* `EquivariantForms.rationalFormsLidEquiv`: the forms for the base change of `τ` to `R` itself
  are the forms for `τ`.
* `DefiniteForms.rationalBaseRep σ ρ`: the action `γ ↦ ρ(γ)` of the rational points on `W`,
  whose base change to `S` is the published `rationalRep σ ρ S`
  (`rationalRep_eq_baseChangeRepresentation`); `finiteForms_eq_rationalForms`.
* `DefiniteForms.finiteFormsBaseChangeEquiv σ ρ K S`: Harris's (3.4),
  `S ⊗[L] 𝒜_f(GJ, ρ, K)(L) ≃ 𝒜_f(GJ, ρ, K)(S)` for every `L`-algebra `S`, when
  `GJ(ℚ)\GJ(𝔸^f)/K` is finite.
-/

noncomputable section

open scoped TensorProduct

namespace Langlands.Shimura.EquivariantForms

open Langlands.Cohomology

universe uR uS t uΓ uG

variable {R : Type uR} [CommRing R] {Γ : Type uΓ} {G : Type uG} [Group Γ] [Group G]
  (ι : Γ →* G) (K : Subgroup G) {V : Type t} [AddCommGroup V] [Module R V]

section RationalForms

variable (τ : Representation R Γ V)

/-- The `R`-module of functions `f : G → V` with `f (ι γ * g) = τ γ (f g)` for `γ : Γ` and
`f (g * k) = f g` for `k : K`: the functional equations of Harris's `𝒜_f(GJ, ρ, K)`
(1999, (3.2)) for an arbitrary group, level and representation `τ` of the rational points. -/
def rationalForms : Submodule R (G → V) where
  carrier := {f | (∀ (γ : Γ) (g : G), f (ι γ * g) = τ γ (f g)) ∧
    ∀ (g : G) (k : K), f (g * k) = f g}
  add_mem' {f₁ f₂} hf₁ hf₂ := ⟨fun γ g => by simp [hf₁.1 γ g, hf₂.1 γ g],
    fun g k => by simp [hf₁.2 g k, hf₂.2 g k]⟩
  zero_mem' := ⟨fun _ _ => by simp, fun _ _ => rfl⟩
  smul_mem' r f hf := ⟨fun γ g => by simp [hf.1 γ g], fun g k => by simp [hf.2 g k]⟩

variable {ι K τ} in
/-- Membership in `rationalForms` is the two functional equations. -/
lemma mem_rationalForms {f : G → V} :
    f ∈ rationalForms ι K τ ↔ (∀ (γ : Γ) (g : G), f (ι γ * g) = τ γ (f g)) ∧
      ∀ (g : G) (k : K), f (g * k) = f g :=
  Iff.rfl

/-- The published `twistedForms` for a representation `ρ` of `G` are the `rationalForms` for its
restriction `ρ.comp ι` to `Γ`. -/
lemma twistedForms_eq_rationalForms (ρ : Representation R G V) :
    twistedForms ι K ρ = rationalForms ι K (ρ.comp ι) :=
  Submodule.ext fun _ => Iff.rfl

end RationalForms

section BaseChange

variable (τ : Representation R Γ V) (S : Type uS) [CommRing S] [Algebra R S]

/-- The `R`-linear map `f ↦ (g ↦ 1 ⊗ f g)` from the forms for `τ` to the forms for its base change
`baseChangeRepresentation S τ` to `S`. -/
def rationalFormsScalar :
    rationalForms ι K τ →ₗ[R] rationalForms ι K (baseChangeRepresentation S τ) where
  toFun f := ⟨fun g => (1 : S) ⊗ₜ f.1 g, fun γ g => by
      change (1 : S) ⊗ₜ f.1 (ι γ * g) = (1 : S) ⊗ₜ τ γ (f.1 g)
      rw [f.2.1 γ g], fun g k => by
      change (1 : S) ⊗ₜ f.1 (g * k) = (1 : S) ⊗ₜ f.1 g
      rw [f.2.2 g k]⟩
  map_add' f₁ f₂ := Subtype.ext (funext fun g => TensorProduct.tmul_add _ (f₁.1 g) (f₂.1 g))
  map_smul' r f := Subtype.ext (funext fun g => TensorProduct.tmul_smul r _ (f.1 g))

/-- The `S`-linear map `S ⊗[R] rationalForms ι K τ → rationalForms ι K (baseChangeRepresentation S τ)`,
`s ⊗ f ↦ (g ↦ s ⊗ f g)`. -/
def rationalFormsBaseChange :
    S ⊗[R] rationalForms ι K τ →ₗ[S] rationalForms ι K (baseChangeRepresentation S τ) :=
  (rationalFormsScalar ι K τ S).liftBaseChange S

/-- `rationalFormsBaseChange` sends `s ⊗ f` to `g ↦ s ⊗ f g`. -/
@[simp]
lemma rationalFormsBaseChange_tmul (s : S) (f : rationalForms ι K τ) (g : G) :
    (rationalFormsBaseChange ι K τ S (s ⊗ₜ f)).1 g = s ⊗ₜ f.1 g := by
  change s • ((1 : S) ⊗ₜ[R] f.1 g) = _
  rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]

variable {S} {I : Type*} [DecidableEq I] (b : Module.Basis I R S)

/-- The coordinates of a value of `rationalFormsBaseChange x` in a basis `b` of `S` are the
values of the coordinates of `x`. -/
lemma equivFinsuppOfBasisLeft_rationalFormsBaseChange (x : S ⊗[R] rationalForms ι K τ)
    (g : G) (i : I) :
    TensorProduct.equivFinsuppOfBasisLeft b ((rationalFormsBaseChange ι K τ S x).1 g) i =
      (TensorProduct.equivFinsuppOfBasisLeft b x i).1 g := by
  induction x using TensorProduct.inductionOn with
  | tmul s f =>
    rw [rationalFormsBaseChange_tmul, TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply,
      TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply]
    rfl
  | add x y hx hy =>
    rw [map_add, Submodule.coe_add, Pi.add_apply, map_add, Finsupp.add_apply, hx, hy, map_add,
      Finsupp.add_apply]
    rfl

/-- The coordinates in a basis `b` of `S` commute with the base change of `τ γ`. -/
lemma equivFinsuppOfBasisLeft_baseChange (γ : Γ) (y : S ⊗[R] V) (i : I) :
    TensorProduct.equivFinsuppOfBasisLeft b (baseChangeRepresentation S τ γ y) i =
      τ γ (TensorProduct.equivFinsuppOfBasisLeft b y i) := by
  induction y using TensorProduct.inductionOn with
  | tmul s v =>
    rw [baseChangeRepresentation_apply_tmul,
      TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply,
      TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply, map_smul]
  | add x y hx hy => rw [map_add, map_add, Finsupp.add_apply, hx, hy, map_add, Finsupp.add_apply,
      map_add]

variable {τ} in
/-- The `i`-th coordinate in the basis `b` of a form for the base change of `τ` is a form for
`τ`. -/
def coordinateForm (F : rationalForms ι K (baseChangeRepresentation S τ)) (i : I) :
    rationalForms ι K τ :=
  ⟨fun g => TensorProduct.equivFinsuppOfBasisLeft b (F.1 g) i, fun γ g => by
      change TensorProduct.equivFinsuppOfBasisLeft b (F.1 (ι γ * g)) i = _
      rw [F.2.1 γ g, equivFinsuppOfBasisLeft_baseChange], fun g k => by
      change TensorProduct.equivFinsuppOfBasisLeft b (F.1 (g * k)) i = _
      rw [F.2.2 g k]⟩

/-- The values of `coordinateForm b F i` are the `i`-th coordinates of the values of `F`. -/
@[simp]
lemma coordinateForm_apply (F : rationalForms ι K (baseChangeRepresentation S τ)) (i : I)
    (g : G) :
    (coordinateForm ι K b F i).1 g = TensorProduct.equivFinsuppOfBasisLeft b (F.1 g) i :=
  rfl

variable [Finite (DoubleCosets ι K)]

variable {τ} in
/-- For finitely many double cosets `ι Γ \ G / K`, only finitely many coordinates of a form for
the base change of `τ` are nonzero. -/
lemma finite_support_coordinateForm (F : rationalForms ι K (baseChangeRepresentation S τ)) :
    ∃ T : Finset I, ∀ i, coordinateForm ι K b F i ≠ 0 → i ∈ T := by
  classical
  have := Fintype.ofFinite (DoubleCosets ι K)
  refine ⟨Finset.univ.biUnion fun x : DoubleCosets ι K =>
    (TensorProduct.equivFinsuppOfBasisLeft b (F.1 x.out)).support, fun i hi => ?_⟩
  by_contra hT
  apply hi
  refine Subtype.ext (funext fun g => ?_)
  obtain ⟨γ, k, hg⟩ := exists_eq_mul_out_mul (ι := ι) (K := K) g
  have h0 : TensorProduct.equivFinsuppOfBasisLeft b
      (F.1 (DoubleCoset.mk ι.range K g).out) i = 0 := by
    by_contra h
    exact hT (Finset.mem_biUnion.2 ⟨_, Finset.mem_univ _, Finsupp.mem_support_iff.2 h⟩)
  change TensorProduct.equivFinsuppOfBasisLeft b (F.1 g) i = 0
  rw [hg, F.2.2, F.2.1, equivFinsuppOfBasisLeft_baseChange, h0, map_zero]

variable [Module.Free R S]

omit [Finite (DoubleCosets ι K)] in
/-- For free `S`, `rationalFormsBaseChange` is injective: the coordinates of `x` in a basis of
`S` are read off from the values of its image. -/
lemma rationalFormsBaseChange_injective :
    Function.Injective (rationalFormsBaseChange ι K τ S) := by
  classical
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  let b := Module.Free.chooseBasis R S
  apply (TensorProduct.equivFinsuppOfBasisLeft b).injective
  rw [map_zero]
  refine Finsupp.ext fun i => Subtype.ext (funext fun g => ?_)
  rw [← equivFinsuppOfBasisLeft_rationalFormsBaseChange, hx]
  simp

/-- For free `S` and finitely many double cosets, `rationalFormsBaseChange` is surjective: a
form is the image of the finite sum of its coordinate forms. -/
lemma rationalFormsBaseChange_surjective :
    Function.Surjective (rationalFormsBaseChange ι K τ S) := by
  classical
  intro F
  let b := Module.Free.chooseBasis R S
  obtain ⟨T, hT⟩ := finite_support_coordinateForm ι K b F
  refine ⟨(TensorProduct.equivFinsuppOfBasisLeft b).symm
    (Finsupp.onFinset T (coordinateForm ι K b F) hT), Subtype.ext (funext fun g => ?_)⟩
  apply (TensorProduct.equivFinsuppOfBasisLeft b).injective
  refine Finsupp.ext fun i => ?_
  rw [equivFinsuppOfBasisLeft_rationalFormsBaseChange, LinearEquiv.apply_symm_apply,
    Finsupp.onFinset_apply, coordinateForm_apply]

/-- For an `R`-algebra `S` that is free as an `R`-module and finitely many double cosets
`ι Γ \ G / K`, the forms for the base change of `τ` to `S` are the base change of the forms for
`τ`: `S ⊗[R] rationalForms ι K τ ≃ rationalForms ι K (baseChangeRepresentation S τ)`,
`s ⊗ f ↦ (g ↦ s ⊗ f g)` (`rationalFormsBaseChangeEquiv_tmul`). -/
def rationalFormsBaseChangeEquiv :
    S ⊗[R] rationalForms ι K τ ≃ₗ[S] rationalForms ι K (baseChangeRepresentation S τ) :=
  LinearEquiv.ofBijective (rationalFormsBaseChange ι K τ S)
    ⟨rationalFormsBaseChange_injective ι K τ, rationalFormsBaseChange_surjective ι K τ⟩

/-- `rationalFormsBaseChangeEquiv` sends `s ⊗ f` to `g ↦ s ⊗ f g`. -/
@[simp]
lemma rationalFormsBaseChangeEquiv_tmul (s : S) (f : rationalForms ι K τ) (g : G) :
    (rationalFormsBaseChangeEquiv ι K τ (s ⊗ₜ f)).1 g = s ⊗ₜ f.1 g :=
  rationalFormsBaseChange_tmul ι K τ S s f g

end BaseChange

section Lid

variable (τ : Representation R Γ V)

/-- `TensorProduct.lid` intertwines the base change of `τ` to `R` with `τ`. -/
lemma lid_baseChangeRepresentation (γ : Γ) (y : R ⊗[R] V) :
    TensorProduct.lid R V (baseChangeRepresentation R τ γ y) = τ γ (TensorProduct.lid R V y) := by
  induction y using TensorProduct.inductionOn with
  | tmul r v => rw [baseChangeRepresentation_apply_tmul, TensorProduct.lid_tmul,
      TensorProduct.lid_tmul, map_smul]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

/-- For the base change of `τ` to `R` itself, `R ⊗[R] V ≃ V` (`TensorProduct.lid`) identifies the
forms for `baseChangeRepresentation R τ` with the forms for `τ`. -/
def rationalFormsLidEquiv :
    rationalForms ι K (baseChangeRepresentation R τ) ≃ₗ[R] rationalForms ι K τ where
  toFun f := ⟨fun g => TensorProduct.lid R V (f.1 g), fun γ g => by
      change TensorProduct.lid R V (f.1 (ι γ * g)) = _
      rw [f.2.1 γ g, lid_baseChangeRepresentation], fun g k => by
      change TensorProduct.lid R V (f.1 (g * k)) = _
      rw [f.2.2 g k]⟩
  invFun f := rationalFormsScalar ι K τ R f
  map_add' f₁ f₂ := Subtype.ext (funext fun g => map_add _ (f₁.1 g) (f₂.1 g))
  map_smul' r f := Subtype.ext (funext fun g => map_smul _ r (f.1 g))
  left_inv f := Subtype.ext (funext fun g => (TensorProduct.lid R V).symm_apply_apply (f.1 g))
  right_inv f := Subtype.ext (funext fun g => (TensorProduct.lid R V).apply_symm_apply (f.1 g))

/-- `rationalFormsLidEquiv` applies `TensorProduct.lid` to the values. -/
@[simp]
lemma rationalFormsLidEquiv_apply_coe (f : rationalForms ι K (baseChangeRepresentation R τ))
    (g : G) : (rationalFormsLidEquiv ι K τ f).1 g = TensorProduct.lid R V (f.1 g) :=
  rfl

end Lid

end Langlands.Shimura.EquivariantForms

namespace Langlands.Shimura.DefiniteForms

open Langlands.Global Langlands.Shimura.EquivariantForms Langlands.Cohomology

universe u v w uS

variable {A : Type v} [Ring A] [Algebra ℚ A] (σ : AlgebraInvolution ℚ A)
  {L : Type u} [Field L] [Algebra ℚ L] {W : Type w} [AddCommGroup W] [Module L W]
  (ρ : (σ.baseChange L).AlgebraicRepresentation W)

/-- The action `γ ↦ ρ(γ)` of the rational points of the similitude group on `W` itself; its
base change to an `L`-algebra `S` is the published `rationalRep σ ρ S`. -/
def rationalBaseRep : Representation L σ.similitudes W :=
  LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp
    (ρ.rationalAction.comp (σ.diagonalPoints L))

/-- The published `rationalRep σ ρ S` is the base change of `rationalBaseRep σ ρ` to `S`. -/
lemma rationalRep_eq_baseChangeRepresentation (S : Type uS) [CommRing S] [Algebra L S] :
    rationalRep σ ρ S = baseChangeRepresentation S (rationalBaseRep σ ρ) :=
  rfl

variable (K : Subgroup σ.FiniteAdelicPoints)

/-- `𝒜_f(GJ, ρ, K)(S)` is the generic `rationalForms` for the base change of `rationalBaseRep`. -/
lemma finiteForms_eq_rationalForms (S : Type uS) [CommRing S] [Algebra L S] :
    finiteForms σ ρ S K =
      rationalForms σ.finiteAdelicDiagonal K (baseChangeRepresentation S (rationalBaseRep σ ρ)) :=
  Submodule.ext fun _ => Iff.rfl

/-- `𝒜_f(GJ, ρ, K)(L)`, with values in `L ⊗[L] W`, as the `W`-valued forms for
`rationalBaseRep σ ρ`. -/
def finiteFormsBaseEquiv :
    finiteForms σ ρ L K ≃ₗ[L] rationalForms σ.finiteAdelicDiagonal K (rationalBaseRep σ ρ) :=
  (LinearEquiv.ofEq _ _ (finiteForms_eq_rationalForms σ ρ K L)).trans
    (rationalFormsLidEquiv σ.finiteAdelicDiagonal K (rationalBaseRep σ ρ))

variable [Finite (DoubleCosets σ.finiteAdelicDiagonal K)] (S : Type uS) [CommRing S]
  [Algebra L S]

/-- Harris's base change isomorphism (1999, (3.4)) `𝒜_f(GJ, ρ, K)(L') = 𝒜_f(GJ, ρ, K)(L) ⊗ L'`
for an `L`-algebra `S` (Harris's `L'`), when `GJ(ℚ)\GJ(𝔸^f)/K` is finite:
`S ⊗[L] 𝒜_f(GJ, ρ, K)(L) ≃ 𝒜_f(GJ, ρ, K)(S)`, `s ⊗ f ↦ (g ↦ s ⊗ f g)` with `f g` read in `W`
(`finiteFormsBaseChangeEquiv_tmul`). -/
def finiteFormsBaseChangeEquiv : S ⊗[L] finiteForms σ ρ L K ≃ₗ[S] finiteForms σ ρ S K :=
  ((LinearEquiv.baseChange L S _ _ (finiteFormsBaseEquiv σ ρ K)).trans
    (rationalFormsBaseChangeEquiv σ.finiteAdelicDiagonal K (rationalBaseRep σ ρ))).trans
    (LinearEquiv.ofEq _ _ (finiteForms_eq_rationalForms σ ρ K S).symm)

/-- `finiteFormsBaseChangeEquiv` sends `s ⊗ f` to `g ↦ s ⊗ f g`, with `f g ∈ L ⊗[L] W` read in
`W` by `TensorProduct.lid`. -/
lemma finiteFormsBaseChangeEquiv_tmul (s : S) (f : finiteForms σ ρ L K)
    (g : σ.FiniteAdelicPoints) :
    (finiteFormsBaseChangeEquiv σ ρ K S (s ⊗ₜ f)).1 g = s ⊗ₜ TensorProduct.lid L W (f.1 g) :=
  rationalFormsBaseChange_tmul _ K _ S s _ g

end Langlands.Shimura.DefiniteForms
