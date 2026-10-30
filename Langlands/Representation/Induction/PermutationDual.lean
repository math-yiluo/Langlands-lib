import Langlands.Representation.Induction.PermutationInvariants

/-!
# Hom out of permutation modules: functions and freeness

Harris, *Galois properties of cohomological automorphic forms on GL(n)*, p.311: "The right-hand
side of (4.7) is the sum of `M` copies of the group `D_m(K_{ℓ,m} × C_p/H_p)` of `𝒪_m`-valued
functions on `K_{ℓ,m} × C_p/H_p`. Via the duality between functions and group rings, this is
canonically isomorphic to `Hom(𝒪_m[K_{ℓ,m} × C_p/H_p]^M, 𝒪_m)`", and p.312: "Since
`C^j_m(ẽ)^{H_p}` and `Hom(𝒪_m[C_p/H_p]^M, 𝓛_m)` are both free `𝒪/ℓ^m𝒪[S(ẽ)/H_p]`-modules, it
follows that the maps (4.10.3) are surjective for all `m`."

This module proves both facts for a commutative ring `R` (Harris's `𝒪_m = 𝒪/ℓ^m𝒪`), a group `G`
acting on a set `X`, and the permutation representation `permutation R G X M` on `M[X] = X →₀ M`;
the module `M` plays the role of `𝒪_m^M`.

* `functionRepresentation σ X`: the representation of `G` on all functions `X → W` with values
  in a representation `(W, σ)`, `(g • f) x = σ g (f (g⁻¹ • x))`;
* `permutationDualEquiv σ X`: the duality between functions and group rings,
  `Hom_R(R[X], W) ≃ (X → W)`, `φ ↦ (x ↦ φ (single x 1))`, as an equivalence of
  representations; `permutationHomEquiv σ X M` is the version with coefficients `M`, with values
  in `Hom_R(M, W)`;
* `functionPermutationEquiv`, `permutationHomPermutationEquiv`: for finite `X` and trivial
  actions on `M` and `W`, `Hom_R(M[X], W)` is the permutation representation on
  `Hom_R(M, W)[X]`;
* `freeActionEquiv`: for a free action, `G × X / G ≃ X`, `(g, ω) ↦ g • ω.out`;
* `permutationFreeEquiv`: for a free action and a basis of `W` indexed by `I`, the permutation
  representation on `W[X]` is the free representation `R[G]^(X / G × I)`;
* `permutation_asModule_free`, `linHom_permutation_asModule_free`: for a free action, `W[X]` is a
  free `R[G]`-module when `W` is a free `R`-module, and, when `X` is finite, `G` acts trivially on
  `M` and `W`, `M` is finite free and `W` is free, `Hom_R(M[X], W)` is a free `R[G]`-module;
* `linHom_permutation_subgroup_asModule_free`: the case of a subgroup `S` of a finite group `Q`
  acting on `Q` by left multiplication; Harris's case is `Q = C_p/H_p` and `S = S(ẽ)/H_p` when
  `H_p` is normal in `C_p`.

That `S(ẽ)/H_p` acts trivially on `𝓛_m` and freely on `C_p/H_p` is our reading of Harris's
setting; the identifications (4.7) and (4.8) of automorphic forms with these modules are not
formalized.
-/

noncomputable section

open CategoryTheory

namespace Langlands.Induction

universe uR uG uX uM uW uI

section Functions

variable {R : Type uR} {G : Type uG} {M : Type uM} {W : Type uW}
variable [CommRing R] [Group G] [AddCommGroup M] [Module R M] [AddCommGroup W] [Module R W]

/-- The representation of `G` on all functions `X → W` from a `G`-set `X` to a representation
`(W, σ)`: `(g • f) x = σ g (f (g⁻¹ • x))`. -/
def functionRepresentation (σ : Representation R G W) (X : Type uX) [MulAction G X] :
    Representation R G (X → W) where
  toFun g :=
    { toFun := fun f x => σ g (f (g⁻¹ • x))
      map_add' := fun f f' => funext fun x => map_add (σ g) (f (g⁻¹ • x)) (f' (g⁻¹ • x))
      map_smul' := fun r f => funext fun x => map_smul (σ g) r (f (g⁻¹ • x)) }
  map_one' := by
    refine LinearMap.ext fun f => funext fun x => ?_
    simp
  map_mul' g h := by
    refine LinearMap.ext fun f => funext fun x => ?_
    simp [mul_smul]

variable (σ : Representation R G W) (X : Type uX) [MulAction G X]

/-- The value of `g • f` at `x` is `σ g` applied to the value of `f` at `g⁻¹ • x`. -/
@[simp] theorem functionRepresentation_apply (g : G) (f : X → W) (x : X) :
    functionRepresentation σ X g f x = σ g (f (g⁻¹ • x)) :=
  rfl

/-- Harris's duality between functions and group rings: a linear map `R[X] → W` is determined by
its values on the basis vectors `single x 1`, and this identifies the representation of `G` on
`Hom_R(R[X], W)` with the representation on functions `X → W`. -/
def permutationDualEquiv :
    ((permutation R G X R).linHom σ).Equiv (functionRepresentation σ X) :=
  .mk (Finsupp.llift W R R X).symm fun g => by
    refine LinearMap.ext fun φ => funext fun x => ?_
    simp [Finsupp.llift_symm_apply, Representation.linHom_apply]

/-- The duality sends `φ : R[X] → W` to the function `x ↦ φ (single x 1)`. -/
theorem permutationDualEquiv_apply (φ : (X →₀ R) →ₗ[R] W) (x : X) :
    permutationDualEquiv σ X φ x = φ (Finsupp.single x 1) :=
  rfl

/-- With coefficients in a module `M`, a linear map `X →₀ M → W` is the family of its
restrictions `φ ∘ single x` to the summands; this identifies the representation of `G` on
`Hom_R(M[X], W)` with the representation on functions `X → Hom_R(M, W)`, where `G` acts on
`Hom_R(M, W)` through `W`. -/
def permutationHomEquiv (M : Type uM) [AddCommGroup M] [Module R M] :
    ((permutation R G X M).linHom σ).Equiv
      (functionRepresentation ((Representation.trivial R G M).linHom σ) X) :=
  .mk (Finsupp.lsum R).symm fun g => by
    refine LinearMap.ext fun φ => funext fun x => LinearMap.ext fun m => ?_
    simp [Finsupp.lsum_symm_apply, Representation.linHom_apply]

/-- If `G` acts trivially on `W` and `X` is finite, the representation on all functions `X → W`
is the permutation representation on `W[X]`. -/
def functionPermutationEquiv [Finite X] (hσ : ∀ g, σ g = LinearMap.id) :
    (functionRepresentation σ X).Equiv (permutation R G X W) :=
  .mk (Finsupp.linearEquivFunOnFinite R W X).symm fun g => by
    refine LinearMap.ext fun f => Finsupp.ext fun x => ?_
    simp [permutation_apply, hσ]

/-- `functionPermutationEquiv` keeps the values of a function. -/
theorem functionPermutationEquiv_apply [Finite X] (hσ : ∀ g, σ g = LinearMap.id) (f : X → W)
    (x : X) : functionPermutationEquiv σ X hσ f x = f x :=
  rfl

/-- If `G` acts trivially on `M` and `W` and `X` is finite, `Hom_R(M[X], W)` is the permutation
representation on `Hom_R(M, W)[X]`. -/
def permutationHomPermutationEquiv [Finite X] (hσ : ∀ g, σ g = LinearMap.id)
    (M : Type uM) [AddCommGroup M] [Module R M] :
    ((permutation R G X M).linHom σ).Equiv (permutation R G X (M →ₗ[R] W)) :=
  (permutationHomEquiv σ X M).trans <| functionPermutationEquiv _ X fun g =>
    LinearMap.ext fun φ => LinearMap.ext fun m => by
      simp [Representation.linHom_apply, hσ]

/-- `permutationHomPermutationEquiv` sends `φ : M[X] → W` to the family `x ↦ φ ∘ single x`. -/
theorem permutationHomPermutationEquiv_apply [Finite X] (hσ : ∀ g, σ g = LinearMap.id)
    (M : Type uM) [AddCommGroup M] [Module R M] (φ : (X →₀ M) →ₗ[R] W) (x : X) (m : M) :
    permutationHomPermutationEquiv σ X hσ M φ x m = φ (Finsupp.single x m) :=
  rfl

end Functions

section FreeAction

variable {G : Type uG} [Group G] {X : Type uX} [MulAction G X]

/-- For a free action of `G` on `X`, the bijection `G × X / G ≃ X`, `(g, ω) ↦ g • ω.out`, where
`ω.out` is a chosen point of the orbit `ω`. It is the inverse of Mathlib's
`MulAction.selfEquivOrbitsQuotientProd` with the factors swapped. -/
def freeActionEquiv (h : ∀ x : X, MulAction.stabilizer G x = ⊥) :
    G × MulAction.orbitRel.Quotient G X ≃ X :=
  (Equiv.prodComm _ _).trans (MulAction.selfEquivOrbitsQuotientProd h).symm

/-- `freeActionEquiv h (g, ω) = g • ω.out`. -/
theorem freeActionEquiv_apply (h : ∀ x : X, MulAction.stabilizer G x = ⊥)
    (p : G × MulAction.orbitRel.Quotient G X) : freeActionEquiv h p = p.1 • p.2.out :=
  rfl

/-- `freeActionEquiv` is equivariant for left multiplication on the factor `G`. -/
theorem freeActionEquiv_symm_smul (h : ∀ x : X, MulAction.stabilizer G x = ⊥) (g : G) (x : X) :
    (freeActionEquiv h).symm (g • x) =
      (g * ((freeActionEquiv h).symm x).1, ((freeActionEquiv h).symm x).2) := by
  rw [Equiv.symm_apply_eq]
  conv_lhs => rw [← (freeActionEquiv h).apply_symm_apply x]
  rw [freeActionEquiv_apply, freeActionEquiv_apply, mul_smul]

end FreeAction

section Free

variable (R : Type uR) (G : Type uG) [CommRing R] [Group G]
variable {X : Type uX} [MulAction G X] {M : Type uM} {W : Type uW}
variable [AddCommGroup M] [Module R M] [AddCommGroup W] [Module R W]

/-- A linear equivalence of coefficient modules induces an equivalence of permutation
representations. -/
def permutationCongr (X : Type uX) [MulAction G X] (e : M ≃ₗ[R] W) :
    (permutation R G X M).Equiv (permutation R G X W) :=
  .mk (Finsupp.mapRange.linearEquiv e) fun g => by
    refine Finsupp.lhom_ext fun x m => ?_
    simp

/-- For a free action of `G` on `X`, the permutation representation on `W[X]` is the permutation
representation of `G` on itself (by left multiplication) with coefficients `W[X / G]`. -/
def permutationFreeActionEquiv (h : ∀ x : X, MulAction.stabilizer G x = ⊥) :
    (permutation R G X W).Equiv (permutation R G G (MulAction.orbitRel.Quotient G X →₀ W)) :=
  .mk (Finsupp.domLCongr (freeActionEquiv h).symm ≪≫ₗ Finsupp.curryLinearEquiv R) fun g => by
    refine Finsupp.lhom_ext fun x w => ?_
    simp [freeActionEquiv_symm_smul, Finsupp.curry_single]

/-- For a free action of `G` on `X` and a basis of `W` indexed by `I`, the permutation
representation on `W[X]` is the free representation `R[G]^(X / G × I)`. -/
def permutationFreeEquiv (h : ∀ x : X, MulAction.stabilizer G x = ⊥) {I : Type uI}
    (b : Module.Basis I R W) :
    (permutation R G X W).Equiv (Representation.free R G (MulAction.orbitRel.Quotient G X × I)) :=
  (permutationFreeActionEquiv R G h).trans <|
    (permutationCongr R G G
      (Finsupp.mapRange.linearEquiv b.repr ≪≫ₗ (Finsupp.curryLinearEquiv R).symm)).trans
      (permutationFinsuppEquiv R G G _)

variable {R G}

/-- For a free action of `G` on `X` and a free `R`-module `W`, the permutation representation
on `W[X]` is a free module over the group algebra `R[G]`. -/
theorem permutation_asModule_free (h : ∀ x : X, MulAction.stabilizer G x = ⊥) [Module.Free R W] :
    Module.Free (MonoidAlgebra R G) (permutation R G X W).asModule :=
  have := Representation.free_asModule_free R G
    (MulAction.orbitRel.Quotient G X × Module.Free.ChooseBasisIndex R W)
  Module.Free.of_equiv
    (asModuleLinearEquiv (permutationFreeEquiv R G h (Module.Free.chooseBasis R W))).symm

/-- Harris's freeness of `Hom(O_m[C_p / H_p]^M, L_m)`: if `G` acts freely on a finite set `X` and
trivially on `M` and `W`, where `M` is finite free and `W` is free over `R`, then `Hom_R(M[X], W)`
is a free module over `R[G]`. -/
theorem linHom_permutation_asModule_free [Finite X] (h : ∀ x : X, MulAction.stabilizer G x = ⊥)
    [Module.Free R M] [Module.Finite R M] [Module.Free R W] :
    Module.Free (MonoidAlgebra R G)
      ((permutation R G X M).linHom (Representation.trivial R G W)).asModule :=
  have := permutation_asModule_free (R := R) (G := G) (W := M →ₗ[R] W) h
  Module.Free.of_equiv (asModuleLinearEquiv
    (permutationHomPermutationEquiv (Representation.trivial R G W) X (fun _ => rfl) M)).symm

/-- The case of Harris's proof of Prop. 4.10: for a subgroup `S` of a finite group `Q` (acting on
`Q` by left multiplication), `Hom_R(M[Q], W)` is free over `R[S]`. -/
theorem linHom_permutation_subgroup_asModule_free {Q : Type uG} [Group Q] [Finite Q]
    (S : Subgroup Q) [Module.Free R M] [Module.Finite R M] [Module.Free R W] :
    Module.Free (MonoidAlgebra R S)
      ((permutation R S Q M).linHom (Representation.trivial R S W)).asModule :=
  linHom_permutation_asModule_free IsCancelSMul.stabilizer_eq_bot

end Free

end Langlands.Induction
