import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.LocallyConstant.Algebra
import Langlands.Cohomology.DivisibleSystem.RegularFreeLimit
import Langlands.Shimura.DefiniteFormsDoubleCoset
import Langlands.Shimura.EquivariantFormsTensor

/-!
# Harris's function modules `D_m(K_ℓ)` and `D_m(K_{ℓ,n})`

This file formalizes the function modules of Harris, *Galois properties of cohomological
automorphic forms on GL(n)*, 1999, p. 308: the module `D_m(K_ℓ) = C(K_ℓ, 𝒪/ℓ^m𝒪)` of
continuous `𝒪/ℓ^m𝒪`-valued functions on `K_ℓ`, with `K_ℓ` acting by right translation, the
form (3.10) of the restriction to double cosets, the observation that the right-hand side of
(3.10) is a sum of copies of `D_m(K_{ℓ,n})`, and the tautological identification (3.11).

We replace `𝒪/ℓ^m𝒪` by a commutative ring `R` and allow values in an `R`-module `M`. Since
Harris's coefficients are discrete, his continuous functions are the locally constant ones.

## Main definitions

* `FunctionModule.rightRegular R G M`: the representation of a topological group `G` on the
  locally constant functions `G → M` by right translation, `(g • f)(x) = f (x * g)`;
  `FunctionModule.rightRegularEquivRegular` identifies it, by `f ↦ (x ↦ f x⁻¹)`, with the
  Library's `Langlands.Induction.regularRepresentation` (left translation).
* `FunctionModule.functionRightRep ρ`, `FunctionModule.functionRightRegular R Q M`: the
  representations of a group `Q` on the functions `Q → V`, `(g • F)(x) = ρ g (F (x * g))`, and
  on the functions `Q → M` by right translation; `FunctionModule.functionInvEquiv` identifies the
  latter, for `Q = G ⧸ H`, with the Library's `functionRepresentation` (left translation of the
  argument).
* `FunctionModule.invariantsEquiv hH`, `FunctionModule.quotientInvariantsEquiv hH`: for an
  open normal subgroup `H` of `G`, the `H`-invariant locally constant functions on `G` are the
  functions on `G ⧸ H`, `f ↦ ([y] ↦ f y)`, as representations of `G` and of `G ⧸ H`, both acting
  by right translation.
* `FunctionModule.rightRegularPi R G M X`, `FunctionModule.rightRegularPiEquiv`: for a finite type
  `X`, the locally constant functions `G → (X → M)` are `X` copies of the locally constant
  functions `G → M`.
* `FunctionModule.inducedFunctions ρ`, `FunctionModule.tautologicalEquiv ρ`: Harris's (3.11) for a
  finite group `Q` and a representation `ρ` of `Q` on `V`: the functions `f : Q → V` with
  `f k = ρ(k)⁻¹ f(1)` are the `Q`-invariants of `(Q → R) ⊗ V`, with `Q` acting by right
  translation on `Q → R`.
* `DefiniteForms.functionModuleRep σ ℓ K R M`, `DefiniteForms.functionModuleForms σ ℓ K R M`:
  Harris's `D_m(K_ℓ)` for the local level `K_ℓ` of `Langlands.Shimura.DefiniteFormsDoubleCoset`,
  and the forms `𝒜_ℓ(GJ, D_m(K_ℓ), K)` defined by analogy with (3.7).
* `DefiniteForms.congruenceFunctionEquiv σ ℓ R H h hH`: Harris's (3.10), under (3.6): the forms
  of level `K(n)` with trivial coefficients are the `K_ℓ(n)`-invariants of `D(K_ℓ)` with values in
  the functions on the double cosets `GJ(ℚ)\GJ(𝔸^f)/K`.
* `DefiniteForms.congruencePiEquiv σ ℓ R H h hH`: Harris's (3.10) as printed, with
  `[D(K_ℓ)^N]^{K_ℓ(n)}`, for finitely many double cosets.
-/

noncomputable section

open scoped TensorProduct

namespace Langlands.Shimura.FunctionModule

universe uR uG uM uV

section Group

variable {R : Type uR} [CommRing R] {Q : Type uG} [Group Q] {V : Type uV} [AddCommGroup V]
  [Module R V]

/-- The representation of a group `Q` on the functions `Q → V` by right translation and `ρ`,
`(g • F)(x) = ρ g (F (x * g))`. -/
def functionRightRep (ρ : Representation R Q V) : Representation R Q (Q → V) where
  toFun g := (ρ g).compLeft Q ∘ₗ LinearMap.funLeft R V (· * g)
  map_one' := by
    refine LinearMap.ext fun F => funext fun x => ?_
    change ρ 1 (F (x * 1)) = F x
    rw [mul_one, map_one, Module.End.one_apply]
  map_mul' g h := by
    refine LinearMap.ext fun F => funext fun x => ?_
    change ρ (g * h) (F (x * (g * h))) = ρ g (ρ h (F (x * g * h)))
    rw [mul_assoc, map_mul, Module.End.mul_apply]

@[simp]
lemma functionRightRep_apply (ρ : Representation R Q V) (g : Q) (F : Q → V) (x : Q) :
    functionRightRep ρ g F x = ρ g (F (x * g)) :=
  rfl

variable (R Q) (M : Type uM) [AddCommGroup M] [Module R M]

/-- The representation of a group `Q` on the functions `Q → M` by right translation,
`(g • φ)(x) = φ (x * g)`. -/
abbrev functionRightRegular : Representation R Q (Q → M) :=
  functionRightRep (Representation.trivial R Q M)

lemma functionRightRegular_apply (g : Q) (φ : Q → M) (x : Q) :
    functionRightRegular R Q M g φ x = φ (x * g) :=
  rfl

variable {Q} {G : Type uG} [Group G] (H : Subgroup G) [H.Normal]

/-- For a normal subgroup `H` of `G`, inversion `φ ↦ (q ↦ φ q⁻¹)` identifies the functions on
`G ⧸ H` with `G` acting by left translation of the argument with the functions on `G ⧸ H` with
`G` acting through `G ⧸ H` by right translation. -/
def functionInvEquiv :
    Representation.Equiv
      (Langlands.Induction.functionRepresentation (Representation.trivial R G M) (G ⧸ H))
      ((functionRightRegular R (G ⧸ H) M).comp (QuotientGroup.mk' H)) :=
  .mk (LinearEquiv.funCongrLeft R M (Equiv.inv (G ⧸ H))) fun g => by
    refine LinearMap.ext fun φ => funext fun q => ?_
    induction q using QuotientGroup.induction_on with
    | H y =>
      change φ (g⁻¹ • ((y : G ⧸ H))⁻¹) = φ (((y : G ⧸ H) * (g : G ⧸ H))⁻¹)
      rw [← QuotientGroup.mk_inv, MulAction.Quotient.smul_mk, ← QuotientGroup.mk_mul,
        ← QuotientGroup.mk_inv, mul_inv_rev, smul_eq_mul]

@[simp]
lemma functionInvEquiv_apply (φ : G ⧸ H → M) (q : G ⧸ H) :
    functionInvEquiv R M H φ q = φ q⁻¹ :=
  rfl

end Group

section LocallyConstant

variable (R : Type uR) [CommRing R] (G : Type uG) [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] (M : Type uM) [AddCommGroup M] [Module R M]

/-- Harris's `D_m(K_ℓ)` for a topological group `G` and an `R`-module `M`: the representation
of `G` on the locally constant functions `G → M` by right translation,
`(g • f)(x) = f (x * g)`. -/
def rightRegular : Representation R G (LocallyConstant G M) where
  toFun g := LocallyConstant.comapₗ R ⟨fun x => x * g, continuous_mul_const g⟩
  map_one' := by
    refine LinearMap.ext fun f => LocallyConstant.ext fun x => ?_
    change f (x * 1) = f x
    rw [mul_one]
  map_mul' g h := by
    refine LinearMap.ext fun f => LocallyConstant.ext fun x => ?_
    change f (x * (g * h)) = f (x * g * h)
    rw [mul_assoc]

variable {R G M}

@[simp]
lemma rightRegular_apply (g : G) (f : LocallyConstant G M) (x : G) :
    rightRegular R G M g f x = f (x * g) :=
  rfl

/-- Inversion `f ↦ (x ↦ f x⁻¹)` identifies the right regular representation with the Library's
`regularRepresentation`, on which `G` acts by left translation, `(g • f)(x) = f (g⁻¹ * x)`. -/
def rightRegularEquivRegular :
    Representation.Equiv (rightRegular R G M) (Langlands.Induction.regularRepresentation R M) :=
  .mk
    { LocallyConstant.comapₗ R ⟨fun x : G => x⁻¹, continuous_inv⟩ with
      invFun := LocallyConstant.comapₗ R ⟨fun x : G => x⁻¹, continuous_inv⟩
      left_inv := fun f => LocallyConstant.ext fun x => congrArg f (inv_inv x)
      right_inv := fun f => LocallyConstant.ext fun x => congrArg f (inv_inv x) }
    fun g => LinearMap.ext fun f => LocallyConstant.ext fun x => by
      change f (x⁻¹ * g) = f (g⁻¹ * x)⁻¹
      rw [mul_inv_rev, inv_inv]

@[simp]
lemma rightRegularEquivRegular_apply (f : LocallyConstant G M) (x : G) :
    rightRegularEquivRegular (R := R) f x = f x⁻¹ :=
  rfl

variable (H : Subgroup G)

lemma apply_mul_of_mem_invariants {f : LocallyConstant G M}
    (hf : f ∈ Representation.invariants ((rightRegular R G M).comp H.subtype)) (x : G) {h : G}
    (hh : h ∈ H) : f (x * h) = f x :=
  congrArg (fun φ : LocallyConstant G M => φ x) (hf ⟨h, hh⟩)

/-- An `H`-invariant locally constant function `f`, as the function `[y] ↦ f y` on `G ⧸ H`. -/
def invariantsDescend
    (f : Representation.invariants ((rightRegular R G M).comp H.subtype)) : G ⧸ H → M :=
  fun q => Quotient.liftOn' q (fun y => f.1 y) fun y z hyz => by
    have hz : z = y * (y⁻¹ * z) := by group
    change f.1 y = f.1 z
    rw [hz, apply_mul_of_mem_invariants H f.2 _ (QuotientGroup.leftRel_apply.mp hyz)]

@[simp]
lemma invariantsDescend_mk
    (f : Representation.invariants ((rightRegular R G M).comp H.subtype)) (y : G) :
    invariantsDescend H f (QuotientGroup.mk y) = f.1 y :=
  rfl

variable {H} (hH : IsOpen (H : Set G))

include hH in
/-- A function `φ` on `G ⧸ H`, for `H` open, as the `H`-invariant locally constant function
`y ↦ φ [y]` on `G`. -/
def invariantsPullback (φ : G ⧸ H → M) :
    Representation.invariants ((rightRegular R G M).comp H.subtype) :=
  haveI := QuotientGroup.discreteTopology hH
  ⟨⟨fun y => φ (QuotientGroup.mk y),
    (IsLocallyConstant.of_discrete φ).comp_continuous continuous_quot_mk⟩,
    fun h => LocallyConstant.ext fun x => by
      change φ (QuotientGroup.mk (x * (h : G))) = φ (QuotientGroup.mk x)
      rw [QuotientGroup.mk_mul_of_mem x h.2]⟩

@[simp]
lemma invariantsPullback_apply (φ : G ⧸ H → M) (y : G) :
    (invariantsPullback (R := R) hH φ).1 y = φ (QuotientGroup.mk y) :=
  rfl

variable [H.Normal]

include hH in
/-- For an open normal subgroup `H` of `G`, the `H`-invariants of the right regular
representation on the locally constant functions `G → M` are the functions on `G ⧸ H` with
values in `M`, with `G` acting through `G ⧸ H` by right translation. A function `f` goes to
`[y] ↦ f y`. -/
def invariantsEquiv :
    Representation.Equiv ((rightRegular R G M).toInvariants H)
      ((functionRightRegular R (G ⧸ H) M).comp (QuotientGroup.mk' H)) :=
  .mk
    { toFun := invariantsDescend H
      map_add' := fun f g => funext fun q => Quotient.inductionOn' q fun _ => rfl
      map_smul' := fun r f => funext fun q => Quotient.inductionOn' q fun _ => rfl
      invFun := invariantsPullback hH
      left_inv := fun f => Subtype.ext (LocallyConstant.ext fun _ => rfl)
      right_inv := fun φ => funext fun q => Quotient.inductionOn' q fun _ => rfl }
    fun g => by
      refine LinearMap.ext fun f => funext fun q => ?_
      induction q using QuotientGroup.induction_on with
      | H y => rfl

@[simp]
lemma invariantsEquiv_apply_mk
    (f : Representation.invariants ((rightRegular R G M).comp H.subtype)) (y : G) :
    invariantsEquiv hH f (QuotientGroup.mk y) = f.1 y :=
  rfl

@[simp]
lemma invariantsEquiv_symm_apply (φ : G ⧸ H → M) (y : G) :
    ((invariantsEquiv (R := R) hH).symm φ).1 y = φ (QuotientGroup.mk y) :=
  rfl

include hH in
/-- `invariantsEquiv` as an equivalence of representations of `G ⧸ H`: the `H`-invariants of
the right regular representation on the locally constant functions `G → M` are the functions
on `G ⧸ H` with values in `M`, with `G ⧸ H` acting by right translation. -/
def quotientInvariantsEquiv :
    Representation.Equiv ((rightRegular R G M).quotientToInvariants H)
      (functionRightRegular R (G ⧸ H) M) :=
  .mk (invariantsEquiv hH).toLinearEquiv fun q => by
    induction q using QuotientGroup.induction_on with
    | H g =>
      refine LinearMap.ext fun f => funext fun q => ?_
      induction q using QuotientGroup.induction_on with
      | H y => rfl

variable (R G M) (X : Type*)

/-- `X` copies of `rightRegular R G M`: the representation of `G` on the families
`X → LocallyConstant G M` by right translation in each coordinate. -/
def rightRegularPi : Representation R G (X → LocallyConstant G M) where
  toFun g := (rightRegular R G M g).compLeft X
  map_one' := by
    refine LinearMap.ext fun F => funext fun x => ?_
    change rightRegular R G M 1 (F x) = F x
    rw [map_one, Module.End.one_apply]
  map_mul' g h := by
    refine LinearMap.ext fun F => funext fun x => ?_
    change rightRegular R G M (g * h) (F x) = rightRegular R G M g (rightRegular R G M h (F x))
    rw [map_mul, Module.End.mul_apply]

@[simp]
lemma rightRegularPi_apply (g : G) (F : X → LocallyConstant G M) (x : X) :
    rightRegularPi R G M X g F x = rightRegular R G M g (F x) :=
  rfl

variable [Finite X]

/-- For a finite type `X`, the locally constant functions `G → (X → M)` are the families of
`X` locally constant functions `G → M` (Mathlib's `LocallyConstant.flip`), compatibly with right
translation. -/
def rightRegularPiEquiv :
    Representation.Equiv (rightRegular R G (X → M)) (rightRegularPi R G M X) :=
  .mk
    { toFun := LocallyConstant.flip
      map_add' := fun _ _ => funext fun _ => LocallyConstant.ext fun _ => rfl
      map_smul' := fun _ _ => funext fun _ => LocallyConstant.ext fun _ => rfl
      invFun := LocallyConstant.unflip
      left_inv := LocallyConstant.unflip_flip
      right_inv := LocallyConstant.flip_unflip }
    fun _ => LinearMap.ext fun _ => funext fun _ => LocallyConstant.ext fun _ => rfl

@[simp]
lemma rightRegularPiEquiv_apply (f : LocallyConstant G (X → M)) (x : X) (y : G) :
    rightRegularPiEquiv R G M X f x y = f y x :=
  rfl

end LocallyConstant

section Finite

variable {R : Type uR} [CommRing R] {Q : Type uG} [Group Q] {V : Type uV} [AddCommGroup V]
  [Module R V] (ρ : Representation R Q V)

/-- Harris's left-hand side of (3.11): the functions `f : Q → V` with `f k = ρ(k)⁻¹ f(1)`. -/
def inducedFunctions : Submodule R (Q → V) where
  carrier := {f | ∀ k, f k = ρ k⁻¹ (f 1)}
  add_mem' {f f'} hf hf' k := by
    change (f + f') k = ρ k⁻¹ ((f + f') 1)
    rw [Pi.add_apply, Pi.add_apply, hf k, hf' k, map_add]
  zero_mem' k := by simp
  smul_mem' r f hf k := by
    change (r • f) k = ρ k⁻¹ ((r • f) 1)
    rw [Pi.smul_apply, Pi.smul_apply, hf k, map_smul]

lemma mem_inducedFunctions {f : Q → V} : f ∈ inducedFunctions ρ ↔ ∀ k, f k = ρ k⁻¹ (f 1) :=
  Iff.rfl

/-- The invariants of `functionRightRep ρ` are the functions with `f k = ρ(k)⁻¹ f(1)`. -/
lemma invariants_functionRightRep : (functionRightRep ρ).invariants = inducedFunctions ρ := by
  ext F
  rw [Representation.mem_invariants, mem_inducedFunctions]
  constructor
  · intro hF k
    have h1 := congrFun (hF k) 1
    rw [functionRightRep_apply, one_mul] at h1
    rw [← h1, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  · intro hF g
    refine funext fun x => ?_
    rw [functionRightRep_apply, hF (x * g), hF x, mul_inv_rev, map_mul, Module.End.mul_apply,
      ← Module.End.mul_apply (ρ g), ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

variable [Finite Q]

/-- For a finite group `Q`, the tensor product of the functions `Q → R` (right translation) with
`V` is the representation on the functions `Q → V`: `φ ⊗ v ↦ (x ↦ φ x • v)`. -/
def tensorFunctionEquiv :
    Representation.Equiv ((functionRightRegular R Q R).tprod ρ) (functionRightRep ρ) :=
  haveI := Fintype.ofFinite Q
  open scoped Classical in
  .mk ((TensorProduct.comm R (Q → R) V).trans (TensorProduct.piScalarRight R R V Q)) fun g => by
    refine TensorProduct.ext' fun φ v => funext fun x => ?_
    simp

lemma tensorFunctionEquiv_tmul (φ : Q → R) (v : V) (x : Q) :
    tensorFunctionEquiv ρ (φ ⊗ₜ v) x = φ x • v := by
  simp [tensorFunctionEquiv]

/-- Harris's tautological identification (1999, (3.11)) for a finite group `Q` (Harris's
`K_{ℓ,n}`) and a representation `ρ` of `Q` on `V` (Harris's `𝓛`): the functions `f : Q → V`
with `f k = ρ(k)⁻¹ f(1)` are the `Q`-invariants of the tensor product of the functions `Q → R`
(Harris's `D_m(K_{ℓ,n})`, with `Q` acting by right translation) with `V`. -/
def tautologicalEquiv :
    inducedFunctions ρ ≃ₗ[R] ((functionRightRegular R Q R).tprod ρ).invariants :=
  (LinearEquiv.ofEq _ _ (invariants_functionRightRep ρ).symm).trans
    (EquivariantForms.invariantsEquivOfEquiv (tensorFunctionEquiv ρ).symm)

lemma tautologicalEquiv_symm_apply (t : ((functionRightRegular R Q R).tprod ρ).invariants)
    (k : Q) : ((tautologicalEquiv ρ).symm t).1 k = tensorFunctionEquiv ρ t.1 k :=
  rfl

end Finite

end Langlands.Shimura.FunctionModule

namespace Langlands.Shimura.DefiniteForms

open Langlands.Global Langlands.Shimura.EquivariantForms Langlands.Cohomology.HyperextAbutment

universe v t uR

variable {A : Type v} [Ring A] [Algebra ℚ A] (σ : AlgebraInvolution ℚ A) [Module.Finite ℚ A]
  (ℓ : FinitePlace ℚ)

section Functions

variable (K : Subgroup σ.FiniteAdelicPoints) (R : Type uR) [CommRing R] (M : Type t)
  [AddCommGroup M] [Module R M]

/-- Harris's `D_m(K_ℓ)` with values in `M`: the representation of the local level `K_ℓ` on the
locally constant functions `K_ℓ → M` by right translation. -/
abbrev functionModuleRep :
    Representation R (localLevel σ ℓ K) (LocallyConstant (localLevel σ ℓ K) M) :=
  FunctionModule.rightRegular R (localLevel σ ℓ K) M

/-- Harris's `𝒜_ℓ(GJ, D_m(K_ℓ), K)`, defined by analogy with (3.7). -/
abbrev functionModuleForms :
    Submodule R (σ.FiniteAdelicPoints → LocallyConstant (localLevel σ ℓ K) M) :=
  ellModuleForms σ ℓ K (functionModuleRep σ ℓ K R M)

variable {K} (H : Subgroup (localLevel σ ℓ K)) [H.Normal]

/-- Harris's restriction to double cosets (1999, (3.10)), under the hypothesis (3.6), for an
open normal subgroup `H` of `K_ℓ` (Harris's `K_ℓ(n)`): the forms of level `K(n)` with
trivial coefficients `R`, with `K` acting by right translation (`levelAction`), are the
`H`-invariants of `D(K_ℓ)` with values in the functions on the double cosets
`GJ(ℚ)\GJ(𝔸^f)/K`, with `K` acting through `k ↦ k_ℓ`. A form `f` goes to the function
`k_ℓ ↦ (x ↦ f (x.out * k))` (`congruenceFunctionEquiv_apply`). -/
def congruenceFunctionEquiv (h : LocalLevelFree σ ℓ K)
    (hH : IsOpen (H : Set (localLevel σ ℓ K))) :
    Representation.Equiv
      (levelAction σ.finiteAdelicDiagonal (Representation.trivial R K R)
        (congruenceLevel_le σ ℓ K H))
      (((functionModuleRep σ ℓ K R (DoubleCosets σ.finiteAdelicDiagonal K → R)).toInvariants
        H).comp (localLevelMap σ ℓ K)) :=
  ((congruenceLevelEquiv σ ℓ H h).trans
    (equivComp (FunctionModule.functionInvEquiv R (DoubleCosets σ.finiteAdelicDiagonal K → R) H)
      (localLevelMap σ ℓ K))).trans
    (equivComp (FunctionModule.invariantsEquiv (R := R) hH).symm (localLevelMap σ ℓ K))

lemma congruenceFunctionEquiv_apply (h : LocalLevelFree σ ℓ K)
    (hH : IsOpen (H : Set (localLevel σ ℓ K)))
    (f : forms σ.finiteAdelicDiagonal (congruenceLevel σ ℓ K H)
      ((Representation.trivial R K R).comp (Subgroup.inclusion (congruenceLevel_le σ ℓ K H))))
    (k : K) (x : DoubleCosets σ.finiteAdelicDiagonal K) :
    (congruenceFunctionEquiv σ ℓ R H h hH f).1 (localLevelMap σ ℓ K k) x =
      f.1 (x.out * (k : σ.FiniteAdelicPoints)) := by
  change congruenceLevelEquiv σ ℓ H h f
    ((localLevelMap σ ℓ K k : localLevel σ ℓ K ⧸ H))⁻¹ x = _
  rw [← QuotientGroup.mk_inv, ← map_inv, congruenceLevelEquiv_apply_mk]
  simp

/-- Harris's (3.10) with `N` copies of `D(K_ℓ)`, under (3.6), for an open normal subgroup `H` of
`K_ℓ`: `congruenceFunctionEquiv` followed by `rightRegularPiEquiv`, which writes a locally
constant function with values in the functions on the double cosets as a family, indexed by the
double cosets, of locally constant functions with values in `R`. The double cosets are assumed
finite, as in Harris's (3.9). A form `f` goes to `x ↦ (k_ℓ ↦ f (x.out * k))`
(`congruencePiEquiv_apply`). -/
def congruencePiEquiv [Finite (DoubleCosets σ.finiteAdelicDiagonal K)] (h : LocalLevelFree σ ℓ K)
    (hH : IsOpen (H : Set (localLevel σ ℓ K))) :
    Representation.Equiv
      (levelAction σ.finiteAdelicDiagonal (Representation.trivial R K R)
        (congruenceLevel_le σ ℓ K H))
      (((FunctionModule.rightRegularPi R (localLevel σ ℓ K) R
        (DoubleCosets σ.finiteAdelicDiagonal K)).toInvariants H).comp (localLevelMap σ ℓ K)) :=
  (congruenceFunctionEquiv σ ℓ R H h hH).trans
    (equivComp (Langlands.Induction.invariantsEquivOfEquiv H
        (FunctionModule.rightRegularPiEquiv R (localLevel σ ℓ K) R
          (DoubleCosets σ.finiteAdelicDiagonal K)))
      ((QuotientGroup.mk' H).comp (localLevelMap σ ℓ K)) :)

lemma congruencePiEquiv_apply [Finite (DoubleCosets σ.finiteAdelicDiagonal K)]
    (h : LocalLevelFree σ ℓ K) (hH : IsOpen (H : Set (localLevel σ ℓ K)))
    (f : forms σ.finiteAdelicDiagonal (congruenceLevel σ ℓ K H)
      ((Representation.trivial R K R).comp (Subgroup.inclusion (congruenceLevel_le σ ℓ K H))))
    (x : DoubleCosets σ.finiteAdelicDiagonal K) (k : K) :
    (congruencePiEquiv σ ℓ R H h hH f).1 x (localLevelMap σ ℓ K k) =
      f.1 (x.out * (k : σ.FiniteAdelicPoints)) :=
  congruenceFunctionEquiv_apply σ ℓ R H h hH f k x

end Functions

end Langlands.Shimura.DefiniteForms
