import Langlands.Shimura.DefiniteFormsDoubleCoset
import Langlands.Shimura.EquivariantFormsTensor

/-!
# Harris's isomorphism (3.8) for definite similitude groups

Let `σ` be an involution of a finite-dimensional `ℚ`-algebra with finite adelic points
`σ.FiniteAdelicPoints` (Harris's `GJ(𝔸^f)`), `ℓ` a finite place of `ℚ`, `K` a subgroup of the
finite adelic points with `ℓ`-adic image `K_ℓ = localLevel σ ℓ K`, and `H` a normal subgroup of
`K_ℓ` (Harris's `K_ℓ(n)`), so that `K(n) = congruenceLevel σ ℓ K H`. This file specializes the
generic tensor product isomorphism of `Langlands.Shimura.EquivariantFormsTensor` to Harris,
*Galois properties of cohomological automorphic forms on GL(n)*, 1999, (3.8):
`𝒜_ℓ(GJ, 𝓛, K) ≅ [𝒜_ℓ(GJ, 𝒪/ℓ^m𝒪, K(n)) ⊗ 𝓛]^{K_{ℓ,n}}` for a finite free module `𝓛` with an
action of `K_ℓ` that factors through `K_{ℓ,n} = K_ℓ ⧸ K_ℓ(n)`.

## Main definitions

* `congruenceRep σ ℓ K H ρ`: a representation `ρ` of `K_ℓ ⧸ H` inflated to `K` along
  `k ↦ [k_ℓ]`; it is trivial on `K(n)`.
* `congruenceTensorSpace σ ℓ K H`: the tensor product of the forms of level `K(n)` with trivial
  coefficients `R` and `𝓛`.
* `congruenceTensorAction σ ℓ K H ρ`: the action of `K_ℓ ⧸ H` on the tensor product of the forms
  of level `K(n)` with trivial coefficients and `𝓛`, `[k_ℓ]` acting by right translation by `k`
  on the forms and by `ρ [k_ℓ]` on `𝓛` (`congruenceTensorAction_mk`).
* `congruenceTensorEquiv σ ℓ K H ρ`: Harris's (3.8), in the direction
  `[𝒜_ℓ(GJ, R, K(n)) ⊗ 𝓛]^{K_ℓ ⧸ H} ≃ 𝒜_ℓ(GJ, 𝓛, K)`, `f ⊗ v ↦ (g ↦ f g • v)`, for finite free
  `𝓛`.
* `congruenceTensorDoubleCosetEquiv σ ℓ H ρ h`: under Harris's (3.6), both sides of (3.8) are
  the functions on the double cosets `GJ(ℚ)\GJ(𝔸^f)/K` with values in `𝓛`.
-/

noncomputable section

namespace Langlands.Shimura.DefiniteForms

open Langlands.Global Langlands.Shimura.EquivariantForms
open scoped TensorProduct

universe v t uR

variable {A : Type v} [Ring A] [Algebra ℚ A] (σ : AlgebraInvolution ℚ A) [Module.Finite ℚ A]
  (ℓ : FinitePlace ℚ) (K : Subgroup σ.FiniteAdelicPoints) (H : Subgroup (localLevel σ ℓ K))
  [H.Normal] {R : Type uR} [CommRing R] {V : Type t} [AddCommGroup V] [Module R V]
  (ρ : Representation R (localLevel σ ℓ K ⧸ H) V)

/-- The restriction of the trivial representation is trivial; a local instance, needed to state
the forms of level `K(n)` with trivial coefficients as an argument of `tensorForms`. -/
local instance isTrivial_trivial_comp {G G' : Type*} [Group G] [Group G'] (f : G →* G') :
    Representation.IsTrivial ((Representation.trivial R G' R).comp f) where
  out g := Representation.isTrivial_def (Representation.trivial R G' R) (f g)

/-- A representation `ρ` of `K_ℓ ⧸ H` (Harris's `K_{ℓ,n}`) inflated to `K` along `k ↦ [k_ℓ]`:
the representation of `K` whose forms are `ellModuleForms σ ℓ K (ρ.comp (QuotientGroup.mk' H))`,
Harris's `𝒜_ℓ(GJ, 𝓛, K)` for the action of `K_ℓ` on `𝓛` through `K_{ℓ,n}`. -/
abbrev congruenceRep : Representation R K V :=
  (ρ.comp (QuotientGroup.mk' H)).comp (localLevelMap σ ℓ K)

/-- The inflated representation is trivial on `K(n)`. -/
instance : Representation.IsTrivial
    ((congruenceRep σ ℓ K H ρ).comp (Subgroup.inclusion (congruenceLevel_le σ ℓ K H))) where
  out k := by
    have hk : Subgroup.inclusion (congruenceLevel_le σ ℓ K H) k ∈
        (congruenceLevel σ ℓ K H).subgroupOf K :=
      Subgroup.mem_subgroupOf.2 k.2
    rw [congruenceLevel_subgroupOf, Subgroup.mem_comap] at hk
    change ρ (QuotientGroup.mk' H (localLevelMap σ ℓ K _)) = LinearMap.id
    rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff _).2 hk, map_one]
    rfl

/-- The tensor product `𝒜_ℓ(GJ, R, K(n)) ⊗[R] 𝓛` of the forms of level `K(n)` with trivial
coefficients and `𝓛`. -/
abbrev congruenceTensorSpace : Type _ :=
  forms σ.finiteAdelicDiagonal (congruenceLevel σ ℓ K H)
    ((Representation.trivial R K R).comp (Subgroup.inclusion (congruenceLevel_le σ ℓ K H))) ⊗[R] V

/-- The action of `K_ℓ ⧸ H` on `𝒜_ℓ(GJ, R, K(n)) ⊗ 𝓛`: the published `tensorQuotientAction` of
`K ⧸ K(n)` (right translation on the forms, `ρ` on `𝓛`), transported along
`congruenceQuotientEquiv : K ⧸ K(n) ≃* K_ℓ ⧸ H`. -/
def congruenceTensorAction :
    Representation R (localLevel σ ℓ K ⧸ H) (congruenceTensorSpace σ ℓ K H (R := R) (V := V)) :=
  (tensorQuotientAction σ.finiteAdelicDiagonal (congruenceRep σ ℓ K H ρ)
    (congruenceLevel_le σ ℓ K H)).comp (congruenceQuotientEquiv σ ℓ K H).symm.toMonoidHom

/-- The class `[k_ℓ]` acts on `𝒜_ℓ(GJ, R, K(n)) ⊗ 𝓛` as `k` acts in the tensor product of the
level action on the forms and the inflated representation on `𝓛`. -/
lemma congruenceTensorAction_mk (k : K) :
    congruenceTensorAction σ ℓ K H ρ (localLevelMap σ ℓ K k : localLevel σ ℓ K ⧸ H) =
      (levelAction σ.finiteAdelicDiagonal (Representation.trivial R K R)
        (congruenceLevel_le σ ℓ K H)).tprod (congruenceRep σ ℓ K H ρ) k := by
  have hk : (congruenceQuotientEquiv σ ℓ K H).symm
      (localLevelMap σ ℓ K k : localLevel σ ℓ K ⧸ H) = (k : K ⧸ _) := by
    rw [MulEquiv.symm_apply_eq, congruenceQuotientEquiv_mk]
  change tensorQuotientAction σ.finiteAdelicDiagonal (congruenceRep σ ℓ K H ρ)
    (congruenceLevel_le σ ℓ K H)
      ((congruenceQuotientEquiv σ ℓ K H).symm (localLevelMap σ ℓ K k : localLevel σ ℓ K ⧸ H)) = _
  rw [hk]
  rfl

/-- The `K_ℓ ⧸ H`-invariants are the `K ⧸ K(n)`-invariants of `tensorQuotientAction`. -/
lemma congruenceTensorAction_invariants :
    Representation.invariants (k := R) (G := localLevel σ ℓ K ⧸ H)
      (V := congruenceTensorSpace σ ℓ K H (R := R) (V := V)) (congruenceTensorAction σ ℓ K H ρ) =
      Representation.invariants (k := R) (G := K ⧸ (congruenceLevel σ ℓ K H).subgroupOf K)
        (V := congruenceTensorSpace σ ℓ K H (R := R) (V := V))
        (tensorQuotientAction σ.finiteAdelicDiagonal
          (congruenceRep σ ℓ K H ρ) (congruenceLevel_le σ ℓ K H)) := by
  ext x
  simp only [Representation.mem_invariants]
  refine ⟨fun hx q => ?_, fun hx q => hx ((congruenceQuotientEquiv σ ℓ K H).symm q)⟩
  have := hx (congruenceQuotientEquiv σ ℓ K H q)
  simpa only [congruenceTensorAction, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.symm_apply_apply] using this

variable [Module.Free R V] [Module.Finite R V]

/-- Harris's isomorphism (1999, (3.8)), in the opposite direction: for a finite free `R`-module
`𝓛` with an action `ρ` of `K_{ℓ,n} = K_ℓ ⧸ K_ℓ(n)`, the `K_{ℓ,n}`-invariants of
`𝒜_ℓ(GJ, R, K(n)) ⊗ 𝓛` are `𝒜_ℓ(GJ, 𝓛, K)`; `f ⊗ v ↦ (g ↦ f g • v)`. It is the published
`tensorQuotientInvariantsEquiv` for the level `K(n) ≤ K`. -/
def congruenceTensorEquiv :
    Representation.invariants (k := R) (G := localLevel σ ℓ K ⧸ H)
      (V := congruenceTensorSpace σ ℓ K H (R := R) (V := V)) (congruenceTensorAction σ ℓ K H ρ) ≃ₗ[R]
      ellModuleForms σ ℓ K (ρ.comp (QuotientGroup.mk' H)) :=
  (LinearEquiv.ofEq _ _ (congruenceTensorAction_invariants σ ℓ K H ρ)).trans
    (tensorQuotientInvariantsEquiv σ.finiteAdelicDiagonal (congruenceRep σ ℓ K H ρ)
      (congruenceLevel_le σ ℓ K H))

@[simp]
lemma congruenceTensorEquiv_apply_coe
    (x : Representation.invariants (k := R) (G := localLevel σ ℓ K ⧸ H)
      (V := congruenceTensorSpace σ ℓ K H (R := R) (V := V)) (congruenceTensorAction σ ℓ K H ρ)) :
    (congruenceTensorEquiv σ ℓ K H ρ x).1 =
      (tensorForms σ.finiteAdelicDiagonal (congruenceLevel σ ℓ K H)
        ((Representation.trivial R K R).comp (Subgroup.inclusion (congruenceLevel_le σ ℓ K H)))
        ((congruenceRep σ ℓ K H ρ).comp (Subgroup.inclusion (congruenceLevel_le σ ℓ K H)))
        x.1).1 :=
  rfl

variable {K} in
/-- Under Harris's (3.6), both sides of (3.8) are the functions on the double cosets
`GJ(ℚ)\GJ(𝔸^f)/K` with values in `𝓛`: `congruenceTensorEquiv` followed by restriction to the
representatives (`ellModuleFormsEquiv`). -/
def congruenceTensorDoubleCosetEquiv (h : LocalLevelFree σ ℓ K) :
    Representation.invariants (k := R) (G := localLevel σ ℓ K ⧸ H)
      (V := congruenceTensorSpace σ ℓ K H (R := R) (V := V)) (congruenceTensorAction σ ℓ K H ρ) ≃ₗ[R]
      (DoubleCosets σ.finiteAdelicDiagonal K → V) :=
  (congruenceTensorEquiv σ ℓ K H ρ).trans (ellModuleFormsEquiv σ ℓ h)

@[simp]
lemma congruenceTensorDoubleCosetEquiv_apply (h : LocalLevelFree σ ℓ K)
    (x : Representation.invariants (k := R) (G := localLevel σ ℓ K ⧸ H)
      (V := congruenceTensorSpace σ ℓ K H (R := R) (V := V)) (congruenceTensorAction σ ℓ K H ρ))
    (y : DoubleCosets σ.finiteAdelicDiagonal K) :
    congruenceTensorDoubleCosetEquiv σ ℓ H ρ h x y = (congruenceTensorEquiv σ ℓ K H ρ x).1 y.out :=
  rfl

end Langlands.Shimura.DefiniteForms
