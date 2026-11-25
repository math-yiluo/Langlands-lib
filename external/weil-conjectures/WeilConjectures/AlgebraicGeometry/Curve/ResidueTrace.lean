/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.AdelicDifferentials
public import WeilConjectures.AlgebraicGeometry.Curve.AdelicLocal
public import WeilConjectures.AlgebraicGeometry.Curve.TracePairing
public import WeilConjectures.AlgebraicGeometry.GlobalSectionsBijective
public import WeilConjectures.AlgebraicGeometry.Modules.Endomorphism
public import WeilConjectures.RingTheory.TateResidue.LocalResidue
public import WeilConjectures.RingTheory.TateResidue.ResidueTheorem

/-!
# Serre duality on a curve with the residue trace

Let `X` be an integral scheme, smooth of relative dimension one and proper over a field `k`, with
function field `K` and canonical module `ω = Ω¹_{X/k}`. For a closed point `x` let
`𝒪_{X,x} ⊆ K` be the local ring and `ω_x ⊆ Ω[K⁄k]` the differentials regular at `x`, the image
of `Ω[𝒪_{X,x}⁄k]`. The residue sequence identifies
```
  H¹(X, ω) ≅ (⨁_{x closed} Ω[K⁄k] ⧸ ω_x) ⧸ Ω[K⁄k]
```
(`AlgebraicGeometry.Scheme.differentialsH1Equiv`). Tate's local residue
`res_x = TateResidue.localRes 𝒪_{X,x} : Ω[K⁄k] → k` kills `ω_x`, and by the residue theorem
`∑_x res_x(η) = 0` for `η ∈ Ω[K⁄k]`, so that
```
  t_X : H¹(X, ω) → k,    [(η_x)_x] ↦ ∑_x res_x(η_x)
```
is a well-defined `k`-linear form, the **residue trace**.

It is nonzero: at a closed point `x` with `κ(x)` separable over `k` and a uniformiser `ϖ`,
`res_x(u ϖ⁻¹ dϖ) = Tr_{κ(x)/k}(u)`, which is nonzero for a suitable `u`. Serre duality with this
trace follows from the abstract form `exists_trace_bijective_dualPairing`: the abstract trace
`t` and `t_X` differ by an endomorphism of `ω`, i.e. by a global function, which is a nonzero
element of the field `Γ(X, 𝒪_X)`, hence a unit.

## Main definitions

- `AlgebraicGeometry.Scheme.residueAt`: `res_x : Ω[K⁄k] ⧸ ω_x → k`.
- `AlgebraicGeometry.Scheme.residueSum`: `⨁_x Ω[K⁄k] ⧸ ω_x → k`, `(η_x)_x ↦ ∑_x res_x(η_x)`.
- `AlgebraicGeometry.Scheme.residueTrace`: the residue trace `t_X : H¹(X, ω) → k`.

## Main statements

- `AlgebraicGeometry.Scheme.residueSum_differentialsPrincipalPartsMap`: the residue theorem
  `∑_x res_x(η) = 0` for `η ∈ Ω[K⁄k]`.
- `AlgebraicGeometry.Scheme.residueTrace_symm_mk`: the formula for `t_X`.
- `AlgebraicGeometry.Scheme.residueTrace_ne_zero`: `t_X ≠ 0`.
- `AlgebraicGeometry.Scheme.serreDuality_residueTrace`: Serre duality on a curve: for every
  finite locally free `ℱ` the cup-product pairing
  `H¹(X, ℱ) ⊗ H⁰(X, ℱᵛ ⊗ ω) → H¹(X, ℱ ⊗ ℱᵛ ⊗ ω) → H¹(X, ω) → k` with the residue trace is
  perfect.

(blueprint: `theorem-riemann-roch-coherent-serre-duality--2`)
-/

@[expose] public section

universe u

open CategoryTheory Opposite TopologicalSpace Pointwise MonoidalCategory

namespace Subalgebra

variable {k K : Type*} [Field k] [Field K] [Algebra k K] (O : Subalgebra k K)
  [IsDiscreteValuationRing O] [Module.Finite k (IsLocalRing.ResidueField O)]

/-- `O ⧸ c O` is finite-dimensional for every nonzero `c ∈ O`. -/
lemma finite_quotient_span_singleton {c : O} (hc : c ≠ 0) :
    Module.Finite k (O ⧸ Ideal.span {c}) := by
  have := finiteDimensional_quotient_smul O c.2 fun h ↦ hc (Subtype.ext h)
  let f : ↥(toSubmodule O) →ₗ[k] O ⧸ Ideal.span {c} :=
    (Ideal.Quotient.mkₐ k _).toLinearMap ∘ₗ O.toSubmoduleEquiv.toLinearMap
  have hle : ((c : K) • toSubmodule O).comap (toSubmodule O).subtype ≤ LinearMap.ker f := by
    rintro ⟨a, ha⟩ h
    obtain ⟨b, hb, hab⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 h
    rw [LinearMap.mem_ker]
    refine Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton'.2 ⟨⟨b, hb⟩, ?_⟩)
    refine Subtype.ext ?_
    change b * c = a
    rw [mul_comm]
    exact hab
  refine Module.Finite.of_surjective (Submodule.liftQ _ f hle) fun y ↦ ?_
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
  exact ⟨Submodule.Quotient.mk (O.toSubmoduleEquiv.symm a), rfl⟩

variable [IsFractionRing O K]

/-- A discrete valuation ring `O ⊆ K` with fraction field `K` and residue field finite over `k`
is admissible in Tate's sense: `f O ≺ O` for every `f ∈ K`. -/
theorem admissible_of_isDiscreteValuationRing :
    TateResidue.Admissible K (toSubmodule O) :=
  TateResidue.admissible_of_exists O fun f ↦ by
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := O) f
    have hb0 : (b : K) ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
    refine ⟨b, hb0.isUnit, ?_, finite_quotient_span_singleton O (nonZeroDivisors.ne_zero hb)⟩
    change (b : K) * ((a : K) / (b : K)) ∈ O
    rw [mul_div_cancel₀ _ hb0]
    exact a.2

end Subalgebra

namespace AlgebraicGeometry.Scheme

section General

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]

variable (k X) in
/-- A curve over a field has dimension at most one. -/
lemma topologicalKrullDim_le_one [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))] :
    topologicalKrullDim X ≤ 1 := by
  exact_mod_cast topologicalKrullDim_le_of_smoothOfRelativeDimension (X ↘ Spec (.of k)) 1

variable (k X) in
/-- A scheme of finite type over a field is a noetherian topological space. -/
lemma noetherianSpace_of_locallyOfFiniteType [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] : NoetherianSpace X := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  have : IsNoetherian X := {}
  infer_instance

variable (k X) in
/-- On an integral scheme proper over `k`, `Γ(X, 𝒪_X)` is a field: it is a domain which is
integral over `k`. -/
lemma isField_Γ_of_isProper [IsIntegral X] [IsProper (X ↘ Spec (.of k))] : IsField Γ(X, ⊤) := by
  let := (globalSectionsRingHom k (X := X)).toAlgebra
  have : Algebra.IsIntegral k Γ(X, ⊤) := ⟨isIntegral_globalSectionsRingHom (k := k) (X := X)⟩
  exact isField_of_isIntegral_of_isField' (Field.toIsField k)

/-- The duality pairing of `t ∘ H¹(φ)` is the duality pairing of `t` precomposed with `φ`. -/
lemma Modules.dualPairing_dualPairing {ω : X.Modules} (t : Module.Dual k (ω.H 1))
    (φ : ω ⟶ ω) (G : X.Modules) (ψ : G ⟶ ω) :
    dualPairing (dualPairing t ω φ) G ψ = dualPairing t G (ψ ≫ φ) := by
  ext a
  rw [dualPairing_apply, dualPairing_apply, dualPairing_apply, H.map_comp_apply]

end General

variable (k : Type u) [Field k] (X : Scheme.{u}) [IsIntegral X] [X.Over (Spec (.of k))]
  [Algebra k X.functionField] [IsFunctionFieldAlgebra k X]

section Residue

/-- The **local residue** `res_x : Ω[K⁄k] ⧸ ω_x → k` at a point `x`: Tate's residue
`TateResidue.localRes 𝒪_{X,x}`, which kills `ω_x`, the image of `Ω[𝒪_{X,x}⁄k]`. -/
noncomputable def residueAt (x : X) :
    Ω[X.functionField⁄k] ⧸ Modules.stalkLattice k (differentialsToGeneric k X) x →ₗ[k] k :=
  (Modules.stalkLattice k (differentialsToGeneric k X) x).liftQ
    (TateResidue.localRes (localSubalgebra k X x)) fun v hv ↦ by
      have hv' : v ∈ (Modules.stalkLattice k (differentialsToGeneric k X) x :
        Set Ω[X.functionField⁄k]) := hv
      rw [coe_stalkLattice_differentialsToGeneric] at hv'
      obtain ⟨w, rfl⟩ := hv'
      exact TateResidue.localRes_map_eq_zero _ w

@[simp]
lemma residueAt_mk (x : X) (v : Ω[X.functionField⁄k]) :
    residueAt k X x (Submodule.Quotient.mk v) = TateResidue.localRes (localSubalgebra k X x) v :=
  rfl

open Classical in
/-- The **sum of residues** `⨁_{x closed} Ω[K⁄k] ⧸ ω_x → k`, `(η_x)_x ↦ ∑_x res_x(η_x)`. -/
noncomputable def residueSum :
    (Π₀ x : closedPoints X, Ω[X.functionField⁄k] ⧸
      Modules.stalkLattice k (differentialsToGeneric k X) x.1) →ₗ[k] k :=
  DFinsupp.lsum ℕ fun x ↦ residueAt k X x.1

lemma residueSum_apply
    (d : Π₀ x : closedPoints X, Ω[X.functionField⁄k] ⧸
      Modules.stalkLattice k (differentialsToGeneric k X) x.1) :
    residueSum k X d = ∑ᶠ x : closedPoints X, residueAt k X x.1 (d x) := by
  classical
  rw [residueSum, DFinsupp.lsum_apply_apply, DFinsupp.sumAddHom_apply, DFinsupp.sum]
  refine (finsum_eq_sum_of_support_subset _ fun x hx ↦ ?_).symm
  rw [Finset.mem_coe, DFinsupp.mem_support_iff]
  intro h
  exact hx (by simp [h])

lemma residueSum_single [DecidableEq (closedPoints X)] (x : closedPoints X)
    (v : Ω[X.functionField⁄k]) :
    residueSum k X (DFinsupp.single x (Submodule.Quotient.mk v)) =
      TateResidue.localRes (localSubalgebra k X x.1) v := by
  rw [residueSum_apply, finsum_eq_single _ x fun y hy ↦ by
    rw [DFinsupp.single_eq_of_ne hy, map_zero], DFinsupp.single_eq_same, residueAt_mk]

variable [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))]

/-- The local rings of a curve at its closed points are admissible in Tate's sense. -/
lemma admissible_localSubalgebra {x : X} (hx : IsClosed {x}) :
    TateResidue.Admissible X.functionField (Subalgebra.toSubmodule (localSubalgebra k X x)) :=
  have := isDiscreteValuationRing_localSubalgebra k X hx
  have := finite_residueField_localSubalgebra k X hx
  Subalgebra.admissible_of_isDiscreteValuationRing _

variable [IsProper (X ↘ Spec (.of k))]

/-- **The residue theorem on a curve.** For `η ∈ Ω[K⁄k]`, `∑_{x closed} res_x(η) = 0`: this is
Tate's abstract residue theorem `TateResidue.residue_theorem` for the local rings `𝒪_{X,x}`,
whose hypotheses are the finiteness of `H⁰(X, 𝒪_X)` and `H¹(X, 𝒪_X)`.

(blueprint: `theorem-riemann-roch-coherent-serre-duality--2`) -/
theorem residueSum_differentialsPrincipalPartsMap [NoetherianSpace X]
    (hdim : topologicalKrullDim X ≤ 1) (η : Ω[X.functionField⁄k]) :
    residueSum k X (differentialsPrincipalPartsMap k hdim η) = 0 := by
  let O (x : closedPoints X) : Subalgebra k X.functionField := localSubalgebra k X x.1
  have hfin (f : X.functionField) : {x | f ∉ O x}.Finite :=
    finite_setOf_not_mem_localSubalgebra k X hdim f
  have hadm (x : closedPoints X) : TateResidue.Admissible X.functionField
      (Subalgebra.toSubmodule (O x)) := admissible_localSubalgebra k X x.2
  have hH0 : Module.Finite k (⨅ x, O x : Subalgebra k X.functionField) := by
    have : Module.Finite k ↥(⨅ x, Subalgebra.toSubmodule (O x)) :=
      finiteDimensional_iInf_localSubalgebra k X hdim
    exact Module.Finite.equiv ((LinearEquiv.ofEq _ _
      (Algebra.iInf_toSubmodule O).symm).trans (Subalgebra.toSubmoduleEquiv _))
  have hpp : TateResidue.principalParts O hfin = localPrincipalPartsMap k X hdim :=
    LinearMap.ext fun f ↦ DFinsupp.ext fun x ↦ TateResidue.principalParts_apply O hfin f x
  have hH1 : Module.Finite k ((Π₀ x, X.functionField ⧸ Subalgebra.toSubmodule (O x)) ⧸
      LinearMap.range (TateResidue.principalParts O hfin)) := by
    rw [hpp]
    exact finiteDimensional_quotient_range_localPrincipalPartsMap k X hdim
  rw [residueSum_apply]
  exact (TateResidue.residue_theorem O hfin hadm hH0 hH1 η).2

/-- The **residue trace** `t_X : H¹(X, ω) → k` of a smooth proper integral curve `X` over `k`,
`ω = Ω¹_{X/k}`. Under `H¹(X, ω) ≅ (⨁_{x closed} Ω[K⁄k] ⧸ ω_x) ⧸ Ω[K⁄k]`
(`differentialsH1Equiv`), it sends the class of `(η_x)_x` to the sum of the local residues
`∑_x res_x(η_x)` (`residueTrace_symm_mk`); it is well defined by the residue theorem
`residueSum_differentialsPrincipalPartsMap`.

(blueprint: `theorem-riemann-roch-coherent-serre-duality--2`) -/
noncomputable def residueTrace :
    Module.Dual k (Modules.H (X := X) (X ↘ Spec (.of k)).relativeDifferentials 1) :=
  have := SmoothOfRelativeDimension.smooth 1 (X ↘ Spec (.of k))
  have := noetherianSpace_of_locallyOfFiniteType k X
  (LinearMap.range (differentialsPrincipalPartsMap k (topologicalKrullDim_le_one k X))).liftQ
    (residueSum k X) (by
      rintro _ ⟨η, rfl⟩
      exact residueSum_differentialsPrincipalPartsMap k X _ η) ∘ₗ
    (differentialsH1Equiv k (topologicalKrullDim_le_one k X)).toLinearMap

/-- **The residue trace of a class of principal parts.** If the class in `H¹(X, ω)` is
represented by `d ∈ ⨁_x Ω[K⁄k] ⧸ ω_x`, then `t_X` takes the value `∑_x res_x(d_x)`. -/
lemma residueTrace_symm_mk_eq_residueSum [NoetherianSpace X] [Smooth (X ↘ Spec (.of k))]
    (hdim : topologicalKrullDim X ≤ 1)
    (d : Π₀ x : closedPoints X, Ω[X.functionField⁄k] ⧸
      Modules.stalkLattice k (differentialsToGeneric k X) x.1) :
    residueTrace k X ((differentialsH1Equiv k hdim).symm (Submodule.Quotient.mk d)) =
      residueSum k X d := by
  rw [residueTrace, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply,
    Submodule.liftQ_apply]

/-- **The formula for the residue trace.** If the class in `H¹(X, ω)` is represented by
`d ∈ ⨁_x Ω[K⁄k] ⧸ ω_x`, `d_x = η_x mod ω_x` for differentials `η_x ∈ Ω[K⁄k]`, then
`t_X` takes the value `∑_x res_x(η_x)`, where `res_x` is Tate's residue at `x`.

(blueprint: `theorem-riemann-roch-coherent-serre-duality--2`) -/
lemma residueTrace_symm_mk [NoetherianSpace X] [Smooth (X ↘ Spec (.of k))]
    (hdim : topologicalKrullDim X ≤ 1)
    (d : Π₀ x : closedPoints X, Ω[X.functionField⁄k] ⧸
      Modules.stalkLattice k (differentialsToGeneric k X) x.1)
    (η : closedPoints X → Ω[X.functionField⁄k]) (hη : ∀ x, Submodule.Quotient.mk (η x) = d x) :
    residueTrace k X ((differentialsH1Equiv k hdim).symm (Submodule.Quotient.mk d)) =
      ∑ᶠ x, TateResidue.localRes (localSubalgebra k X x.1) (η x) := by
  rw [residueTrace_symm_mk_eq_residueSum, residueSum_apply]
  exact finsum_congr fun x ↦ by rw [← hη, residueAt_mk]

/-- **The residue trace is nonzero.** At a closed point `x` with `κ(x)` separable over `k`
(such points exist, `Hom.dense_setOf_isClosed_finite_isSeparable`) with uniformiser `ϖ`, the
class of the principal part `u ϖ⁻¹ dϖ` at `x` has residue trace `Tr_{κ(x)/k}(u)` (R5,
`TateResidue.localRes_mul_inv_smul_D`), which is nonzero for a suitable `u`. -/
theorem residueTrace_ne_zero : residueTrace k X ≠ 0 := by
  classical
  have := SmoothOfRelativeDimension.smooth 1 (X ↘ Spec (.of k))
  have := noetherianSpace_of_locallyOfFiniteType k X
  have hdim := topologicalKrullDim_le_one k X
  obtain ⟨x, hx, -, hsep⟩ :=
    (Hom.dense_setOf_isClosed_finite_isSeparable (X ↘ Spec (.of k))).nonempty
  set O := localSubalgebra k X x
  have := isDiscreteValuationRing_localSubalgebra k X hx
  have := finite_residueField_localSubalgebra k X hx
  let := ((X ↘ Spec (.of k)).residueFieldAlgebraMap x).toAlgebra
  have : Algebra.IsSeparable k (IsLocalRing.ResidueField O) :=
    Algebra.IsSeparable.of_algHom _ _ (residueFieldLocalSubalgebraEquiv k X x).toAlgHom
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨u, hu⟩ := Subalgebra.exists_trace_residue_ne_zero O
  have hϖ0 : (ϖ : X.functionField) ≠ 0 := fun h ↦ hϖ.ne_zero (Subtype.ext h)
  have := Subalgebra.finite_quotient_span_singleton O hϖ.ne_zero
  intro h
  refine hu ?_
  have h1 := LinearMap.congr_fun h ((differentialsH1Equiv k hdim).symm (Submodule.Quotient.mk
    (DFinsupp.single ⟨x, hx⟩ (Submodule.Quotient.mk
      (((u : X.functionField) * (ϖ : X.functionField)⁻¹) •
        KaehlerDifferential.D k X.functionField ϖ)))))
  rw [residueTrace_symm_mk_eq_residueSum, residueSum_single, LinearMap.zero_apply,
    TateResidue.localRes_mul_inv_smul_D (admissible_localSubalgebra k X hx) u ϖ hϖ0] at h1
  have e := Algebra.trace_eq_of_algEquiv (Ideal.quotientEquivAlgOfEq k hϖ.maximalIdeal_eq.symm)
    (Ideal.Quotient.mk (Ideal.span {ϖ}) u)
  rw [h1] at e
  exact e

end Residue

section Duality

variable [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))] [IsProper (X ↘ Spec (.of k))]

/-- **Serre duality on a curve with the residue trace**, in the form `Hom(ℱ, ω) ≅ H¹(X, ℱ)^∨`,
`φ ↦ t_X ∘ H¹(φ)`, for every finite locally free `ℱ`.

The abstract trace `t` of `exists_trace_bijective_dualPairing` satisfies `t_X = t ∘ H¹(φ₀)` for
an endomorphism `φ₀` of `ω`; `φ₀` is multiplication by a global function `c`
(`Modules.exists_eq_smulHom`), `c ≠ 0` since `t_X ≠ 0`, so `c` is a unit of the field
`Γ(X, 𝒪_X)` and `φ₀` is an isomorphism. -/
theorem bijective_dualPairing_residueTrace (ℱ : X.Modules)
    (hℱ : SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf) ℱ) :
    Function.Bijective (Modules.dualPairing (residueTrace k X) ℱ) := by
  set ω : X.Modules := (X ↘ Spec (.of k)).relativeDifferentials
  have := Hom.isInvertible_relativeDifferentials (X ↘ Spec (.of k))
  have := Modules.IsInvertible.of_sheafOfModules ω
  have hω : SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf) ω :=
    SheafOfModules.IsInvertible.isFiniteLocallyFree ω
  obtain ⟨t, ht⟩ := exists_trace_bijective_dualPairing (k := k) (X := X)
  obtain ⟨φ₀, hφ₀⟩ := (ht ω hω).2 (residueTrace k X)
  obtain ⟨c, rfl⟩ := Modules.exists_eq_smulHom ω φ₀
  have hc : c ≠ 0 := by
    rintro rfl
    rw [Modules.smulHom_zero, map_zero] at hφ₀
    exact residueTrace_ne_zero k X hφ₀.symm
  obtain ⟨d, hd⟩ := (isField_Γ_of_isProper k X).mul_inv_cancel hc
  have hiso : IsIso (ω.smulHom c) :=
    ⟨ω.smulHom d, by rw [← Modules.smulHom_mul, mul_comm, hd, Modules.smulHom_one],
      by rw [← Modules.smulHom_mul, hd, Modules.smulHom_one]⟩
  have heq : ⇑(Modules.dualPairing (residueTrace k X) ℱ) =
      Modules.dualPairing t ℱ ∘ fun ψ ↦ ψ ≫ ω.smulHom c := by
    rw [← hφ₀]
    exact funext fun ψ ↦ Modules.dualPairing_dualPairing t _ ℱ ψ
  rw [heq]
  refine (ht ℱ hℱ).comp (Function.bijective_iff_has_inverse.2
    ⟨fun ψ ↦ ψ ≫ inv (ω.smulHom c), fun ψ ↦ ?_, fun ψ ↦ ?_⟩) <;> simp

/-- **Serre duality on a curve with the residue trace**, as a perfect pairing
`H⁰(X, Hom(ℱ, ω)) × H¹(X, ℱ) → k`, `(b, a) ↦ t_X(H¹(b)(a))`: both
`H⁰(X, Hom(ℱ, ω)) → H¹(X, ℱ)^∨` and `H¹(X, ℱ) → H⁰(X, Hom(ℱ, ω))^∨` are bijective. -/
theorem bijective_dualPairingH_residueTrace (ℱ : X.Modules)
    (hℱ : SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf) ℱ) :
    Function.Bijective (Modules.dualPairingH (residueTrace k X) ℱ) ∧
      Function.Bijective (Modules.dualPairingH (residueTrace k X) ℱ).flip := by
  have hL := (Modules.bijective_dualPairingH_iff _ ℱ).2
    (bijective_dualPairing_residueTrace k X ℱ hℱ)
  refine ⟨hL, ?_⟩
  have := hℱ
  have := SheafOfModules.IsFiniteLocallyFree.isFinitePresentation ℱ
  have := SheafOfModules.instIsQuasicoherentOfIsLocallyFree ℱ
  have := Modules.finiteDimensional_H_of_isProper (k := k) ℱ 1
  let L := LinearEquiv.ofBijective (Modules.dualPairingH (residueTrace k X) ℱ) hL
  have hflip : (Modules.dualPairingH (residueTrace k X) ℱ).flip =
      L.dualMap.toLinearMap ∘ₗ (Module.evalEquiv k (ℱ.H 1)).toLinearMap := by
    ext a b
    rfl
  rw [hflip, LinearMap.coe_comp]
  exact L.dualMap.bijective.comp (Module.evalEquiv k (ℱ.H 1)).bijective

open scoped AlgebraicGeometry.Scheme.Modules in
/-- **Serre duality on a smooth proper curve with the residue trace.** Let `X` be an integral
scheme, smooth of relative dimension one and proper over a field `k`, with canonical module
`ω = Ω¹_{X/k}`, and let `t_X : H¹(X, ω) → k` be the residue trace
(`residueTrace`: under `H¹(X, ω) ≅ (⨁_{x closed} Ω[K⁄k] ⧸ ω_x) ⧸ Ω[K⁄k]` it is
`(η_x)_x ↦ ∑_x res_x(η_x)`, with `res_x` Tate's residue at `x`). Then for every finite locally
free `ℱ` the trace pairing
```
  H¹(X, ℱ) ⊗ H⁰(X, ℱᵛ ⊗ ω) --∪--> H¹(X, ℱ ⊗ ℱᵛ ⊗ ω) --H¹(ev)--> H¹(X, ω) --t_X--> k
```
(`Modules.cupPairing`) is perfect: both `H⁰(X, ℱᵛ ⊗ ω) → H¹(X, ℱ)^∨` and
`H¹(X, ℱ) → H⁰(X, ℱᵛ ⊗ ω)^∨` are bijective. This is the case `n = 1` of Serre duality with the
explicit trace of the blueprint.

(blueprint: `theorem-riemann-roch-coherent-serre-duality--2`) -/
theorem serreDuality_residueTrace (ℱ : X.Modules)
    (hℱ : SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf) ℱ) :
    Function.Bijective (Modules.cupPairing (residueTrace k X) ℱ) ∧
      Function.Bijective (Modules.cupPairing (residueTrace k X) ℱ).flip := by
  have := Hom.isInvertible_relativeDifferentials (X ↘ Spec (.of k))
  have := Modules.IsInvertible.of_sheafOfModules (X ↘ Spec (.of k)).relativeDifferentials
  obtain ⟨h₁, h₂⟩ := bijective_dualPairingH_residueTrace k X ℱ hℱ
  let L : Modules.H (X := X) (ℱᵛ ⊗ (X ↘ Spec (.of k)).relativeDifferentials) 0 ≃ₗ[k]
      Modules.H (X := X) (Modules.homObj ℱ (X ↘ Spec (.of k)).relativeDifferentials) 0 :=
    LinearEquiv.ofBijective (Modules.H.mapLinearMap k
      (Modules.dualTensorHom ℱ (X ↘ Spec (.of k)).relativeDifferentials) 0)
      (Modules.H.mapLinearEquiv
        (asIso (Modules.dualTensorHom ℱ (X ↘ Spec (.of k)).relativeDifferentials)) 0).bijective
  have hc := Modules.cupPairing_eq (residueTrace k X) ℱ
  refine ⟨?_, ?_⟩
  · rw [hc, LinearMap.coe_comp]
    exact h₁.comp L.bijective
  · have hflip : (Modules.cupPairing (residueTrace k X) ℱ).flip =
        L.dualMap.toLinearMap ∘ₗ (Modules.dualPairingH (residueTrace k X) ℱ).flip := by
      rw [hc]
      rfl
    rw [hflip, LinearMap.coe_comp]
    exact L.dualMap.bijective.comp h₂

end Duality

end AlgebraicGeometry.Scheme
