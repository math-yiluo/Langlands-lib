/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.Construction
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.Weights
public import WeilConjectures.Mathlib.RepresentationTheory.Irreducible

/-!
# Restricting lisse Weil sheaves to an open subcurve

Let `j : U₀ ⟶ C₀` be a nonempty open immersion of curves over a finite field and
`R : AlgebraicGeometry.WeilGroup.Restriction j W(U₀) W(C₀)` a restriction of Weil groups. Pulling
a Weil representation `ρ` of `W(C₀)` back along `R.restrict` is the restriction `j^* ℱ` of the
corresponding lisse Weil sheaf. This file records how the notions of `definition-weights` and
`definition-weil-representation` behave under this operation: lisse sheaves restrict to
lisse sheaves, the local eigenvalues at a closed point of `U₀` are those at its image, so reality,
determinant weights and punctual purity are inherited, and since `R.restrict` is surjective,
constituents restrict to constituents (`lemma-boundary-stalk--2`).

Every Weil group `W` of a smooth geometrically connected curve receives a restriction from some
Weil group of any nonempty geometrically connected open
(`AlgebraicGeometry.WeilGroup.Restriction.exists_weilGroup`), obtained from
`AlgebraicGeometry.WeilGroup.restrictionOfPath` and the identification
`AlgebraicGeometry.WeilGroup.toStandard` of `W` with the standard Weil group of its base point.

## Main statements

- `Representation.isIrreducible_comp_iff`: pulling back
  along a surjective homomorphism preserves and reflects irreducibility.
- `AlgebraicGeometry.WeilGroup.Restriction.exists_weilGroup`
- `AlgebraicGeometry.WeilGroup.Restriction.localEigenvalues_comp`
- `AlgebraicGeometry.WeilGroup.Restriction.isReal_comp`
- `AlgebraicGeometry.WeilGroup.Restriction.hasDetWeight_comp`
- `AlgebraicGeometry.WeilGroup.Restriction.isConstituent_comp`
-/

@[expose] public section

universe u

open CategoryTheory

namespace Subrepresentation

variable {k G G' V : Type*} [CommSemiring k] [Monoid G] [Monoid G'] [AddCommMonoid V]
  [Module k V] {ρ : Representation k G V}

/-- Pulling a representation back along a surjective monoid homomorphism `f : G' →* G` does not
change its invariant subspaces: a subspace is `ρ (f g')`-stable for all `g'` if and only if it is
`ρ g`-stable for all `g`. -/
def compOrderIso (f : G' →* G) (hf : Function.Surjective f) :
    Subrepresentation (ρ.comp f) ≃o Subrepresentation ρ where
  toFun N := ⟨N.toSubmodule, fun g v hv ↦ by
    obtain ⟨g', rfl⟩ := hf g
    exact N.apply_mem_toSubmodule g' hv⟩
  invFun N := ⟨N.toSubmodule, fun g' _ hv ↦ N.apply_mem_toSubmodule (f g') hv⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

@[simp]
lemma toSubmodule_compOrderIso (f : G' →* G) (hf : Function.Surjective f)
    (N : Subrepresentation (ρ.comp f)) : (compOrderIso f hf N).toSubmodule = N.toSubmodule :=
  rfl

@[simp]
lemma toSubmodule_compOrderIso_symm (f : G' →* G) (hf : Function.Surjective f)
    (N : Subrepresentation ρ) : ((compOrderIso f hf).symm N).toSubmodule = N.toSubmodule :=
  rfl

end Subrepresentation

namespace Representation

variable {k G G' V V' : Type*} [Field k] [Group G] [Group G'] [AddCommGroup V] [Module k V]
  [AddCommGroup V'] [Module k V'] {ρ : Representation k G V} {σ : Representation k G V'}

/-- Pulling a representation back along a surjective homomorphism preserves and reflects
irreducibility, since it does not change the invariant subspaces. -/
theorem isIrreducible_comp_iff (f : G' →* G) (hf : Function.Surjective f) :
    IsIrreducible (ρ.comp f) ↔ ρ.IsIrreducible :=
  (Subrepresentation.compOrderIso f hf).isSimpleOrder_iff

end Representation

namespace AlgebraicGeometry.WeilGroup

section Existence

variable {K : Type u} [Field K] [Finite K] {C U : Scheme.{u}} {p : C ⟶ Spec (.of K)} [IsCurve p]
  [GeometricallyConnected p] {pU : U ⟶ Spec (.of K)} [IsCurve pU] [GeometricallyConnected pU]
  (W : WeilGroup p)

/-- The embedding of a Weil group into its fundamental group is that of the standard Weil group,
transported along `AlgebraicGeometry.WeilGroup.toStandard`. -/
lemma toFundamentalGroup_toStandard_symm (g : W.standard.carrier) :
    W.toFundamentalGroup (W.toStandard.symm g) = W.standard.toFundamentalGroup g := by
  have h : W.weilGroupEquiv (W.toStandard.symm g) = g := W.weilGroupEquiv.apply_symm_apply g
  rw [toFundamentalGroup_apply, toFundamentalGroup_apply, h]
  rfl

/-- The degree of a Weil group is that of the standard Weil group, transported along
`AlgebraicGeometry.WeilGroup.toStandard`. -/
lemma deg_toStandard_symm (g : W.standard.carrier) :
    W.deg (W.toStandard.symm g) = W.standard.deg g := by
  rw [W.deg_eq]
  exact congrArg _ (W.weilGroupEquiv.apply_symm_apply g)

/-- **Every Weil group of a smooth curve receives a restriction** from a Weil group of any
nonempty geometrically connected open `j : U₀ ⟶ C₀`: compose the restriction
`AlgebraicGeometry.WeilGroup.restrictionOfPath` into the standard Weil group of the base point
of `W` with the isomorphism `AlgebraicGeometry.WeilGroup.toStandard`, which carries local
Frobenius elements to conjugates of local Frobenius elements. -/
theorem Restriction.exists_weilGroup [Smooth p] (j : U ⟶ C) [IsOpenImmersion j] [Nonempty U]
    (hj : j ≫ p = pU) : ∃ WU : WeilGroup pU, Nonempty (Restriction j WU W) := by
  have := W.connectedSpace
  have : ConnectedSpace U := GeometricallyConnected.connectedSpace_of_subsingleton pU
  obtain ⟨sU⟩ := pU.nonempty_algebraicClosure_point
  obtain ⟨GU, _, _⟩ := Scheme.FiniteEtale.exists_isFundamentalGroup sU
  obtain ⟨τ⟩ := PreGaloisCategory.nonempty_iso_of_fiberFunctor
    (Scheme.FiniteEtale.fiber (sU ≫ j)) (Scheme.FiniteEtale.fiber W.basePoint)
  let R₀ := restrictionOfPath j hj τ GU W.fundamentalGroup
  let φ : W.standard.carrier →* W.carrier := W.toStandard.symm.toMulEquiv.toMonoidHom
  refine ⟨_, ⟨{ comp_eq := hj
                restrict := φ.comp R₀.restrict
                fiberIso := R₀.fiberIso
                restrict_smul := fun g P y ↦ ?_
                continuous_restrict := W.toStandard.symm.continuous.comp R₀.continuous_restrict
                deg_restrict := ?_
                surjective_restrict := W.toStandard.symm.surjective.comp R₀.surjective_restrict
                restrict_frobenius := fun x y hxy ↦ ?_ }⟩⟩
  · rw [MonoidHom.comp_apply]
    exact (congrArg (· • _) (W.toFundamentalGroup_toStandard_symm _)).trans
      (R₀.restrict_smul g P y)
  · ext g
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply]
    exact (W.deg_toStandard_symm _).trans (congrArg (· g) R₀.deg_restrict)
  · have h₁ := φ.map_isConj (W.isConj_toStandard_frobenius y)
    have e₁ : φ (W.toStandard (W.frobenius y)) = W.frobenius y :=
      W.toStandard.symm_apply_apply _
    rw [e₁] at h₁
    exact h₁.trans (φ.map_isConj (R₀.restrict_frobenius x y hxy))

end Existence

/-- The image of a closed point of `U` under an open immersion `j : U ⟶ C`, a closed point of `C`
with the same residue field. -/
def _root_.AlgebraicGeometry.Scheme.Hom.mapFinitePoints {U C : Scheme.{u}} (j : U ⟶ C)
    [IsOpenImmersion j] (x : U.finitePoints) : C.finitePoints :=
  ⟨j.base x.1, (Scheme.Hom.mem_finitePoints_iff_of_isIso j x.1).2 x.2⟩

@[simp]
lemma _root_.AlgebraicGeometry.Scheme.Hom.coe_mapFinitePoints {U C : Scheme.{u}} (j : U ⟶ C)
    [IsOpenImmersion j] (x : U.finitePoints) : (j.mapFinitePoints x).1 = j.base x.1 :=
  rfl

/-- The residue cardinality of a closed point is that of its image under an open immersion. -/
lemma _root_.AlgebraicGeometry.Scheme.Hom.pointNorm_mapFinitePoints {U C : Scheme.{u}}
    (j : U ⟶ C) [IsOpenImmersion j] (x : U.finitePoints) :
    C.pointNorm (j.mapFinitePoints x).1 = U.pointNorm x.1 :=
  Scheme.Hom.pointNorm_of_isIso j x.1

namespace Restriction

variable {K : Type u} [Field K] [Finite K] {C U : Scheme.{u}} {p : C ⟶ Spec (.of K)} [IsCurve p]
  {pU : U ⟶ Spec (.of K)} [IsCurve pU] {j : U ⟶ C} [IsOpenImmersion j] [Nonempty U]
  {WU : WeilGroup pU} {WC : WeilGroup p} (R : Restriction j WU WC) (l : ℕ) [Fact l.Prime]
  {V : Type u} [AddCommGroup V] [Module (PadicAlgCl l) V] [FiniteDimensional (PadicAlgCl l) V]

/-- A lisse Weil sheaf on `C₀` restricts to a lisse Weil sheaf on `U₀`: the geometric part of
`W(U₀)` maps continuously into that of `W(C₀)`. -/
theorem isLisse_comp {ρ : Representation (PadicAlgCl l) WC.carrier V} (hρ : WC.IsLisse l ρ) :
    WU.IsLisse l (ρ.comp R.restrict) := by
  refine IsLisse.of_continuous_apply fun φ v ↦ ?_
  have hmaps (g : WU.geometric) : R.restrict g.1 ∈ WC.geometric := by
    rw [MonoidHom.mem_ker, ← MonoidHom.comp_apply, R.deg_restrict]
    exact g.2
  have hc : Continuous fun g : WU.geometric ↦ (⟨R.restrict g.1, hmaps g⟩ : WC.geometric) :=
    (R.continuous_restrict.comp continuous_subtype_val).subtype_mk _
  exact (hρ.continuous_apply φ v).comp hc

variable (ρ : Representation (PadicAlgCl l) WC.carrier V)

/-- The local polynomial of `j^* ℱ` at a closed point `x` of `U₀` is that of `ℱ` at the image
of `x`: the restriction carries the local Frobenius at `x` into the Frobenius conjugacy class at
`j x`. -/
theorem localPolynomial_comp (x : U.finitePoints) :
    WU.localPolynomial l (ρ.comp R.restrict) x = WC.localPolynomial l ρ (j.mapFinitePoints x) :=
  (localPolynomial_eq_charpolyRev_of_isConj
    (R.restrict_frobenius x (j.mapFinitePoints x) rfl)).symm

/-- The local eigenvalues of `j^* ℱ` at a closed point `x` of `U₀` are those of `ℱ` at the
image of `x`. -/
theorem localEigenvalues_comp (x : U.finitePoints) :
    WU.localEigenvalues l (ρ.comp R.restrict) x = WC.localEigenvalues l ρ (j.mapFinitePoints x) :=
  congrArg Polynomial.roots
    (LinearMap.charpoly_of_isConj
      (ρ.map_isConj (R.restrict_frobenius x (j.mapFinitePoints x) rfl))).symm

variable (ι : PadicAlgCl l →+* ℂ)

/-- The restriction of an `ι`-real lisse Weil sheaf is `ι`-real: reality is a condition on the
local polynomials, and those of `j^* ℱ` are local polynomials of `ℱ`. -/
theorem isReal_comp (h : WC.IsReal l ρ ι) : WU.IsReal l (ρ.comp R.restrict) ι := by
  intro x n
  rw [R.localPolynomial_comp l ρ x]
  exact h _ n

omit [FiniteDimensional (PadicAlgCl l) V] in
/-- The restriction of a Weil sheaf of determinant weight `γ` has determinant weight `γ`: the
determinant of the local Frobenius at a closed point of `U₀` is that at its image, and the
residue cardinalities agree. -/
theorem hasDetWeight_comp {γ : ℝ} (h : WC.HasDetWeight l ρ ι γ) :
    WU.HasDetWeight l (ρ.comp R.restrict) ι γ := by
  intro x
  have hdet := isConj_iff_eq.1 (MonoidHom.map_isConj
    (LinearMap.det : Module.End (PadicAlgCl l) V →* PadicAlgCl l)
    (ρ.map_isConj (R.restrict_frobenius x (j.mapFinitePoints x) rfl)))
  rw [← j.pointNorm_mapFinitePoints, MonoidHom.comp_apply, ← hdet]
  exact h _

/-- If the restriction `j^* ℱ` is punctually `ι`-pure of weight `w`, then `ℱ` is pure of weight
`w` at every closed point of `C₀` lying in `U₀`. -/
theorem frobeniusWeight_eq_of_isPunctuallyPure_comp {w : ℝ}
    (h : WU.IsPunctuallyPure l (ρ.comp R.restrict) ι w) (x : U.finitePoints) :
    ∀ α ∈ WC.localEigenvalues l ρ (j.mapFinitePoints x),
      frobeniusWeight ι (C.pointNorm (j.mapFinitePoints x).1) α = w := by
  intro α hα
  rw [← R.localEigenvalues_comp] at hα
  rw [j.pointNorm_mapFinitePoints]
  exact h x α hα

omit [FiniteDimensional (PadicAlgCl l) V] in
/-- Restriction to `U₀` preserves constituents (`lemma-boundary-stalk--2`): the restriction of Weil
groups is surjective, so `j^*` does not change the invariant subspaces. -/
theorem isConstituent_comp {V' : Type u} [AddCommGroup V'] [Module (PadicAlgCl l) V']
    {σ : Representation (PadicAlgCl l) WC.carrier V'} (hσ : σ.IsConstituent ρ) :
    Representation.IsConstituent (σ.comp R.restrict) (ρ.comp R.restrict) :=
  hσ.comp R.surjective_restrict

end Restriction

end AlgebraicGeometry.WeilGroup
