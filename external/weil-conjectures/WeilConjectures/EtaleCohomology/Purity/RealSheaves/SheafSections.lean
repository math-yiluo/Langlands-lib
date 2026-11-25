/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Regular
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryConstruction
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.LocalSystems
public import WeilConjectures.WeilSheaf.GlobalSectionsUpperStar

/-!
# Global sections of lisse Weil sheaves on an open subcurve

Let `C₀` be a smooth geometrically connected curve over the finite field `K`, `F` a lisse Weil
sheaf on `C₀` with Weil fundamental representation `(V, ρ)` and `j : U₀ ⟶ C₀` a nonempty open
subcurve. The global sections `H⁰(Ū, j^* F)` of the restriction of `F` to `Ū` are the
invariants `V ^ {π₁(U)}` of the geometric fundamental group of `U`, acting through the
restriction `W(U₀) → W(C₀)` of Weil groups, compatibly with the Frobenius
(`AlgebraicGeometry.WeilGroup.exists_globalSections_upperStar_linearEquiv_invariants`,
blueprint `lemma-degree-zero-top-cohomology--1`).

The sheaf-theoretic input is that `F ≅ j_* j^* F` for a lisse `F`
(`AlgebraicGeometry.WeilSheaf.IsLisse.isIso_upperStarLowerStarAdjunction_unit_app`), so that
restriction of global sections `H⁰(C̄, F) → H⁰(Ū, j^* F)` is bijective
(`AlgebraicGeometry.WeilSheaf.IsLisse.bijective_globalSectionsRestrict_of_isOpenImmersion`). The
representation-theoretic input is that `π₁(U) → π₁(C)` is surjective
(`AlgebraicGeometry.WeilGroup.Restriction.surjective_restrict`), so that `V ^ {π₁(U)}` is
`V ^ {π₁(C)}`, which is `H⁰(C̄, F)` by the case `U₀ = C₀`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {K : Type u} [Field K] [Finite K] {l : ℕ} [Fact l.Prime] [Fact (ringChar K ≠ l)]

/-- A nonempty open immersion into an irreducible scheme has dense range. -/
theorem dense_range_of_isOpenImmersion {U C : Scheme.{u}} [IrreducibleSpace C] (j : U ⟶ C)
    [IsOpenImmersion j] [Nonempty U] : Dense (Set.range j.base) :=
  j.isOpenEmbedding.isOpen_range.dense (Set.range_nonempty _)

namespace WeilSheaf

/-- **Restriction of global sections to a nonempty open subcurve.** For a lisse Weil sheaf `F` on
a smooth geometrically connected curve `C₀` and a nonempty open `j : U₀ ⟶ C₀`, restriction of
global sections `H⁰(C̄, F) → H⁰(Ū, j^* F)` is bijective: the unit `F ⟶ j_* j^* F` is an
isomorphism. -/
theorem IsLisse.bijective_globalSectionsRestrict_of_isOpenImmersion {C U : Scheme.{u}}
    [C.Over (Spec (.of K))] [U.Over (Spec (.of K))] [IsCurve (C ↘ Spec (.of K))]
    [IsCurve (U ↘ Spec (.of K))] [SmoothOfRelativeDimension 1 (C ↘ Spec (.of K))]
    [ConnectedSpace C] (j : U ⟶ C) [IsOpenImmersion j] [Nonempty U]
    [j.IsOver (Spec (.of K))] {F : WeilSheaf K l C} (hF : F.IsLisse) :
    Function.Bijective (globalSectionsRestrict j F) := by
  have : Smooth (C ↘ Spec (.of K)) := SmoothOfRelativeDimension.smooth 1 _
  have := WeilGroup.irreducibleSpace_of_smooth (p := C ↘ Spec (.of K))
  have : QuasiCompact j := by
    have : QuasiCompact (j ≫ C ↘ Spec (.of K)) := by
      rw [comp_over j]
      infer_instance
    exact QuasiCompact.of_comp j (C ↘ Spec (.of K))
  have := hF.isIso_upperStarLowerStarAdjunction_unit_app j (dense_range_of_isOpenImmersion j)
  exact bijective_globalSectionsRestrict j F

end WeilSheaf

namespace WeilGroup

variable {C U : Scheme.{u}} [C.Over (Spec (.of K))] [U.Over (Spec (.of K))]
  [IsCurve (C ↘ Spec (.of K))] [IsCurve (U ↘ Spec (.of K))]
  {W : WeilGroup (C ↘ Spec (.of K))} {WU : WeilGroup (U ↘ Spec (.of K))}
  {j : U ⟶ C} [IsOpenImmersion j] [Nonempty U]

/-- The restriction of Weil groups maps the geometric fundamental group `π₁(U)` onto `π₁(C)`:
it is surjective and preserves degrees. -/
theorem Restriction.exists_restrict_eq_of_mem_geometric (R : Restriction j WU W) {g : W.carrier}
    (hg : g ∈ W.geometric) : ∃ h : WU.geometric, R.restrict h = g := by
  obtain ⟨h, rfl⟩ := R.surjective_restrict g
  refine ⟨⟨h, ?_⟩, rfl⟩
  rw [MonoidHom.mem_ker, ← R.deg_restrict, MonoidHom.comp_apply]
  exact hg

/-- The restriction of Weil groups maps `π₁(U)` into `π₁(C)`. -/
theorem Restriction.restrict_mem_geometric (R : Restriction j WU W) (h : WU.geometric) :
    R.restrict h ∈ W.geometric := by
  rw [MonoidHom.mem_ker, ← MonoidHom.comp_apply, R.deg_restrict]
  exact h.2

omit [Fact (ringChar K ≠ l)] in
/-- The invariants of `π₁(U)`, acting through the restriction `W(U₀) → W(C₀)`, are the
invariants of `π₁(C)`, since `π₁(U) → π₁(C)` is surjective. -/
theorem Restriction.mem_invariants_iff (R : Restriction j WU W) {V : Type*} [AddCommGroup V]
    [Module (PadicAlgCl l) V] (ρ : Representation (PadicAlgCl l) W.carrier V) (v : V) :
    v ∈ Representation.invariants ((ρ.comp R.restrict).comp WU.geometric.subtype) ↔
      v ∈ Representation.invariants (ρ.comp W.geometric.subtype) := by
  simp only [Representation.mem_invariants, MonoidHom.comp_apply, Subgroup.subtype_apply]
  refine ⟨fun h g ↦ ?_, fun h g ↦ h ⟨_, R.restrict_mem_geometric g⟩⟩
  obtain ⟨g', hg'⟩ := R.exists_restrict_eq_of_mem_geometric g.2
  rw [← hg']
  exact h g'

omit [Fact (ringChar K ≠ l)] in
/-- On `π₁(C)`-invariants, the restriction of the Frobenius lift of `W(U₀)` acts as the Frobenius
lift of `W(C₀)`: the two have the same degree, so they differ by an element of `π₁(C)`. -/
theorem Restriction.apply_restrict_frobeniusLift (R : Restriction j WU W) {V : Type*}
    [AddCommGroup V] [Module (PadicAlgCl l) V] (ρ : Representation (PadicAlgCl l) W.carrier V)
    {v : V} (hv : v ∈ Representation.invariants (ρ.comp W.geometric.subtype)) :
    ρ (R.restrict WU.frobeniusLift) v = ρ W.frobeniusLift v := by
  have hmem : W.frobeniusLift⁻¹ * R.restrict WU.frobeniusLift ∈ W.geometric := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, ← MonoidHom.comp_apply, R.deg_restrict,
      W.deg_frobeniusLift, WU.deg_frobeniusLift, inv_mul_cancel]
  have h := hv ⟨_, hmem⟩
  simp only [MonoidHom.comp_apply, Subgroup.subtype_apply] at h
  rw [← mul_inv_cancel_left W.frobeniusLift (R.restrict WU.frobeniusLift), map_mul,
    Module.End.mul_apply, h]

variable [SmoothOfRelativeDimension 1 (C ↘ Spec (.of K))] [j.IsOver (Spec (.of K))]

/-- Blueprint `lemma-degree-zero-top-cohomology--1` (subsection
`lemma-degree-zero-top-cohomology--1`): Global sections as invariants.

Let `e` be an equivalence between lisse Weil sheaves on `C₀` and lisse representations of
`W(C₀)` which identifies the global sections `H⁰(C̄, F)` with the invariants `V ^ {π₁(C)}`,
compatibly with the Frobenius `ρ (γ)` — the equivalence of
`AlgebraicGeometry.WeilGroup.exists_equivalence_isLisse` is one. Let `j : U₀ ⟶ C₀` be a nonempty
open subcurve with restriction of Weil groups `R : W(U₀) → W(C₀)`. Then

`H⁰(Ū, F|_U) ≅ V ^ {π₁(U)}`,

`π₁(U)` acting through `R`, compatibly with the Frobenius of the global sections and the action
of the Frobenius lift `ρ (R γ_U)` of `W(U₀)`.

Restriction of global sections `H⁰(C̄, F) → H⁰(Ū, F|_U)` is bijective and Frobenius-equivariant
(`AlgebraicGeometry.WeilSheaf.IsLisse.bijective_globalSectionsRestrict_of_isOpenImmersion`,
`AlgebraicGeometry.WeilSheaf.globalSectionsRestrict_frobenius`), and `V ^ {π₁(U)} = V ^ {π₁(C)}`
since `π₁(U) → π₁(C)` is surjective; on these invariants `ρ (R γ_U)` and `ρ (γ_C)` agree. -/
theorem exists_globalSections_upperStar_linearEquiv_invariants
    (e : ObjectProperty.FullSubcategory (fun F : WeilSheaf K l C ↦ F.IsLisse) ≌
      ObjectProperty.FullSubcategory (W.isLisseRep l))
    (he : ∀ F : ObjectProperty.FullSubcategory (fun F : WeilSheaf K l C ↦ F.IsLisse),
      ∃ f : F.obj.globalSections.carrier ≃ₗ[PadicAlgCl l]
          Representation.invariants ((e.functor.obj F).obj.ρ.comp W.geometric.subtype),
        ∀ v, (f (F.obj.globalSections.frobenius v) : (e.functor.obj F).obj.V) =
          (e.functor.obj F).obj.ρ W.frobeniusLift (f v))
    (R : Restriction j WU W) (F : ObjectProperty.FullSubcategory (fun F : WeilSheaf K l C ↦
      F.IsLisse)) :
    ∃ f : ((WeilSheaf.upperStar j).obj F.obj).globalSections.carrier ≃ₗ[PadicAlgCl l]
        Representation.invariants
          (((e.functor.obj F).obj.ρ.comp R.restrict).comp WU.geometric.subtype),
      ∀ v, (f (((WeilSheaf.upperStar j).obj F.obj).globalSections.frobenius v) :
          (e.functor.obj F).obj.V) =
        (e.functor.obj F).obj.ρ (R.restrict WU.frobeniusLift) (f v) := by
  have := W.connectedSpace
  obtain ⟨a, ha⟩ := he F
  let r := LinearEquiv.ofBijective (WeilSheaf.globalSectionsRestrict j F.obj)
    (F.property.bijective_globalSectionsRestrict_of_isOpenImmersion j)
  let s : Representation.invariants ((e.functor.obj F).obj.ρ.comp W.geometric.subtype)
      ≃ₗ[PadicAlgCl l]
      Representation.invariants
        (((e.functor.obj F).obj.ρ.comp R.restrict).comp WU.geometric.subtype) :=
    LinearEquiv.ofEq _ _ (Submodule.ext fun v ↦ (R.mem_invariants_iff _ v).symm)
  refine ⟨(r.symm.trans a).trans s, fun v ↦ ?_⟩
  have hr : r.symm (((WeilSheaf.upperStar j).obj F.obj).globalSections.frobenius v) =
      F.obj.globalSections.frobenius (r.symm v) := by
    have h1 := WeilSheaf.globalSectionsRestrict_frobenius j F.obj (r.symm v)
    have h2 : WeilSheaf.globalSectionsRestrict j F.obj (r.symm v) = v := r.apply_symm_apply v
    rw [h2] at h1
    apply r.injective
    rw [r.apply_symm_apply]
    exact h1.symm
  simp only [LinearEquiv.trans_apply, hr]
  exact (ha _).trans (R.apply_restrict_frobeniusLift _ (a (r.symm v)).2).symm

end WeilGroup

end AlgebraicGeometry
