/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.RingTheory.Finiteness.Defs
import WeilConjectures.AlgebraicGeometry.SteinFactorizationAffine
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.Topology.NoetherianSpace
import Mathlib.Topology.Separation.Basic
import Mathlib.RingTheory.Ideal.GoingUp
import WeilConjectures.PointCount
import Mathlib.FieldTheory.Tower

/-!
# Finite fibres and residue extensions of the affine Stein factor

## References

* Stacks Project, More on Morphisms, Tag 0E0M
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A subextension of a finite extension is finite. -/
private theorem finite_left_of_comp {K L M : Type u} [Field K] [Field L] [Field M]
    (i : K →+* L) (j : L →+* M) (hij : (j.comp i).Finite) : i.Finite := by
  let : Algebra K L := i.toAlgebra
  let : Algebra L M := j.toAlgebra
  let : Algebra K M := (j.comp i).toAlgebra
  have : IsScalarTower K L M := IsScalarTower.of_algebraMap_eq' rfl
  have : Module.Finite K M := hij
  exact Module.Finite.left K L M

/-- The affine Stein factor of a proper morphism has finite point fibres and finite
residue-field extensions, without a Noetherian assumption on the base ring. Here
`f.steinFactorizationBase` is the canonical map from `Spec Γ(X, ⊤)` to `Spec A`. -/
theorem Scheme.Hom.steinFactorizationBase_finite_fibres_residueFields
    {A : Type u} [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f]
    (s : Spec (CommRingCat.of A)) :
    (f.steinFactorizationBase ⁻¹' {s}).Finite ∧
      ∀ b : Spec Γ(X, ⊤), f.steinFactorizationBase b = s →
        (f.steinFactorizationBase.residueFieldMap b).hom.Finite := by
  classical
  let φ := (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop
  have hstein := f.steinFactorization_affine
  let : Algebra A Γ(X, ⊤) := φ.hom.toAlgebra
  have : Algebra.IsIntegral A Γ(X, ⊤) := ⟨hstein.1⟩
  let T := f.steinFactorizationBase ⁻¹' {s}
  have : T1Space T := by
    apply t1Space_iff_specializes_imp_eq.mpr
    intro b c hbc
    apply Subtype.ext
    apply PrimeSpectrum.ext
    have hle : b.val.asIdeal ≤ c.val.asIdeal :=
      (PrimeSpectrum.le_iff_specializes _ _).mpr
        (hbc.map continuous_subtype_val)
    by_contra hne
    have hlt := Ideal.IsIntegral.under_lt_under (R := A) (lt_of_le_of_ne hle hne)
    apply (ne_of_lt hlt)
    exact congrArg PrimeSpectrum.asIdeal (b.property.trans c.property.symm)
  let Y := f.fiber s
  let g := f.fiberToSpecResidueField s
  have : LocallyOfFiniteType g :=
    MorphismProperty.pullback_snd _ _ inferInstance
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian g
  have : CompactSpace Y := inferInstance
  have : IsNoetherian Y := ⟨⟩
  let a : Y ⟶ Spec Γ(X, ⊤) := f.fiberι s ≫ X.toSpecΓ
  have ha (y : Y) : f.steinFactorizationBase (a y) = s := by
    rw [← Scheme.Hom.comp_apply, Category.assoc, Scheme.toSpecΓ_steinFactorizationBase]
    exact (f.fiberHomeo s y).property
  let h : Y → T := fun y ↦ ⟨a y, ha y⟩
  have hc : Continuous h := a.continuous.subtype_mk _
  have hs : Function.Surjective h := by
    intro b
    obtain ⟨z, hz⟩ := (hstein.2.2.2 b.val).2.nonempty
    have hz' : X.toSpecΓ z = b.val := hz
    have hfz : f z = s := by
      rw [← Scheme.toSpecΓ_steinFactorizationBase f, Scheme.Hom.comp_apply, hz']
      exact b.property
    refine ⟨(f.fiberHomeo s).symm ⟨z, hfz⟩, ?_⟩
    apply Subtype.ext
    change X.toSpecΓ (f.fiberι s ((f.fiberHomeo s).symm ⟨z, hfz⟩)) = b.val
    simpa using hz'
  have hG := genericPoints.finite (α := Y)
    (TopologicalSpace.NoetherianSpace.finite_irreducibleComponents (α := Y))
  have hclosed : IsClosed (h '' genericPoints Y) := (hG.image h).isClosed
  have hall : ∀ y : Y, h y ∈ h '' genericPoints Y := by
    have hsub := closure_minimal (Set.subset_preimage_image h (genericPoints Y))
      (hclosed.preimage hc)
    rw [genericPoints.closure] at hsub
    exact fun y ↦ hsub (Set.mem_univ y)
  refine ⟨?_, ?_⟩
  · have hu : (Set.univ : Set T) ⊆ h '' genericPoints Y := by
      intro b _
      obtain ⟨y, rfl⟩ := hs b
      exact hall y
    exact Set.finite_coe_iff.mp (Finite.of_finite_univ ((hG.image h).subset hu))
  · intro b hb
    obtain ⟨x, hx, hxclosed⟩ :=
      ((isClosed_singleton (x := (⟨b, hb⟩ : T))).preimage hc).exists_closed_singleton
        (by obtain ⟨y, hy⟩ := hs ⟨b, hb⟩; exact ⟨y, hy⟩)
    have hx' : a x = b := congrArg Subtype.val hx
    have hfin := g.finite_residueField_of_isClosed x hxclosed
    let S := Spec (CommRingCat.of A)
    let i : S.residueField s ⟶ (Spec Γ(X, ⊤)).residueField (a x) :=
      (S.residueFieldCongr (ha x)).inv ≫ f.steinFactorizationBase.residueFieldMap (a x)
    let j := a.residueFieldMap x
    have heq : i ≫ j = CommRingCat.ofHom (g.residueFieldAlgebraMap x) := by
      apply Spec.map_injective
      apply (cancel_mono (S.fromSpecResidueField s)).mp
      have hafac : a ≫ f.steinFactorizationBase = g ≫ S.fromSpecResidueField s := by
        dsimp only [a]
        rw [Category.assoc, Scheme.toSpecΓ_steinFactorizationBase, f.fiber_fac]
      calc
        Spec.map (i ≫ j) ≫ S.fromSpecResidueField s =
            Spec.map j ≫ Spec.map (f.steinFactorizationBase.residueFieldMap (a x)) ≫
              S.fromSpecResidueField (f.steinFactorizationBase (a x)) := by
          simp only [i, Spec.map_comp, Category.assoc, Scheme.residueFieldCongr_inv,
            Scheme.residueFieldCongr_fromSpecResidueField]
        _ = Y.fromSpecResidueField x ≫ a ≫ f.steinFactorizationBase := by
          rw [Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField,
            ← Category.assoc, Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField,
            Category.assoc]
        _ = (Y.fromSpecResidueField x ≫ g) ≫ S.fromSpecResidueField s := by
          rw [hafac, Category.assoc]
        _ = Spec.map (CommRingCat.ofHom (g.residueFieldAlgebraMap x)) ≫
            S.fromSpecResidueField s := by rw [g.specMap_residueFieldAlgebraMap]
    have hij : (j.hom.comp i.hom).Finite := by
      change (i ≫ j).hom.Finite
      rw [heq]
      exact hfin
    have hi := finite_left_of_comp i.hom j.hom hij
    have hres : (f.steinFactorizationBase.residueFieldMap (a x)).hom.Finite :=
      RingHom.Finite.of_comp_finite hi
    exact (congrArg (fun z ↦
      (f.steinFactorizationBase.residueFieldMap z).hom.Finite) hx').mp hres

end AlgebraicGeometry
