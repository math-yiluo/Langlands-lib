/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.FieldTheory.Separable
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Etale

/-!
# The points of an etale fibre

Source: Stacks Project, Morphisms, Lemma 02GL, part (2)
(blueprint: lem-weil-pbc-etale-fibre-discrete-separable-points).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- The fibre of an etale morphism is discrete, and each singleton open subscheme is the
spectrum of its residue field, finite and separable over the base residue field.
Source: Stacks Project, Morphisms, Lemma 02GL(2)
(blueprint: lem-weil-pbc-etale-fibre-discrete-separable-points).

Proof:
1. The fibre projection is etale by base change
   (`situation-conventions`, Stacks 02GO).
2. An affine open around a fibre point is etale over the base field by restriction and
   composition (`definition-torsion-sheaves--3`). Its coordinate algebra is
   a finite product of finite separable fields
   (`lem-weil-pbc-etale-algebra-over-field-product`, Stacks 00U3).
3. The spectrum of that product has open singleton components, each isomorphic over the
   base field to the spectrum of the corresponding factor
   (`lem-weil-pbc-spec-finite-product-fields`).
4. Every point is open, so every subset is open and every singleton is also closed.
5. The residue field at the point agrees with that of its singleton open subscheme,
   hence with the corresponding finite separable factor. Transport the component
   isomorphism along this identification to obtain the claimed isomorphism over the base.

The ring map `i` is the canonical base-field map obtained by applying the fully faithful
spectrum functor to the composite from the point's residue-field spectrum to the base. -/
theorem Scheme.Hom.etale_fibre_discrete_separable_points
    {X S : Scheme.{u}} (f : X ⟶ S) [Etale f] (s : S) :
    DiscreteTopology (f.fiber s) ∧
      ∀ y : f.fiber s,
        let i := Spec.homEquiv
          ((f.fiber s).fromSpecResidueField y ≫ f.fiberToSpecResidueField s)
        letI := i.hom.toAlgebra
        Module.Finite (S.residueField s) ((f.fiber s).residueField y) ∧
          (∀ a : (f.fiber s).residueField y,
            ∃ p : Polynomial (S.residueField s), p.Separable ∧ Polynomial.aeval a p = 0) ∧
          ∃ U : (f.fiber s).Opens,
            (U : Set (f.fiber s)) = {y} ∧
              ∃ e : U.toScheme ≅ Spec ((f.fiber s).residueField y),
                e.hom ≫ Spec.map i = U.ι ≫ f.fiberToSpecResidueField s := by
  -- Proved quasi-finiteness and residue-field tools bypass the affine-product plan above.
  have : DiscreteTopology (f ⁻¹' {s}) := (f.isDiscrete_preimage_singleton s).to_subtype
  have : DiscreteTopology (f.fiber s) := (f.fiberHomeo s).symm.discreteTopology
  refine ⟨inferInstance, fun y ↦ ?_⟩
  let p := f.fiberToSpecResidueField s
  let F := f.fiber s
  let i := Spec.homEquiv (F.fromSpecResidueField y ≫ p)
  let := i.hom.toAlgebra
  have : IsClosedImmersion ((Spec (S.residueField s)).fromSpecResidueField (p y)) :=
    isClosed_singleton_iff_isClosedImmersion.mp (isClosed_discrete _)
  have : Surjective ((Spec (S.residueField s)).fromSpecResidueField (p y)) :=
    ⟨fun z ↦ ⟨default, Subsingleton.elim _ _⟩⟩
  have := isIso_of_isClosedImmersion_of_surjective
    ((Spec (S.residueField s)).fromSpecResidueField (p y))
  have : Etale (Spec.map (p.residueFieldMap y)) :=
    HasRingHomProperty.Spec_iff.mpr (p.etale_residueFieldMap y)
  have : Etale (F.fromSpecResidueField y ≫ p) := by
    rw [← p.SpecMap_residueFieldMap_fromSpecResidueField y]
    infer_instance
  have heq : Spec.map i = F.fromSpecResidueField y ≫ p := Spec.homEquiv.symm_apply_apply _
  have : Etale (Spec.map i) := heq ▸ ‹Etale (F.fromSpecResidueField y ≫ p)›
  have : Algebra.Etale (S.residueField s) (F.residueField y) := by
    rw [← RingHom.etale_algebraMap, RingHom.algebraMap_toAlgebra]
    exact HasRingHomProperty.Spec_iff.mp ‹Etale (Spec.map i)›
  have : Module.Finite (S.residueField s) (F.residueField y) :=
    Algebra.FormallyUnramified.finite_of_free _ _
  have : Algebra.IsSeparable (S.residueField s) (F.residueField y) :=
    (Algebra.FormallyEtale.iff_isSeparable _ _).mp inferInstance
  refine ⟨inferInstance, (fun a ↦ ⟨minpoly (S.residueField s) a,
    Algebra.IsSeparable.isSeparable (S.residueField s) a, minpoly.aeval _ _⟩), ?_⟩
  have : IsReduced F := isReduced_of_etale (f.fiberToSpecResidueField s)
  let U : F.Opens := ⟨{y}, isOpen_discrete _⟩
  let g := F.fromSpecResidueField y
  have hr : Set.range g ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι, Scheme.range_fromSpecResidueField]
    exact Set.Subset.rfl
  let l := IsOpenImmersion.lift U.ι g hr
  have hl : l ≫ U.ι = g := IsOpenImmersion.lift_fac _ _ _
  have : IsPreimmersion (l ≫ U.ι) := hl ▸ inferInstance
  have : IsPreimmersion l := .of_comp l U.ι
  have : Surjective l := by
    constructor
    intro z
    refine ⟨default, ?_⟩
    apply (U.ι).isOpenEmbedding.injective
    change (l ≫ U.ι) default = z.val
    rw [hl, Scheme.fromSpecResidueField_apply]
    exact z.property.symm
  have : IsClosedImmersion l := .of_isPreimmersion l (isClosed_discrete _)
  have : IsReduced U.toScheme := isReduced_of_isOpenImmersion U.ι
  have : IsIso l := isIso_of_isClosedImmersion_of_surjective l
  refine ⟨U, rfl, (asIso l).symm, ?_⟩
  change inv l ≫ Spec.map i = U.ι ≫ p
  rw [heq]
  change inv l ≫ g ≫ p = U.ι ≫ p
  rw [← hl]
  simp

end AlgebraicGeometry
