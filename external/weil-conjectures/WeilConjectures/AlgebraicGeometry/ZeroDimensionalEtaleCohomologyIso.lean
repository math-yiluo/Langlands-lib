/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.Topology.KrullDimension
import WeilConjectures.AlgebraicGeometry.ZeroDimensionalSectionsStalks

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

namespace AlgebraicGeometry

/-- The canonical degree-zero comparison followed by the product of the chosen
geometric stalk germs is invertible.

Source: literature/blueprint/master/blueprint/sec-curve-estimates/lem-sc-arbitrary-curve-cd/
lem-weil-pbc-zero-dimensional-cohomology.md, both proof paragraphs;
Stacks Project, Tags 00KH, 00FV, 054M, 03QO, 03SI and 03Q1.
(blueprint: zero-dimensional-etale-cohomology-iso).

Proof:
1. `lem-weil-pbc-finite-type-dim-zero-artinian` gives a finite discrete space of
   closed points. `lem-weil-pbc-reduction-universal-homeomorphism` gives the reduced
   scheme with the same space. It is finite type, being a closed subscheme of C.
   `lem-weil-pbc-closed-point-residue-field-base` identifies its residue fields with k.
   Each singleton is open and closed and affine by
   `lem-weil-pbc-finite-discrete-scheme-affine`. Its reduced coordinate ring has one
   prime, hence is a field, identified with k by its residue field. The inclusions
   induce a map from the coproduct supplied by `lem-weil-pbc-scheme-coproduct-family`.
   Disjoint open summands cover the reduction, so this bijective local isomorphism
   is an isomorphism with the finite coproduct of Spec k.
2. `lem-weil-pbc-finite-geometric-point-coproduct-cohomology` computes the cohomology
   of the pulled-back sheaf there: positive degrees are zero and the canonical
   degree-zero germ map is an isomorphism. Each chosen `s x` factors through the
   reduction since its source is reduced. On each Spec k summand, apply
   `lem-weil-pbc-strictly-henselian-sections-stalk` (Tag 03QO) with R = k to both the
   canonical k-point and the specified geometric point. Both natural germ maps
   from sections are isomorphisms. Composing the inverse canonical germ with the
   specified germ gives the stalk comparison and identifies the canonical
   product-of-germs map with the specified product-of-germs map. No algebraicity
   of the chosen geometric field over k or extra k-linearity of `s x` is required.
3. `thm-weil-pbc-universal-homeomorphism-invariance` transports this calculation to C.
   `lem-weil-pbc-inverse-image-stalk-germ` identifies the pulled-back stalks with those
   of F, preserving germs of sections. Consequently the transported degree-zero map
   is the displayed derived-to-underived comparison, restriction to the identity
   étale object, and product of germs, rather than merely some isomorphism.
   This proves invertibility of the specified composite for the original sheaf.
   For the empty scheme the product and global sections are both zero; the same
   argument applies to the empty coproduct. For nonreduced C the reduction
   equivalence is essential, so reducedness is never added as a hypothesis.
-/
theorem zero_dimensional_etale_cohomology_iso
    (k : Type u) [Field k] [IsAlgClosed k] (C : Scheme.{u})
    (f : C ⟶ Spec (.of k)) [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] (hdim : topologicalKrullDim C ≤ 0)
    (F : Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1})
    (Ω : C → Type u) [∀ x, Field (Ω x)] [∀ x, IsAlgClosed (Ω x)]
    (s : ∀ x : C, Spec (.of (Ω x)) ⟶ C)
    (hs : ∀ x : C, (s x).base.hom default = x) :
    IsIso ((Functor.homologyRightDerivedFunctorObjSingleFunctorIso
        (Sheaf.Γ C.smallEtaleTopology AddCommGrpCat.{u + 1}) F 0).hom ≫
          (Functor.rightDerivedZeroIsoSelf
            (Sheaf.Γ C.smallEtaleTopology AddCommGrpCat.{u + 1})).hom.app F ≫
          F.ΓRes (op (Scheme.Etale.mk (𝟙 C))) ≫ Pi.lift (fun x : C =>
            (Scheme.pointSmallEtale (s x)).toPresheafFiber
              (Scheme.Etale.mk (𝟙 C))
              (Over.homMk (s x) (Category.comp_id (s x))) F.obj)) := by
  let : C.Over (Spec (.of k)) := ⟨f⟩
  let : IsSeparated (C ↘ Spec (.of k)) := inferInstanceAs (IsSeparated f)
  let : LocallyOfFiniteType (C ↘ Spec (.of k)) := inferInstanceAs (LocallyOfFiniteType f)
  let : QuasiCompact (C ↘ Spec (.of k)) := inferInstanceAs (QuasiCompact f)
  have hg := (Scheme.zeroDimensional_sections_stalks.{u, u}
    k C hdim Ω s hs).2.1 F
  have hr : IsIso (F.ΓRes (op (Scheme.Etale.mk (𝟙 C)))) :=
    F.isLimitConeΓ.isIso_π_app_of_isInitial _
      (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale C).op
  infer_instance

end AlgebraicGeometry
