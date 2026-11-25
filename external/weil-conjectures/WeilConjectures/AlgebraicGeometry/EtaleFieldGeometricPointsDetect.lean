/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleFieldGeometricAction
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Gluing
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Etale

/-!
# Detection of morphisms by geometric points over a field

Source: Stacks Project, Tags 02GL and 03QR.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- Geometric points detect morphisms from an étale scheme over a field.
Source: Stacks Project, Tag 03QR, full-faithfulness argument, using Tag 02GL
(blueprint: lem-exc-etale-field-geometric-points-detect).

Proof: An étale scheme over K is discrete by quasi-finiteness and reduced because
Spec K is reduced. The singleton open U at each point is reduced and irreducible,
hence integral. Since Ksep is separably closed, the étale lifting theorem supplies
p : Spec Ksep → U over K. It is surjective because U has one point and flat because
U is integral with one point. Thus p is an epimorphism. The assumed equality on
geometric points, applied to p followed by U → X, cancels p and gives equality on U.
The singleton opens cover X, so open-local extensionality gives f = g. An empty
source is covered by the same universal quantification over its empty point type.
The target need not be étale. -/
theorem etaleFieldGeometricPoints_detect
    (K Ksep : Type u) [Field K] [Field Ksep] [Algebra K Ksep]
    [IsSepClosure K Ksep] (X : Scheme.Etale (Spec (CommRingCat.of K)))
    {Y : Scheme.{u}} (f g : X.left ⟶ Y)
    (h : ∀ p : etaleFieldBasePoint K Ksep ⟶ (Scheme.Etale.forget _).obj X,
      p.left ≫ f = p.left ≫ g) : f = g := by
  classical
  let q : X.left ⟶ Spec (CommRingCat.of K) := X.hom
  have : Etale q := inferInstance
  let : IsSepClosed Ksep := IsSepClosure.sep_closed K
  have : DiscreteTopology X.left := by
    have hd := q.isDiscrete_preimage_singleton
      (default : Spec (CommRingCat.of K))
    have heq : q ⁻¹' {default} = Set.univ := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_univ, iff_true]
      exact Subsingleton.elim _ _
    rw [heq] at hd
    exact isDiscrete_univ_iff.mp hd
  have : IsReduced X.left := isReduced_of_etale q
  apply Scheme.hom_ext_of_forall
  intro x
  let U : X.left.Opens := ⟨{x}, isOpen_discrete _⟩
  have : Subsingleton U.toScheme := by
    refine ⟨fun a b ↦ Subtype.ext ?_⟩
    exact a.property.trans b.property.symm
  have : Nonempty U.toScheme := ⟨⟨x, rfl⟩⟩
  have : IsReduced U.toScheme := isReduced_of_isOpenImmersion U.ι
  have : IrreducibleSpace U.toScheme :=
    { toNonempty := inferInstance }
  have : IsIntegral U.toScheme := isIntegral_of_irreducibleSpace_of_isReduced _
  obtain ⟨p, hp, _⟩ := Scheme.exists_fac_of_etale_of_isSepClosed
    (U.ι ≫ q) (etaleFieldBasePoint K Ksep).hom
    (⟨x, rfl⟩ : U.toScheme) (by
      change q x = (etaleFieldBasePoint K Ksep).hom (default : Spec (CommRingCat.of Ksep))
      exact Subsingleton.elim _ _)
  have : Surjective p := ⟨fun z ↦ ⟨default, Subsingleton.elim _ _⟩⟩
  have : Epi p := Flat.epi_of_flat_of_surjective p
  refine ⟨U, rfl, (cancel_epi p).mp ?_⟩
  have hh := h (Over.homMk (p ≫ U.ι) hp)
  change (p ≫ U.ι) ≫ f = (p ≫ U.ι) ≫ g at hh
  simpa only [Category.assoc] using hh

end AlgebraicGeometry
