/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.GenericGeometricIrreducibilityShrink

/-! # Simultaneous geometric irreducibility on an open

Source: Stacks Project, Tags 0559 and 055G.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Topology
namespace AlgebraicGeometry

private theorem irreducibleSpace_iff_range {X Y : Scheme.{u}} (j : X ⟶ Y)
    (hj : IsEmbedding j) : IrreducibleSpace X ↔ IsIrreducible (Set.range j) := by
  rw [isIrreducible_iff_irreducibleSpace]
  exact hj.toHomeomorph.irreducibleSpace_iff

private theorem closed_baseChange_irreducible_iff {Z P T B : Scheme.{u}}
    (j : Z ⟶ P) [IsClosedImmersion j] (p : P ⟶ T) (g : B ⟶ T) :
    IrreducibleSpace ↥(pullback (j ≫ p) g) ↔
      IsIrreducible ((pullback.fst p g) ⁻¹' Set.range j) := by
  rw [← (pullbackRightPullbackFstIso p g j).hom.homeomorph.irreducibleSpace_iff]
  rw [irreducibleSpace_iff_range _ (pullback.snd j (pullback.fst p g)).isEmbedding]
  rw [Scheme.Pullback.range_snd]

set_option backward.isDefEq.respectTransparency false in
private theorem closed_geometric_fibre_irreducible_iff {Z P T : Scheme.{u}}
    (j : Z ⟶ P) [IsClosedImmersion j] (p : P ⟶ T) (t : T) :
    GeometricallyIrreducible ((j ≫ p).fiberToSpecResidueField t) ↔
      ∀ (E : Type u) (_ : Field E)
        (z : Spec (CommRingCat.of E) ⟶ Spec (CommRingCat.of (T.residueField t))),
        IsIrreducible ((pullback.fst (p.fiberToSpecResidueField t) z ≫
          p.fiberι t) ⁻¹' Set.range j) := by
  rw [GeometricallyIrreducible.eq_geometrically,
    geometrically_iff_of_isClosedUnderIsomorphisms]
  dsimp [Scheme.Hom.fiberToSpecResidueField, Scheme.Hom.fiberι, Scheme.Hom.fiber]
  constructor
  · intro h E hE z
    have hZ := h E z
    let eZ := pullbackLeftPullbackSndIso (j ≫ p) (T.fromSpecResidueField t) z
    rw [eZ.hom.homeomorph.irreducibleSpace_iff] at hZ
    have hP := (closed_baseChange_irreducible_iff j p (z ≫ T.fromSpecResidueField t)).mp hZ
    let eP := pullbackLeftPullbackSndIso p (T.fromSpecResidueField t) z
    have h := hP.preimage eP.hom.isOpenEmbedding (by
      simpa [Set.range_eq_univ.mpr eP.hom.surjective] using hP.nonempty)
    change IsIrreducible ((eP.hom ≫ pullback.fst p
      (z ≫ T.fromSpecResidueField t)) ⁻¹' Set.range j) at h
    rw [pullbackLeftPullbackSndIso_hom_fst] at h
    exact h
  · intro h E hE z
    let eP := pullbackLeftPullbackSndIso p (T.fromSpecResidueField t) z
    have hP := (h E hE z).image eP.hom eP.hom.continuous.continuousOn
    have hpre : (pullback.fst (pullback.snd p (T.fromSpecResidueField t)) z ≫
        pullback.fst p (T.fromSpecResidueField t)) ⁻¹' Set.range j = eP.hom ⁻¹'
          ((pullback.fst p (z ≫ T.fromSpecResidueField t)) ⁻¹' Set.range j) := by
      change _ = (eP.hom ≫ pullback.fst p (z ≫ T.fromSpecResidueField t)) ⁻¹' _
      rw [pullbackLeftPullbackSndIso_hom_fst]
      rfl
    change IsIrreducible (eP.hom '' ((pullback.fst
      (pullback.snd p (T.fromSpecResidueField t)) z ≫
        pullback.fst p (T.fromSpecResidueField t)) ⁻¹' Set.range j)) at hP
    rw [hpre, Set.image_preimage_eq _ eP.hom.surjective] at hP
    have hZ := (closed_baseChange_irreducible_iff j p (z ≫ T.fromSpecResidueField t)).mpr hP
    let eZ := pullbackLeftPullbackSndIso (j ≫ p) (T.fromSpecResidueField t) z
    exact eZ.hom.homeomorph.irreducibleSpace_iff.mpr hZ

/-- A finite family of generically geometrically irreducible closed subsets has
geometrically irreducible fibres on a common open.

Source: Stacks Project, Tag 0559 (Lemma 37.27.5), applied to reduced closed
subschemes; Tag 055G, the simultaneous shrinking of the component closures.
Proof: the generic-point hypothesis makes T irreducible. Replace T by its reduction
and pull back the total space and its closed subsets. Reduction is a universal
homeomorphism, so it preserves the subset tests after every field base change.
Give each subset its reduced induced closed subscheme structure. Its map to the
reduced base is finite type: its inclusion is a closed immersion and the total
space map is the base change of p. The generic-fibre hypothesis is precisely geometric
irreducibility, including nonemptiness, of this closed subscheme's generic fibre.
For each index apply the argument of Tag 0559: reduce the closed scheme too;
use Stacks Proposition 29.28.1 on this reduced finite type scheme over an integral
base to make its map flat and finitely presented (generic flatness alone would
only assert flatness). Its generic fibre is irreducible and nonempty. Choose a
nonempty affine open of that scheme;
its generic fibre is dense. The generic-density shrinking lemma makes this open
dense in every fibre, also after field extension, so one may work on the affine
open. If the function field is not separably generated, spread a finite purely
inseparable extension of the base function field making its reduction separably
generated. To spread it, choose field generators b_j with b_j raised to a
characteristic-power q_j in the base fraction field. Write b_j^q_j = a_j/d_j
and replace b_j by d_j*b_j; then (d_j*b_j)^q_j = a_j*d_j^(q_j-1) lies in the
base ring. The subalgebra generated by these scaled generators is finite integral,
has the required fraction field, and is radicial: the generators have unique roots
over any algebraically closed residue field. Its spectrum is therefore a universal
homeomorphism and does not change geometric irreducibility. Reduce the pulled-back
closed scheme and apply Proposition 29.28.1 again to restore flatness and finite
presentation after shrinking. In characteristic zero the field extension is trivial.
A separating transcendence basis presents that function field birationally as an
absolutely irreducible hypersurface. Spread the birational identification to
common affine opens by clearing the finitely many coefficients and denominators.
Shrink so these common opens are fibrewise dense. The polynomial specialization
argument of Tag 0557 first makes the polynomial monic in one variable: replace
other variables by themselves plus sufficiently separated powers of that variable,
so distinct monomials have distinct highest exponents, and invert the resulting
nonzero leading coefficient. For each pair of positive monic factor degrees, bound
all other variable degrees by those of the polynomial and impose the coefficient
relations for a factorization in a finite type algebra. This algebra has no point
over the algebraic closure of the generic field; Nullstellensatz makes its generic
localization zero. Some nonzero base element therefore kills its unit. Inverting
the product of these finitely many elements rules out every nontrivial factorization
in every field specialization, so all hypersurface geometric fibres are irreducible
on a nonempty open of the base; its dense common open then proves the same for
the original closed scheme. Nonemptiness is retained by flatness and openness,
shrinking to the image if necessary. Thus there is a nonempty open for each
index. Each contains the generic point; intersect the finitely many opens and
transfer this open back through the reduction homeomorphism.
The geometric fibre of each induced closed subscheme embeds in the geometric
fibre of P as the inverse image of C_i. Its irreducibility therefore gives exactly
the stated inverse-image test for all field-valued maps. For an empty index family
choose the entire base; the assertions about subsets are vacuous. No covering or intersection
hypothesis is required.

(blueprint: lem-sbc-closed-family-geometric-fibre-shrink) -/
theorem exists_open_closed_family_geometric_fibre_shrink {P T : Scheme.{u}}
    (p : P ⟶ T) [LocallyOfFiniteType p] [QuasiCompact p]
    (η : T) (hη : IsGenericPoint η Set.univ) {I : Type u} [Finite I]
    (C : I → Set P) (hclosed : ∀ i, IsClosed (C i))
    (hgeom : ∀ i, ∀ (E : Type u) (_ : Field E)
      (z : Spec (CommRingCat.of E) ⟶ Spec (CommRingCat.of (T.residueField η))),
      IsIrreducible ((pullback.fst (p.fiberToSpecResidueField η) z ≫
        p.fiberι η) ⁻¹' C i)) :
    ∃ U : T.Opens, η ∈ U ∧ ∀ i t, t ∈ U →
      ∀ (E : Type u) (_ : Field E)
        (z : Spec (CommRingCat.of E) ⟶ Spec (CommRingCat.of (T.residueField t))),
        IsIrreducible ((pullback.fst (p.fiberToSpecResidueField t) z ≫
          p.fiberι t) ⁻¹' C i) := by
  classical
  let J (i : I) := Scheme.IdealSheafData.vanishingIdeal
    (⟨C i, hclosed i⟩ : TopologicalSpace.Closeds P)
  have hrange (i : I) : Set.range (J i).subschemeι = C i := by
    rw [Scheme.IdealSheafData.range_subschemeι]
    rfl
  have hgeneric (i : I) :
      GeometricallyIrreducible (((J i).subschemeι ≫ p).fiberToSpecResidueField η) := by
    apply (closed_geometric_fibre_irreducible_iff (J i).subschemeι p η).mpr
    simpa only [hrange] using hgeom i
  have hshrink (i : I) := exists_open_generic_geometric_irreducibility_shrink
    ((J i).subschemeι ≫ p) η hη (hgeneric i)
  choose U hηU hU using hshrink
  refine ⟨⨅ i, U i, ?_, ?_⟩
  · change η ∈ (↑(⨅ i, U i) : Set T)
    rw [TopologicalSpace.Opens.coe_iInf]
    exact Set.mem_iInter.mpr hηU
  · intro i t ht E hE z
    have hi : t ∈ U i := (iInf_le U i) ht
    have h := (closed_geometric_fibre_irreducible_iff (J i).subschemeι p t).mp
      (hU i t hi) E hE z
    simpa only [hrange] using h

end AlgebraicGeometry
