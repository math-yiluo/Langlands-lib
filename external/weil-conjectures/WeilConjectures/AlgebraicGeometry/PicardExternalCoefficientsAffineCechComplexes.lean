/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FieldLinearModuleCohomologyOperations
public import WeilConjectures.Topology.Sheaves.CechComparison
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
import WeilConjectures.AlgebraicGeometry.PicardExternalCoefficientsAffineCechDifferential

/-! # The affine-right product-cover Cech calculation

Source: Stacks Project, Varieties, Tag 0BED, lemma-kunneth, the equality of complexes
following "Let V be an affine open".
(blueprint: lem-sc-picard-external-coefficients-affine-cech-complexes).
-/

@[expose] public section

set_option autoImplicit false
universe w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules

/-- The termwise external tensor formula on the inverse image of an affine open.
There is no covering hypothesis and no assertion about cohomology or derived functors.
Source: Stacks Project, Tag 0BED, lemma-kunneth, the equality of complexes after
"Let V be an affine open"; Tags 01I9 and 01CD for affine sections and pullback tensor.
(blueprint: lem-sc-picard-external-coefficients-affine-cech-complexes).

Proof: The intersection of the inverse images of U_i in pr2 inverse V is the
fibre product of their intersection with V over Spec k. Both factors are affine,
so this intersection is affine by the affine fibre-product ring formula. The
restriction/pullback isomorphism for an open immersion, its adjunction-unit equation,
pullback composition, and pullback tensor identify the restricted coefficient with
the external coefficient of the restricted F and G. Put A = Gamma(U_intersection,O),
B = Gamma(V,O), M = F(U_intersection), and N = G(V). Affine pullback sections and
tensor sections identify its sections with the tensor over A tensor_k B of the
extensions of M and N. The map (m tensor b) tensor (a tensor n) maps to
(a*m) tensor (b*n); its inverse maps m tensor n to (m tensor 1) tensor (1 tensor n).
The balance relations make these maps well-defined, and tensor induction verifies
the inverse identities. These are the pure-tensor section formulas of the pullback
units and tensor section map. For a face inclusion, let r be restriction of sections
of F. The inverse chart map sends m tensor n to the tensor section of the two
pullback-unit sections. Restricting this section gives the tensor of the unit of r(m)
and the unit of n, by unit naturality and restriction of a tensor section. The forward
chart map therefore sends its restriction to r(m) tensor n. Tensor induction extends
this equation to every section, including faces with repeated indices. For a fixed
degree the set of tuples is finite. Tensoring a tuple with n
maps to the tuple of tensors; the inverse is the sum of the coordinate inclusions.
The two composites are identities by tensor induction and coordinate extensionality.
Thus the coordinate comparisons commute with the finite alternating face sum and
give an isomorphism of the displayed additive-group complexes. Restriction of scalars
along scalarMap changes neither the sections nor the differential. Zero coefficients,
empty intersections, empty V, and an empty index type give zero terms and are included.
The single affine second factor is essential: this is not a claim that the general
Kunneth tensor total is isomorphic to a product-cover Cech complex. -/
theorem picardExternalCupCoefficients_affine_cech_complexes
    (k : Type w) [Field k] (X Y : Scheme.{w})
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    (F : X.Modules) (G : Y.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent]
    {ι : Type w} [Finite ι] (U : ι → X.Opens)
    (hU : ∀ (n : ℕ) (y : Fin (n + 1) → ι), IsAffineOpen (⨅ l, U (y l)))
    (V : Y.Opens) (hV : IsAffineOpen V) :
    let Z := Limits.pullback f g
    let W : Z.Opens := (pullback.snd f g) ⁻¹ᵁ V
    let E := (externalCupCoefficients f g F G).restrict W.ι
    let U' : ι → W.toScheme.Opens := fun i ↦ W.ι ⁻¹ᵁ ((pullback.fst f g) ⁻¹ᵁ U i)
    let B := (cechComplexFunctor U').obj E.presheafModuleCat
    let R := ModuleCat.restrictScalars (scalarMap f ⊤)
    let C := (R.mapHomologicalComplex (.up ℕ)).obj
      ((cechComplexFunctor U).obj F.presheafModuleCat)
    let T := tensorRight (scalarObj (V.ι ≫ g) (G.restrict V.ι) (Opposite.op ⊤))
    Nonempty
        (((forget₂ (ModuleCat.{w} Γ(W.toScheme, ⊤)) AddCommGrpCat.{w}).mapHomologicalComplex
            (.up ℕ)).obj B ≅
          ((forget₂ (ModuleCat.{w} k) AddCommGrpCat.{w}).mapHomologicalComplex
            (.up ℕ)).obj ((T.mapHomologicalComplex (.up ℕ)).obj C)) := by
  obtain ⟨e, he⟩ := picardAffineCech_normalized_terms f g F G U V hU hV
  exact ⟨(HomologicalComplex.Hom.isoOfComponents e
    (picardAffineCech_normalized_differential k X Y f g F G U V e he)).symm⟩

end AlgebraicGeometry.Scheme.Modules
