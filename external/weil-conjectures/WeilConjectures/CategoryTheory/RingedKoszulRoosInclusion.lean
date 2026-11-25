/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Homology.ExactProductsRoosComparison
public import WeilConjectures.CategoryTheory.RingedKoszulSystem
import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
import WeilConjectures.Algebra.Homology.TelescopeHomRoosArrow
import WeilConjectures.CategoryTheory.RingedKoszulFiniteHomTower

/-! # Ordinary Koszul limits and the explicit Roos fibre

Source: Stacks Project, sites-cohomology.tex, Tag 0A0A; derived.tex, Tag 0949.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable (O : Sheaf J CommRingCat.{u}) (r : ℕ)
variable (b : Fin r → (O.obj ⋙ forget CommRingCat).sections)

/-- The zero-second-coordinate map from the ordinary limit of the strict Koszul tensor
 tower to its explicit Roos fibre is a quasi-isomorphism on K-injective coefficients.

Source: Stacks Project, sites-cohomology.tex, Tag 0A0A,
lemma-colim-and-lim-of-duals; derived.tex, Tag 0949, lemma-colim-hocolim.
(auxiliary; not a blueprint node).

Proof: write P for the positive finite Koszul diagram and S for its direct sum.
The canonical telescope map Cone(1-shift:S→S)→colim P is a quasi-isomorphism.
Internal Hom into I inverts this map, because I is K-injective. Finite Koszul
 evaluation identifies Hom(P_m,I) with I tensor Hom(P_m,O[0]), naturally in m,
 including transitions. Hom sends S to the product of these complexes. Applying
 Hom to the telescope gives the mapping fibre of minus one-minus-shift on that
 product. Explicitly, put T=Hom(S,I) and let delta be precomposition by 1-shift.
 A degree-n map on the telescope has coordinates (a,b) in T^n and T^(n-1).
 Its differential is (d a, d b + (-1)^(n+1) delta(a)). The map
 (a,b) ↦ (a,(-1)^n b) identifies this with Cone(-delta)[-1], whose differential
 is (d a, delta(a)-d c) in coordinates (a,c). Hom(colim P,I) is the
 ordinary inverse limit, by the colimit universal property degree by degree.
 Under these identifications Hom of the canonical telescope map is exactly the
 ordinary-limit inclusion with zero second coordinate: the unshifted direct-sum
 leg is the family of colimit legs, and the shifted leg is zero. Hence the map
 in the statement is a quasi-isomorphism. For r=0 the diagram is constant and
 the same telescope argument applies. Zero and invertible generators change
 neither the universal properties nor the cone identification. No assertion
 about a derived-limit functor or about exactness of products is used. -/
theorem quasiIso_ringedKoszul_roosComparison (I : ringedSiteComplex O)
    [I.IsKInjective] :
    QuasiIso (ExactProductsRoos.comparison.app (ringedKoszulTensorTowerComplex O r b I)) := by
  obtain ⟨f, hf₁, hf₂, hf⟩ :=
    CochainComplex.quasiIso_telescopeColimit O (ringedKoszulDiagram O r b)
  let : QuasiIso f := hf
  have hHom : QuasiIso (((homComplexFunctor (R := O)).map f.op).app I) := by
    simpa only [Functor.map_id, Category.comp_id] using
      (quasiIso_homComplex_map (𝟙 I) f)
  obtain ⟨e⟩ := exists_ringedKoszul_finiteHomTower_iso O r b I
  obtain ⟨a⟩ := telescopeHom_roos_arrow_iso O (ringedKoszulDiagram O r b) I
    (ringedKoszulTensorTowerComplex O r b I) e f hf₁ hf₂
  exact (quasiIso_iff_of_arrow_mk_iso _ _ a).mp hHom

end CategoryTheory
