/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.KInjective

/-!
# Resolution independence of derived functors computed by K-injective resolutions

If `s : K ⟶ I` and `t : K ⟶ J` are two K-injective resolutions of a cochain complex `K`, then
`I` and `J` are isomorphic in the homotopy category. Consequently, for every additive functor
`G`, the complexes `G(I)` and `G(J)` have isomorphic cohomology: the groups `Hᵠ(T_ét, F)`
computed from a K-injective resolution of `F` do not depend on the chosen resolution.

## Main statements

- `CochainComplex.IsKInjective.nonempty_iso_quotient_obj`: two K-injective resolutions are
  isomorphic in the homotopy category.
- `CochainComplex.IsKInjective.nonempty_homology_iso`: their images under an additive functor
  have isomorphic cohomology.
- `CochainComplex.IsKInjective.isIso_of_isIso_Qh_map`: `Qh` reflects isomorphisms between
  K-injective complexes.
-/

@[expose] public section

open CategoryTheory DerivedCategory

namespace CochainComplex.IsKInjective

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]

/-- Two K-injective resolutions `s : K ⟶ I`, `t : K ⟶ J` of the same complex are isomorphic in
the homotopy category: the isomorphism `Q(I) ≅ Q(K) ≅ Q(J)` of the derived category lifts,
since `Qh` is bijective on morphisms with K-injective target. -/
theorem nonempty_iso_quotient_obj {K I J : CochainComplex C ℤ} (s : K ⟶ I) (t : K ⟶ J)
    [QuasiIso s] [QuasiIso t] [I.IsKInjective] [J.IsKInjective] :
    Nonempty ((HomotopyCategory.quotient C (.up ℤ)).obj I ≅
      (HomotopyCategory.quotient C (.up ℤ)).obj J) := by
  let e : Qh.obj ((HomotopyCategory.quotient C (.up ℤ)).obj I) ≅
      Qh.obj ((HomotopyCategory.quotient C (.up ℤ)).obj J) :=
    (quotientCompQhIso C).app I ≪≫ (asIso (Q.map s)).symm ≪≫ asIso (Q.map t) ≪≫
      (quotientCompQhIso C).symm.app J
  obtain ⟨a, ha⟩ := (Qh_map_bijective ((HomotopyCategory.quotient C (.up ℤ)).obj I) J).2 e.hom
  obtain ⟨b, hb⟩ := (Qh_map_bijective ((HomotopyCategory.quotient C (.up ℤ)).obj J) I).2 e.inv
  refine ⟨⟨a, b, (Qh_map_bijective _ I).1 ?_, (Qh_map_bijective _ J).1 ?_⟩⟩
  · rw [Functor.map_comp, ha, hb, e.hom_inv_id, CategoryTheory.Functor.map_id]
  · rw [Functor.map_comp, ha, hb, e.inv_hom_id, CategoryTheory.Functor.map_id]

/-- **Resolution independence.** If `s : K ⟶ I` and `t : K ⟶ J` are two K-injective resolutions
of a cochain complex `K` and `G` is an additive functor, then `Hᵠ(G(I)) ≅ Hᵠ(G(J))` for every
`q`: the two resolutions are homotopy equivalent, and `G` preserves homotopies. For
`G = Γ(T, -)` and `K = F[0]` this says that the étale cohomology groups `Hᵠ(T_ét, F)` do not
depend on the chosen K-injective resolution of `F`.
(blueprint: `prop-weil-pbc-cohomology-resolution-independent`) -/
theorem nonempty_homology_iso {D : Type*} [Category* D] [Abelian D] (G : C ⥤ D) [G.Additive]
    {K I J : CochainComplex C ℤ} (s : K ⟶ I) (t : K ⟶ J) [QuasiIso s] [QuasiIso t]
    [I.IsKInjective] [J.IsKInjective] (q : ℤ) :
    Nonempty (((G.mapHomologicalComplex _).obj I).homology q ≅
      ((G.mapHomologicalComplex _).obj J).homology q) := by
  obtain ⟨e⟩ := nonempty_iso_quotient_obj s t
  exact ⟨(HomotopyCategory.homologyFunctorFactors D (.up ℤ) q).symm.app _ ≪≫
    (HomotopyCategory.homologyFunctor D (.up ℤ) q).mapIso
      ((G.mapHomotopyCategoryFactors (.up ℤ)).symm.app I ≪≫
        (G.mapHomotopyCategory (.up ℤ)).mapIso e ≪≫
        (G.mapHomotopyCategoryFactors (.up ℤ)).app J) ≪≫
    (HomotopyCategory.homologyFunctorFactors D (.up ℤ) q).app _⟩

/-- A morphism between K-injective complexes in the homotopy category is an isomorphism as soon
as its image in the derived category is: `Qh` is fully faithful on K-injective complexes. -/
theorem isIso_of_isIso_Qh_map {I J : CochainComplex C ℤ} [I.IsKInjective] [J.IsKInjective]
    (f : (HomotopyCategory.quotient C (.up ℤ)).obj I ⟶ (HomotopyCategory.quotient C (.up ℤ)).obj J)
    [IsIso (Qh.map f)] : IsIso f := by
  obtain ⟨g, hg⟩ := (Qh_map_bijective ((HomotopyCategory.quotient C (.up ℤ)).obj J) I).2
    (inv (Qh.map f))
  refine ⟨g, (Qh_map_bijective _ I).1 ?_, (Qh_map_bijective _ J).1 ?_⟩
  · rw [Functor.map_comp, hg, IsIso.hom_inv_id, CategoryTheory.Functor.map_id]
  · rw [Functor.map_comp, hg, IsIso.inv_hom_id, CategoryTheory.Functor.map_id]

end CochainComplex.IsKInjective
