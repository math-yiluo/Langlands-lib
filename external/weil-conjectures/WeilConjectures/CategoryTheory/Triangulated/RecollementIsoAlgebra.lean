/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraAdjunction
public import WeilConjectures.CategoryTheory.Triangulated.Recollement

/-!
# Equivariant recollements

Consider recollement data in the sense of `WeilConjectures.CategoryTheory.Triangulated.Recollement`:
a fully faithful `i : Z ⥤ C`, an adjunction `j^* ⊣ j_*` (`C ⇄ U`) with invertible counit, the
right adjoint `G = i^!` of `i`, `j^* i = 0`, and every object killed by `j^*` in the essential
image of `i`. Let `FC`, `FZ`, `FU` be endofunctors of `C`, `Z`, `U` (a "Frobenius"), `FC` being
triangulated, together with commutation isomorphisms `αi : i ⋙ FC ≅ FZ ⋙ i`,
`αj : j^* ⋙ FU ≅ FC ⋙ j^*` and `αjLow : j_* ⋙ FC ≅ FU ⋙ j_*`.

We show the formal part of the Weil clause of blueprint `lemma-local-cohomology-right-adjoint--2`:

1. the mate `G ⋙ FZ ⟶ FC ⋙ G` of `αi⁻¹` is an isomorphism
   (`CategoryTheory.Pretriangulated.Recollement.rightAdjointIso`), because `FC` carries the
   supported localization triangle of `K` to the one of `FC K`; hence `i ⊣ i^!` lifts to an
   adjunction between the categories of objects with a Frobenius structure
   `CategoryTheory.Endofunctor.IsoAlgebra` (`Recollement.isoAlgebraAdjunction`): `i^!` carries
   Frobenius structures, and the adjunction, unit and counit are equivariant;
2. the mate `FC ⋙ j^* ⟶ j^* ⋙ FU` of `αjLow` is an isomorphism
   (`CategoryTheory.Pretriangulated.Recollement.leftAdjointIso`), so that `j^* ⊣ j_*` lifts to
   objects with Frobenius structure as well
   (`Recollement.mateEquiv_leftAdjointIso_inv`,
   `CategoryTheory.Endofunctor.IsoAlgebra.mapOfNatIsoAdjunction`);
3. if `αjLow` is the mate of `αj⁻¹`, then for `(K, θ : FC K ≅ K)` all three arrows of the
   supported localization triangle `i i^! K ⟶ K ⟶ j_* j^* K ⟶ (i i^! K)⟦1⟧` commute with the
   Frobenius structures (`Recollement.mapTriangleIso`): for the third arrow this follows from the
   uniqueness of the third arrow (`Recollement.map_mor₃_comp_str`).
-/

@[expose] public section

namespace CategoryTheory.Pretriangulated.Recollement

open Limits Category Endofunctor

variable {C Z U : Type*} [Category* C] [Category* Z] [Category* U]
  [Preadditive C] [HasZeroObject C] [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] [Preadditive U] [HasZeroObject U] [HasShift U ℤ]
  [∀ n : ℤ, (shiftFunctor U n).Additive] [Pretriangulated U]
  {i : Z ⥤ C} {jUp : C ⥤ U} [jUp.CommShift ℤ] [jUp.IsTriangulated] {jLow : U ⥤ C}
  (adj : jUp ⊣ jLow) {G : C ⥤ Z} (adj' : i ⊣ G)
  {FC : C ⥤ C} [FC.CommShift ℤ] [FC.IsTriangulated] {FZ : Z ⥤ Z} {FU : U ⥤ U}
  (αi : i ⋙ FC ≅ FZ ⋙ i) (αj : jUp ⋙ FU ≅ FC ⋙ jUp) (αjLow : jLow ⋙ FC ≅ FU ⋙ jLow)
  (hi : i.FullyFaithful) [IsIso adj.counit] (h₀ : ∀ M, IsZero (jUp.obj (i.obj M)))
  (hess : ∀ K, IsZero (jUp.obj K) → i.essImage K)

include adj αjLow hi h₀ hess in
/-- In a recollement, the mate `G ⋙ FZ ⟶ FC ⋙ G` of `αi⁻¹ : FZ ⋙ i ⟶ i ⋙ FC` along `i ⊣ G` is
an isomorphism: `FC` carries the supported localization triangle of `K` to a distinguished
triangle with vertices in the essential images of `i` and `j_*`, which is therefore the supported
localization triangle of `FC K` (`CategoryTheory.Pretriangulated.Recollement.exists_iso_triangle`).
Blueprint `lemma-local-cohomology-right-adjoint--2` (Weil clause). -/
lemma isIso_mateEquiv : IsIso (mateEquiv adj' adj' αi.inv) := by
  have (K : C) : IsIso ((mateEquiv adj' adj' αi.inv).app K) := by
    obtain ⟨w, hw⟩ := exists_distTriang_counit_unit adj adj' hi h₀ hess K
    obtain ⟨w', hw'⟩ := exists_distTriang_counit_unit adj adj' hi h₀ hess (FC.obj K)
    obtain ⟨e, he⟩ := exists_iso_triangle adj adj' h₀ (FC.map_distinguished _ hw)
      ⟨_, ⟨(αi.app (G.obj K)).symm⟩⟩ ⟨_, ⟨(αjLow.app (jUp.obj K)).symm⟩⟩ hw'
    refine adj'.isIso_mateEquiv_app adj' hi αi.inv K (Triangle.π₁.mapIso e) ?_
    have h := e.hom.comm₁
    rw [he, comp_id] at h
    exact h.symm
  exact NatIso.isIso_of_isIso_app _

/-- In a recollement, the isomorphism `i^! ⋙ FZ ≅ FC ⋙ i^!`, the mate of `αi⁻¹` along `i ⊣ i^!`
(`CategoryTheory.Pretriangulated.Recollement.isIso_mateEquiv`). It is the Frobenius structure of
`i^!` of blueprint `lemma-local-cohomology-right-adjoint--2` (Weil clause). -/
noncomputable def rightAdjointIso : G ⋙ FZ ≅ FC ⋙ G :=
  have := isIso_mateEquiv adj adj' αi αjLow hi h₀ hess
  asIso (mateEquiv adj' adj' αi.inv)

lemma mateEquiv_inv_eq_rightAdjointIso_hom :
    mateEquiv adj' adj' αi.inv = (rightAdjointIso adj adj' αi αjLow hi h₀ hess).hom :=
  rfl

/-- Blueprint `lemma-local-cohomology-right-adjoint--2` (Weil clause): in a recollement, `i ⊣ i^!`
lifts to an adjunction between objects with Frobenius structure (`IsoAlgebra FZ ⇄ IsoAlgebra FC`),
`i^!` carrying the Frobenius structure `CategoryTheory.Pretriangulated.Recollement.rightAdjointIso`;
its unit and counit have the unit and counit of `i ⊣ i^!` as underlying morphisms, i.e. they are
equivariant. -/
noncomputable def isoAlgebraAdjunction :
    IsoAlgebra.mapOfNatIso αi ⊣
      IsoAlgebra.mapOfNatIso (rightAdjointIso adj adj' αi αjLow hi h₀ hess) :=
  IsoAlgebra.mapOfNatIsoAdjunction adj' _ _
    (mateEquiv_inv_eq_rightAdjointIso_hom adj adj' αi αjLow hi h₀ hess)

include αi h₀ hess in
/-- In a recollement, the mate `FC ⋙ j^* ⟶ j^* ⋙ FU` of `αjLow : j_* ⋙ FC ≅ FU ⋙ j_*` along
`j^* ⊣ j_*` is an isomorphism: at `K` it is `j^*` of `FC` of the unit `K ⟶ j_* j^* K`, followed
by isomorphisms, and the fibre of the unit lies in the essential image of `i`, which `FC` carries
into the essential image of `i` (by `αi`) and `j^*` kills.
Blueprint `lemma-local-cohomology-right-adjoint--2` (Weil clause). -/
lemma isIso_mateEquiv_symm : IsIso ((mateEquiv adj adj).symm αjLow.hom) := by
  have (K : C) : IsIso (((mateEquiv adj adj).symm αjLow.hom).app K) := by
    obtain ⟨F, a, δ, hT, M, ⟨e⟩⟩ := exists_distTriang_unit adj hess K
    have : IsIso (jUp.map (FC.map (adj.unit.app K))) :=
      (Triangle.isZero₁_iff_isIso₂ _ (jUp.map_distinguished _ (FC.map_distinguished _ hT))).1
        ((h₀ (FZ.obj M)).of_iso (jUp.mapIso (FC.mapIso e.symm ≪≫ αi.app M)))
    have h : ((mateEquiv adj adj).symm αjLow.hom).app K =
        jUp.map (FC.map (adj.unit.app K)) ≫ jUp.map (αjLow.hom.app (jUp.obj K)) ≫
          adj.counit.app (FU.obj (jUp.obj K)) := by
      simp [mateEquiv]
    rw [h]
    infer_instance
  exact NatIso.isIso_of_isIso_app _

/-- In a recollement, the isomorphism `j^* ⋙ FU ≅ FC ⋙ j^*` whose inverse is the mate of
`αjLow : j_* ⋙ FC ≅ FU ⋙ j_*` along `j^* ⊣ j_*`
(`CategoryTheory.Pretriangulated.Recollement.isIso_mateEquiv_symm`).
Blueprint `lemma-local-cohomology-right-adjoint--2` (Weil clause). -/
noncomputable def leftAdjointIso : jUp ⋙ FU ≅ FC ⋙ jUp :=
  have := isIso_mateEquiv_symm adj αi αjLow h₀ hess
  (asIso ((mateEquiv adj adj).symm αjLow.hom)).symm

/-- `αjLow` is the mate of the inverse of
`CategoryTheory.Pretriangulated.Recollement.leftAdjointIso`, so that `j^* ⊣ j_*` lifts to objects
with Frobenius structure (`CategoryTheory.Endofunctor.IsoAlgebra.mapOfNatIsoAdjunction`). -/
lemma mateEquiv_leftAdjointIso_inv :
    mateEquiv adj adj (leftAdjointIso adj αi αjLow h₀ hess).inv = αjLow.hom :=
  (mateEquiv adj adj).apply_symm_apply _

/-- The Frobenius structure `FC (i i^! K) ≅ i i^! K` of the first vertex of the supported
localization triangle of an object `K` with Frobenius structure. -/
noncomputable abbrev strClosed (K : IsoAlgebra FC) : FC.obj (i.obj (G.obj K.carrier)) ≅
    i.obj (G.obj K.carrier) :=
  ((IsoAlgebra.mapOfNatIso αi).obj
    ((IsoAlgebra.mapOfNatIso (rightAdjointIso adj adj' αi αjLow hi h₀ hess)).obj K)).str

/-- The Frobenius structure `FC (j_* j^* K) ≅ j_* j^* K` of the third vertex of the supported
localization triangle of an object `K` with Frobenius structure. -/
noncomputable abbrev strOpen (K : IsoAlgebra FC) : FC.obj (jLow.obj (jUp.obj K.carrier)) ≅
    jLow.obj (jUp.obj K.carrier) :=
  ((IsoAlgebra.mapOfNatIso αjLow).obj ((IsoAlgebra.mapOfNatIso αj).obj K)).str

/-- The counit `i i^! K ⟶ K` is Frobenius-equivariant. -/
@[reassoc]
lemma map_counit_comp_str (K : IsoAlgebra FC) :
    FC.map (adj'.counit.app K.carrier) ≫ K.str.hom =
      (strClosed adj adj' αi αjLow hi h₀ hess K).hom ≫ adj'.counit.app K.carrier :=
  ((isoAlgebraAdjunction adj adj' αi αjLow hi h₀ hess).counit.app K).hom.h

variable {αj αjLow} (hj : mateEquiv adj adj αj.inv = αjLow.hom)

omit [Preadditive C] [HasShift C ℤ] [Preadditive U] [HasShift U ℤ] [HasZeroObject C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [HasZeroObject U] [∀ n : ℤ, (shiftFunctor U n).Additive] [Pretriangulated U]
  [jUp.CommShift ℤ] [jUp.IsTriangulated] [FC.CommShift ℤ] [FC.IsTriangulated]
  [IsIso adj.counit] in
include hj in
/-- The unit `K ⟶ j_* j^* K` is Frobenius-equivariant, if `αjLow` is the mate of `αj⁻¹`. -/
@[reassoc]
lemma map_unit_comp_str (K : IsoAlgebra FC) :
    FC.map (adj.unit.app K.carrier) ≫ (strOpen αj αjLow K).hom =
      K.str.hom ≫ adj.unit.app K.carrier :=
  ((IsoAlgebra.mapOfNatIsoAdjunction adj _ _ hj).unit.app K).hom.h

include hj in
/-- Blueprint `lemma-local-cohomology-right-adjoint--2` (Weil clause): the third arrow
`w : j_* j^* K ⟶ (i i^! K)⟦1⟧` of the supported localization triangle of an object `K` with
Frobenius structure is Frobenius-equivariant. Indeed, transporting the image under `FC` of the
triangle along the Frobenius structures of its vertices gives a distinguished triangle whose
first two arrows are the counit and the unit (`map_counit_comp_str`, `map_unit_comp_str`), so
its third arrow is `w` by uniqueness
(`CategoryTheory.Pretriangulated.Recollement.existsUnique_distTriang_counit_unit`). -/
theorem map_mor₃_comp_str (K : IsoAlgebra FC) {w : jLow.obj (jUp.obj K.carrier) ⟶ _}
    (hw : triangle adj adj' K.carrier w ∈ distTriang C) :
    FC.map w ≫ (FC.commShiftIso (1 : ℤ)).hom.app _ ≫
        (strClosed adj adj' αi αjLow hi h₀ hess K).hom⟦(1 : ℤ)⟧' =
      (strOpen αj αjLow K).hom ≫ w := by
  set s₁ := strClosed adj adj' αi αjLow hi h₀ hess K
  set s₃ := strOpen αj αjLow K
  let w' := s₃.inv ≫ FC.map w ≫ (FC.commShiftIso (1 : ℤ)).hom.app _ ≫ s₁.hom⟦(1 : ℤ)⟧'
  have e : FC.mapTriangle.obj (triangle adj adj' K.carrier w) ≅ triangle adj adj' K.carrier w' :=
    Triangle.isoMk _ _ s₁ K.str s₃ (map_counit_comp_str adj adj' αi αjLow hi h₀ hess K)
      (map_unit_comp_str adj hj K) (by simp only [w', Iso.hom_inv_id_assoc]; exact assoc _ _ _)
  have hw' := isomorphic_distinguished _ (FC.map_distinguished _ hw) _ e.symm
  have := (existsUnique_distTriang_counit_unit adj adj' hi h₀ hess K.carrier).unique hw' hw
  exact (Iso.inv_comp_eq s₃).1 this

/-- Blueprint `lemma-local-cohomology-right-adjoint--2` (Weil clause): the supported localization
triangle `i i^! K ⟶ K ⟶ j_* j^* K ⟶ (i i^! K)⟦1⟧` of an object `K` with Frobenius structure is
Frobenius-equivariant: the Frobenius structures of its vertices form an isomorphism of triangles
from its image under `FC`. -/
noncomputable def mapTriangleIso (K : IsoAlgebra FC) {w : jLow.obj (jUp.obj K.carrier) ⟶ _}
    (hw : triangle adj adj' K.carrier w ∈ distTriang C) :
    FC.mapTriangle.obj (triangle adj adj' K.carrier w) ≅ triangle adj adj' K.carrier w :=
  Triangle.isoMk _ _ (strClosed adj adj' αi αjLow hi h₀ hess K) K.str (strOpen αj αjLow K)
    (map_counit_comp_str adj adj' αi αjLow hi h₀ hess K) (map_unit_comp_str adj hj K)
    (by rw [← map_mor₃_comp_str adj adj' αi hi h₀ hess hj K hw]; exact assoc _ _ _)

@[simp]
lemma mapTriangleIso_hom_hom₁ (K : IsoAlgebra FC) {w : jLow.obj (jUp.obj K.carrier) ⟶ _}
    (hw : triangle adj adj' K.carrier w ∈ distTriang C) :
    (mapTriangleIso adj adj' αi hi h₀ hess hj K hw).hom.hom₁ =
      (strClosed adj adj' αi αjLow hi h₀ hess K).hom :=
  rfl

@[simp]
lemma mapTriangleIso_hom_hom₂ (K : IsoAlgebra FC) {w : jLow.obj (jUp.obj K.carrier) ⟶ _}
    (hw : triangle adj adj' K.carrier w ∈ distTriang C) :
    (mapTriangleIso adj adj' αi hi h₀ hess hj K hw).hom.hom₂ = K.str.hom :=
  rfl

@[simp]
lemma mapTriangleIso_hom_hom₃ (K : IsoAlgebra FC) {w : jLow.obj (jUp.obj K.carrier) ⟶ _}
    (hw : triangle adj adj' K.carrier w ∈ distTriang C) :
    (mapTriangleIso adj adj' αi hi h₀ hess hj K hw).hom.hom₃ = (strOpen αj αjLow K).hom :=
  rfl

end CategoryTheory.Pretriangulated.Recollement
