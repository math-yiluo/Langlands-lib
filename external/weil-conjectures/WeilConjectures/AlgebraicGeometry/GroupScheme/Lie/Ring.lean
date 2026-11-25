/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.Basic
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Functoriality

/-!
# The Lie algebra of a group scheme over a ring

The Lie algebra of a group scheme over `Spec R` through the points with values in the ring of
dual numbers.
-/

@[expose] public section

universe u

open CategoryTheory TrivSqZeroExt
open scoped MonObj

namespace AlgebraicGeometry

/-! ### Group schemes over a ring -/

section Ring

variable {R : Type u} [CommRing R]

namespace GrpObj

variable (G : Over (Spec (.of R))) [GrpObj G]

/-- The `R`-module structure on `Lie(G)` for a group scheme over `Spec R`, through
`R ≅ Γ(Spec R, 𝒪)`. -/
noncomputable instance : Module R (Lie G) :=
  Module.compHom (Lie G) (Scheme.ΓSpecIso (.of R)).inv.hom

end GrpObj

/-! ### Points with values in the ring of dual numbers -/

/-- The `A`-points `X(A)` of a scheme `X` over `R`: the morphisms `Spec A ⟶ X` over `Spec R`. For a
group scheme `X` they form a group by `Hom.group`. -/
abbrev points (X : Over (Spec (.of R))) (A : Type u) [CommRing A] [Algebra R A] :=
  (Spec (.of A)).asOver (Spec (.of R)) ⟶ X

/-- The map `X(A) → X(B)` induced by an `R`-algebra homomorphism `φ : A → B`: precomposition with
`Spec φ : Spec B ⟶ Spec A`. -/
noncomputable def points.map (X : Over (Spec (.of R))) {A B : Type u} [CommRing A] [Algebra R A]
    [CommRing B] [Algebra R B] (φ : A →ₐ[R] B) (x : points X A) : points X B :=
  (Spec.map (CommRingCat.ofHom φ.toRingHom)).asOver (Spec (.of R)) ≫ x

variable (G : Over (Spec (.of R))) [GrpObj G]

/-- The tangent group `T_1 G = ker(G(R[ε]) → G(R))` of a group scheme `G` over `R`: the points of
`G` with values in the ring of dual numbers that reduce to the identity modulo `ε`. Through the
isomorphism `(Spec R)[ε] ≅ Spec R[ε]` these are the infinitesimal points of `G`.
(blueprint: `def-wf-lie-algebra-derivation`) -/
noncomputable def tangentGroup : Subgroup (points G (DualNumber R)) :=
  (pointsPrecomp G ((Spec.map (CommRingCat.ofHom (fstHom R R R).toRingHom)).asOver _)).ker

theorem mem_tangentGroup {x : points G (DualNumber R)} :
    x ∈ tangentGroup G ↔ points.map G (fstHom R R R) x = 1 :=
  MonoidHom.mem_ker

/-- The isomorphism `(Spec R)[ε] ⟶ Spec R[ε]` as a morphism over `Spec R`. -/
noncomputable def dualNumbersToSpecOver :
    Scheme.dualNumbersOver (Spec (.of R)) ⟶ (Spec (.of (DualNumber R))).asOver (Spec (.of R)) :=
  Over.homMk (Scheme.dualNumbersToSpec (.of R)) (Scheme.dualNumbersToSpec_comp_specMap (.of R))

instance : IsIso (dualNumbersToSpecOver (R := R)) := by
  have : IsIso ((Over.forget _).map (dualNumbersToSpecOver (R := R))) :=
    Scheme.isIso_dualNumbersToSpec (.of R)
  exact isIso_of_reflects_iso _ (Over.forget _)

/-- The point `ε ↦ 0` of `Spec R[ε]` is the closed immersion `i : S ⟶ S[ε]` through
`(Spec R)[ε] ≅ Spec R[ε]`. -/
theorem specMap_fstHom_asOver_eq :
    (Spec.map (CommRingCat.ofHom (fstHom R R R).toRingHom)).asOver (Spec (.of R)) =
      CartesianMonoidalCategory.toUnit _ ≫ Scheme.dualNumbersιOver (Spec (.of R)) ≫
        dualNumbersToSpecOver := by
  ext1
  simp [dualNumbersToSpecOver, Scheme.ι_comp_dualNumbersToSpec, Over.toUnit_left,
    specOverSpec_over]
  rfl

/-- An infinitesimal point gives a point of the tangent group through `(Spec R)[ε] ≅ Spec R[ε]`. -/
theorem GrpObj.inv_dualNumbersToSpecOver_comp_mem_tangentGroup
    {v : Scheme.dualNumbersOver (Spec (.of R)) ⟶ G} (hv : v ∈ GrpObj.infPoints G) :
    inv dualNumbersToSpecOver ≫ v ∈ tangentGroup G := by
  rw [mem_tangentGroup, points.map, specMap_fstHom_asOver_eq]
  simp only [Category.assoc, IsIso.hom_inv_id_assoc]
  rw [(GrpObj.mem_infPoints G).1 hv, MonObj.comp_one]

/-- A point of the tangent group gives an infinitesimal point through `(Spec R)[ε] ≅ Spec R[ε]`. -/
theorem GrpObj.dualNumbersToSpecOver_comp_mem_infPoints {x : points G (DualNumber R)}
    (hx : x ∈ tangentGroup G) :
    dualNumbersToSpecOver ≫ x ∈ GrpObj.infPoints G := by
  rw [mem_tangentGroup, points.map, specMap_fstHom_asOver_eq] at hx
  -- Writing `Over.homMk (𝟙 (Spec (.of R)))` rather than `Over.homMk (𝟙 _)` avoids a slow kernel
  -- check.
  let s : Over.mk (𝟙 (Spec (.of R))) ⟶ (Spec (.of R)).asOver (Spec (.of R)) :=
    Over.homMk (𝟙 (Spec (.of R))) (by simp [specOverSpec_over])
  have e : s ≫ CartesianMonoidalCategory.toUnit _ = 𝟙 _ :=
    CartesianMonoidalCategory.toUnit_unique _ _
  simp only [Category.assoc] at hx
  have h := congrArg (s ≫ ·) hx
  simp only [MonObj.comp_one] at h
  rw [← Category.assoc s, e, Category.id_comp] at h
  exact (GrpObj.mem_infPoints G).2 h

/-- The infinitesimal points of `G` are the points with values in the ring of dual numbers reducing
to the identity, through `(Spec R)[ε] ≅ Spec R[ε]`. -/
noncomputable def GrpObj.infPointsEquivTangentGroup : GrpObj.infPoints G ≃* tangentGroup G where
  toFun v :=
    ⟨inv dualNumbersToSpecOver ≫ v.1, GrpObj.inv_dualNumbersToSpecOver_comp_mem_tangentGroup G v.2⟩
  invFun x := ⟨dualNumbersToSpecOver ≫ x.1, GrpObj.dualNumbersToSpecOver_comp_mem_infPoints G x.2⟩
  left_inv v := Subtype.ext (IsIso.hom_inv_id_assoc dualNumbersToSpecOver v.1)
  right_inv x := Subtype.ext (IsIso.inv_hom_id_assoc dualNumbersToSpecOver x.1)
  map_mul' _ _ := Subtype.ext (MonObj.comp_mul _ _ _)

@[simp]
theorem GrpObj.coe_infPointsEquivTangentGroup_apply (v : GrpObj.infPoints G) :
    (GrpObj.infPointsEquivTangentGroup G v : points G (DualNumber R)) =
      inv dualNumbersToSpecOver ≫ (v : Scheme.dualNumbersOver _ ⟶ G) :=
  rfl

/-- Through `(Spec R)[ε] ≅ Spec R[ε]`, scaling the infinitesimal by `c ∈ R` is `Spec` of
`ε ↦ cε`. -/
theorem dualNumbersScaleOver_comp_dualNumbersToSpecOver (c : R) :
    Scheme.dualNumbersScaleOver (Spec (.of R)) ((Scheme.ΓSpecIso (.of R)).inv c) ≫
        dualNumbersToSpecOver =
      dualNumbersToSpecOver ≫
        (Spec.map (CommRingCat.ofHom (DualNumber.scale c).toRingHom)).asOver (Spec (.of R)) := by
  ext1
  dsimp only [Over.comp_left, Scheme.dualNumbersScaleOver_left]
  exact Scheme.dualNumbersScale_comp_dualNumbersToSpec (.of R) c

/-! ### Tangent points -/

namespace GrpObj

variable {G}

/-- The point of `G` with values in the dual numbers `R[ε]` of a tangent vector `x ∈ Lie(G)`: the
infinitesimal point of `x`, through `(Spec R)[ε] ≅ Spec R[ε]`. (blueprint:
`def-wf-lie-algebra-derivation`) -/
noncomputable def tangentPoint (x : Lie G) : points G (DualNumber R) :=
  infPointsEquivTangentGroup G ((lieEquiv G).symm x)

theorem tangentPoint_mem_tangentGroup (x : Lie G) : tangentPoint x ∈ tangentGroup G :=
  (infPointsEquivTangentGroup G ((lieEquiv G).symm x)).2

theorem tangentPoint_injective : Function.Injective (tangentPoint (G := G)) := fun _ _ h ↦
  (lieEquiv G).symm.injective ((infPointsEquivTangentGroup G).injective (Subtype.ext h))

theorem exists_tangentPoint_eq {p : points G (DualNumber R)} (hp : p ∈ tangentGroup G) :
    ∃ x : Lie G, tangentPoint x = p :=
  ⟨lieEquiv G ((infPointsEquivTangentGroup G).symm ⟨p, hp⟩), by
    simp [tangentPoint]⟩

end GrpObj

end Ring

end AlgebraicGeometry
