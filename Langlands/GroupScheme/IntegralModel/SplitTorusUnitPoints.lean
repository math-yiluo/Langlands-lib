import Langlands.GroupScheme.IntegralModel.SplitTorusClosure
import Langlands.GroupScheme.Torus.UniversalPoint
import Langlands.GroupScheme.CorepresentedAffineComparison

/-! # Split coordinates of the universal point of the generic split torus -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.IntegralModel.SplitTorusClosure

open Langlands.Algebra.HopfPointIntegralClosure

section Coordinates

variable {S : Scheme.{u}} {I : Type u} [Finite I]

/-- The split coordinates of a point depend only on its underlying scheme morphism. -/
theorem pointsEquiv_eq_of_left_eq {X : Scheme.{u}} {f₁ f₂ : X ⟶ S}
    (x : Over.mk f₁ ⟶ (splitTorus S I).X) (y : Over.mk f₂ ⟶ (splitTorus S I).X)
    (h : (x.left : X ⟶ (splitTorus S I).X.left) = y.left) :
    splitTorus.pointsEquiv I (Over.mk f₁) x = splitTorus.pointsEquiv I (Over.mk f₂) y := by
  funext i
  apply Units.ext
  rw [splitTorus.pointsEquiv_apply, splitTorus.pointsEquiv_apply, Gm.pointsEquiv_val,
    Gm.pointsEquiv_val, Over.comp_left, Over.comp_left, h]
  rfl

/-- Affine split coordinates are the global-section images of the split coordinates. -/
theorem affinePointsEquiv_val {A : CommRingCat.{u}} (f : Spec A ⟶ S)
    (x : Over.mk f ⟶ (splitTorus S I).X) (i : I) :
    (splitTorus.affinePointsEquiv I f x i : A) =
      (Scheme.ΓSpecIso A).hom (splitTorus.pointsEquiv I (Over.mk f) x i).val :=
  rfl

end Coordinates

section SplitIso

variable (R : Type u) [CommRing R] (I : Type u) [Fintype I] [DecidableEq I]

/-- The split isomorphism `D_R(ℤ^I) ≅ 𝔾_m^I`. -/
abbrev splitIsoR :
    (torus R I).toGrp ≅ splitTorus (Spec (CommRingCat.of R)) I :=
  Diagonalizable.splitIso (CommRingCat.of R) (AddEquiv.refl (I → ℤ))

/-- The split isomorphism `D_R(ℤ^I) ≅ 𝔾_m^I`, viewed as a point of `𝔾_m^I` with values in
the Laurent polynomial ring `R[ℤ^I]`. -/
def splitIsoPoint : Lie.AffinePoints (splitTorus (Spec (CommRingCat.of R)) I)
    (AddMonoidAlgebra R (I → ℤ)) :=
  (splitIsoR R I).hom.hom.hom

/-- The split coordinates of the image of `splitIsoPoint` under an algebra map
`φ : R[ℤ^I] → C` are the values of `φ` on the coordinate monomials. -/
theorem algebraPointsEquiv_affineMap_splitIsoPoint (C : Type u) [CommRing C] [Algebra R C]
    (φ : AddMonoidAlgebra R (I → ℤ) →ₐ[R] C) (i : I) :
    (splitTorus.algebraPointsEquiv (R := CommRingCat.of R) I C
        (Lie.affineMap _ φ (splitIsoPoint R I)) i : C) =
      φ (AddMonoidAlgebra.single (Pi.single i 1) 1) := by
  have hpts := isoOfPointModels_hom
    (fun T : Over (Spec (CommRingCat.of R)) => I → (Γ(T.left, ⊤))ˣ)
    (fun a => splitTorus.unitsRestrict I a)
    (Diagonalizable.splitPointsEquiv (CommRingCat.of R) (AddEquiv.refl (I → ℤ)))
    (fun T => splitTorus.pointsEquiv I T)
    (Diagonalizable.splitPointsEquiv_naturality (CommRingCat.of R) (AddEquiv.refl (I → ℤ)))
    (fun a y => splitTorus.pointsEquiv_naturality I a y)
    ((algSpec (CommRingCat.of R)).obj (op (CommAlgCat.of (CommRingCat.of R) C)))
    ((algSpec (CommRingCat.of R)).map (CommAlgCat.ofHom φ).op)
  rw [Lie.affineMap_apply]
  change (Scheme.ΓSpecIso (CommRingCat.of C)).hom
    (splitTorus.pointsEquiv I ((algSpec (CommRingCat.of R)).obj
      (op (CommAlgCat.of (CommRingCat.of R) C)))
      ((algSpec (CommRingCat.of R)).map (CommAlgCat.ofHom φ).op ≫
        (splitIsoR R I).hom.hom.hom) i).val = _
  erw [hpts]
  change (Scheme.ΓSpecIso (CommRingCat.of C)).hom
    ((DFunLike.coe (F := Multiplicative (I → ℤ) →*
        (Γ(Spec (CommRingCat.of C), ⊤))ˣ)
      (Corepresented.pointsEquiv (Diagonalizable.functor (CommRingCat.of R) (I → ℤ))
        (Diagonalizable.grpCorepresentation (CommRingCat.of R) (I → ℤ)) _
        ((algSpec (CommRingCat.of R)).map (CommAlgCat.ofHom φ).op))
      (Multiplicative.ofAdd (Pi.single i 1))).val) = _
  rw [Corepresented.pointsEquiv_eq_affinePointsEquiv]
  erw [Corepresented.affinePointsEquiv_map]
  change (Scheme.ΓSpecIso (CommRingCat.of C)).hom
    ((Corepresented.affineSectionsIso (CommAlgCat.of (CommRingCat.of R) C)).inv.hom
      (φ (AddMonoidAlgebra.single (Pi.single i 1) 1))) = _
  rw [← RingHom.coe_coe (Corepresented.affineSectionsIso _).inv.hom,
    ← AlgHom.toRingHom_eq_coe, Corepresented.affineSectionsIso_inv_ringHom]
  change ((Scheme.ΓSpecIso (CommRingCat.of C)).inv ≫ (Scheme.ΓSpecIso (CommRingCat.of C)).hom)
    _ = _
  rw [Iso.inv_hom_id]
  rfl

/-- The split isomorphism is the universal point of the split torus. -/
theorem splitIsoPoint_eq_universalPoint :
    splitIsoPoint R I = splitTorus.universalPoint (R := CommRingCat.of R) I := by
  apply (splitTorus.algebraPointsEquiv (R := CommRingCat.of R) I _).injective
  rw [splitTorus.algebraPointsEquiv_universalPoint]
  funext i
  apply Units.ext
  have h := algebraPointsEquiv_affineMap_splitIsoPoint R I _ (AlgHom.id R _) i
  rw [Lie.affineMap_id] at h
  rw [h]
  rfl

end SplitIso

section Generic

variable (R K : Type u) [CommRing R] [CommRing K] [Algebra R K] (I : Type u) [Fintype I]
  [DecidableEq I]

/-- The generic fibre of `D_R(ℤ^I)` is the split torus `𝔾_m^I` over `K`. -/
def genericSplitIso : genericTorus R K I ≅ splitTorus (Spec (CommRingCat.of K)) I :=
  (GroupScheme.baseChange (Spec.algebraMap R K)).mapIso (splitIsoR R I) ≪≫
    splitTorus.baseChangeIso (Spec.algebraMap R K) I

/-- Under the generic split isomorphism, the universal point of the generic fibre of
`D_R(ℤ^I)` is the universal point of `𝔾_m^I` over `K`. -/
theorem universalPoint_genericSplitIso :
    universalPoint R K I ≫ (genericSplitIso R K I).hom.hom.hom =
      splitTorus.universalPoint (R := CommRingCat.of K) I := by
  apply (splitTorus.algebraPointsEquiv (R := CommRingCat.of K) I _).injective
  rw [splitTorus.algebraPointsEquiv_universalPoint]
  funext i
  apply Units.ext
  let U := (algSpec (CommRingCat.of K)).obj
    (op (CommAlgCat.of (CommRingCat.of K) (AddMonoidAlgebra K (I → ℤ))))
  let T' := (algSpec (CommRingCat.of R)).obj
    (op (CommAlgCat.of (CommRingCat.of R) (AddMonoidAlgebra K (I → ℤ))))
  let b := Spec.algebraMap R K
  let x := GroupScheme.baseChangePointsEquiv b (torus R I).toGrp U (universalPoint R K I) ≫
    (splitIsoR R I).hom.hom.hom
  let y := (algSpec (CommRingCat.of R)).map (CommAlgCat.ofHom (incl R K I)).op ≫
    (splitIsoR R I).hom.hom.hom
  have hstep : splitTorus.pointsEquiv I U
      (universalPoint R K I ≫ (genericSplitIso R K I).hom.hom.hom) =
      splitTorus.pointsEquiv I ((Over.map b).obj U) x := by
    simp only [genericSplitIso, Iso.trans_hom, Grp.comp_hom_hom, Functor.mapIso_hom]
    rw [← Category.assoc, splitTorus.pointsEquiv_baseChangeIso_hom,
      splitTorus.baseChangePointsEquiv, MulEquiv.trans_apply]
    erw [GroupScheme.baseChangePointsEquiv_comp]
    rfl
  have hleft : (x.left : Spec (CommRingCat.of (AddMonoidAlgebra K (I → ℤ))) ⟶
      (splitTorus (Spec (CommRingCat.of R)) I).X.left) = y.left := by
    simp only [x, y, Over.comp_left]
    rw [GroupScheme.baseChangePointsEquiv_left, universalPoint_left, universalPointLeft_fst]
    rfl
  have hxy := pointsEquiv_eq_of_left_eq (S := Spec (CommRingCat.of R)) (I := I)
    (f₁ := ((Over.map b).obj U).hom) (f₂ := T'.hom) x y hleft
  have hcoord := algebraPointsEquiv_affineMap_splitIsoPoint R I _ (incl R K I) i
  change (Scheme.ΓSpecIso (CommRingCat.of (AddMonoidAlgebra K (I → ℤ)))).hom
    (splitTorus.pointsEquiv I U
      (universalPoint R K I ≫ (genericSplitIso R K I).hom.hom.hom) i).val = _
  rw [hstep]
  change (Scheme.ΓSpecIso (CommRingCat.of (AddMonoidAlgebra K (I → ℤ)))).hom
    (splitTorus.pointsEquiv I (Over.mk ((Over.map b).obj U).hom) x i).val = _
  rw [hxy]
  refine hcoord.trans ?_
  simp [incl]

/-- Under the generic split isomorphism, the unit point attached to a family of units `t` is
the point of `𝔾_m^I` with coordinates `t`. -/
theorem unitPoint_genericSplitIso (L : Type u) [CommRing L] [Algebra K L] (t : I → Lˣ) :
    unitPoint R K I L t ≫ (genericSplitIso R K I).hom.hom.hom =
      (splitTorus.algebraPointsEquiv (R := CommRingCat.of K) I L).symm t := by
  rw [← splitTorus.universalPoint_evaluateUnits, ← universalPoint_genericSplitIso R K I,
    unitPoint, affinePointMap_apply, Lie.affineMap_apply, Category.assoc]
  rfl

end Generic

section Closure

variable {R K : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K]
  [IsFractionRing R K] {G : GroupScheme (Spec (CommRingCat.of K))} (M : IntegralModel R K G)
  {I : Type u} [Fintype I] [DecidableEq I]
  (A L : Type u) [CommRing A] [IsDomain A] [ValuationRing A] [Field L]
  [Algebra R A] [Algebra A L] [IsFractionRing A L]
  [Algebra K L] [Algebra R L] [IsScalarTower R A L] [IsScalarTower R K L]
  [Infinite (IsLocalRing.ResidueField A)]

/-- **A closed split torus of the model from integral unit points.** Let `ψ : T → G` be a closed
subgroup of the generic fibre with `T ≅ 𝔾_m^I` split. If every family of units of `A` gives an
`L`-point of `T` whose image in `G` is an integral point of the base change of `M` to `A`, and
`K ∩ A = R` inside `L`, then `ψ` extends to a closed subgroup `D_R(ℤ^I) → M`. -/
theorem exists_isClosedSubgroup_genericTorusMap_eq {T : GroupScheme (Spec (CommRingCat.of K))}
    (e : T ≅ splitTorus (Spec (CommRingCat.of K)) I) (ψ : T ⟶ G) (hψ : IsClosedSubgroup ψ)
    (hunits : ∀ t : I → Aˣ,
      (splitTorus.algebraPointsEquiv (R := CommRingCat.of K) I L).symm
          (fun i => Units.map (algebraMap A L : A →* L) (t i)) ≫ e.inv.hom.hom ≫ ψ.hom.hom ∈
        (M.baseChange A L).coefficientIntegralPoints K L)
    (hint : ∀ x : K, algebraMap K L x ∈ Set.range (algebraMap A L) →
      x ∈ Set.range (algebraMap R K)) :
    ∃ j : (torus R I).toGrp ⟶ M.group, IsClosedSubgroup j ∧
      M.genericTorusMap (torus R I) j = (genericSplitIso R K I).hom ≫ e.inv ≫ ψ := by
  obtain ⟨j, hj⟩ := exists_genericTorusMap_eq M A L ((genericSplitIso R K I).hom ≫ e.inv ≫ ψ)
    (fun t => by
      have h := hunits t
      rw [← unitPoint_genericSplitIso R K I, Category.assoc] at h
      rw [affinePointsTarget_apply]
      exact h)
    hint
  refine ⟨j, isClosedSubgroup_of_genericTorusMap M j ?_, hj⟩
  rw [hj]
  exact IsClosedSubgroup.iso_comp _ (IsClosedSubgroup.iso_comp e.symm hψ)

end Closure

end Langlands.GroupScheme.IntegralModel.SplitTorusClosure
