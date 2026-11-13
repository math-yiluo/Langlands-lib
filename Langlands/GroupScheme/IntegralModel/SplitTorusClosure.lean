import Langlands.Algebra.HopfPointIntegralClosure
import Langlands.GroupScheme.IntegralModel.IntegralPointDescent
import Langlands.GroupScheme.IntegralModel.UnramifiedSplitMaximalTorus
import Langlands.GroupScheme.Torus.ClosedImmersionLocusAffine
import Langlands.GroupScheme.Torus.DiagonalizableHopf
import Langlands.GroupScheme.Descent.FiniteCoefficientHom

/-! # Extending a split torus with integral unit points to a closed split torus of a model -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj CategoryTheory.Obj TensorProduct

attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory
  CategoryTheory.Over.braidedCategory

namespace Langlands.GroupScheme.IntegralModel.SplitTorusClosure

open Langlands.AlgebraicGeometry.PointTopology
open Langlands.Algebra.HopfPointIntegralClosure

section UniversalPoint

variable (R K : Type u) [CommRing R] [CommRing K] [Algebra R K]
  (I : Type u)

/-- The split torus `D_R(ℤ^I) = Spec R[ℤ^I]` over `Spec R`. -/
abbrev torus : CommGroupScheme (Spec (CommRingCat.of R)) :=
  Diagonalizable.groupScheme (CommRingCat.of R) (I → ℤ)

/-- Extension of coefficients `R[ℤ^I] → K[ℤ^I]`. -/
abbrev incl : AddMonoidAlgebra R (I → ℤ) →ₐ[R] AddMonoidAlgebra K (I → ℤ) :=
  AddMonoidAlgebra.mapAlgHom (I → ℤ) (Algebra.ofId R K)

/-- The ring isomorphism `R[ℤ^I] ⊗[R] K ≃ K[ℤ^I]`. -/
def tensorEquiv : AddMonoidAlgebra R (I → ℤ) ⊗[R] K ≃+* AddMonoidAlgebra K (I → ℤ) :=
  (Algebra.TensorProduct.comm R (AddMonoidAlgebra R (I → ℤ)) K).toRingEquiv.trans
    (AddMonoidAlgebra.scalarTensorEquiv R K).toRingEquiv

theorem tensorEquiv_tmul (p : AddMonoidAlgebra R (I → ℤ)) (k : K) :
    tensorEquiv R K I (p ⊗ₜ[R] k) = k • incl R K I p := by
  simp [tensorEquiv]

theorem tensorEquiv_comp_includeLeft :
    (tensorEquiv R K I).toRingHom.comp Algebra.TensorProduct.includeLeftRingHom =
      (incl R K I).toRingHom := by
  ext p
  · simp [tensorEquiv_tmul]
  · simp [tensorEquiv_tmul]

theorem tensorEquiv_comp_includeRight :
    (tensorEquiv R K I).toRingHom.comp
        (RingHomClass.toRingHom (Algebra.TensorProduct.includeRight :
          K →ₐ[R] AddMonoidAlgebra R (I → ℤ) ⊗[R] K)) =
      algebraMap K (AddMonoidAlgebra K (I → ℤ)) := by
  ext k
  simp [tensorEquiv_tmul, Algebra.smul_def]

/-- The generic fibre of `D_R(ℤ^I)`. -/
abbrev genericTorus : GroupScheme (Spec (CommRingCat.of K)) :=
  ((CommGroupScheme.baseChange (Spec.algebraMap R K)).obj (torus R I)).toGrp

/-- The underlying scheme map of the universal point `Spec K[ℤ^I] → D_R(ℤ^I)_K`. -/
def universalPointLeft :
    Spec (CommRingCat.of (AddMonoidAlgebra K (I → ℤ))) ⟶
      pullback (torus R I).X.hom (Spec.algebraMap R K) :=
  Spec.map (CommRingCat.ofHom (tensorEquiv R K I).toRingHom) ≫
    (pullbackSpecIso R (AddMonoidAlgebra R (I → ℤ)) K).inv

theorem universalPointLeft_fst :
    universalPointLeft R K I ≫ pullback.fst (torus R I).X.hom (Spec.algebraMap R K) =
      Spec.map (CommRingCat.ofHom (incl R K I).toRingHom) := by
  change Spec.map _ ≫ (pullbackSpecIso R (AddMonoidAlgebra R (I → ℤ)) K).inv ≫
    pullback.fst _ _ = _
  rw [pullbackSpecIso_inv_fst, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    tensorEquiv_comp_includeLeft]

theorem universalPointLeft_snd :
    universalPointLeft R K I ≫ pullback.snd (torus R I).X.hom (Spec.algebraMap R K) =
      Spec.algebraMap K (AddMonoidAlgebra K (I → ℤ)) := by
  change Spec.map _ ≫ (pullbackSpecIso R (AddMonoidAlgebra R (I → ℤ)) K).inv ≫
    pullback.snd _ _ = _
  rw [pullbackSpecIso_inv_snd, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    tensorEquiv_comp_includeRight]

instance : IsIso (universalPointLeft R K I) := by
  have : IsIso (CommRingCat.ofHom (tensorEquiv R K I).toRingHom) :=
    (RingEquiv.toCommRingCatIso (tensorEquiv R K I)).isIso_hom
  unfold universalPointLeft
  infer_instance

/-- The universal point of the generic torus, with values in `K[ℤ^I]`. -/
def universalPoint :
    (genericTorus R K I).affinePoints (CommAlgCat.of K (AddMonoidAlgebra K (I → ℤ))) :=
  Over.homMk (universalPointLeft R K I) (universalPointLeft_snd R K I)

theorem universalPoint_left :
    (universalPoint R K I).left = universalPointLeft R K I :=
  rfl

theorem incl_injective (h : Function.Injective (algebraMap R K)) :
    Function.Injective (incl R K I) := by
  intro x y hxy
  apply AddMonoidAlgebra.coeff_injective
  ext m
  have := congrArg (fun z => z.coeff m) hxy
  simp only [incl, AddMonoidAlgebra.coeff_mapAlgHom, Algebra.ofId_apply] at this
  exact h this

/-- The `L`-point of the generic torus given by an `I`-indexed family of units of `L`. -/
def unitPoint (L : Type u) [CommRing L] [Algebra K L] [Fintype I] (t : I → Lˣ) :
    (genericTorus R K I).affinePoints (CommAlgCat.of K L) :=
  (genericTorus R K I).affinePointMap (CommAlgCat.ofHom (evalUnits K t)) (universalPoint R K I)

theorem flat_torus : Flat (torus R I).toGrp.X.hom := by
  change Flat (Spec.map (CommRingCat.ofHom (algebraMap R (AddMonoidAlgebra R (I → ℤ)))))
  rw [Flat.SpecMap_iff, CommRingCat.hom_ofHom, RingHom.flat_algebraMap_iff]
  infer_instance

end UniversalPoint

section Lift

open Langlands.AlgebraicGeometry.PointTopology

variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
  (X : Over (Spec (CommRingCat.of R))) [IsAffine X.left]

/-- Lift a point along an injective coefficient map when all its coordinates lie in the
image. -/
def pointLift (f : S →ₐ[R] T) (hf : Function.Injective f) (p : RingPoint R X T)
    (hp : ∀ a : AffineCoordinateRing R X, affineSchemePointEquiv R X T p a ∈ f.range) :
    RingPoint R X S :=
  affinePointLift X f hf p hp

theorem pointLift_changeRing (f : S →ₐ[R] T) (hf : Function.Injective f)
    (p : RingPoint R X T)
    (hp : ∀ a : AffineCoordinateRing R X, affineSchemePointEquiv R X T p a ∈ f.range) :
    (pointLift X f hf p hp).changeRing f = p :=
  affinePointLift_changeRing X f hf p hp

end Lift

section Descent

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  {G : GroupScheme (Spec (CommRingCat.of K))} (M : IntegralModel R K G)
  {I : Type u} [Fintype I]
  (A L : Type u) [CommRing A] [IsDomain A] [ValuationRing A] [Field L]
  [Algebra R A] [Algebra A L] [IsFractionRing A L]
  [Algebra K L] [Algebra R L] [IsScalarTower R A L] [IsScalarTower R K L]
  [Infinite (IsLocalRing.ResidueField A)]

private instance modelAffine : IsAffine M.group.X.left :=
  isAffine_of_isAffineHom M.group.X.hom

/-- If a generic torus homomorphism sends every family of integral units to an integral point,
then every model coordinate of its universal point has integral Laurent coefficients. -/
theorem genericCoordinate_universalPoint_mem_range (ψ : genericTorus R K I ⟶ G)
    (hψ : ∀ t : I → Aˣ, (genericTorus R K I).affinePointsTarget ψ (CommAlgCat.of K L)
        (unitPoint R K I L (fun i => Units.map (algebraMap A L : A →* L) (t i))) ∈
      (M.baseChange A L).coefficientIntegralPoints K L)
    (hint : ∀ x : K, algebraMap K L x ∈ Set.range (algebraMap A L) →
      x ∈ Set.range (algebraMap R K))
    (a : AffineCoordinateRing R M.group.X) :
    G.affinePointEvaluation (CommAlgCat.of K (AddMonoidAlgebra K (I → ℤ)))
        (universalPoint R K I ≫ ψ.hom.hom) (M.genericCoordinate a) ∈ (incl R K I).range := by
  set P := G.affinePointEvaluation (CommAlgCat.of K (AddMonoidAlgebra K (I → ℤ)))
    (universalPoint R K I ≫ ψ.hom.hom) (M.genericCoordinate a) with hP
  apply mem_range_mapAlgHom_of_coeff
  intro m
  apply hint
  have hcoeff := coeff_mem_range_of_forall_evalUnits_mem (A := A) (K := L)
    (AddMonoidAlgebra.mapRingHom (I → ℤ) (algebraMap K L) P) ?_ m
  · simpa only [AddMonoidAlgebra.coeff_mapRingHom] using hcoeff
  intro t
  rw [evalUnits_mapRingHom_algebraMap]
  have h := (M.mem_baseChange_coefficientIntegralPoints_iff_genericCoordinates A L _).mp
    (hψ t) a
  have hpt : (genericTorus R K I).affinePointsTarget ψ (CommAlgCat.of K L)
      (unitPoint R K I L (fun i => Units.map (algebraMap A L : A →* L) (t i))) =
      G.affinePointMap (CommAlgCat.ofHom (evalUnits K
        (fun i => Units.map (algebraMap A L : A →* L) (t i))))
        (universalPoint R K I ≫ ψ.hom.hom) := by
    simp only [unitPoint, affinePointMap_apply, affinePointsTarget_apply, Category.assoc]
  rw [hpt, affinePointEvaluation_map] at h
  exact h

/-- **Descent of a generic torus homomorphism.** If a homomorphism from the generic fibre of
`D_R(ℤ^I)` sends every family of integral units to an integral point, it is the generic fibre
of an integral homomorphism `D_R(ℤ^I) → M`. -/
theorem exists_genericTorusMap_eq (ψ : genericTorus R K I ⟶ G)
    (hψ : ∀ t : I → Aˣ, (genericTorus R K I).affinePointsTarget ψ (CommAlgCat.of K L)
        (unitPoint R K I L (fun i => Units.map (algebraMap A L : A →* L) (t i))) ∈
      (M.baseChange A L).coefficientIntegralPoints K L)
    (hint : ∀ x : K, algebraMap K L x ∈ Set.range (algebraMap A L) →
      x ∈ Set.range (algebraMap R K)) :
    ∃ j : (torus R I).toGrp ⟶ M.group, M.genericTorusMap (torus R I) j = ψ := by
  let p : G.affinePoints (CommAlgCat.of K (AddMonoidAlgebra K (I → ℤ))) :=
    universalPoint R K I ≫ ψ.hom.hom
  have hp : ∀ a : AffineCoordinateRing R M.group.X,
      affineSchemePointEquiv R M.group.X (AddMonoidAlgebra K (I → ℤ))
        (M.genericModelPointEquiv (AddMonoidAlgebra K (I → ℤ)) p) a ∈ (incl R K I).range := by
    intro a
    rw [genericModelPointEquiv_evaluation]
    exact genericCoordinate_universalPoint_mem_range M A L ψ hψ hint a
  let q := pointLift M.group.X (incl R K I) (incl_injective R K I (IsFractionRing.injective R K))
    _ hp
  have hq : q.changeRing (incl R K I) =
      M.genericModelPointEquiv (AddMonoidAlgebra K (I → ℤ)) p :=
    pointLift_changeRing _ _ _ _ _
  let φ : (torus R I).toGrp.X ⟶ M.group.X := q
  have hmap : (Over.pullback (Spec.algebraMap R K)).map φ =
      ψ.hom.hom ≫ M.genericIso.inv.hom.hom := by
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · apply (cancel_epi (universalPointLeft R K I)).mp
      have hl := congrArg (fun x : RingPoint R M.group.X (AddMonoidAlgebra K (I → ℤ)) =>
        x.left) hq
      change Spec.map (CommRingCat.ofHom (incl R K I).toRingHom) ≫ q.left =
        (M.genericModelPointEquiv (AddMonoidAlgebra K (I → ℤ)) p).left at hl
      rw [genericModelPointEquiv_left] at hl
      have h1 : ((Over.pullback (Spec.algebraMap R K)).map φ).left ≫
          pullback.fst M.group.X.hom (Spec.algebraMap R K) =
          pullback.fst (torus R I).X.hom (Spec.algebraMap R K) ≫ q.left := by
        simp only [Over.pullback_map_left, pullback.lift_fst]
        rfl
      rw [h1, ← Category.assoc, universalPointLeft_fst, hl]
      simp only [p, Over.comp_left, universalPoint_left, Category.assoc]
    · exact ((Over.pullback (Spec.algebraMap R K)).map φ).w.trans
        (ψ.hom.hom ≫ M.genericIso.inv.hom.hom).w.symm
  have : IsMonHom ((Over.pullback (Spec.algebraMap R K)).map φ) := by
    rw [hmap]
    infer_instance
  have : Flat (torus R I).toGrp.X.hom := flat_torus R I
  have : IsMonHom φ := Descent.FiniteCoefficient.isMonHom_of_generic (K := K) φ
  refine ⟨Grp.homMk φ, ?_⟩
  have heq : (GroupScheme.baseChange (Spec.algebraMap R K)).map (Grp.homMk φ) =
      ψ ≫ M.genericIso.inv := by
    apply Grp.hom_ext
    exact hmap
  change (GroupScheme.baseChange (Spec.algebraMap R K)).map (Grp.homMk φ) ≫
    M.genericIso.hom = ψ
  rw [heq, Category.assoc, Iso.inv_hom_id, Category.comp_id]

end Descent

section Closed

variable {R K : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K]
  [IsFractionRing R K] {G : GroupScheme (Spec (CommRingCat.of K))} (M : IntegralModel R K G)
  {I : Type u}

private instance modelAffine' : IsAffine M.group.X.left :=
  isAffine_of_isAffineHom M.group.X.hom

/-- **Closedness from the generic fibre.** Over a noetherian domain, a homomorphism
`D_R(ℤ^I) → M` whose generic fibre is a closed immersion is itself a closed immersion: its Hopf
coordinate map is surjective because its coefficient ideals are idempotent and nonzero. -/
theorem isClosedSubgroup_of_genericTorusMap (j : (torus R I).toGrp ⟶ M.group)
    (hj : IsClosedSubgroup (M.genericTorusMap (torus R I) j)) : IsClosedSubgroup j := by
  let e := Diagonalizable.hopfSpecIso (CommRingCat.of R) (I → ℤ)
  let i : TorusClosedImmersionLocus.diagonalSource (CommRingCat.of R) (I → ℤ) ⟶ M.group :=
    e.hom ≫ j
  have hjK : IsClosedImmersion
      ((GroupScheme.baseChange (Spec.algebraMap R K)).map j).hom.hom.left := by
    have hcomp : M.genericTorusMap (torus R I) j ≫ M.genericIso.inv =
        (GroupScheme.baseChange (Spec.algebraMap R K)).map j := by
      rw [genericTorusMap, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rw [← hcomp]
    have : IsIso M.genericIso.inv.hom.hom.left :=
      (Grp.forget _ ⋙ Over.forget _).map_isIso M.genericIso.inv
    have : IsClosedImmersion (M.genericTorusMap (torus R I) j).hom.hom.left := hj
    change IsClosedImmersion
      ((M.genericTorusMap (torus R I) j).hom.hom.left ≫ M.genericIso.inv.hom.hom.left)
    infer_instance
  have hgen : IsClosedImmersion
      ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap R K)))).map
        i).hom.hom.left :=
    (TorusClosedImmersionLocus.closed_baseChange_precomp_iso_iff _ e j).mpr hjK
  have hsurjK := (TorusClosedImmersionLocus.diagonal_closed_iff i K).mp hgen
  let δ := TorusClosedImmersionLocus.diagonalCoordinateMap i
  have hsurj : Function.Surjective δ := by
    refine surjective_of_coeff_ne_zero δ (fun m => ?_)
    obtain ⟨b, hb⟩ :=
      CommutativeAlgebra.DiagonalCoalgebraLocus.exists_nonzero_coefficient δ.toAlgHom K hsurjK m
    refine ⟨b, fun h => hb ?_⟩
    change algebraMap R K ((δ b).coeff m) = 0
    rw [h, map_zero]
  have hi : IsClosedImmersion i.hom.hom.left := by
    let φ : CommRingCat.of (AffineCoordinates.hopfAlgebra M.group) ⟶
        CommRingCat.of (AddMonoidAlgebra R (I → ℤ)) :=
      CommRingCat.ofHom δ.toAlgHom.toRingHom
    have hc : IsClosedImmersion (Spec.map φ) := IsClosedImmersion.spec_of_surjective φ hsurj
    have he : i = (hopfSpec (CommRingCat.of R)).map (CommHopfAlgCat.ofHom δ).op ≫
        (AffineCoordinates.hopfSpecIso M.group).hom := by
      rw [TorusClosedImmersionLocus.diagonalCoordinateMap_map, Category.assoc,
        Iso.inv_hom_id, Category.comp_id]
    rw [he]
    have : IsIso (AffineCoordinates.hopfSpecIso M.group).hom.hom.hom.left :=
      (Grp.forget _ ⋙ Over.forget _).map_isIso (AffineCoordinates.hopfSpecIso M.group).hom
    change IsClosedImmersion (Spec.map φ ≫ (AffineCoordinates.hopfSpecIso M.group).hom.hom.hom.left)
    infer_instance
  have hj' : j = e.inv ≫ i := by
    simp only [i, Iso.inv_hom_id_assoc]
  show IsClosedImmersion j.hom.hom.left
  rw [hj']
  have : IsIso e.inv.hom.hom.left := (Grp.forget _ ⋙ Over.forget _).map_isIso e.inv
  change IsClosedImmersion (e.inv.hom.hom.left ≫ i.hom.hom.left)
  infer_instance

end Closed

end Langlands.GroupScheme.IntegralModel.SplitTorusClosure
