import Langlands.GroupScheme.Lie.AdjointDeterminantCharacter
import Langlands.GroupScheme.Dynamic.AdjointDeterminant
import Langlands.GroupScheme.Dynamic.AdjointDeterminantModelIndependence
import Langlands.GroupScheme.Dynamic.AdjointDeterminantFunctorialityProof
import Langlands.GroupScheme.Dynamic.CentralizerAdjointAction
import Langlands.GroupScheme.Dynamic.SchemeDecomposition
import Langlands.GroupScheme.Rational.DynamicSemistandardIntersectionModels

/-! # `Lie P = Lie U ⊕ Lie Z` and the restriction of `det Ad_P` to the Levi factor

For representing group schemes `P`, `Z`, `U` of the dynamic subgroups `P(χ)`, `Z(χ)`, `U(χ)`,
the map `(x, y) ↦ x + y` from `Lie U × Lie Z` to `Lie P` is a linear isomorphism on every
test algebra, and conjugation by a point of `Z` acts on it diagonally. Hence the restriction
to `Z` of the adjoint determinant character of `P` is the determinant character of `Z` on
`Lie U` plus the adjoint determinant character of `Z`. -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Dynamic

section Points

variable {S : Scheme.{u}} {G : GroupScheme S} (χ : (Gm S).toGrp ⟶ G) [IsSeparated G.X.hom]

/-- A point of `U(χ)` times a point of `Z(χ)` is trivial only if both factors are trivial. -/
theorem eq_one_of_unipotent_mul_centralizer_eq_one {T : Over S} {u z : T ⟶ G.X}
    (hu : u ∈ (unipotent χ).carrier T) (hz : z ∈ (centralizer χ).carrier T)
    (h : u * z = 1) : u = 1 ∧ z = 1 := by
  have key : semidirectEquiv χ T ⟨⟨u, hu⟩, ⟨z, hz⟩⟩ = semidirectEquiv χ T 1 := by
    apply Subtype.ext
    rw [semidirectEquiv_apply_coe, map_one]
    exact h
  have he := (semidirectEquiv χ T).injective key
  exact ⟨congrArg (fun x => (x.left : T ⟶ G.X)) he,
    congrArg (fun x => (x.right : T ⟶ G.X)) he⟩

variable {P Z U : GroupScheme S} {iP : P ⟶ G} {iZ : Z ⟶ G} {iU : U ⟶ G}
  (hP : (parabolic χ).IsRepresentedBy iP) (hZ : (centralizer χ).IsRepresentedBy iZ)
  (hU : (unipotent χ).IsRepresentedBy iU)

include hU in
/-- Every point of the represented parabolic is a point of `U` times a point of `Z`. -/
theorem exists_eq_unipotent_mul_centralizer {T : Over S} (p : T ⟶ P.X) :
    ∃ (u : T ⟶ U.X) (z : T ⟶ Z.X),
      p = (u ≫ (unipotentToParabolic hP hU).hom.hom) *
        (z ≫ (centralizerToParabolic hP hZ).hom.hom) := by
  let g : (parabolic χ).carrier T := hP.pointsEquiv T p
  let s := (semidirectEquiv χ T).symm g
  refine ⟨(hU.pointsEquiv T).symm s.left, (hZ.pointsEquiv T).symm s.right, ?_⟩
  apply hP.1.right_cancellation
  rw [MonObj.mul_comp, Category.assoc, Category.assoc, ← Grp.comp_hom_hom,
    ← Grp.comp_hom_hom, unipotentToParabolic_comp, centralizerToParabolic_comp,
    SubgroupFunctor.IsRepresentedBy.pointsEquiv_symm_comp,
    SubgroupFunctor.IsRepresentedBy.pointsEquiv_symm_comp]
  have h := congrArg Subtype.val ((semidirectEquiv χ T).apply_symm_apply g)
  rw [semidirectEquiv_apply_coe] at h
  exact h.symm

/-- A point of the represented parabolic has trivial limit exactly when it is a point of
`U(χ)`. -/
theorem limitGroupHom_eq_one_iff {T : Over S} (p : T ⟶ P.X) :
    p ≫ (limitGroupHom hP hZ).hom.hom = 1 ↔ p ≫ iP.hom.hom ∈ (unipotent χ).carrier T := by
  have hl := limitGroupHom_comp hP hZ p
  have hiff := limit_eq_one_iff χ (hP.pointsEquiv T p)
  rw [SubgroupFunctor.IsRepresentedBy.pointsEquiv_apply_coe] at hiff
  rw [← hiff, ← hl]
  constructor
  · intro h
    rw [h, MonObj.one_comp]
  · intro h
    apply hZ.1.right_cancellation
    rw [h, MonObj.one_comp]

end Points

section Lie

variable {R : CommRingCat.{u}} {G P Z U : GroupScheme (Spec R)} [IsSeparated G.X.hom]
  {χ : (Gm (Spec R)).toGrp ⟶ G} {iP : P ⟶ G} {iZ : Z ⟶ G} {iU : U ⟶ G}
  (hP : (parabolic χ).IsRepresentedBy iP) (hZ : (centralizer χ).IsRepresentedBy iZ)
  (hU : (unipotent χ).IsRepresentedBy iU)
  [IsAffineHom P.X.hom] [IsAffineHom Z.X.hom] [IsAffineHom U.X.hom]
  (A : Type u) [CommRing A] [Algebra R A]

/-- The linear map `Lie U × Lie Z → Lie P`, `(x, y) ↦ x + y`, on the actual dual-number
kernels, through the inclusions `U ⟶ P` and `Z ⟶ P`. -/
def lieProductMap :
    (Additive (lieKernel U A) × Additive (lieKernel Z A)) →ₗ[A] Additive (lieKernel P A) :=
  (Lie.targetMapLinear (unipotentToParabolic hP hU) A).coprod
    (Lie.targetMapLinear (centralizerToParabolic hP hZ) A)

variable {A}

omit [IsSeparated G.X.hom] in
/-- After the inclusion into `G`, the sum is the product of the two images. -/
theorem lieProductMap_val_comp (x : Additive (lieKernel U A)) (y : Additive (lieKernel Z A)) :
    (lieProductMap hP hZ hU A (x, y)).toMul.val ≫ iP.hom.hom =
      (x.toMul.val ≫ iU.hom.hom) * (y.toMul.val ≫ iZ.hom.hom) := by
  change ((x.toMul.val ≫ (unipotentToParabolic hP hU).hom.hom) *
      (y.toMul.val ≫ (centralizerToParabolic hP hZ).hom.hom)) ≫ iP.hom.hom = _
  rw [MonObj.mul_comp, Category.assoc, Category.assoc, ← Grp.comp_hom_hom,
    ← Grp.comp_hom_hom, unipotentToParabolic_comp, centralizerToParabolic_comp]

theorem lieProductMap_injective : Function.Injective (lieProductMap hP hZ hU A) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  rintro ⟨x, y⟩ h
  have hv : (lieProductMap hP hZ hU A (x, y)).toMul.val ≫ iP.hom.hom = 1 := by
    rw [h]
    exact MonObj.one_comp _
  rw [lieProductMap_val_comp] at hv
  obtain ⟨h1, h2⟩ := eq_one_of_unipotent_mul_centralizer_eq_one χ
    (hU.pointsEquiv _ x.toMul.val).2 (hZ.pointsEquiv _ y.toMul.val).2 hv
  have hx : x.toMul.val = 1 := hU.1.right_cancellation _ _ (h1.trans (MonObj.one_comp _).symm)
  have hy : y.toMul.val = 1 := hZ.1.right_cancellation _ _ (h2.trans (MonObj.one_comp _).symm)
  refine Prod.ext ?_ ?_
  · exact Additive.toMul.injective (Subtype.ext hx)
  · exact Additive.toMul.injective (Subtype.ext hy)

theorem lieProductMap_surjective : Function.Surjective (lieProductMap hP hZ hU A) := by
  intro w
  let T : Over (Spec R) := (algSpec R).obj (op (CommAlgCat.of R (DualNumber A)))
  let g : (parabolic χ).carrier T := hP.pointsEquiv T w.toMul.val
  let s := (semidirectEquiv χ T).symm g
  let u' : T ⟶ U.X := (hU.pointsEquiv T).symm s.left
  let z' : T ⟶ Z.X := (hZ.pointsEquiv T).symm s.right
  have hsu : u' ≫ iU.hom.hom = s.left := SubgroupFunctor.IsRepresentedBy.pointsEquiv_symm_comp hU _
  have hsz : z' ≫ iZ.hom.hom = s.right :=
    SubgroupFunctor.IsRepresentedBy.pointsEquiv_symm_comp hZ _
  have hprod : (s.left : T ⟶ G.X) * s.right = w.toMul.val ≫ iP.hom.hom := by
    have h := congrArg Subtype.val ((semidirectEquiv χ T).apply_symm_apply g)
    rw [semidirectEquiv_apply_coe] at h
    exact h
  let b : (algSpec R).obj (op (CommAlgCat.of R A)) ⟶ T :=
    (algSpec R).map (CommAlgCat.ofHom (TrivSqZeroExt.fstHom R A A)).op
  have hred : b ≫ w.toMul.val = 1 := w.toMul.property
  have hb : (b ≫ (s.left : T ⟶ G.X)) * (b ≫ (s.right : T ⟶ G.X)) = 1 := by
    rw [← MonObj.comp_mul, hprod, ← Category.assoc, hred, MonObj.one_comp]
  obtain ⟨h1, h2⟩ := eq_one_of_unipotent_mul_centralizer_eq_one χ
    ((unipotent χ).comp_mem b s.left.2) ((centralizer χ).comp_mem b s.right.2) hb
  have hu1 : b ≫ u' = 1 := by
    apply hU.1.right_cancellation
    rw [Category.assoc, hsu, h1, MonObj.one_comp]
  have hz1 : b ≫ z' = 1 := by
    apply hZ.1.right_cancellation
    rw [Category.assoc, hsz, h2, MonObj.one_comp]
  refine ⟨(Additive.ofMul ⟨u', hu1⟩, Additive.ofMul ⟨z', hz1⟩), ?_⟩
  apply Additive.toMul.injective
  apply Subtype.ext
  apply hP.1.right_cancellation
  rw [lieProductMap_val_comp]
  change (u' ≫ iU.hom.hom) * (z' ≫ iZ.hom.hom) = w.toMul.val ≫ iP.hom.hom
  rw [hsu, hsz, hprod]

variable (A) in
/-- The linear isomorphism `Lie U × Lie Z ≃ Lie P`. -/
def lieProductEquiv :
    (Additive (lieKernel U A) × Additive (lieKernel Z A)) ≃ₗ[A] Additive (lieKernel P A) :=
  LinearEquiv.ofBijective (lieProductMap hP hZ hU A)
    ⟨lieProductMap_injective hP hZ hU, lieProductMap_surjective hP hZ hU⟩

@[simp] theorem lieProductEquiv_apply
    (x : Additive (lieKernel U A) × Additive (lieKernel Z A)) :
    lieProductEquiv hP hZ hU A x = lieProductMap hP hZ hU A x := rfl

omit [IsSeparated G.X.hom] in
/-- Conjugation by a point of `Z` acts diagonally on `Lie U × Lie Z`: by the conjugation
action of `Z` on `U` on the first factor and by the adjoint action of `Z` on the second. -/
theorem differential_lieProductMap (z : Lie.AffinePoints Z A)
    (x : Additive (lieKernel U A)) (y : Additive (lieKernel Z A)) :
    (AutomorphicAction.conjugation (𝟙 P)).differential
        (z ≫ (centralizerToParabolic hP hZ).hom.hom) (lieProductMap hP hZ hU A (x, y)) =
      lieProductMap hP hZ hU A
        ((centralizerAdjointAction hZ hU).differential z x,
          (AutomorphicAction.conjugation (𝟙 Z)).differential z y) := by
  apply Additive.toMul.injective
  apply Subtype.ext
  apply hP.1.right_cancellation
  rw [lieProductMap_val_comp, AutomorphicAction.differential_val,
    AutomorphicAction.conjugation_act, AutomorphicAction.differential_val,
    AutomorphicAction.differential_val, centralizerAdjointAction_act_comp,
    AutomorphicAction.conjugation_act]
  have hc : Lie.constant P (z ≫ (centralizerToParabolic hP hZ).hom.hom) =
      Lie.constant Z z ≫ (centralizerToParabolic hP hZ).hom.hom := by
    simp only [Lie.constant, Lie.affineMap_apply, Category.assoc]
  have hcP : (Lie.constant Z z ≫ (centralizerToParabolic hP hZ).hom.hom) ≫ iP.hom.hom =
      Lie.constant Z z ≫ iZ.hom.hom := by
    rw [Category.assoc, ← Grp.comp_hom_hom, centralizerToParabolic_comp]
  simp only [Grp.id_hom_hom, Category.comp_id, MonObj.mul_comp, GrpObj.inv_comp, hc, hcP,
    lieProductMap_val_comp]
  group

/-- **Determinant of `Ad_P` on Levi points.** For a point `z` of `Z`, the determinant of
conjugation by `z` on `Lie P` is the product of the determinants of conjugation by `z` on
`Lie U` and on `Lie Z`. -/
theorem det_conjugation_centralizerToParabolic
    [Module.Free A (Additive (lieKernel U A))] [Module.Finite A (Additive (lieKernel U A))]
    [Module.Free A (Additive (lieKernel Z A))] [Module.Finite A (Additive (lieKernel Z A))]
    (z : Lie.AffinePoints Z A) :
    LinearEquiv.det ((AutomorphicAction.conjugation (𝟙 P)).differential
        (z ≫ (centralizerToParabolic hP hZ).hom.hom)) =
      LinearEquiv.det ((centralizerAdjointAction hZ hU).differential z) *
        LinearEquiv.det ((AutomorphicAction.conjugation (𝟙 Z)).differential z) := by
  set e := lieProductEquiv hP hZ hU A
  have hconj : (AutomorphicAction.conjugation (𝟙 P)).differential
      (z ≫ (centralizerToParabolic hP hZ).hom.hom) =
      (e.symm.trans (LinearEquiv.prodCongr
        ((centralizerAdjointAction hZ hU).differential z)
        ((AutomorphicAction.conjugation (𝟙 Z)).differential z))).trans e := by
    apply LinearEquiv.ext
    intro w
    obtain ⟨⟨x, y⟩, rfl⟩ := e.surjective w
    rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply,
      LinearEquiv.prodCongr_apply]
    exact differential_lieProductMap hP hZ hU z x y
  rw [hconj, LinearEquiv.det_conj]
  apply Units.ext
  rw [LinearEquiv.coe_det, Units.val_mul, LinearEquiv.coe_det, LinearEquiv.coe_det,
    LinearEquiv.coe_prodCongr]
  exact LinearMap.det_prodMap _ _

end Lie

section Field

variable {k : Type u} [Field k] {G P Z U : GroupScheme (Spec (CommRingCat.of k))}
  [IsSeparated G.X.hom] {χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G}
  {iP : P ⟶ G} {iZ : Z ⟶ G} {iU : U ⟶ G}
  (hP : (parabolic χ).IsRepresentedBy iP) (hZ : (centralizer χ).IsRepresentedBy iZ)
  (hU : (unipotent χ).IsRepresentedBy iU)
  [IsAffine P.X.left] [LocallyOfFiniteType P.X.hom]
  [IsAffine Z.X.left] [LocallyOfFiniteType Z.X.hom] [IsAffineHom U.X.hom]
  {d : ℕ} (c : Lie.FiniteCoordinates U d)

/-- **Levi restriction of `det Ad_P`.** The restriction of the adjoint determinant character
of `P` to `Z` is the determinant character of the conjugation action of `Z` on `Lie U` plus
the adjoint determinant character of `Z`. -/
theorem characterRestrict_adjointDeterminantCharacter_parabolic :
    characterRestrict (centralizerToParabolic hP hZ) (Lie.adjointDeterminantCharacter P) =
      (centralizerAdjointAction hZ hU).determinantCharacter c +
        Lie.adjointDeterminantCharacter Z := by
  apply rationalCharacters_ext_affinePoints
  intro A z
  rw [rationalCharacters.comp_add]
  apply (Gm.affinePointsEquiv ((algSpec (CommRingCat.of k)).obj (op A)).hom).injective
  have hp : z ≫ (characterRestrict (centralizerToParabolic hP hZ)
      (Lie.adjointDeterminantCharacter P)).toMul.hom.hom =
      (z ≫ (centralizerToParabolic hP hZ).hom.hom) ≫
        (Lie.adjointDeterminantCharacter P).toMul.hom.hom := by
    rw [characterRestrict_apply, Grp.comp_hom_hom, Category.assoc]
  have : Module.Free A (Additive (lieKernel U A)) := Module.Free.of_equiv (c.equiv A).symm
  have : Module.Finite A (Additive (lieKernel U A)) := Module.Finite.equiv (c.equiv A).symm
  have : Module.Free A (Additive (lieKernel Z A)) :=
    Module.Free.of_equiv ((Lie.finiteCoordinates Z).equiv A).symm
  have : Module.Finite A (Additive (lieKernel Z A)) :=
    Module.Finite.equiv ((Lie.finiteCoordinates Z).equiv A).symm
  rw [hp]
  refine (Lie.adjointDeterminantCharacter_affinePoints P A _).trans ?_
  rw [det_conjugation_centralizerToParabolic hP hZ hU z]
  refine Eq.trans ?_ (map_mul (Gm.affinePointsEquiv ((algSpec (CommRingCat.of k)).obj (op A)).hom)
    _ _).symm
  exact congrArg₂ (· * ·)
    ((centralizerAdjointAction hZ hU).determinantCharacter_affinePoints c A z).symm
    (Lie.adjointDeterminantCharacter_affinePoints Z A z).symm

end Field

end Langlands.GroupScheme.Dynamic
