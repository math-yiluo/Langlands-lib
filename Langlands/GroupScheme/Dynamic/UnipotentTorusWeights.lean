import Langlands.GroupScheme.Dynamic.UnipotentPrimitiveCoordinate
import Langlands.GroupScheme.Dynamic.ActionStability
import Langlands.GroupScheme.Dynamic.UnipotentCocharacterConjugacy
import Langlands.GroupScheme.Rational.TorusActionBridge
import Langlands.GroupScheme.Rational.TorusStableLine
import Langlands.GroupScheme.Torus.ExponentCocharacters

/-! # Torus weights on dynamic unipotent coordinate algebras -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicGeometry Opposite Polynomial
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Corepresented

variable {R : CommRingCat.{u}} {F : CommAlgCat.{u} R ⥤ GrpCat.{u}}
  {B : CommAlgCat.{u} R} (e : (F ⋙ forget GrpCat).CorepresentableBy B)
  {I : Type u} [Fintype I] [DecidableEq I] (σ : TorusAction F I)
  {c : B →+* LaurentPolynomial B} (hc : CommutativeAlgebra.GradedLine.IsGrading R c)
  (degree : (I → ℤ) → ℤ)
  (hdegree : ∀ m b, IsHomogeneous e σ m b →
    b ∈ CommutativeAlgebra.GradedLine.homog hc (degree m))

include hdegree in
/-- Weight projections commute with the degree projections of a grading obtained
by restricting the torus action to a cocharacter. -/
theorem comp_grading_comp (m : I → ℤ) (n : ℤ) (b : B) :
    comp e σ m (CommutativeAlgebra.GradedLine.comp hc n b) =
      CommutativeAlgebra.GradedLine.comp hc n (comp e σ m b) := by
  classical
  let s := (rho e σ b).coeff.support
  have hs := congrArg (fun y => comp e σ m (CommutativeAlgebra.GradedLine.comp hc n y))
    (sum_support_comp e σ b)
  have hsum : comp e σ m (CommutativeAlgebra.GradedLine.comp hc n b) =
      ∑ k ∈ s, comp e σ m (CommutativeAlgebra.GradedLine.comp hc n (comp e σ k b)) := by
    simpa only [map_sum] using hs.symm
  rw [hsum]
  have hterm (k : I → ℤ) :
      comp e σ m (CommutativeAlgebra.GradedLine.comp hc n (comp e σ k b)) =
        if k = m then CommutativeAlgebra.GradedLine.comp hc n (comp e σ m b) else 0 := by
    rw [CommutativeAlgebra.GradedLine.comp_of_mem hc
      (hdegree k _ (isHomogeneous_comp e σ k b))]
    by_cases hkm : k = m
    · subst k
      rw [ite_eq_left rfl, CommutativeAlgebra.GradedLine.comp_of_mem hc
        (hdegree m _ (isHomogeneous_comp e σ m b))]
      split_ifs <;> simp [comp_comp]
    · rw [ite_eq_right hkm]
      split_ifs <;> simp [comp_comp, Ne.symm hkm]
  simp_rw [hterm]
  by_cases hm : m ∈ s
  · simp [hm]
  · have hb0 : comp e σ m b = 0 := comp_eq_zero_of_notMem e σ hm
    simp [hb0]

include hdegree in
/-- Every torus weight projection preserves a degree for the restricted grading. -/
theorem comp_mem_grading_homog {n : ℤ} {b : B}
    (hb : b ∈ CommutativeAlgebra.GradedLine.homog hc n) (m : I → ℤ) :
    comp e σ m b ∈ CommutativeAlgebra.GradedLine.homog hc n := by
  rw [← CommutativeAlgebra.GradedLine.comp_self hc hb,
    comp_grading_comp e σ hc degree hdegree]
  exact CommutativeAlgebra.GradedLine.comp_mem_homog hc n _

end Langlands.GroupScheme.Corepresented

namespace Langlands.GroupScheme.Corepresented.UnipotentPrimitive

variable {R : CommRingCat.{u}} {F : CommAlgCat.{u} R ⥤ GrpCat.{u}}
  {B : CommAlgCat.{u} R} (e : (F ⋙ forget GrpCat).CorepresentableBy B)

/-- The affine-point comparison commutes with change of test algebra. -/
theorem affinePoint_map {A A' : CommAlgCat.{u} R} (g : A ⟶ A') (y : F.obj A) :
    affinePoint (A := A') e (F.map g y) =
      RingCoordinates.specMapOver g.hom ≫ affinePoint (A := A) e y := by
  change (affinePointsEquiv F e A').symm (F.map g y) =
    (algSpec R).map g.op ≫ (affinePointsEquiv F e A).symm y
  apply (affinePointsEquiv F e A').injective
  rw [MulEquiv.apply_symm_apply, affinePointsEquiv_naturality, MulEquiv.apply_symm_apply]

end Langlands.GroupScheme.Corepresented.UnipotentPrimitive

namespace Langlands.GroupScheme.Corepresented.UnipotentTorus

open AffineLine UnipotentPrimitive

variable {R : CommRingCat.{u}} {F : CommAlgCat.{u} R ⥤ GrpCat.{u}}
  {B : CommAlgCat.{u} R} {e : (F ⋙ forget GrpCat).CorepresentableBy B}
  {I : Type u} [Fintype I] [DecidableEq I]
  (i : splitTorus (Spec R) I ⟶ groupScheme F e) (ν : I → ℤ)

/-- The given cocharacter in the acting split torus, composed with its homomorphism. -/
abbrev cocharacter : (Gm (Spec R)).toGrp ⟶ groupScheme F e :=
  CommGroupScheme.groupHom (splitTorus.exponentCocharacter (Spec R) I ν) ≫ i

/-- Conjugation by the whole torus on the actual dynamic unipotent subgroup. -/
def action : AutomorphicAction (splitTorus (Spec R) I) (unipotentScheme (cocharacter i ν)) :=
  (AutomorphicAction.conjugation i).onRepresentedSubgroup
    (unipotentHom (cocharacter i ν)) (isRepresentedBy_unipotentHom (cocharacter i ν))
    (Dynamic.unipotent_isStable_conjugation
      (A := splitTorus.commGroupScheme (Spec R) I) i
      (CommGroupScheme.groupHom (splitTorus.exponentCocharacter (Spec R) I ν)))

/-- The induced action of unit coordinates on the actual quotient-algebra points. -/
def torusAction : TorusAction (unipotentFunctor (cocharacter i ν)) I :=
  TorusAction.ofAutomorphicAction (unipotentCorepresentation (cocharacter i ν)) (action i ν)

omit [DecidableEq I] in
theorem action_act_comp {T : Over (Spec R)}
    (t : T ⟶ (splitTorus (Spec R) I).X)
    (y : T ⟶ (unipotentScheme (cocharacter i ν)).X) :
    (action i ν).act t y ≫ (unipotentHom (cocharacter i ν)).hom.hom =
      (t ≫ i.hom.hom) * (y ≫ (unipotentHom (cocharacter i ν)).hom.hom) *
        (t ≫ i.hom.hom)⁻¹ := by
  rw [action, AutomorphicAction.onRepresentedSubgroup_act_comp,
    AutomorphicAction.conjugation_act]

variable {A : CommAlgCat.{u} R}

/-- The split-torus point on the affine test object used for ring coordinates. -/
abbrev torusPoint (A : CommAlgCat.{u} R) (t : I → Aˣ) :
    RingCoordinates.specOver R A ⟶ (splitTorus (Spec R) I).X :=
  torusPt I A t

omit [DecidableEq I] in
theorem affinePoint_val (y : (unipotentFunctor (cocharacter i ν)).obj A) :
    affinePoint (A := A) e y.val =
      affinePoint (A := A) (unipotentCorepresentation (cocharacter i ν)) y ≫
      (unipotentHom (cocharacter i ν)).hom.hom := by
  apply hom_ext_of_pointRing
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro b
  rw [pointRing_affinePoint, pointRing_unipotentHom, CommRingCat.comp_apply,
    pointRing_affinePoint, coord_val]
  rfl

omit [DecidableEq I] in
theorem affinePoint_act (t : I → Aˣ) (y : (unipotentFunctor (cocharacter i ν)).obj A) :
    affinePoint (A := A) e ((torusAction i ν).act t y).val =
      (torusPoint A t ≫ i.hom.hom) * affinePoint (A := A) e y.val *
        (torusPoint A t ≫ i.hom.hom)⁻¹ := by
  rw [affinePoint_val]
  have h : affinePoint (A := A) (unipotentCorepresentation (cocharacter i ν))
      ((torusAction i ν).act t y) =
      (action i ν).act (torusPt I A t)
        (affinePoint (A := A) (unipotentCorepresentation (cocharacter i ν)) y) := by
    simp only [affinePoint, torusAction, TorusAction.ofAutomorphicAction,
      MulEquiv.symm_apply_apply]
  rw [h, action_act_comp, ← affinePoint_val]

omit [DecidableEq I] in
theorem torusPt_cocharacter (u : Aˣ) :
    torusPt I A (fun j => u ^ ν j) =
      unitPoint (Spec.map (CommRingCat.ofHom (algebraMap R A))) u ≫
        (CommGroupScheme.groupHom (splitTorus.exponentCocharacter (Spec R) I ν)).hom.hom := by
  apply (splitTorus.algebraPointsEquiv I A).injective
  rw [torusPt, MulEquiv.apply_symm_apply]
  funext j
  change u ^ ν j = Gm.affinePointsEquiv
    (Spec.map (CommRingCat.ofHom (algebraMap R A)))
    ((unitPoint (Spec.map (CommRingCat.ofHom (algebraMap R A))) u ≫
      (CommGroupScheme.groupHom
        (splitTorus.exponentCocharacter (Spec R) I ν)).hom.hom) ≫
      (CommGroupScheme.groupHom (splitTorus.proj (Spec R) I j)).hom.hom)
  rw [← comp_groupHom_comp, splitTorus.exponentCocharacter_comp_proj,
    Gm.powerHom_apply]
  have hp := congrArg
    (Gm.affinePointsEquiv (S := Spec R)
      (Spec.map (CommRingCat.ofHom (algebraMap R A))))
    (Gm.comp_zsmul_id (S := Spec R) (U := RingCoordinates.specOver R A)
      (unitPoint (Spec.map (CommRingCat.ofHom (algebraMap R A))) u) (ν j))
  rw [map_zpow] at hp
  have hu : Gm.affinePointsEquiv (S := Spec R)
      (Spec.map (CommRingCat.ofHom (algebraMap R A)))
      (unitPoint (Spec.map (CommRingCat.ofHom (algebraMap R A))) u) = u :=
    affinePointsEquiv_unitPoint (S := Spec R)
      (Spec.map (CommRingCat.ofHom (algebraMap R A))) u
  exact (congrArg (fun v : Aˣ => v ^ ν j) hu).symm.trans hp.symm

omit [DecidableEq I] in
/-- The Laurent orbit is the restriction of the full torus action along its
specified cocharacter, on every algebra-valued point. -/
theorem orbitFun_eq (y : (unipotentFunctor (cocharacter i ν)).obj A) :
    orbitFun (cocharacter i ν) y =
      (torusAction i ν).act (fun j => unitT A ^ ν j)
        ((unipotentFunctor (cocharacter i ν)).map
          (CommAlgCat.ofHom (UnipotentPrimitive.constHom (R := R) (A := A))) y) := by
  apply Subtype.ext
  apply (affinePointsEquiv F e (CommAlgCat.of R (LaurentPolynomial A))).symm.injective
  change affinePoint (A := CommAlgCat.of R (LaurentPolynomial A)) e
    (orbitFun (A := A) (cocharacter i ν) y).val =
      affinePoint (A := CommAlgCat.of R (LaurentPolynomial A)) e
        ((torusAction i ν).act (fun j => unitT A ^ ν j)
          ((unipotentFunctor (cocharacter i ν)).map
            (CommAlgCat.ofHom (UnipotentPrimitive.constHom (R := R) (A := A))) y)).val
  rw [affinePoint_orbitFun, affinePoint_act]
  have ht := torusPt_cocharacter (ν := ν) (A := CommAlgCat.of R (LaurentPolynomial A))
    (unitT A)
  change torusPoint (CommAlgCat.of R (LaurentPolynomial A)) (fun j => unitT A ^ ν j) =
    _ at ht
  rw [ht, Category.assoc]
  change _ * _ * _ = _ *
    affinePoint (A := CommAlgCat.of R (LaurentPolynomial A)) e
      (F.map (CommAlgCat.ofHom
        (UnipotentPrimitive.constHom (R := R) (A := A))) y.val) * _
  rw [affinePoint_map]
  rfl

/-- A monomial restricted to the exponent cocharacter has its dot-product degree. -/
theorem exponentValue_unitT (D : Type u) [CommRing D] (m : I → ℤ) :
    (splitTorus.exponentValue I (fun j => unitT D ^ ν j) (Multiplicative.ofAdd m) :
      LaurentPolynomial D) = LaurentPolynomial.T (∑ j, m j * ν j) := by
  classical
  have hp (s : Finset I) :
      (∏ j ∈ s, (unitT D ^ ν j) ^ m j) = unitT D ^ (∑ j ∈ s, m j * ν j) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert j s hjs ih =>
      simp only [Finset.prod_insert hjs, Finset.sum_insert hjs, ih, zpow_add]
      rw [← zpow_mul, mul_comm (ν j) (m j)]
  change ((∏ j, (unitT D ^ ν j) ^ m j : (LaurentPolynomial D)ˣ) :
    LaurentPolynomial D) = _
  rw [hp, unitT_zpow]

/-- A homogeneous torus weight restricts to the corresponding degree of the
actual dynamic unipotent coaction. -/
theorem isHomogeneous_mem_homog {m : I → ℤ}
    {b : quotientAlgebra (unipotentIdeal (cocharacter i ν))}
    (hb : IsHomogeneous (unipotentCorepresentation (cocharacter i ν))
      (torusAction i ν) m b) :
    b ∈ CommutativeAlgebra.GradedLine.homog
      (isGrading_unipCoaction (cocharacter i ν)) (∑ j, m j * ν j) := by
  let C := quotientAlgebra (unipotentIdeal (cocharacter i ν))
  let eu := unipotentCorepresentation (cocharacter i ν)
  have h := coord_act_of_isHomogeneous eu (torusAction i ν)
    (fun j => unitT C ^ ν j)
    ((unipotentFunctor (cocharacter i ν)).map
      (CommAlgCat.ofHom (UnipotentPrimitive.constHom (R := R) (A := C))) (univ eu)) hb
  rw [← orbitFun_eq, coord_orbitFun, coord_map, coord_univ] at h
  change AddMonoidAlgebra.mapRingHom ℤ (RingHom.id C)
      (unipCoaction (cocharacter i ν) b) =
    LaurentPolynomial.C b *
      (splitTorus.exponentValue I (fun j => unitT C ^ ν j) (Multiplicative.ofAdd m) :
        LaurentPolynomial C) at h
  rw [AddMonoidAlgebra.mapRingHom_id, RingHom.id_apply, exponentValue_unitT,
    ← LaurentPolynomial.single_eq_C_mul_T] at h
  exact (CommutativeAlgebra.GradedLine.mem_homog _).2 h

/-- Every full-torus weight projection preserves the actual cocharacter grading. -/
theorem comp_mem_homog {n : ℤ}
    {b : quotientAlgebra (unipotentIdeal (cocharacter i ν))}
    (hb : b ∈ CommutativeAlgebra.GradedLine.homog
      (isGrading_unipCoaction (cocharacter i ν)) n) (m : I → ℤ) :
    comp (unipotentCorepresentation (cocharacter i ν)) (torusAction i ν) m b ∈
      CommutativeAlgebra.GradedLine.homog
        (isGrading_unipCoaction (cocharacter i ν)) n :=
  comp_mem_grading_homog (unipotentCorepresentation (cocharacter i ν)) (torusAction i ν)
    (isGrading_unipCoaction (cocharacter i ν)) (fun m => ∑ j, m j * ν j)
    (fun _ _ h => isHomogeneous_mem_homog i ν h) hb m

/-- A positive homogeneous polynomial coordinate of the actual unipotent group
has one weight for the full torus, over an arbitrary local ring. -/
theorem exists_isHomogeneous [IsLocalRing R] {d : ℕ} (hd : 0 < d)
    {x : quotientAlgebra (unipotentIdeal (cocharacter i ν))}
    (hx : x ∈ CommutativeAlgebra.GradedLine.homog
      (isGrading_unipCoaction (cocharacter i ν)) d)
    (hgen : Function.Bijective (Polynomial.aeval x :
      R[X] →ₐ[R] quotientAlgebra (unipotentIdeal (cocharacter i ν)))) :
    ∃ m : I → ℤ, IsHomogeneous (unipotentCorepresentation (cocharacter i ν))
      (torusAction i ν) m x :=
  exists_isHomogeneous_of_preserves_degree (unipotentCorepresentation (cocharacter i ν))
    (torusAction i ν) (isGrading_unipCoaction (cocharacter i ν)) hd hx hgen
    (comp_mem_homog i ν hx)

/-- A chosen full-torus weight of a positive homogeneous polynomial coordinate. -/
def coordinateWeight [IsLocalRing R] {d : ℕ} (hd : 0 < d)
    {x : quotientAlgebra (unipotentIdeal (cocharacter i ν))}
    (hx : x ∈ CommutativeAlgebra.GradedLine.homog
      (isGrading_unipCoaction (cocharacter i ν)) d)
    (hgen : Function.Bijective (Polynomial.aeval x :
      R[X] →ₐ[R] quotientAlgebra (unipotentIdeal (cocharacter i ν)))) : I → ℤ :=
  (exists_isHomogeneous i ν hd hx hgen).choose

/-- The selected weight is the coordinate's weight for actual torus conjugation. -/
theorem isHomogeneous_coordinateWeight [IsLocalRing R] {d : ℕ} (hd : 0 < d)
    {x : quotientAlgebra (unipotentIdeal (cocharacter i ν))}
    (hx : x ∈ CommutativeAlgebra.GradedLine.homog
      (isGrading_unipCoaction (cocharacter i ν)) d)
    (hgen : Function.Bijective (Polynomial.aeval x :
      R[X] →ₐ[R] quotientAlgebra (unipotentIdeal (cocharacter i ν)))) :
    IsHomogeneous (unipotentCorepresentation (cocharacter i ν)) (torusAction i ν)
      (coordinateWeight i ν hd hx hgen) x :=
  (exists_isHomogeneous i ν hd hx hgen).choose_spec

end Langlands.GroupScheme.Corepresented.UnipotentTorus
