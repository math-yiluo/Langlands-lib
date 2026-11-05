import Langlands.GroupScheme.Rational.PointedLaurentCoordinates
import Langlands.GroupScheme.Rational.PrimitivePolynomialRelations
import Langlands.GroupScheme.Unipotent.AdditiveKernelGeometry

/-! # One additive equation for a proper closed vector subgroup -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry MvPolynomial
open scoped CategoryTheory.MonObj BigOperators

namespace Langlands.GroupScheme.ClosedVectorSubgroup

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k]
    {F : CommAlgCat.{u} (CommRingCat.of k) ⥤ GrpCat.{u}}
    {B : CommAlgCat.{u} (CommRingCat.of k)}
    (e : (F ⋙ forget GrpCat).CorepresentableBy B) {n : ℕ}
    (q : Corepresented.groupScheme F e ⟶ VectorGroup.groupScheme (CommRingCat.of k) n)

/-- Coordinate pullback of a homomorphism into the standard vector group. -/
def coordinatePullback : VectorGroup.coordinateAlgebra (CommRingCat.of k) n ⟶ B :=
  (algSpec.fullyFaithful.preimage q.hom.hom).unop

theorem map_coordinatePullback :
    (algSpec (CommRingCat.of k)).map (coordinatePullback e q).op = q.hom.hom :=
  algSpec.fullyFaithful.map_preimage _

/-- The pulled-back linear coordinates. -/
def coordinateFamily (j : Fin n) : B :=
  (coordinatePullback e q).hom (X j)

theorem coordinatePullback_eq_aeval :
    (coordinatePullback e q).hom = aeval (coordinateFamily e q) := by
  ext j
  simp [coordinateFamily]

theorem affine_coordinates (A : CommAlgCat.{u} (CommRingCat.of k)) (x : F.obj A) :
    (Corepresented.affinePointsEquiv _ (VectorGroup.corepresentableBy (CommRingCat.of k) n) A
      ((Corepresented.affinePointsEquiv F e A).symm x ≫ q.hom.hom)).toAdd =
        fun j => (e.homEquiv.symm x).hom (coordinateFamily e q j) := by
  have hx : (Corepresented.affinePointsEquiv F e A).symm x =
      (algSpec (CommRingCat.of k)).map (e.homEquiv.symm x).op := by
    apply (Corepresented.affinePointsEquiv F e A).injective
    rw [MulEquiv.apply_symm_apply, Corepresented.affinePointsEquiv_map,
      Equiv.apply_symm_apply]
  rw [hx, ← map_coordinatePullback e q, ← Functor.map_comp]
  change (Corepresented.affinePointsEquiv (VectorGroup.functor (CommRingCat.of k) n)
    (VectorGroup.corepresentableBy (CommRingCat.of k) n) A
    ((algSpec (CommRingCat.of k)).map
      (coordinatePullback e q ≫ e.homEquiv.symm x).op)).toAdd = _
  rw [Corepresented.affinePointsEquiv_map]
  rfl

theorem coordinateFamily_primitive :
    VectorGroup.IsPrimitiveFamily e (coordinateFamily e q) := by
  intro A x y j
  have h := congrArg (fun z =>
    (Corepresented.affinePointsEquiv _ (VectorGroup.corepresentableBy (CommRingCat.of k) n)
      A z).toAdd j)
    (MonObj.mul_comp ((Corepresented.affinePointsEquiv F e A).symm x)
      ((Corepresented.affinePointsEquiv F e A).symm y) q.hom.hom)
  rw [← map_mul, affine_coordinates e q A (x * y)] at h
  rw [(Corepresented.affinePointsEquiv (VectorGroup.functor (CommRingCat.of k) n)
    (VectorGroup.corepresentableBy (CommRingCat.of k) n) A).map_mul] at h
  change (e.homEquiv.symm (x * y)).hom (coordinateFamily e q j) =
    (Corepresented.affinePointsEquiv _ (VectorGroup.corepresentableBy (CommRingCat.of k) n)
      A ((Corepresented.affinePointsEquiv F e A).symm x ≫ q.hom.hom)).toAdd j +
    (Corepresented.affinePointsEquiv _ (VectorGroup.corepresentableBy (CommRingCat.of k) n)
      A ((Corepresented.affinePointsEquiv F e A).symm y ≫ q.hom.hom)).toAdd j at h
  simpa only [
    affine_coordinates e q A x, affine_coordinates e q A y] using h

/-- A closed immersion into a vector group is a quotient on coordinate algebras. -/
theorem coordinatePullback_surjective [IsClosedImmersion q.hom.hom.left] :
    Function.Surjective (coordinatePullback e q).hom := by
  let ψ := CommRingCat.ofHom (coordinatePullback e q).hom.toRingHom
  have hψ : Spec.map ψ = q.hom.hom.left :=
    congrArg CommaMorphism.left (map_coordinatePullback e q)
  have : IsClosedImmersion (Spec.map ψ) := hψ.symm ▸ inferInstance
  have happ : Function.Surjective (Spec.map ψ).appTop :=
    (Spec.map ψ).app_surjective ⊤ (isAffineOpen_top _)
  have heq : ψ = (Scheme.ΓSpecIso _).inv ≫ (Spec.map ψ).appTop ≫
      (Scheme.ΓSpecIso _).hom := by
    rw [Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
  have hs : Function.Surjective ψ.hom := by
    rw [heq, CommRingCat.hom_comp, CommRingCat.hom_comp,
      RingHom.coe_comp, RingHom.coe_comp]
    exact (Scheme.ΓSpecIso _).commRingCatIsoToRingEquiv.surjective.comp
      (happ.comp (Scheme.ΓSpecIso _).symm.commRingCatIsoToRingEquiv.surjective)
  exact hs

/-- Bijective coordinate pullback makes the original group homomorphism an isomorphism. -/
theorem isIso_of_coordinatePullback_bijective
    (hbij : Function.Bijective (coordinatePullback e q).hom) : IsIso q := by
  let φ := RingEquiv.ofBijective (coordinatePullback e q).hom hbij
  have : IsIso q.hom.hom.left := by
    rw [← map_coordinatePullback e q]
    change IsIso (Spec.map φ.toCommRingCatIso.hom)
    infer_instance
  have : IsIso ((Over.forget _).map q.hom.hom) := by
    change IsIso q.hom.hom.left
    infer_instance
  have : IsIso q.hom.hom := isIso_of_reflects_iso _ (Over.forget _)
  have : IsIso ((Mon.forget _).map q.hom) := by
    change IsIso q.hom.hom
    infer_instance
  have : IsIso q.hom := isIso_of_reflects_iso _ (Mon.forget _)
  have : IsIso ((Grp.forget₂Mon _).map q) := by
    change IsIso q.hom
    infer_instance
  exact isIso_of_reflects_iso q (Grp.forget₂Mon _)

/-- A proper closed embedding supplies a nonzero relation in primitive coordinates. -/
theorem exists_additive_equation [IsClosedImmersion q.hom.hom.left]
    (hq : ¬ IsIso q) :
    ∃ f : MvPolynomial (Fin n) k, f ≠ 0 ∧ TorusLinearization.IsAddPoly f ∧
      aeval (coordinateFamily e q) f = 0 := by
  let := AffineLinearEmbedding.bialgebra e
  have hx : ∀ j, Bialgebra.IsPrimitiveElem k (coordinateFamily e q j) := by
    intro j
    exact (Corepresented.mem_primitiveFunctions_iff e).mpr
      (fun A x y => coordinateFamily_primitive e q A x y j)
  apply PrimitivePolynomial.exists_additive_relation hx
  have hn : ¬ Function.Injective (coordinatePullback e q).hom := by
    intro hi
    exact hq (isIso_of_coordinatePullback_bijective e q
      ⟨hi, coordinatePullback_surjective e q⟩)
  obtain ⟨f, g, hfg, hne⟩ := Function.not_injective_iff.mp hn
  refine ⟨f - g, sub_ne_zero.mpr hne, ?_⟩
  rw [← coordinatePullback_eq_aeval, map_sub, hfg, sub_self]

/-- The recovered primitive coordinates define the original homomorphism. -/
theorem eq_quotientMap :
    q = VectorGroup.quotientMap (coordinateFamily_primitive e q) := by
  apply Grp.hom_ext
  apply Over.OverMorphism.ext
  rw [VectorGroup.quotientMap_left, ← map_coordinatePullback e q]
  change Spec.map (CommRingCat.ofHom (coordinatePullback e q).hom.toRingHom) =
    Spec.map (CommRingCat.ofHom (aeval (coordinateFamily e q)).toRingHom)
  rw [coordinatePullback_eq_aeval]

/-- A separated additive coordinate relation vanishes as an actual group map. -/
theorem comp_polynomialRow_eq_zero
    (f : Fin n → Polynomial k)
    (hf : ∀ i, Unipotent.OneDimensional.IsAdditive (f i))
    (hrel : (∑ i, Polynomial.aeval (coordinateFamily e q i) (f i)) = 0) :
    q ≫ Unipotent.polynomialRow f hf = 0 := by
  apply hom_ext_points
  intro T x
  rw [Grp.comp_hom_hom, ← Category.assoc, Unipotent.comp_polynomialRow,
    Grp.zero_hom, Mon.zero_hom, ← Hom.one_def, MonObj.comp_one]
  apply VectorGroup.points_ext
  intro j
  rw [Unipotent.polynomialRowPoints_coord]
  simp only [map_one, toAdd_one, Pi.zero_apply]
  rw [eq_quotientMap e q]
  simp_rw [VectorGroup.coordinates_quotientMap]
  let A := ((algΓ (CommRingCat.of k)).obj T).unop
  let σ : B ⟶ A := e.homEquiv.symm (Corepresented.pointsEquiv F e T x)
  have hz := congrArg σ.hom hrel
  rw [map_sum, map_zero] at hz
  change (∑ i, Polynomial.aeval (σ.hom (coordinateFamily e q i)) (f i)) = 0
  simpa only [Polynomial.aeval_algHom_apply] using hz

/-- Every proper closed subgroup of a vector group is annihilated by a nonzero
row of additive one-variable polynomials. -/
theorem exists_annihilating_polynomialRow [IsClosedImmersion q.hom.hom.left]
    (hq : ¬ IsIso q) :
    ∃ (f : Fin n → Polynomial k)
      (hf : ∀ i, Unipotent.OneDimensional.IsAdditive (f i)),
      (∃ i, f i ≠ 0) ∧ q ≫ Unipotent.polynomialRow f hf = 0 := by
  obtain ⟨g, hg, hga, hge⟩ := exists_additive_equation e q hq
  let f : Fin n → Polynomial k := fun i => TorusLinearization.part i g
  have hf : ∀ i, Unipotent.OneDimensional.IsAdditive (f i) := by
    intro i
    exact Unipotent.OneDimensional.isAdditive_of_aeval _
      (hga.isAddPoly₁_part i _ _ _)
  refine ⟨f, hf, ?_, comp_polynomialRow_eq_zero e q f hf ?_⟩
  · by_contra hn
    push Not at hn
    apply hg
    rw [hga.eq_sum_part]
    exact Finset.sum_eq_zero fun i _ => by rw [show TorusLinearization.part i g = 0 from hn i, map_zero]
  · rw [hga.eq_sum_part, map_sum] at hge
    simpa only [f, ← Polynomial.aeval_algHom_apply, aeval_X] using hge

end Langlands.GroupScheme.ClosedVectorSubgroup
