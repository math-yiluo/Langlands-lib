import Langlands.GroupScheme.Dynamic.LieProof
import Langlands.GroupScheme.Rational.CoordinateWeightDecompositionProof
import Langlands.GroupScheme.Dynamic.AffineInclusionCriterion

/-! # Torus weights of coordinates and the dynamic unipotent subgroup of a cocharacter -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Dynamic.CocharacterWeights

open AffineLine

variable {k : Type u} [Field k]

section Laurent

variable (A : Type u) [CommRing A] [Algebra k A]

/-- The structure morphism of the actual affine test scheme of a `k`-algebra. -/
abbrev testMap : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of k) :=
  ((algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of (CommRingCat.of k) A))).hom

/-- The Laurent test scheme of `Spec A` is the actual affine test scheme of `A[T, T⁻¹]`. -/
def laurentIso :
    (algSpec (CommRingCat.of k)).obj
        (op (CommAlgCat.of (CommRingCat.of k) (LaurentPolynomial A))) ≅
      laurentScheme (testMap (k := k) A) :=
  Over.isoMk (Iso.refl _) (by
    change 𝟙 _ ≫ Spec.map (polynomialToLaurent (CommRingCat.of A)) ≫
        Spec.map (polynomialC (CommRingCat.of A)) ≫
          Spec.map (CommRingCat.ofHom (algebraMap k A)) =
      Spec.map (CommRingCat.ofHom (algebraMap k (LaurentPolynomial A)))
    rw [Category.id_comp, ← Spec.map_comp, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    change Polynomial.toLaurent (Polynomial.C (algebraMap k A a)) =
      algebraMap k (LaurentPolynomial A) a
    rw [Polynomial.toLaurent_C, LaurentPolynomial.algebraMap_apply])

/-- The constant inclusion `A ⟶ A[T, T⁻¹]` as a `k`-algebra map. -/
abbrev constAlg : A →ₐ[k] LaurentPolynomial A :=
  IsScalarTower.toAlgHom k A (LaurentPolynomial A)

/-- The first coordinate of the Laurent point is the constant coefficient extension. -/
theorem laurentIso_hom_comp_fst :
    (laurentIso (k := k) A).hom ≫ laurentPoint (testMap (k := k) A) ≫
        fst _ (Gm (Spec (CommRingCat.of k))).X =
      (algSpec (CommRingCat.of k)).map (CommAlgCat.ofHom (constAlg (k := k) A)).op := by
  apply Over.OverMorphism.ext
  rw [laurentPoint, lift_fst]
  change 𝟙 _ ≫ Spec.map (polynomialToLaurent (CommRingCat.of A)) ≫
      Spec.map (polynomialC (CommRingCat.of A)) =
    Spec.map (CommRingCat.ofHom (constAlg (k := k) A).toRingHom)
  rw [Category.id_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  change Polynomial.toLaurent (Polynomial.C a) = algebraMap A (LaurentPolynomial A) a
  rw [Polynomial.toLaurent_C, LaurentPolynomial.algebraMap_apply]
  rfl

/-- The `𝔾_m`-point of the Laurent test scheme. -/
abbrev laurentGmPoint : Lie.AffinePoints (Gm (Spec (CommRingCat.of k))).toGrp
    (LaurentPolynomial A) :=
  (laurentIso (k := k) A).hom ≫ laurentPoint (testMap (k := k) A) ≫
    snd _ (Gm (Spec (CommRingCat.of k))).X

/-- The `𝔾_m`-point of the Laurent test scheme is the Laurent coordinate. -/
theorem affinePointsEquiv_laurentGmPoint :
    Gm.affinePointsEquiv (R := CommRingCat.of (LaurentPolynomial A))
        (testMap (k := k) (LaurentPolynomial A)) (laurentGmPoint (k := k) A) =
      Gm.relativeCoordUnit A := by
  apply Units.ext
  rw [Gm.affinePointsEquiv_val, laurentGmPoint, laurentPoint, lift_snd,
    Gm.pointsEquiv_naturality, MulEquiv.apply_symm_apply]
  change (Scheme.ΓSpecIso (CommRingCat.of (LaurentPolynomial A))).hom
      ((Scheme.ΓSpecIso (CommRingCat.of (LaurentPolynomial A))).inv
        (LaurentPolynomial.T 1 : LaurentPolynomial A)) = (LaurentPolynomial.T 1 : LaurentPolynomial A)
  exact Iso.inv_hom_id_apply _ _

end Laurent

section Orbit

variable {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
  (A : Type u) [CommRing A] [Algebra k A]

/-- On the Laurent test scheme, the orbit map of a cocharacter `ν` of `T` is the conjugation
action of the torus point `ν(T)` on the constant extension of the point. -/
theorem laurentOrbit_eq (x : Lie.AffinePoints G A) :
    (laurentIso (k := k) A).hom ≫ laurentPoint (testMap (k := k) A) ≫
        orbit (CommGroupScheme.groupHom ν ≫ i) x =
      (AutomorphicAction.conjugation i).act
        (laurentGmPoint (k := k) A ≫ (CommGroupScheme.groupHom ν).hom.hom)
        (Lie.affineMap G (constAlg (k := k) A) x) := by
  rw [AutomorphicAction.conjugation_act, Lie.affineMap_apply, ← laurentIso_hom_comp_fst]
  simp only [orbit, MonObj.comp_mul, GrpObj.comp_inv, Grp.comp_hom_hom, Category.assoc]

/-- A character `w` takes the value `T ^ ⟨w, ν⟩` at the torus point `ν(T)`. -/
theorem characterValue_laurentGmPoint (w : characterLattice T) :
    (Lie.characterValue w (laurentGmPoint (k := k) A ≫ (CommGroupScheme.groupHom ν).hom.hom) :
      LaurentPolynomial A) = LaurentPolynomial.T (latticePairing T w ν) := by
  have hνw : ν ≫ w = (gmEndEquiv k).symm (latticePairing T w ν) := by
    rw [latticePairing_apply, AddEquiv.symm_apply_apply]
  rw [Lie.characterValue, ← comp_groupHom_comp, hνw, gmEndEquiv_symm_comp, map_zpow,
    affinePointsEquiv_laurentGmPoint, Gm.relativeCoordUnit_zpow_val]

variable [IsAffineHom G.X.hom]

/-- The coordinates of the Laurent orbit point at a torus eigenfunction. -/
theorem pointCoordinates_laurentOrbit (x : Lie.AffinePoints G A) {w : characterLattice T}
    {c : CharacterUnits.Coord G}
    (hc : c ∈ CoordinateWeights.weightSpace (AutomorphicAction.conjugation i) w) :
    Lie.pointCoordinates G ((laurentIso (k := k) A).hom ≫ laurentPoint (testMap (k := k) A) ≫
        orbit (CommGroupScheme.groupHom ν ≫ i) x) c =
      LaurentPolynomial.T (latticePairing T w ν) *
        LaurentPolynomial.C (Lie.pointCoordinates G x c) := by
  rw [laurentOrbit_eq, hc, Lie.pointCoordinates_naturality, characterValue_laurentGmPoint]
  rfl

end Orbit

section Coefficients

open AffineChart

variable {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom] [IsAffine G.X.left]
  {A : Type u} [CommRing A] [Algebra k A]

/-- The coefficients of the coaction at a point are the coefficients of the coordinates of the
Laurent orbit point. -/
theorem pointRing_coeff_coaction (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (x : Lie.AffinePoints G A) (b : Γ(G.X.left, ⊤)) (n : ℤ) :
    pointRing x ((coaction χ b).coeff n) =
      (Lie.pointCoordinates G ((laurentIso (k := k) A).hom ≫
        laurentPoint (testMap (k := k) A) ≫ orbit χ x)
          (DynamicLie.chartCoordinates G b)).coeff n := by
  have h1 : pointRing ((laurentIso (k := k) A).hom ≫ laurentPoint (testMap (k := k) A) ≫
      orbit χ x) = coaction χ ≫ laurentCoeffMap (pointRing x) := by
    rw [pointRing_comp, pointRing_laurentPoint_comp_orbit]
    change _ ≫ Spec.preimage (𝟙 _) = _
    rw [Spec.preimage_id, Category.comp_id]
  rw [DynamicLie.pointRing_eq_pointCoordinates] at h1
  have h2 := congrArg (fun φ => (φ b).coeff n) h1
  simp only [CommRingCat.comp_apply] at h2
  rw [← Corepresented.coeff_laurentCoeffMap]
  exact h2.symm

/-- The counit of a spectrum test, through the chosen Lie coordinates. -/
theorem preimage_testMap_counit (b : Γ(G.X.left, ⊤)) :
    Spec.preimage (testMap (k := k) A) (counit G b) =
      algebraMap k A (Lie.coordinateOrigin G (DynamicLie.chartCoordinates G b)) := by
  rw [← CommRingCat.comp_apply, ← pointRing_one, DynamicLie.pointRing_eq_pointCoordinates,
    CommRingCat.comp_apply]
  change Lie.pointCoordinates G (1 : Lie.AffinePoints G A) _ = _
  rw [Lie.pointCoordinates_one]
  rfl

variable (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

omit [IsAffine G.X.left] in
/-- At a torus eigenfunction of weight `w`, the coordinates of the Laurent orbit point of `ν`
are concentrated in degree `⟨w, ν⟩`. -/
theorem coeff_pointCoordinates_laurentOrbit (x : Lie.AffinePoints G A) {w : characterLattice T}
    {c : CharacterUnits.Coord G}
    (hc : c ∈ CoordinateWeights.weightSpace (AutomorphicAction.conjugation i) w) (n : ℤ) :
    (Lie.pointCoordinates G ((laurentIso (k := k) A).hom ≫ laurentPoint (testMap (k := k) A) ≫
        orbit (CommGroupScheme.groupHom ν ≫ i) x) c).coeff n =
      if latticePairing T w ν = n then Lie.pointCoordinates G x c else 0 := by
  rw [pointCoordinates_laurentOrbit i ν A x hc, mul_comm,
    ← LaurentPolynomial.single_eq_C_mul_T, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]

omit [IsAffine G.X.left] in
/-- The coordinates of the Laurent orbit point at a constant. -/
theorem coeff_pointCoordinates_laurentOrbit_algebraMap (x : Lie.AffinePoints G A) (r : k)
    (n : ℤ) :
    (Lie.pointCoordinates G ((laurentIso (k := k) A).hom ≫ laurentPoint (testMap (k := k) A) ≫
        orbit (CommGroupScheme.groupHom ν ≫ i) x)
          (algebraMap k (CharacterUnits.Coord G) r)).coeff n =
      if n = 0 then algebraMap k A r else 0 := by
  rw [AlgHom.commutes, LaurentPolynomial.algebraMap_apply, LaurentPolynomial.C_apply]

/-- A point of `G` lies in the dynamic unipotent subgroup of the cocharacter `ν` of a split torus
exactly when it kills the augmentation eigenfunctions of every weight `w` with `⟨w, ν⟩ ≤ 0`. -/
theorem mem_unipotent_iff_weights (hT : IsSplitTorus T.toGrp) (x : Lie.AffinePoints G A) :
    x ∈ (unipotent (CommGroupScheme.groupHom ν ≫ i)).carrier (Over.mk (testMap (k := k) A)) ↔
      ∀ w : characterLattice T, latticePairing T w ν ≤ 0 →
        ∀ g ∈ CoordinateWeights.augmentationWeightSpace (AutomorphicAction.conjugation i) w,
          Lie.pointCoordinates G x (g : CharacterUnits.Coord G) = 0 := by
  classical
  rw [mem_unipotent_iff]
  constructor
  · rintro ⟨hneg, hzero⟩ w hw g hg
    obtain ⟨b, hb⟩ := DynamicLie.chartCoordinates_surjective G (g : CharacterUnits.Coord G)
    have hbw : DynamicLie.chartCoordinates G b ∈
        CoordinateWeights.weightSpace (AutomorphicAction.conjugation i) w := by
      rw [hb]
      exact hg
    have hc := coeff_pointCoordinates_laurentOrbit i ν x hbw (latticePairing T w ν)
    rw [ite_eq_left rfl] at hc
    have hx : Lie.pointCoordinates G x (g : CharacterUnits.Coord G) =
        pointRing x ((coaction (CommGroupScheme.groupHom ν ≫ i) b).coeff
          (latticePairing T w ν)) := by
      rw [← hb, ← hc]
      exact (pointRing_coeff_coaction _ x b _).symm
    rw [hx]
    rcases hw.lt_or_eq with hw | hw
    · exact hneg b _ hw
    · rw [hw]
      refine (hzero b).trans ?_
      rw [preimage_testMap_counit, hb, CoordinateWeights.mem_augmentation.mp g.property, map_zero]
  · intro h
    have hdec := (CoordinateWeights.coordinateWeightDecomposition k G inferInstance T hT
      (AutomorphicAction.conjugation i)).2.1.submodule_iSup_eq_top
    have haug : ∀ a : CoordinateWeights.augmentation G, ∀ n ≤ 0,
        (Lie.pointCoordinates G ((laurentIso (k := k) A).hom ≫
          laurentPoint (testMap (k := k) A) ≫ orbit (CommGroupScheme.groupHom ν ≫ i) x)
            (a : CharacterUnits.Coord G)).coeff n = 0 := by
      intro a
      have ha : a ∈ ⨆ w, CoordinateWeights.augmentationWeightSpace
          (AutomorphicAction.conjugation i) w := by
        rw [hdec]
        exact Submodule.mem_top
      refine Submodule.iSup_induction
        (p := CoordinateWeights.augmentationWeightSpace (AutomorphicAction.conjugation i))
        (motive := fun (a : CoordinateWeights.augmentation G) => ∀ n ≤ 0,
        (Lie.pointCoordinates G ((laurentIso (k := k) A).hom ≫
          laurentPoint (testMap (k := k) A) ≫ orbit (CommGroupScheme.groupHom ν ≫ i) x)
            (a : CharacterUnits.Coord G)).coeff n = 0) ha ?_ ?_ ?_
      · intro w g hg n hn
        have hg' : (g : CharacterUnits.Coord G) ∈
            CoordinateWeights.weightSpace (AutomorphicAction.conjugation i) w := hg
        refine (coeff_pointCoordinates_laurentOrbit i ν x hg' n).trans ?_
        split_ifs with hwn
        · exact h w (hwn ▸ hn) g hg
        · rfl
      · intro n _
        simp
      · intro a a' ha ha' n hn
        simp only [Submodule.coe_add, map_add]
        rw [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, ha n hn, ha' n hn, add_zero]
    have hall : ∀ c : CharacterUnits.Coord G, ∀ n ≤ 0,
        (Lie.pointCoordinates G ((laurentIso (k := k) A).hom ≫
          laurentPoint (testMap (k := k) A) ≫ orbit (CommGroupScheme.groupHom ν ≫ i) x)
            c).coeff n = if n = 0 then algebraMap k A (Lie.coordinateOrigin G c) else 0 := by
      intro c n hn
      let a : CoordinateWeights.augmentation G :=
        ⟨c - algebraMap k (CharacterUnits.Coord G) (Lie.coordinateOrigin G c), by
          rw [CoordinateWeights.mem_augmentation, map_sub, AlgHom.commutes]
          exact sub_self _⟩
      have hc : c = algebraMap k (CharacterUnits.Coord G) (Lie.coordinateOrigin G c) +
          (a : CharacterUnits.Coord G) := by
        simp [a]
      conv_lhs => rw [hc]
      rw [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, haug a n hn, add_zero,
        coeff_pointCoordinates_laurentOrbit_algebraMap]
    refine ⟨fun b n hn => ?_, fun b => ?_⟩
    · refine (pointRing_coeff_coaction _ x b n).trans ?_
      rw [hall _ n hn.le, ite_eq_right hn.ne]
    · refine (pointRing_coeff_coaction _ x b 0).trans ?_
      rw [hall _ 0 le_rfl, ite_eq_left rfl, preimage_testMap_counit]

end Coefficients

section Transport

variable {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom] [IsAffine G.X.left]

/-- The `k`-algebra structure on the coefficient ring of an affine test over `Spec k`. -/
abbrev testAlgebra {A : CommRingCat.{u}} (f : Spec A ⟶ Spec (CommRingCat.of k)) : Algebra k A :=
  (Spec.preimage f).hom.toAlgebra

/-- An affine test over `Spec k` is the actual affine test scheme of its `k`-algebra. -/
def testIso {A : CommRingCat.{u}} (f : Spec A ⟶ Spec (CommRingCat.of k)) :
    letI := testAlgebra f
    Over.mk (testMap (k := k) A) ≅ Over.mk f :=
  letI := testAlgebra f
  Over.isoMk (Iso.refl _) (by
    change 𝟙 _ ≫ f = Spec.map (Spec.preimage f)
    rw [Category.id_comp, Spec.map_preimage])

variable (i : T.toGrp ⟶ G)

/-- The ideal generated by the augmentation eigenfunctions of all weights `w` with
`⟨w, ν⟩ ≤ 0`. -/
def nonpositiveIdeal (ν : cocharacterLattice T) : Ideal (CharacterUnits.Coord G) :=
  Ideal.span {c | ∃ w, latticePairing T w ν ≤ 0 ∧
    ∃ g ∈ CoordinateWeights.augmentationWeightSpace (AutomorphicAction.conjugation i) w,
      c = (g : CharacterUnits.Coord G)}

/-- If every augmentation eigenfunction of a weight `w` with `⟨w, ζ⟩ ≤ 0` lies in the
nonpositive ideal of `ν`, then the dynamic unipotent subgroup of `ν` is contained in that of
`ζ`. -/
theorem unipotent_le_of_mem_nonpositiveIdeal (hT : IsSplitTorus T.toGrp)
    (ζ ν : cocharacterLattice T)
    (h : ∀ w, latticePairing T w ζ ≤ 0 →
      ∀ g ∈ CoordinateWeights.augmentationWeightSpace (AutomorphicAction.conjugation i) w,
        (g : CharacterUnits.Coord G) ∈ nonpositiveIdeal i ν) :
    unipotent (CommGroupScheme.groupHom ν ≫ i) ≤ unipotent (CommGroupScheme.groupHom ζ ≫ i) := by
  apply unipotent_le_of_affine_tests
  intro A f x hx
  let := testAlgebra f
  have hy := (mem_unipotent_iff_weights (A := A) i ν hT ((testIso f).hom ≫ x)).mp
    ((unipotent _).comp_mem (testIso f).hom hx)
  have hz : (testIso f).hom ≫ x ∈ (unipotent (CommGroupScheme.groupHom ζ ≫ i)).carrier
      (Over.mk (testMap (k := k) A)) := by
    refine (mem_unipotent_iff_weights (A := A) i ζ hT ((testIso f).hom ≫ x)).mpr ?_
    intro w hw g hg
    have hI : nonpositiveIdeal i ν ≤
        RingHom.ker (Lie.pointCoordinates G (A := A) ((testIso f).hom ≫ x)) := by
      rw [nonpositiveIdeal, Ideal.span_le]
      rintro c ⟨w', hw', g', hg', rfl⟩
      exact hy w' hw' g' hg'
    exact hI (h w hw g hg)
  have hx' := (unipotent (CommGroupScheme.groupHom ζ ≫ i)).comp_mem (testIso f).inv hz
  rwa [Iso.inv_hom_id_assoc] at hx'

end Transport

end Langlands.GroupScheme.Dynamic.CocharacterWeights
