import Langlands.GroupScheme.Reductive.RelativeIsogenyRootUnit
import Langlands.GroupScheme.Reductive.LocalWeylNormalizationField
import Langlands.CommutativeAlgebra.AdditivePrimePower

/-! # Root restrictions of locally quasi-finite maps over local rings -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.LocalSplitCell

open LocalSplitRootBaseChange

variable {R : Type u} [CommRing R]

/-- Coefficient base change preserves local quasi-finiteness. -/
theorem locallyQuasiFinite_baseChangeEndomorphism (A : Type u) [CommRing A] [Algebra R A]
    (f : Ga R ⟶ Ga R) [LocallyQuasiFinite f.hom.hom.left] :
    LocallyQuasiFinite (baseChangeEndomorphism A f).hom.hom.left := by
  have : LocallyQuasiFinite
      ((GroupScheme.baseChange (algebraBaseMap R A)).map f).hom.hom.left :=
    MorphismProperty.of_isPullback
      (baseChange_map_isPullback (algebraBaseMap R A) f).flip inferInstance
  have : IsIso (gaIso (R := R) A).inv.hom.hom.left :=
    (inferInstance : IsIso (((Grp.forget _) ⋙ Over.forget _).map (gaIso (R := R) A).inv))
  have : IsIso (gaIso (R := R) A).hom.hom.hom.left :=
    (inferInstance : IsIso (((Grp.forget _) ⋙ Over.forget _).map (gaIso (R := R) A).hom))
  change LocallyQuasiFinite (((gaIso (R := R) A).inv.hom.hom.left ≫
    ((GroupScheme.baseChange (algebraBaseMap R A)).map f).hom.hom.left) ≫
      (gaIso (R := R) A).hom.hom.hom.left)
  infer_instance

/-- The additive line over a field has two distinct points, one specializing to the
other, so it is not discrete. -/
theorem not_discreteTopology_ga (K : Type u) [Field K] :
    ¬ DiscreteTopology (Ga K).X.left := by
  intro hd
  let B := MvPolynomial (Fin 1) K
  let p₀ : PrimeSpectrum B := ⟨⊥, Ideal.isPrime_bot⟩
  let p₁ : PrimeSpectrum B :=
    ⟨RingHom.ker (MvPolynomial.constantCoeff (R := K) (σ := Fin 1)), RingHom.ker_isPrime _⟩
  have hspec : p₀ ⤳ p₁ := (PrimeSpectrum.le_iff_specializes p₀ p₁).1 bot_le
  have hspec' : (show (Ga K).X.left from p₀) ⤳ (show (Ga K).X.left from p₁) := hspec
  have heq := specializes_iff_eq.1 hspec'
  have hX : (MvPolynomial.X 0 : B) ∈ p₁.asIdeal := by
    change MvPolynomial.constantCoeff (MvPolynomial.X 0 : B) = 0
    simp
  have hX' : (MvPolynomial.X 0 : B) ∈ p₀.asIdeal := by
    have : p₀ = p₁ := heq
    rw [this]
    exact hX
  exact MvPolynomial.X_ne_zero (R := K) (0 : Fin 1) hX'

/-- A power formula for a locally quasi-finite additive-line map over a field has
nonzero coefficient. -/
theorem coefficient_ne_zero_of_locallyQuasiFinite {K : Type u} [Field K] (f : Ga K ⟶ Ga K)
    [LocallyQuasiFinite f.hom.hom.left] (c : K) (q : ℕ)
    (hf : ∀ (Z : Over (Spec (CommRingCat.of K))) (a : Γ(Z.left, ⊤)),
      rootPoint f Z a = VectorGroup.scalarPoint _ Z (baseScalar Z c * a ^ q)) : c ≠ 0 := by
  intro hc
  have hzero : f.hom.hom = 1 := by
    have h := hf (Ga K).X (gaCoord (𝟙 (Ga K).X))
    rw [rootPoint, VectorGroup.scalarPoint_coordinate, Category.id_comp] at h
    rw [h]
    apply VectorGroup.points_ext
    intro j
    simp only [VectorGroup.coordinates_scalarPoint, baseScalar, hc, map_zero, zero_mul,
      map_one, toAdd_one, Pi.zero_apply]
  have hconst : ∀ x y : (Ga K).X.left, f.hom.hom.left x = f.hom.hom.left y := by
    intro x y
    rw [hzero, Hom.one_def, Over.comp_left, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
    congr 1
    exact @Subsingleton.elim (Spec (CommRingCat.of K)) _ _ _
  obtain ⟨x₀⟩ : Nonempty (Ga K).X.left :=
    ⟨show (Ga K).X.left from (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (MvPolynomial (Fin 1) K))⟩
  have hdisc := f.hom.hom.left.isDiscrete_preimage_singleton (f.hom.hom.left x₀)
  have huniv : f.hom.hom.left ⁻¹' {f.hom.hom.left x₀} = Set.univ :=
    Set.eq_univ_of_forall fun x => hconst x x₀
  rw [huniv] at hdisc
  exact not_discreteTopology_ga K (isDiscrete_univ_iff.mp hdisc)

/-- A locally quasi-finite additive-line power map over any commutative ring has unit
coefficient. -/
theorem isUnit_coefficient_of_power_of_locallyQuasiFinite (f : Ga R ⟶ Ga R)
    [LocallyQuasiFinite f.hom.hom.left] (c : R) (q : ℕ)
    (hf : ∀ (A : CommAlgCat.{u} (CommRingCat.of R)) (a : A),
      (scalarOperation f).app A a = algebraMap R A c * a ^ q) : IsUnit c := by
  have hc := (scalarOperation f).isUnit_value_one_of_fields (by
    intro K _ _
    let fK := baseChangeEndomorphism K f
    let : LocallyQuasiFinite fK.hom.hom.left := locallyQuasiFinite_baseChangeEndomorphism K f
    have hbc (Z : Over (Spec (CommRingCat.of K))) (a : Γ(Z.left, ⊤)) :
        rootPoint fK Z a =
          VectorGroup.scalarPoint _ Z (baseScalar Z (algebraMap R K c) * a ^ q) := by
      apply VectorGroup.points_ext
      intro j
      rw [Subsingleton.elim j 0]
      change gaCoord (rootPoint (baseChangeEndomorphism K f) Z a) = _
      rw [gaCoord_baseChangeEndomorphism, rootPoint_eq_of_scalarOperation hf,
        gaCoord, VectorGroup.coordinates_scalarPoint, baseScalar_map,
        VectorGroup.coordinates_scalarPoint]
    have hn := coefficient_ne_zero_of_locallyQuasiFinite fK (algebraMap R K c) q hbc
    simpa only [hf, one_pow, mul_one] using hn)
  simpa only [hf, Algebra.algebraMap_self, RingHom.id_apply, one_pow, mul_one] using hc

/-- The coefficient operation of an additive-line homomorphism is additive. -/
theorem scalarOperation_add (f : Ga R ⟶ Ga R) (A : CommAlgCat.{u} (CommRingCat.of R))
    (a b : A) :
    (scalarOperation f).app A (a + b) = (scalarOperation f).app A a + (scalarOperation f).app A b := by
  let Z := Corepresented.RingCoordinates.specOver (CommRingCat.of R) A
  change (Scheme.ΓSpecIso (CommRingCat.of A)).hom (gaCoord (rootPoint f Z
      ((Scheme.ΓSpecIso (CommRingCat.of A)).inv (a + b)))) =
    (Scheme.ΓSpecIso (CommRingCat.of A)).hom (gaCoord (rootPoint f Z
      ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a))) +
    (Scheme.ΓSpecIso (CommRingCat.of A)).hom (gaCoord (rootPoint f Z
      ((Scheme.ΓSpecIso (CommRingCat.of A)).inv b)))
  rw [map_add, rootPoint_add, gaCoord, VectorGroup.coordinates_mul, Pi.add_apply, map_add]

end Langlands.GroupScheme.LocalSplitCell

namespace Langlands.GroupScheme.RelativeIsogeny

open LocalRootGroup LocalSplitCell

variable {R : Type u} [CommRing R] [IsLocalRing R]
  {I I' : Type u} [Fintype I] [Fintype I'] [DecidableEq I] [DecidableEq I']
  {G H : GroupScheme (Spec (CommRingCat.of R))}
  [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
  (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
  (j : splitTorus (Spec (CommRingCat.of R)) I' ⟶ H)
  {J J' : Type u} [Finite J] [Finite J']
  {P : RootDatum J (I → ℤ) (I → ℤ)}
  {Q : RootDatum J' (I' → ℤ) (I' → ℤ)}
  [P.IsReduced] [Q.IsReduced]
  (hP : IsFibrewiseRootDatumOf I G i P) (hQ : IsFibrewiseRootDatumOf I' H j Q)
  {p : ℕ} (r : Langlands.LinearAlgebra.RootDatumIsogeny p Q P)
  (tau : splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I ⟶
    splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I')
  (hweight : ∀ m : I' → ℤ, tau ≫ splitTorus.exponentCharacter _ I' m =
    splitTorus.exponentCharacter _ I (r.weightMap m))
  (phi : G ⟶ H) (hphi : i ≫ phi = CommGroupScheme.groupHom tau ≫ j)
  (hH : IsReductive H)
  (hmaxH : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I') j)
  (b : J')
  {u : Ga R ⟶ G} {v : Ga R ⟶ H}
  (hu : IsRootParametrization i (P.root (r.indexEquiv b)) u)
  (hv : IsRootParametrization j (Q.root b) v)
  [LocallyQuasiFinite phi.hom.hom.left]

/-- An actual root restriction of a locally quasi-finite ambient map is locally
quasi-finite. -/
theorem rootRestriction_locallyQuasiFinite :
    LocallyQuasiFinite
      (rootRestriction i j hP hQ r tau hweight phi hphi hH hmaxH b hu hv).hom.hom.left := by
  let f := rootRestriction i j hP hQ r tau hweight phi hphi hH hmaxH b hu hv
  have : IsClosedImmersion u.hom.hom.left := hu.isClosedSubgroup
  have hcomp : f.hom.hom.left ≫ v.hom.hom.left =
      u.hom.hom.left ≫ phi.hom.hom.left := by
    exact congrArg (fun h : Ga R ⟶ H => h.hom.hom.left)
      (rootRestriction_comp i j hP hQ r tau hweight phi hphi hH hmaxH b hu hv)
  have : LocallyQuasiFinite (f.hom.hom.left ≫ v.hom.hom.left) := hcomp.symm ▸ inferInstance
  exact LocallyQuasiFinite.of_comp f.hom.hom.left v.hom.hom.left

/-- Local quasi-finiteness forces the prescribed-power coefficient of the actual root
restriction to be a unit of the local base ring. -/
theorem isUnit_rootRestrictionCoefficient_of_locallyQuasiFinite :
    IsUnit (rootRestrictionCoefficient i j hP hQ r tau hweight phi hphi hH hmaxH b hu hv) := by
  let f := rootRestriction i j hP hQ r tau hweight phi hphi hH hmaxH b hu hv
  let : LocallyQuasiFinite f.hom.hom.left :=
    rootRestriction_locallyQuasiFinite i j hP hQ r tau hweight phi hphi hH hmaxH b hu hv
  exact isUnit_coefficient_of_power_of_locallyQuasiFinite f _ (r.rootFactor b)
    (rootRestriction_power i j hP hQ r tau hweight phi hphi hH hmaxH b hu hv)

include hP hQ hweight hphi hH hmaxH hu hv in
/-- If a locally quasi-finite map carries the root group of `r.indexEquiv b` to that of `b`
with root factor different from `1`, then the characteristic exponent `p` of `r` vanishes
in the local base ring: the map `x ↦ c x ^ (p ^ n)` on the root groups is additive with unit
coefficient `c`. -/
theorem natCast_eq_zero_of_rootFactor_ne_one (hb : r.rootFactor b ≠ 1) : (p : R) = 0 := by
  obtain ⟨n, hn⟩ := r.rootFactor_pow b
  have hp : p.Prime := by
    rcases r.characteristicExponent with h | h
    · exact absurd (by rw [hn, h, one_pow]) hb
    · exact h
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hb (by rw [hn, pow_zero])
  have hc := isUnit_rootRestrictionCoefficient_of_locallyQuasiFinite
    i j hP hQ r tau hweight phi hphi hH hmaxH b hu hv
  let B : CommAlgCat.{u} (CommRingCat.of R) := CommAlgCat.of R (Polynomial (Polynomial R))
  have hadd := scalarOperation_add
    (rootRestriction i j hP hQ r tau hweight phi hphi hH hmaxH b hu hv) B
    (Polynomial.X : Polynomial (Polynomial R)) (Polynomial.C Polynomial.X)
  rw [rootRestriction_power, rootRestriction_power, rootRestriction_power, hn] at hadd
  exact Langlands.CommutativeAlgebra.natCast_prime_eq_zero_of_add_pow hp hn0 hc hadd

end Langlands.GroupScheme.RelativeIsogeny
