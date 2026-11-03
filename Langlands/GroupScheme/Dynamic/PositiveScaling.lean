import Langlands.GroupScheme.Dynamic.AffineRepresentability
import Langlands.GroupScheme.Torus.Lattice
import Langlands.GroupScheme.RepresentedSubgroup

/-! # Positive integral scaling of actual dynamic parabolics -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace AffineLine

/-- Multiplication by an integer on the Laurent exponent group. -/
def scaleExponent (n : ℤ) : ℤ →+ ℤ where
  toFun m := n * m
  map_zero' := mul_zero n
  map_add' := mul_add n

/-- Substitution `T ↦ Tⁿ` on Laurent polynomials over any commutative ring. -/
def laurentPower (A : CommRingCat.{u}) (n : ℤ) :
    CommRingCat.of (LaurentPolynomial A) ⟶ CommRingCat.of (LaurentPolynomial A) :=
  CommRingCat.ofHom (AddMonoidAlgebra.mapDomainRingHom A (scaleExponent n))

@[simp] theorem laurentPower_single (A : CommRingCat.{u}) (n m : ℤ) (a : A) :
    laurentPower A n (AddMonoidAlgebra.single m a) = AddMonoidAlgebra.single (n * m) a :=
  AddMonoidAlgebra.mapDomain_single

@[simp] theorem laurentPower_C (A : CommRingCat.{u}) (n : ℤ) (a : A) :
    laurentPower A n (LaurentPolynomial.C a) = LaurentPolynomial.C a := by
  simpa only [← LaurentPolynomial.single_eq_C, mul_zero] using laurentPower_single A n 0 a

@[simp] theorem laurentPower_T (A : CommRingCat.{u}) (n m : ℤ) :
    laurentPower A n (LaurentPolynomial.T m) = LaurentPolynomial.T (n * m) :=
  laurentPower_single A n m 1

theorem coeff_laurentPower_mul (A : CommRingCat.{u}) {n : ℤ} (hn : n ≠ 0)
    (q : LaurentPolynomial A) (m : ℤ) :
    (laurentPower A n q).coeff (n * m) = q.coeff m := by
  change (Finsupp.mapDomain (fun i : ℤ => n * i) q.coeff) (n * m) = q.coeff m
  exact Finsupp.mapDomain_apply_of_injective (f := fun i : ℤ => n * i)
    (fun _ _ h => mul_left_cancel₀ hn h) q.coeff m

theorem coeff_laurentPower_of_not_dvd (A : CommRingCat.{u}) (n m : ℤ)
    (hm : ¬ n ∣ m) (q : LaurentPolynomial A) :
    (laurentPower A n q).coeff m = 0 := by
  change (Finsupp.mapDomain (fun i : ℤ => n * i) q.coeff) m = 0
  apply Finsupp.mapDomain_of_notMem_range
  rintro ⟨i, hi⟩
  exact hm ⟨i, hi.symm⟩

theorem polynomialC_comp_polynomialToLaurent_comp_laurentPower
    (A : CommRingCat.{u}) (n : ℤ) :
    polynomialC A ≫ polynomialToLaurent A ≫ laurentPower A n =
      polynomialC A ≫ polynomialToLaurent A := by
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  change laurentPower A n (Polynomial.toLaurent (Polynomial.C a)) =
    Polynomial.toLaurent (Polynomial.C a)
  simpa only [Polynomial.toLaurent_C] using laurentPower_C A n a

theorem specMap_laurentPower_comp (A : CommRingCat.{u}) (n : ℤ) :
    Spec.map (laurentPower A n) ≫ Spec.map (polynomialToLaurent A) ≫
      Spec.map (polynomialC A) =
        Spec.map (polynomialToLaurent A) ≫ Spec.map (polynomialC A) := by
  simp only [← Spec.map_comp]
  congr 1
  exact polynomialC_comp_polynomialToLaurent_comp_laurentPower A n

variable {S : Scheme.{u}} {A : CommRingCat.{u}} (f : Spec A ⟶ S)

/-- Substitution `T ↦ Tⁿ` on the actual affine Laurent test scheme. -/
def laurentPowerMap (n : ℤ) : laurentScheme f ⟶ laurentScheme f :=
  Over.homMk (Spec.map (laurentPower A n)) (by
    change Spec.map (laurentPower A n) ≫
      (Spec.map (polynomialToLaurent A) ≫ Spec.map (polynomialC A) ≫ f) =
        Spec.map (polynomialToLaurent A) ≫ Spec.map (polynomialC A) ≫ f
    simpa only [Category.assoc] using
      congrArg (fun h => h ≫ f) (specMap_laurentPower_comp A n))

/-- The Laurent substitution is the power map on the multiplicative coordinate. -/
theorem laurentPowerMap_comp_laurentPoint (n : ℤ) :
    laurentPowerMap f n ≫ laurentPoint f =
      laurentPoint f ≫
        Over.mk f ◁ (CommGroupScheme.groupHom (Gm.powerHom S n)).hom.hom := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, laurentPoint, lift_fst, whiskerLeft_fst]
    apply Over.OverMorphism.ext
    change Spec.map (laurentPower A n) ≫
      (Spec.map (polynomialToLaurent A) ≫ Spec.map (polynomialC A)) =
        Spec.map (polynomialToLaurent A) ≫ Spec.map (polynomialC A)
    exact specMap_laurentPower_comp A n
  · simp only [Category.assoc, laurentPoint, lift_snd, whiskerLeft_snd]
    rw [← Category.assoc, lift_snd]
    apply (Gm.pointsEquiv S _).injective
    rw [Gm.powerHom_apply, Gm.comp_zsmul_id, map_zpow,
      Gm.pointsEquiv_naturality, MulEquiv.apply_symm_apply]
    rw [laurentUnit]
    rw [← (Units.map
      (Scheme.ΓSpecIso (CommRingCat.of (LaurentPolynomial A))).inv.hom.toMonoidHom).map_zpow]
    apply Units.ext
    change (Spec.map (laurentPower A n)).appTop
        ((Scheme.ΓSpecIso _).inv (LaurentPolynomial.T 1)) =
      (Scheme.ΓSpecIso _).inv
        ((Gm.relativeCoordUnit A ^ n : (LaurentPolynomial A)ˣ) : LaurentPolynomial A)
    rw [Gm.relativeCoordUnit_zpow_val, ← CommRingCat.comp_apply,
      ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply]
    exact congrArg
      (fun z : LaurentPolynomial A => (Scheme.ΓSpecIso (CommRingCat.of (LaurentPolynomial A))).inv z)
      (by simpa only [mul_one] using laurentPower_T A n 1)

end AffineLine

namespace Dynamic
variable {S : Scheme.{u}} {G : GroupScheme S}

/-- Precomposing a cocharacter pulls its orbit back on the multiplicative coordinate. -/
theorem orbit_precomp (χ : (Gm S).toGrp ⟶ G) (p : (Gm S).toGrp ⟶ (Gm S).toGrp)
    {T : Over S} (g : T ⟶ G.X) :
    orbit (p ≫ χ) g = T ◁ p.hom.hom ≫ orbit χ g := by
  simp only [orbit, Grp.comp_hom_hom, MonObj.comp_mul, GrpObj.comp_inv,
    whiskerLeft_snd_assoc, whiskerLeft_fst_assoc]

end Dynamic

namespace Corepresented
open AffineLine

variable {R : CommRingCat.{u}} {F : CommAlgCat.{u} R ⥤ GrpCat.{u}}
    {B : CommAlgCat.{u} R} {e : (F ⋙ forget GrpCat).CorepresentableBy B}

/-- The orbit coaction of a scaled cocharacter substitutes `Tⁿ` for `T`. -/
theorem coaction_precomp_power
    (χ : (Gm (Spec R)).toGrp ⟶ groupScheme F e) (n : ℤ) :
    coaction (CommGroupScheme.groupHom (Gm.powerHom (Spec R) n) ≫ χ) =
      coaction χ ≫ laurentPower (CommRingCat.of B) n := by
  apply Spec.map_injective
  rw [specMap_coaction, Spec.map_comp, specMap_coaction]
  change (laurentPoint (structureMap e) ≫
      Dynamic.orbit (CommGroupScheme.groupHom (Gm.powerHom (Spec R) n) ≫ χ)
        (universalPoint e)).left =
    (laurentPowerMap (structureMap e) n ≫ laurentPoint (structureMap e) ≫
      Dynamic.orbit χ (universalPoint e)).left
  rw [Dynamic.orbit_precomp, ← Category.assoc,
    ← laurentPowerMap_comp_laurentPoint, Category.assoc]

/-- Positive scaling leaves the negative-degree coefficient ideal unchanged. -/
theorem parabolicIdeal_precomp_power
    (χ : (Gm (Spec R)).toGrp ⟶ groupScheme F e) {n : ℤ} (hn : 0 < n) :
    parabolicIdeal (CommGroupScheme.groupHom (Gm.powerHom (Spec R) n) ≫ χ) =
      parabolicIdeal χ := by
  have hc (b : B) :
      coaction (CommGroupScheme.groupHom (Gm.powerHom (Spec R) n) ≫ χ) b =
        laurentPower (CommRingCat.of B) n (coaction χ b) := by
    rw [coaction_precomp_power]
    rfl
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro d ⟨b, m, hm, rfl⟩
    rw [hc]
    by_cases hd : n ∣ m
    · obtain ⟨m', rfl⟩ := hd
      rw [coeff_laurentPower_mul _ hn.ne']
      apply Ideal.subset_span
      refine ⟨b, m', ?_, rfl⟩
      by_contra h
      have := mul_nonneg hn.le (le_of_not_gt h)
      omega
    · rw [coeff_laurentPower_of_not_dvd _ n m hd]
      exact Ideal.zero_mem _
  · apply Ideal.span_le.mpr
    rintro d ⟨b, m, hm, rfl⟩
    apply Ideal.subset_span
    refine ⟨b, n * m, mul_neg_of_pos_of_neg hn hm, ?_⟩
    rw [hc, coeff_laurentPower_mul _ hn.ne']

/-- Affine ideal descriptions by the same ideal determine the same subgroup
functor on every test scheme. -/
theorem IsAffineCutOutBy.eq_of_sameIdeal
    {K K' : SubgroupFunctor (groupScheme F e)} {I : Ideal B}
    (hK : IsAffineCutOutBy e K I) (hK' : IsAffineCutOutBy e K' I) : K = K' := by
  rw [← cutSubgroupFunctor_affineSubgroups hK,
    ← cutSubgroupFunctor_affineSubgroups hK']
  apply SubgroupFunctor.ext
  intro T
  apply Subgroup.ext
  intro x
  rw [mem_cutSubgroupFunctor, mem_cutSubgroupFunctor]
  exact ((isCutOutBy_affineSubgroups hK) _ _).trans
    ((isCutOutBy_affineSubgroups hK') _ _).symm

/-- Positive scaling preserves the actual dynamic parabolic of an affine
corepresented group, on every test scheme. -/
theorem parabolic_precomp_power
    (χ : (Gm (Spec R)).toGrp ⟶ groupScheme F e) {n : ℤ} (hn : 0 < n) :
    Dynamic.parabolic (CommGroupScheme.groupHom (Gm.powerHom (Spec R) n) ≫ χ) =
      Dynamic.parabolic χ := by
  have hcut : IsAffineCutOutBy e
      (Dynamic.parabolic (CommGroupScheme.groupHom (Gm.powerHom (Spec R) n) ≫ χ))
      (parabolicIdeal χ) := by
    rw [← parabolicIdeal_precomp_power χ hn]
    exact isAffineCutOutBy_parabolic _
  exact hcut.eq_of_sameIdeal (isAffineCutOutBy_parabolic χ)

end Corepresented

namespace Dynamic
variable {R : CommRingCat.{u}} {G : GroupScheme (Spec R)} [IsAffine G.X.left]

/-- Every positive integral power gives the same actual dynamic parabolic
for an arbitrary affine group over an affine base. -/
theorem parabolic_precomp_power (χ : (Gm (Spec R)).toGrp ⟶ G) {n : ℤ} (hn : 0 < n) :
    parabolic (CommGroupScheme.groupHom (Gm.powerHom (Spec R) n) ≫ χ) = parabolic χ := by
  let e := (AffineCoordinates.groupSchemeIso G).symm
  rw [parabolic_eq_comap_of_iso _ e, parabolic_eq_comap_of_iso χ e]
  simpa only [Category.assoc] using
    congrArg (fun F => F.comap e.hom) (Corepresented.parabolic_precomp_power (χ ≫ e.hom) hn)

/-- Multiplying an actual integral cocharacter in any specified commutative
group scheme by a positive integer does not change its dynamic parabolic. -/
theorem parabolic_zsmul (T : CommGroupScheme (Spec R)) (j : T.toGrp ⟶ G)
    (ν : cocharacterLattice T) {n : ℤ} (hn : 0 < n) :
    parabolic (CommGroupScheme.groupHom (n • ν) ≫ j) =
      parabolic (CommGroupScheme.groupHom ν ≫ j) := by
  have hν : CommGroupScheme.groupHom (n • ν) =
      CommGroupScheme.groupHom (Gm.powerHom (Spec R) n) ≫ CommGroupScheme.groupHom ν := by
    change CommGroupScheme.groupHom (n • ν) =
      CommGroupScheme.groupHom (Gm.powerHom (Spec R) n ≫ ν)
    rw [Gm.powerHom_apply, Preadditive.zsmul_comp, Category.id_comp]
  rw [hν, Category.assoc]
  exact parabolic_precomp_power _ hn

namespace Affine

/-- The canonical isomorphism between the represented dynamic parabolics of a
cocharacter and any positive integral multiple. -/
def parabolicPowerIso (χ : (Gm (Spec R)).toGrp ⟶ G) {n : ℤ} (hn : 0 < n) :
    parabolicScheme (CommGroupScheme.groupHom (Gm.powerHom (Spec R) n) ≫ χ) ≅
      parabolicScheme χ :=
  (isRepresentedBy_parabolicHom
    (CommGroupScheme.groupHom (Gm.powerHom (Spec R) n) ≫ χ)).isoOfIsRepresentedBy
      (by rw [parabolic_precomp_power χ hn]; exact isRepresentedBy_parabolicHom χ)

/-- The canonical scaling isomorphism commutes with the inclusions into the
original ambient group. -/
theorem parabolicPowerIso_hom_comp (χ : (Gm (Spec R)).toGrp ⟶ G)
    {n : ℤ} (hn : 0 < n) :
    (parabolicPowerIso χ hn).hom ≫ parabolicHom χ =
      parabolicHom (CommGroupScheme.groupHom (Gm.powerHom (Spec R) n) ≫ χ) := by
  exact SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy_hom_comp _ _

end Affine
end Dynamic
end Langlands.GroupScheme
