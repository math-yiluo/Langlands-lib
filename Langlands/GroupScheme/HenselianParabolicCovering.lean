import Langlands.GroupScheme.IntegralParabolicCovering
import Langlands.CommutativeAlgebra.HenselianSections
import Langlands.AlgebraicGeometry.PointTopology.SmoothSeparablyClosedDensity
import Langlands.Global.IntegralModelQuotientCovering
import Langlands.Global.IntegralIwasawaFamilyReduction
import Langlands.GroupScheme.IntegralModel.DynamicParabolic
import Langlands.GroupScheme.Absolute.ParabolicDynamicProof
import Langlands.GroupScheme.Reductive.GenericFiberGeometry
import Langlands.GroupScheme.IntegralModel.UnramifiedSplitMaximalTorus

/-! # Parabolic-left coverings over strictly Henselian valuation rings -/

noncomputable section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj Pointwise ValuativeRel
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.GroupScheme.HenselianParabolicCovering

section Predicate

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] {G : GroupScheme (Spec (CommRingCat.of K))}

/-- The left covering property of a model `M` of `G` by a subgroup `H` of `G(K)`:
every point of `G(K)` is a point of `H` times an integral point of `M`, that is,
`H · M(R) = G(K)`. -/
def HasLeftIntegralCovering (M : IntegralModel R K G) (H : Subgroup (rationalPoints G)) :
    Prop :=
  (H : Set (rationalPoints G)) * (M.integralPoints : Set (rationalPoints G)) = Set.univ

theorem hasLeftIntegralCovering_iff (M : IntegralModel R K G)
    (H : Subgroup (rationalPoints G)) :
    HasLeftIntegralCovering M H ↔ ∀ g : rationalPoints G,
      ∃ h ∈ H, ∃ k ∈ M.integralPoints, h * k = g := by
  unfold HasLeftIntegralCovering
  rw [Set.eq_univ_iff_forall]
  refine forall_congr' fun g => ?_
  rw [Set.mem_mul]
  simp only [SetLike.mem_coe]

end Predicate

section TorsorPoint

variable (R : Type u) [CommRing R] [HenselianLocalRing R]
  [IsSepClosed (IsLocalRing.ResidueField R)]

/-- A smooth surjective scheme over a strictly Henselian local ring has an actual section. -/
theorem nonempty_ringPoint_of_smooth (X : Over (Spec (CommRingCat.of R)))
    [Smooth X.hom] [Surjective X.hom] : Nonempty (RingPoint R X R) := by
  let κ := IsLocalRing.ResidueField R
  let X₀ := ringBaseChange R κ X
  have : Smooth X₀.hom :=
    inferInstanceAs (Smooth (pullback.snd X.hom (Spec.algebraMap R κ)))
  have : Surjective X₀.hom :=
    inferInstanceAs (Surjective (pullback.snd X.hom (Spec.algebraMap R κ)))
  have hd := hasDenseRationalPoints_of_smooth_of_isSepClosed κ X₀
  obtain ⟨s, -⟩ := X₀.hom.surjective (⊥ : PrimeSpectrum κ)
  have : Nonempty X₀.left := ⟨s⟩
  obtain ⟨y, hy⟩ := hd.nonempty
  simp only [Set.mem_iUnion, Set.mem_range] at hy
  obtain ⟨p, -, -⟩ := hy
  let b : RingPoint R X κ :=
    (ringPointBaseChangeEquiv R κ κ X).symm (rationalPointEquiv κ X₀ p)
  obtain ⟨σ, hσ, -⟩ :=
    Langlands.CommutativeAlgebra.HenselianSections.exists_section_of_smooth_of_surjective
    (K := κ) IsLocalRing.residue_surjective X.hom b.left (Over.w b)
  refine ⟨Over.homMk σ ?_⟩
  change σ ≫ X.hom = Spec.map (CommRingCat.ofHom (algebraMap R R))
  rw [hσ, Algebra.algebraMap_self]
  exact (Spec.map_id _).symm

/-- A torsor under a smooth group over a strictly Henselian local ring, given by an
fpqc morphism with invertible shear, has an actual section. No connectedness of the
special fibre is needed. -/
theorem nonempty_ringPoint_of_torsor (H : GroupScheme (Spec (CommRingCat.of R)))
    [Smooth H.X.hom] (X : Over (Spec (CommRingCat.of R))) [ModObj H.X X]
    (hfl : Flat X.hom) (hs : Surjective X.hom) (hqc : QuasiCompact X.hom)
    (hiso : IsIso (ModObj.leftSMul H.X X)) : Nonempty (RingPoint R X R) := by
  have : Smooth X.hom := IntegralTorsorPoint.smooth_of_isIso_leftSMul H X hfl hs hqc hiso
  exact nonempty_ringPoint_of_smooth R X

end TorsorPoint

section Lift

variable (R : Type u) [CommRing R] [HenselianLocalRing R]
  [IsSepClosed (IsLocalRing.ResidueField R)]
variable (G P : GroupScheme (Spec (CommRingCat.of R)))
variable {Q : Over (Spec (CommRingCat.of R))} (q : G.X ⟶ Q) (i : P ⟶ G)
variable [Mono i.hom.hom] [Flat q.left] [Surjective q.left] [QuasiCompact q.left]
variable [Smooth P.X.hom]
variable (hfib : ∀ (T : Over (Spec (CommRingCat.of R))) (g h : T ⟶ G.X),
  g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ (SubgroupFunctor.range i).carrier T)

include hfib in
/-- Every integral point of an exact coset quotient lifts to the group. -/
theorem integral_lifts_of_flagQuotient :
    ∀ p : RingPoint R Q R, ∃ g : RingPoint R G.X R, g ≫ q = p := by
  intro p
  dsimp only [RingPoint] at p
  let p₀ : RationalPoint R Q := (rationalPointEquiv R Q).symm p
  let X := Dynamic.flagQuotientFiber G q p₀
  let : ModObj P.X X := Dynamic.flagQuotientFiberModObj G q p₀ P i hfib
  obtain ⟨x⟩ := nonempty_ringPoint_of_torsor R P X
    (inferInstance : Flat X.hom) (inferInstance : Surjective X.hom)
    (inferInstance : QuasiCompact X.hom)
    (Dynamic.flagQuotientFiber_leftSMul_isIso G q p₀ P i hfib)
  let x₀ : RationalPoint R X := (rationalPointEquiv R X).symm x
  refine ⟨rationalPointEquiv R G.X (x₀ ≫ Dynamic.flagQuotientFiberι G q p₀), ?_⟩
  rw [← rationalPointEquiv_natural]
  have hx : (x₀ ≫ Dynamic.flagQuotientFiberι G q p₀) ≫ q = p₀ := by
    rw [Category.assoc, Dynamic.flagQuotientFiberι_comp, ← Category.assoc]
    have ht : x₀ ≫ toUnit X = 𝟙 (Over.mk (𝟙 (Spec (CommRingCat.of R)))) :=
      toUnit_unique _ _
    rw [ht, Category.id_comp]
  rw [hx]
  exact Equiv.apply_symm_apply _ _

end Lift

section Covering

variable (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R] [HenselianLocalRing R]
  [IsSepClosed (IsLocalRing.ResidueField R)]
variable (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
variable (G P : GroupScheme (Spec (CommRingCat.of R)))
variable {Q : Over (Spec (CommRingCat.of R))} (q : G.X ⟶ Q) (i : P ⟶ G)
variable [Mono i.hom.hom] [Flat q.left] [Surjective q.left] [QuasiCompact q.left]
variable [IsProper Q.hom] [Smooth P.X.hom]
variable (hfib : ∀ (T : Over (Spec (CommRingCat.of R))) (g h : T ⟶ G.X),
  g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ (SubgroupFunctor.range i).carrier T)

include hfib in
/-- Every fraction-field point is a subgroup point times an integral point. -/
theorem exists_mul_integral (g : ringTest R K ⟶ G.X) :
    ∃ (h : ringTest R K ⟶ P.X) (k : ringTest R R ⟶ G.X),
      (h ≫ i.hom.hom) * (ringTestMap R (Algebra.ofId R K) ≫ k) = g := by
  obtain ⟨y, hy⟩ :=
    IntegralParabolicCovering.exists_ringPoint_changeRing_eq R K Q (g⁻¹ ≫ q)
  obtain ⟨k, hk⟩ := integral_lifts_of_flagQuotient R G P q i hfib y
  let k' : ringTest R R ⟶ G.X := k
  have hq : g⁻¹ ≫ q = (show ringTest R K ⟶ G.X from
      k.changeRing (Algebra.ofId R K)) ≫ q := by
    rw [← hy, ← hk]
    exact (Category.assoc _ _ _).symm
  obtain ⟨h, hh⟩ := SubgroupFunctor.mem_range.mp ((hfib _ _ _).mp hq)
  let kinv : ringTest R R ⟶ G.X := k'⁻¹
  refine ⟨h, kinv, ?_⟩
  change (h ≫ i.hom.hom) * (ringTestMap R (Algebra.ofId R K) ≫ k'⁻¹) = g
  rw [GrpObj.comp_inv, hh, inv_inv]
  change g * ringTestMap R (Algebra.ofId R K) ≫ k' *
    (ringTestMap R (Algebra.ofId R K) ≫ k')⁻¹ = g
  rw [mul_inv_cancel_right]

include hfib in
/-- The covering with fraction-field points and integral sections in model-point form. -/
theorem exists_mul_rationalPoint (g : Over.mk (Spec.algebraMap R K) ⟶ G.X) :
    ∃ (h : Over.mk (Spec.algebraMap R K) ⟶ P.X) (k : RationalPoint R G.X),
      (h ≫ i.hom.hom) * ((Over.homMk (Spec.algebraMap R K) (by simp) :
        Over.mk (Spec.algebraMap R K) ⟶ Over.mk (𝟙 (Spec (CommRingCat.of R)))) ≫ k) =
          g := by
  obtain ⟨h, k, hk⟩ := exists_mul_integral R K G P q i hfib g
  have hres : ((Over.homMk (Spec.algebraMap R K) (by simp) :
        Over.mk (Spec.algebraMap R K) ⟶ Over.mk (𝟙 (Spec (CommRingCat.of R)))) ≫
          (rationalPointEquiv R G.X).symm k) =
        (show Over.mk (Spec.algebraMap R K) ⟶ G.X from
          ringTestMap R (Algebra.ofId R K) ≫ k) := by
    apply Over.OverMorphism.ext
    change Spec.algebraMap R K ≫ ((rationalPointEquiv R G.X).symm k).left =
      Spec.algebraMap R K ≫ k.left
    exact congrArg (fun t => Spec.algebraMap R K ≫ t)
      (rationalPointEquiv_symm_left R G.X k)
  refine ⟨h, (rationalPointEquiv R G.X).symm k, ?_⟩
  exact (congrArg (fun z => (h ≫ i.hom.hom) * z) hres).trans hk

end Covering

section Model

open IntegralModel IntegralParabolicCovering

variable {R : Type u} [CommRing R] [IsDomain R] [ValuationRing R] [HenselianLocalRing R]
  [IsSepClosed (IsLocalRing.ResidueField R)]
  {K : Type u} [Field K] [Algebra R K] [IsFractionRing R K]
  {G P : GroupScheme (Spec (CommRingCat.of K))} {f : P ⟶ G}
  (M : IntegralModel R K G) (N : IntegralModel R K P) (φ : N.Hom M f)
  {Q : Over (Spec (CommRingCat.of R))} (q : M.group.X ⟶ Q)
  [Mono φ.hom.hom.hom] [Flat q.left] [Surjective q.left] [QuasiCompact q.left]
  [IsProper Q.hom] (hsmooth : N.IsSmooth)
  (hfib : ∀ (T : Over (Spec (CommRingCat.of R))) (g h : T ⟶ M.group.X),
    g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ (SubgroupFunctor.range φ.hom).carrier T)

include hsmooth hfib in
/-- Over a strictly Henselian valuation ring, every fraction-field point is a generic
subgroup point times an integral point. -/
theorem exists_parabolic_integral_factor (g : rationalPoints G) :
    ∃ (h : rationalPoints P) (x : M.integralSections),
      rationalPoints.map f h * M.integralPointMap x = g := by
  let : Smooth N.group.X.hom := hsmooth
  obtain ⟨h, x, hk⟩ := exists_mul_rationalPoint R K M.group N.group q φ.hom hfib
    (baseChangeBasePointsEquiv (Spec.algebraMap R K) M.group
      (rationalPoints.map M.genericIso.inv g))
  refine ⟨rationalPoints.map N.genericIso.hom
      ((baseChangeBasePointsEquiv (Spec.algebraMap R K) N.group).symm h), x, ?_⟩
  rw [← genericPoint_map M N φ h, integralPointMap_eq, ← map_mul, ← map_mul, hk]
  exact genericPoint_eq M g

include hsmooth hfib in
/-- The parabolic-left integral covering for actual models over a strictly Henselian
valuation ring. -/
theorem range_mul_integralPoints_eq_univ :
    Set.range (rationalPoints.map f) *
      (M.integralPoints : Set (rationalPoints G)) = Set.univ :=
  Set.eq_univ_of_forall fun g => by
    obtain ⟨h, x, hx⟩ := exists_parabolic_integral_factor M N φ q hsmooth hfib g
    exact ⟨_, ⟨h, rfl⟩, _, (M.mem_integralPoints _).mpr ⟨x, rfl⟩, hx⟩

end Model

section Dynamic

open IntegralModel

variable {R : Type u} [CommRing R] [IsDomain R] [ValuationRing R] [HenselianLocalRing R]
  [IsSepClosed (IsLocalRing.ResidueField R)]
  {K : Type u} [Field K] [Algebra R K] [IsFractionRing R K]
  {G : GroupScheme (Spec (CommRingCat.of K))}

/-- Over a strictly Henselian valuation ring, simultaneous reductive-parabolic model data
have the parabolic-left integral covering of the generic group. -/
theorem modelData_range_mul_integralPoints_eq_univ
    {P : GroupScheme (Spec (CommRingCat.of K))} {p : P ⟶ G}
    (D : ReductiveParabolicSpreading.ModelData R K p) :
    Set.range (rationalPoints.map p) *
      (D.ambient.integralPoints : Set (rationalPoints G)) = Set.univ := by
  obtain ⟨hproper, hflat, hsurj, hqc, hfib⟩ :=
    D.quotientMap_spec Langlands.Global.IntegralIwasawaFamily.relativeParabolicQuotient
  have : IsClosedImmersion D.inclusion.hom.hom.hom.left := D.closedImmersion
  have : Mono D.inclusion.hom.hom.hom := Over.mono_of_mono_left _
  exact range_mul_integralPoints_eq_univ D.ambient D.parabolic D.inclusion _
    D.parabolicSmooth hfib

/-- A reductive model over a strictly Henselian Noetherian valuation ring has the
parabolic-left integral covering for every closed subgroup presented as the generic
dynamic parabolic of an integral cocharacter. -/
theorem range_mul_integralPoints_eq_univ_of_cocharacter [IsNoetherianRing R]
    (M : IntegralModel R K G) (hM : IsReductive M.group)
    (χ : (Gm (Spec (CommRingCat.of R))).toGrp ⟶ M.group)
    {P : GroupScheme (Spec (CommRingCat.of K))} (p : P ⟶ G) (hp : IsClosedSubgroup p)
    (hχ : SubgroupFunctor.range (p ≫ M.genericIso.inv) =
      Dynamic.parabolic (Dynamic.baseChangeCocharacter (Spec.algebraMap R K) χ)) :
    Set.range (rationalPoints.map p) * (M.integralPoints : Set (rationalPoints G)) =
      Set.univ := by
  have : Smooth M.group.X.hom := hM.smooth
  exact modelData_range_mul_integralPoints_eq_univ
    (DynamicParabolic.modelData M χ p hp hχ parabolicDynamic hM
      (fun k _ _ => fieldReductive_of_residueReductive M.group Set.univ
        (fun t _ => hM.isConnectedReductive_residueFiber t) (Spec.algebraMap R k)
        (Set.mem_univ _)))

/-- The generic dynamic parabolic `P_G(λ)`, for `λ` the generic fibre of an integral
cocharacter read through the supplied identification, times the integral points is all
of `G(K)`. -/
theorem hasLeftIntegralCovering_parabolic [IsNoetherianRing R] [IsAffine G.X.left]
    (M : IntegralModel R K G) (hM : IsReductive M.group)
    (χ : (Gm (Spec (CommRingCat.of R))).toGrp ⟶ M.group) :
    HasLeftIntegralCovering M ((Dynamic.parabolic
      (Dynamic.baseChangeCocharacter (Spec.algebraMap R K) χ ≫ M.genericIso.hom)).carrier
        (Over.mk (𝟙 _))) := by
  let lam := Dynamic.baseChangeCocharacter (Spec.algebraMap R K) χ ≫ M.genericIso.hom
  have hrep := Dynamic.Affine.isRepresentedBy_parabolicHom lam
  have hχ : SubgroupFunctor.range (Dynamic.Affine.parabolicHom lam ≫ M.genericIso.inv) =
      Dynamic.parabolic (Dynamic.baseChangeCocharacter (Spec.algebraMap R K) χ) :=
    (hrep.comp_iso M.genericIso.symm).2.trans
      (Dynamic.parabolic_eq_comap_of_iso _ M.genericIso).symm
  have h := range_mul_integralPoints_eq_univ_of_cocharacter M hM χ
    (Dynamic.Affine.parabolicHom lam) (Dynamic.Affine.isClosedSubgroup_parabolicHom lam) hχ
  have hset : Set.range (rationalPoints.map (Dynamic.Affine.parabolicHom lam)) =
      ((Dynamic.parabolic lam).carrier (Over.mk (𝟙 _)) : Set (rationalPoints G)) := by
    ext g
    rw [← hrep.2]
    rfl
  rwa [hset] at h

end Dynamic

section Unramified

open IntegralModel Langlands.LocalGalois.Separable GaloisPointComparison

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (M : IntegralModel ↥𝒪[F] F G)

/-- Iwasawa covering after maximal unramified base change: for every cocharacter of the
base-changed model, the generic dynamic parabolic times the original image
`M.baseChangeUnramified.integralPoints` is the whole group of rational points. -/
theorem baseChangeUnramified_hasLeftIntegralCovering_parabolic
    (hG : IsConnectedReductive G)
    (hSpecial : IsConnectedReductive
      ((GroupScheme.baseChange (Spec.algebraMap ↥𝒪[F] 𝓀[F])).obj M.group))
    (χ : (Gm (Spec (CommRingCat.of (fixedFieldIntegers F)))).toGrp ⟶
      M.baseChangeUnramified.group) :
    HasLeftIntegralCovering M.baseChangeUnramified ((Dynamic.parabolic
      (Dynamic.baseChangeCocharacter
        (Spec.algebraMap (fixedFieldIntegers F) (inertiaFixedField F)) χ ≫
          M.baseChangeUnramified.genericIso.hom)).carrier (Over.mk (𝟙 _))) := by
  let : HenselianLocalRing (fixedFieldIntegers F) := fixedFieldIntegersIsHenselian F
  let := (residueToFixedField F).toAlgebra
  let : IsAlgClosure 𝓀[F] (IsLocalRing.ResidueField (fixedFieldIntegers F)) :=
    fixedFieldResidueIsAlgClosure F
  let : IsAlgClosed (IsLocalRing.ResidueField (fixedFieldIntegers F)) :=
    IsAlgClosure.isAlgClosed 𝓀[F]
  let : IsDiscreteValuationRing (fixedFieldIntegers F) :=
    fixedFieldIntegersIsDVR_of_valuesFromBase F (fixedFieldValuesFromBase F)
  have : IsAffineHom (baseChanged F (inertiaFixedField F) G).X.hom := by
    change IsAffineHom
      (CategoryTheory.Limits.pullback.snd G.X.hom (baseMap F (inertiaFixedField F)))
    infer_instance
  have : IsAffine (baseChanged F (inertiaFixedField F) G).X.left :=
    isAffine_of_isAffineHom (baseChanged F (inertiaFixedField F) G).X.hom
  exact hasLeftIntegralCovering_parabolic M.baseChangeUnramified
    (M.isReductive_baseChangeUnramified hG hSpecial) χ

end Unramified

end Langlands.GroupScheme.HenselianParabolicCovering
