import Langlands.Global.AdelicRadicalQuotientProjection
import Langlands.Global.AdelicCuspidalProductVanishing
import Langlands.GroupScheme.Rational.LeviRetraction
import Langlands.GroupScheme.SubgroupFunctor.OpenEquality

/-! # Restriction of nested constant terms to Levi fibres -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

namespace Langlands.Global.StandardParabolicFamily

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
open AdelicSubgroupPoints RepresentationGrowth

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] (fam : StandardParabolicFamily F G)

local notation "S" => Spec (CommRingCat.of F)
local notation "Idx" => StandardIndex F G fam.i fam.ν
local notation "A" => AdelicGroupPoints F G
local notation "pU(" J ")" => (fam.iU J ≫ fam.p J)
local notation "pM(" J ")" => (fam.l J ≫ fam.p J)
local notation "rad(" J ")" => SubgroupFunctor.range (pU(J))
local notation "invSubgroup(" P ")" => parabolicQuotientSubgroup F (fam.p P) (fam.iU P) (fam.l P)

/-- The restriction of a right translate to the actual adelic Levi. -/
def leviFibre (P : Idx) (f : A → ℂ) (g : A) (m : AdelicGroupPoints F (fam.M P)) : ℂ :=
  f (map F (fam.M P) G (pM(P)) m * g)

@[simp]
theorem leviFibre_one (P : Idx) (f : A → ℂ) (g : A) : fam.leviFibre P f g 1 = f g := by
  simp [leviFibre]

theorem continuous_leviFibre (P : Idx) {f : A → ℂ} (hf : Continuous f) (g : A) :
    Continuous (fam.leviFibre P f g) :=
  hf.comp ((map F (fam.M P) G (pM(P))).continuous.mul continuous_const)

theorem isLeftInvariantUnder_leviFibre (P : Idx) {f : A → ℂ}
    (hf : IsLeftInvariantUnder F G (invSubgroup(P)) f) (g : A) :
    IsLeftInvariantUnder F (fam.M P) (AdelicGroupPoints.rationalSubgroup F (fam.M P))
      (fam.leviFibre P f g) := by
  rintro _ ⟨q, rfl⟩ m
  unfold leviFibre
  rw [map_mul, mul_assoc]
  exact hf _ (Subgroup.mem_sup_right ⟨q, rfl⟩) _

/-- Restriction to the Levi with its restricted matrix representation and
translation by a fixed ambient point preserve the moderate-growth bound. -/
theorem hasModerateGrowthFunction_leviFibre {N : ℕ} {rho : MatrixRepresentation G (Fin N)}
    (hN : 0 < N) (P : Idx) {f : A → ℂ} (hf : HasModerateGrowthFunction F G rho f) (g : A) :
    HasModerateGrowthFunction F (fam.M P) (pM(P) ≫ rho) (fam.leviFibre P f g) := by
  apply (hasModerateGrowthFunction_iff_hasHeightGrowth hN _).mpr
  obtain ⟨C, r, hC, hr, hf⟩ := (hasModerateGrowthFunction_iff_hasHeightGrowth hN f).mp hf
  let M := fam.M P
  let leviMap := map F M G (pM(P))
  let H := adelicHeight F G rho
  have hH (x : A) : 0 ≤ H x := zero_le_one.trans (one_le_adelicHeight F G rho hN x)
  have hheight (m : AdelicGroupPoints F M) :
      adelicHeight F M (pM(P) ≫ rho) m = H (leviMap m) := by
    change AdelicMatrixHeight.height F N (GeneralLinearGroupPoints.adelicHomeomorph F N
      (map F M _ (pM(P) ≫ rho) m)) = AdelicMatrixHeight.height F N
        (GeneralLinearGroupPoints.adelicHomeomorph F N (map F G _ rho (leviMap m)))
    rw [map_comp_apply_of_hom]
  refine ⟨C * H g ^ r, r, mul_nonneg hC (Real.rpow_nonneg (hH g) _), hr, fun m => ?_⟩
  rw [hheight]
  calc
    ‖fam.leviFibre P f g m‖ ≤ C * H (leviMap m * g) ^ r := hf _
    _ ≤ C * (H (leviMap m) * H g) ^ r :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (hH _)
        (adelicHeight_mul_le F G rho hN _ _) hr) hC
    _ = C * H g ^ r * H (leviMap m) ^ r := by rw [Real.mul_rpow (hH _) (hH _)]; ring

section Retraction

variable {Q P : StandardIndex F G fam.i fam.ν}
  {V : GroupScheme (Spec (CommRingCat.of F))} (k : V ⟶ fam.M P) [IsClosedImmersion k.hom.hom.left]

omit [NumberField F] in
/-- The image of the smaller parabolic's radical in the larger Levi is its
intersection with that Levi, on every test scheme. -/
private theorem exists_radicalLeviProjection (hQP : Q ≤ P)
    (hk : SubgroupFunctor.range k = (rad(Q)).comap (pM(P))) :
    ∃ π : fam.U Q ⟶ V,
      (∀ X : Over S, Function.Surjective (fun x : X ⟶ (fam.U Q).X => x ≫ π.hom.hom)) ∧
      ∀ (X : Over S) (u : X ⟶ (fam.U Q).X), ∃ n : X ⟶ (fam.U P).X,
        u ≫ (pU(Q)).hom.hom =
          (n ≫ (pU(P)).hom.hom) * (u ≫ (π ≫ k ≫ pM(P)).hom.hom) := by
  let l := fam.l P
  let p := fam.p P
  let : IsClosedImmersion p.hom.hom.left := (fam.isCompatible P).parabolic.isClosedSubgroup
  let : Mono p.hom.hom := Over.mono_of_mono_left _
  let : Mono k.hom.hom := Over.mono_of_mono_left _
  obtain ⟨_, r, hret, hr, -, hl, hker⟩ :=
    (fam.isCompatible P).levi.exists_unipotentRadical_retraction
  let j := SubgroupFunctor.rangeFactor (pU(Q)) p
    ((SubgroupFunctor.range_comp_le _ _).trans ((fam.le_iff_range_le Q P).mp hQP))
  have hj : j ≫ p = pU(Q) := SubgroupFunctor.rangeFactor_comp _ _ _
  have hprod (X : Over S) (u : X ⟶ (fam.U Q).X) : ∃ n : X ⟶ (fam.U P).X,
      u ≫ (pU(Q)).hom.hom = (n ≫ (pU(P)).hom.hom) * (u ≫ ((j ≫ hret) ≫ pM(P)).hom.hom) := by
    let y := u ≫ j.hom.hom
    let m := y ≫ hret.hom.hom
    let z := y * (m ≫ l.hom.hom)⁻¹
    have hm : (m ≫ l.hom.hom) ≫ hret.hom.hom = m := by
      rw [Category.assoc, ← Grp.comp_hom_hom, show l ≫ hret = 𝟙 _ from hl,
        Grp.id_hom_hom, Category.comp_id]
    have hz : z ≫ hret.hom.hom = 1 := by
      rw [show z = y * (m ≫ l.hom.hom)⁻¹ from rfl, MonObj.mul_comp, GrpObj.inv_comp, hm]
      exact mul_inv_cancel m
    have hzmem := (hker X z).mp hz
    rw [hr.1.range_eq (fam.isUnipotentRadical P).1] at hzmem
    obtain ⟨n, hn⟩ := SubgroupFunctor.mem_range.mp hzmem
    refine ⟨n, ?_⟩
    have hy : y = (n ≫ (fam.iU P).hom.hom) * (m ≫ l.hom.hom) := by
      rw [hn]
      dsimp [z]
      group
    have hG := congrArg (fun w : X ⟶ (fam.P P).X => w ≫ p.hom.hom) hy
    simpa only [y, m, l, p, MonObj.mul_comp, Category.assoc, ← Grp.comp_hom_hom, hj] using hG
  have hle : SubgroupFunctor.range (j ≫ hret) ≤ SubgroupFunctor.range k := by
    intro X a ha
    obtain ⟨u, rfl⟩ := SubgroupFunctor.mem_range.mp ha
    rw [hk, SubgroupFunctor.mem_comap]
    obtain ⟨n, hn⟩ := hprod X u
    have hnQ : n ≫ (pU(P)).hom.hom ∈ (rad(Q)).carrier X :=
      fam.radical_le_of_le hQP X (SubgroupFunctor.mem_range.mpr ⟨n, rfl⟩)
    have huQ : u ≫ (pU(Q)).hom.hom ∈ (rad(Q)).carrier X :=
      SubgroupFunctor.mem_range.mpr ⟨u, rfl⟩
    have haQ := ((rad(Q)).carrier X).mul_mem (((rad(Q)).carrier X).inv_mem hnQ) huQ
    rw [hn, inv_mul_cancel_left] at haQ
    simpa only [Grp.comp_hom_hom, Category.assoc] using haQ
  let π := SubgroupFunctor.rangeFactor (j ≫ hret) k hle
  have hπ : π ≫ k = j ≫ hret := SubgroupFunctor.rangeFactor_comp _ _ _
  refine ⟨π, ?_, ?_⟩
  · intro X v
    have hv : v ≫ k.hom.hom ∈ (SubgroupFunctor.range k).carrier X :=
      SubgroupFunctor.mem_range.mpr ⟨v, rfl⟩
    rw [hk, SubgroupFunctor.mem_comap] at hv
    obtain ⟨u, hu⟩ := SubgroupFunctor.mem_range.mp hv
    have huP : u ≫ j.hom.hom = (v ≫ k.hom.hom) ≫ l.hom.hom := by
      apply (cancel_mono p.hom.hom).mp
      simpa only [Category.assoc, ← Grp.comp_hom_hom, hj, l, p] using hu
    refine ⟨u, (cancel_mono k.hom.hom).mp ?_⟩
    rw [Category.assoc, ← Grp.comp_hom_hom, hπ, Grp.comp_hom_hom, ← Category.assoc,
      huP, Category.assoc, ← Grp.comp_hom_hom, hl, Grp.id_hom_hom, Category.comp_id]
  · intro X u
    obtain ⟨n, hn⟩ := hprod X u
    refine ⟨n, ?_⟩
    rw [← Category.assoc π k, hπ]
    exact hn

variable [IsAffine V.X.left]

local notation "M" => fam.M P
local notation "W" => SubgroupFunctor.range k
local notation "QA" => RationalQuotient F G (rad(Q))
local notation "QB" => RationalQuotient F M W
local notation "UA" => adelicPoints F G (rad(Q))
local notation "UB" => adelicPoints F M W
local notation "ΔA" => AdelicSubgroupPoints.rationalSubgroup F G (rad(Q))
local notation "ΔB" => AdelicSubgroupPoints.rationalSubgroup F M W
local notation "μA" => normalizedRationalQuotientHaarMeasure F G (rad(Q))
local notation "μB" => normalizedRationalQuotientHaarMeasure F M W

/-- The ambient `Q` constant term becomes the intrinsic period over the
represented intersection `U_Q ∩ M_P` on the Levi fibre of `P`. -/
theorem subgroupConstantTerm_leviFibre [CompactSpace QB] (hQP : Q ≤ P)
    (hk : W = (rad(Q)).comap (pM(P))) {f : A → ℂ} (hf : Continuous f)
    (hInv : IsLeftInvariantUnder F G (invSubgroup(P)) f)
    (g : A) (m : AdelicGroupPoints F M) :
    subgroupConstantTerm F k (fam.leviFibre P f g) m =
      fam.constantTerm Q f (map F M G (pM(P)) m * g) := by
  let j := pU(Q)
  let mMap := map F M G (pM(P))
  let : IsClosed (UA : Set A) := isClosed_adelicPoints_range F G j
  let : IsClosed (UB : Set (AdelicGroupPoints F M)) := isClosed_adelicPoints_range F M k
  let : CompactSpace QA := fam.compactSpace_radicalRationalQuotient Q
  let : BorelSpace QA := rationalQuotientBorelSpace F G (rad(Q))
  let : BorelSpace QB := rationalQuotientBorelSpace F M W
  obtain ⟨π, hsurj, hprod⟩ := fam.exists_radicalLeviProjection k hQP hk
  have hπ : Function.Surjective (map F (fam.U Q) V π) := hsurj _
  let e := radicalQuotientProjection j k π
  have hmp : MeasurePreserving e μA μB := measurePreserving_radicalQuotientProjection j k π hπ
  let φ : QB → ℂ := LeftCosetSpace.lift ΔB
    (fun v : UB => fam.leviFibre P f g (v.val * m)) (fun r u => by
      change fam.leviFibre P f g ((r.val.val * u.val) * m) = fam.leviFibre P f g (u.val * m)
      rw [mul_assoc]
      exact fam.isLeftInvariantUnder_leviFibre P hInv g _
        (rationalImage_le_rationalSubgroup k ((mem_rationalSubgroup_range_iff k r.val).mp r.2)) _)
  have hφ : Continuous φ := (LeftCosetSpace.continuous_iff ΔB).mpr
    ((fam.continuous_leviFibre P hf g).comp (continuous_subtype_val.mul continuous_const))
  change (∫ q : QB, fam.leviFibre P f g ((Quotient.out q : UB).val * m) ∂μB) =
    ∫ q : QA, f ((Quotient.out q : UA).val * (mMap m * g)) ∂μA
  calc
    _ = ∫ q : QB, φ q ∂μB := integral_congr_ae
      (Filter.Eventually.of_forall (fun q => congrArg φ (Quotient.out_eq q)))
    _ = ∫ q : QA, φ (e q) ∂μA := by
      rw [← hmp.map_eq]
      exact integral_map hmp.measurable.aemeasurable hφ.aestronglyMeasurable
    _ = _ := by
      apply integral_congr_ae
      refine Filter.Eventually.of_forall fun q => ?_
      obtain ⟨u, hu⟩ := adelicRangeMap_surjective F j (Quotient.out q)
      have hq : LeftCosetSpace.mk ΔA (adelicRangeMap F j u) = q := hu ▸ Quotient.out_eq q
      let v := map F (fam.U Q) V π u
      let m' := map F V M k v
      have hφEq : φ (e q) = fam.leviFibre P f g (m' * m) := by
        rw [← hq]
        change φ (radicalQuotientProjection j k π (LeftCosetSpace.mk ΔA (adelicRangeMap F j u))) = _
        rw [radicalQuotientProjection_mk, adelicRangeProjection_apply]
        rfl
      obtain ⟨n, hn⟩ := hprod _ u
      have hn' : (Quotient.out q : UA).val = map F (fam.U P) G (pU(P)) n * mMap m' := by
        rw [← hu]
        change map F _ _ j u = map F _ _ (pU(P)) n * mMap m'
        have h : map F _ _ j u = map F _ _ (pU(P)) n * map F _ _ (π ≫ k ≫ pM(P)) u := hn
        simpa only [map_comp_apply_of_hom, mMap, m', v] using h
      change φ (e q) = f ((Quotient.out q : UA).val * (mMap m * g))
      rw [hφEq, hn']
      change f (mMap (m' * m) * g) = f ((map F _ G (pU(P)) n * mMap m') * (mMap m * g))
      simp only [map_mul, mul_assoc]
      exact (hInv _ (Subgroup.mem_sup_left ⟨n, rfl⟩) _).symm

end Retraction

end Langlands.Global.StandardParabolicFamily
