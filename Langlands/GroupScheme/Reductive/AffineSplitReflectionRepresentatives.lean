import Langlands.GroupScheme.Reductive.LocalOppositeRootNormalization
import Langlands.GroupScheme.Reductive.GlobalSplitRootParametrization
import Langlands.GroupScheme.Reductive.RankOneRingDualBaseChange
import Langlands.GroupScheme.Reductive.FibrewiseRootDatumBaseChange
import Langlands.GroupScheme.Reductive.BaseChange
import Langlands.GroupScheme.Reductive.LocalSplitRootTransport
import Langlands.GroupScheme.HomScheme.TorusChartConstruction
import Langlands.GroupScheme.Torus.SplitReductiveProof
import Langlands.GroupScheme.SubgroupBaseChange

/-! # Global reflection representatives for split reductive groups over rings -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.GroupScheme

namespace AffineSplitReflection

open LocalSplitCell LocalSplitRootBaseChange

section Descent

variable {R : Type u} [CommRing R]

/-- Two morphisms over `Spec R` from an affine scheme to an affine scheme agree as soon as they
agree on every test coming from a scheme over the localization of `R` at a prime. -/
theorem over_hom_ext_of_localization {Z Y : Over (Spec (CommRingCat.of R))}
    [IsAffine Z.left] [IsAffine Y.left] (f g : Z ⟶ Y)
    (h : ∀ (p : Ideal R) [p.IsPrime]
      (W : Over (Spec (CommRingCat.of (Localization.AtPrime p))))
      (k : (Over.map (algebraBaseMap R (Localization.AtPrime p))).obj W ⟶ Z),
      k ≫ f = k ≫ g) :
    f = g := by
  apply Over.OverMorphism.ext
  let e := Z.left.isoSpec
  rw [← cancel_epi e.inv]
  apply HomScheme.TorusChart.hom_ext_of_localization (C := Γ(Z.left, ⊤))
  intro P hP
  let ψ := Spec.preimage (e.inv ≫ Z.hom)
  have hψ : Spec.map ψ = e.inv ≫ Z.hom := Spec.map_preimage _
  let p : Ideal R := P.comap ψ.hom
  let A := Localization.AtPrime p
  let φ : A →+* Localization.AtPrime P := Localization.localRingHom p P ψ.hom rfl
  let W : Over (Spec (CommRingCat.of A)) := Over.mk (Spec.map (CommRingCat.ofHom φ))
  have hφ : (algebraMap Γ(Z.left, ⊤) (Localization.AtPrime P)).comp ψ.hom =
      φ.comp (algebraMap R A) := by
    ext r
    exact (Localization.localRingHom_to_map p P ψ.hom rfl r).symm
  let k : (Over.map (algebraBaseMap R A)).obj W ⟶ Z :=
    Over.homMk (Spec.map (CommRingCat.ofHom
      (algebraMap Γ(Z.left, ⊤) (Localization.AtPrime P))) ≫ e.inv) (by
      change (Spec.map (CommRingCat.ofHom
        (algebraMap Γ(Z.left, ⊤) (Localization.AtPrime P))) ≫ e.inv) ≫ Z.hom =
          Spec.map (CommRingCat.ofHom φ) ≫ Spec.map (CommRingCat.ofHom (algebraMap R A))
      rw [Category.assoc, ← hψ, ← Spec.map_comp, ← Spec.map_comp]
      congr 1
      change CommRingCat.ofHom ((algebraMap Γ(Z.left, ⊤) (Localization.AtPrime P)).comp
        ψ.hom) = CommRingCat.ofHom (φ.comp (algebraMap R A))
      rw [hφ])
  have hk := congrArg (fun q => q.left) (h p W k)
  simpa [k, Category.assoc] using hk

variable {I : Type u} [Fintype I] [DecidableEq I] {G : GroupScheme (Spec (CommRingCat.of R))}

/-- A Weyl identity holds over `R` once it holds at every test scheme coming from a
localization of `R` at a prime ideal. -/
theorem isWeylPoint_of_localizations [IsAffineHom G.X.hom]
    {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
    {n : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ G.X} {f : (I → ℤ) ≃ₗ[ℤ] (I → ℤ)}
    (h : ∀ (p : Ideal R) [p.IsPrime]
      (W : Over (Spec (CommRingCat.of (Localization.AtPrime p))))
      (t : (Over.map (algebraBaseMap R (Localization.AtPrime p))).obj W ⟶
        (splitTorus (Spec (CommRingCat.of R)) I).X),
      (toUnit _ ≫ n) * (t ≫ i.hom.hom) * (toUnit _ ≫ n)⁻¹ =
        t ≫ (splitTorus.exponentIso _ I f).hom.hom.hom ≫ i.hom.hom) :
    IsWeylPoint i n f := by
  let Y := (splitTorus (Spec (CommRingCat.of R)) I).X
  have : IsAffineHom Y.hom := isAffineHom_splitTorus _ I
  have : IsAffine Y.left := isAffine_of_isAffineHom Y.hom
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have hcomp : ∀ (Z : Over (Spec (CommRingCat.of R))) (t : Z ⟶ Y),
      (toUnit Z ≫ n) * (t ≫ i.hom.hom) * (toUnit Z ≫ n)⁻¹ =
        t ≫ ((toUnit Y ≫ n) * (𝟙 Y ≫ i.hom.hom) * (toUnit Y ≫ n)⁻¹) := by
    intro Z t
    rw [MonObj.comp_mul, MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc,
      comp_toUnit, Category.id_comp]
  have hY : (toUnit Y ≫ n) * (𝟙 Y ≫ i.hom.hom) * (toUnit Y ≫ n)⁻¹ =
      𝟙 Y ≫ (splitTorus.exponentIso _ I f).hom.hom.hom ≫ i.hom.hom := by
    apply over_hom_ext_of_localization
    intro p _ W k
    rw [← hcomp, h p W k, Category.id_comp]
  intro Z t
  rw [hcomp, hY, Category.id_comp]

variable (A : Type u) [CommRing A] [Algebra R A]

/-- A Weyl identity for base-changed root maps gives the original identity at every test
scheme coming from the coefficient ring. -/
theorem weylIdentity_of_baseChange {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
    {u v : Ga R ⟶ G} {f : (I → ℤ) ≃ₗ[ℤ] (I → ℤ)}
    (h : IsWeylPoint (splitTorus.baseChangeHom (K := A) G I i)
      (weylPoint (baseChangeRoot A u) (baseChangeRoot A v)) f)
    (W : Over (Spec (CommRingCat.of A)))
    (t : (Over.map (algebraBaseMap R A)).obj W ⟶ (splitTorus (Spec (CommRingCat.of R)) I).X) :
    (toUnit _ ≫ weylPoint u v) * (t ≫ i.hom.hom) * (toUnit _ ≫ weylPoint u v)⁻¹ =
      t ≫ (splitTorus.exponentIso _ I f).hom.hom.hom ≫ i.hom.hom := by
  let E := GroupScheme.baseChangePointsEquiv (algebraBaseMap R A) G W
  let ET := GroupScheme.baseChangePointsEquiv (algebraBaseMap R A) (splitTorus _ I) W
  let W' := (Over.map (algebraBaseMap R A)).obj W
  obtain ⟨tA, htA⟩ : ∃ tA : W ⟶ (splitTorus (Spec (CommRingCat.of A)) I).X,
      ET (tA ≫ (splitTorus.baseChangeIso (algebraBaseMap R A) I).inv.hom.hom) = t := by
    refine ⟨ET.symm t ≫ (splitTorus.baseChangeIso (algebraBaseMap R A) I).hom.hom.hom, ?_⟩
    rw [Category.assoc, ← Grp.comp_hom_hom, Iso.hom_inv_id,
      Grp.id_hom_hom, Category.comp_id]
    exact ET.apply_symm_apply _
  have hN : E (toUnit W ≫ weylPoint (baseChangeRoot A u) (baseChangeRoot A v)) =
      toUnit W' ≫ weylPoint u v := by
    rw [toUnit_comp_eq_constantPoint, constantPoint_weylPoint, map_mul, map_mul,
      baseChangePointsEquiv_rootPoint, baseChangePointsEquiv_rootPoint,
      toUnit_comp_eq_constantPoint, constantPoint_weylPoint]
  have hexp : (splitTorus.exponentIso (Spec (CommRingCat.of A)) I f).hom ≫
      (splitTorus.baseChangeIso (algebraBaseMap R A) I).inv =
        (splitTorus.baseChangeIso (algebraBaseMap R A) I).inv ≫
          (GroupScheme.baseChange (algebraBaseMap R A)).map
            (splitTorus.exponentIso (Spec (CommRingCat.of R)) I f).hom := by
    rw [Iso.eq_inv_comp, ← Category.assoc,
      splitTorus.exponentIso_baseChange (Spec (CommRingCat.of R)) I (algebraBaseMap R A) f,
      Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have ht : ET ((tA ≫ (splitTorus.exponentIso _ I f).hom.hom.hom) ≫
      (splitTorus.baseChangeIso (algebraBaseMap R A) I).inv.hom.hom) =
        ET (tA ≫ (splitTorus.baseChangeIso (algebraBaseMap R A) I).inv.hom.hom) ≫
          (splitTorus.exponentIso (Spec (CommRingCat.of R)) I f).hom.hom.hom := by
    rw [← GroupScheme.baseChangePointsEquiv_comp, Category.assoc, Category.assoc,
      ← Grp.comp_hom_hom, ← Grp.comp_hom_hom, hexp]
  have hW := congrArg E (h W tA)
  rw [map_mul, map_mul, map_inv, hN, baseChangePointsEquiv_torus, ← Category.assoc,
    baseChangePointsEquiv_torus, ht, htA] at hW
  rw [hW, Category.assoc]

end Descent

section DualTransport

open Corepresented.RingCoordinates LocalWeylNormalization

variable {R : Type u} [CommRing R] {I : Type u} [Fintype I]
  {G : GroupScheme (Spec (CommRingCat.of R))}
  (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G) (xm xp : Ga R ⟶ G)
  (A : Type u) [CommRing A] [Algebra R A]

set_option maxHeartbeats 800000 in
/-- An ambient dual-number factorization of `xp(1) xm(ε)` transports to any coefficient
ring, with the extended negative and positive scalar coordinates. -/
theorem dualFactorization_baseChange
    {y : Γ((dualOver R).left, ⊤)}
    {t : dualOver R ⟶ (splitTorus (Spec (CommRingCat.of R)) I).X}
    {x : Γ((dualOver R).left, ⊤)}
    (hx : rootPoint xp (dualOver R) 1 * rootPoint xm (dualOver R) (epsSec R) =
      rootPoint xm (dualOver R) y * ((t ≫ i.hom.hom) * rootPoint xp (dualOver R) x)) :
    ∃ tA : dualOver A ⟶ (splitTorus (Spec (CommRingCat.of A)) I).X,
      rootPoint (baseChangeRoot A xp) (dualOver A) 1 *
          rootPoint (baseChangeRoot A xm) (dualOver A) (epsSec A) =
        rootPoint (baseChangeRoot A xm) (dualOver A)
            ((specMapOver (R := CommRingCat.of R)
              (RingRootCell.DualCell.coefficientMap (R := R) A)).left.appTop y) *
          ((tA ≫ (splitTorus.baseChangeHom (K := A) G I i).hom.hom) *
            rootPoint (baseChangeRoot A xp) (dualOver A)
              ((specMapOver (R := CommRingCat.of R)
                (RingRootCell.DualCell.coefficientMap (R := R) A)).left.appTop x)) := by
  let b := algebraBaseMap R A
  let ψ := specMapOver (R := CommRingCat.of R) (RingRootCell.DualCell.coefficientMap (R := R) A)
  let f := testOverHom (CommRingCat.of R) A (DualNumber A)
  let g := testOverInv (CommRingCat.of R) A (DualNumber A)
  let ET := GroupScheme.baseChangePointsEquiv b (splitTorus _ I) (dualOver A)
  let t₀ := ET.symm (g ≫ ψ ≫ t)
  let tA := t₀ ≫ (splitTorus.baseChangeIso b I).hom.hom.hom
  have hf_inj : Function.Injective
      (fun z : (Over.map b).obj (dualOver A) ⟶ G.X => f ≫ z) := by
    intro v w h
    have h' := congrArg (fun z => g ≫ z) h
    simpa only [f, g, ← Category.assoc, testOverInv_comp_testOverHom,
      Category.id_comp] using h'
  have ht : ET (tA ≫ (splitTorus.baseChangeIso b I).inv.hom.hom) =
      g ≫ ψ ≫ t := by
    dsimp only [tA]
    rw [Category.assoc, ← Grp.comp_hom_hom, Iso.hom_inv_id,
      Grp.id_hom_hom, Category.comp_id]
    exact ET.apply_symm_apply _
  refine ⟨tA, ?_⟩
  apply (GroupScheme.baseChangePointsEquiv b G (dualOver A)).injective
  apply hf_inj
  dsimp only
  rw [map_mul, MonObj.comp_mul,
    RingRootCell.DualCell.testOverHom_rootPoint,
    RingRootCell.DualCell.testOverHom_rootPoint,
    map_mul, map_mul, baseChangePointsEquiv_rootPoint, baseChangePointsEquiv_rootPoint,
    baseChangePointsEquiv_torus, MonObj.comp_mul, MonObj.comp_mul,
    comp_rootPoint, comp_rootPoint,
    RingRootCell.DualCell.testOverHom_appTop,
    RingRootCell.DualCell.testOverHom_appTop, ← Category.assoc]
  change _ = rootPoint xm (specOver (CommRingCat.of R) (DualNumber A)) (ψ.left.appTop y) *
    ((f ≫ ET (tA ≫ (splitTorus.baseChangeIso b I).inv.hom.hom) ≫ i.hom.hom) *
      rootPoint xp (specOver (CommRingCat.of R) (DualNumber A)) (ψ.left.appTop x))
  rw [ht]
  simp only [← Category.assoc, f, g,
    testOverHom_comp_testOverInv, Category.id_comp]
  have heps : ψ.left.appTop (epsSec R) = epsSec A :=
    RingRootCell.DualCell.coefficientMap_appTop_eps A
  have h := congrArg (fun z => ψ ≫ z) hx
  simp only [MonObj.comp_mul, comp_rootPoint, map_one, heps] at h
  simpa only [Category.assoc] using h

end DualTransport

section LocalScalar

open OppositePower Corepresented.RingCoordinates LocalWeylNormalization

variable {A : Type u} [CommRing A] {I : Type u} [Fintype I]
  {G : GroupScheme (Spec (CommRingCat.of A))}

/-- If `d` normalizes the negative root so that the coroot Gauss relation and positive
separation hold, then the positive coordinate of any ambient dual-number factorization of
`xp(1) xm(ε)` has `ε`-coefficient `-d⁻¹`. -/
theorem snd_dual_of_gauss {i : splitTorus (Spec (CommRingCat.of A)) I ⟶ G} {nu : I → ℤ}
    {xp xm : Ga A ⟶ G} (d : Aˣ)
    (hg : HasCorootGaussRelation i nu xp (scaleHom (d : A) ≫ xm))
    (hs : SeparatesPositive (U := splitTorus.commGroupScheme _ I) i xp
      (scaleHom (d : A) ≫ xm))
    {y : Γ((dualOver A).left, ⊤)}
    {t : dualOver A ⟶ (splitTorus (Spec (CommRingCat.of A)) I).X}
    {x : Γ((dualOver A).left, ⊤)}
    (hx : rootPoint xp (dualOver A) 1 * rootPoint xm (dualOver A) (epsSec A) =
      rootPoint xm (dualOver A) y * ((t ≫ i.hom.hom) * rootPoint xp (dualOver A) x)) :
    ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber A))).hom x).snd = -(↑d⁻¹ : A) := by
  let gam := (Scheme.ΓSpecIso (CommRingCat.of (DualNumber A))).inv
  let w : Γ((dualOver A).left, ⊤) := gam (TrivSqZeroExt.inr (↑d⁻¹ : A))
  let u₀ := RingRootCell.DualCell.unit (↑d⁻¹ : A)
  let U : Γ((dualOver A).left, ⊤)ˣ := Units.map gam.hom.toMonoidHom u₀
  have hu : (U : Γ((dualOver A).left, ⊤)) = 1 + (1 : Γ((dualOver A).left, ⊤)) * w := by
    change gam (1 + TrivSqZeroExt.inr (↑d⁻¹ : A)) = _
    simp only [map_add, map_one, one_mul, w]
  have hbd : ∀ c : A, baseScalar (dualOver A) c = gam (algebraMap A (DualNumber A) c) :=
    fun c => by
      change (Spec.map (CommRingCat.ofHom (algebraMap A (DualNumber A)))).appTop
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv c) = _
      exact specMap_appTop_inv _ _
  have heps : baseScalar (dualOver A) (d : A) * w = epsSec A := by
    rw [hbd]
    change gam (algebraMap A (DualNumber A) (d : A)) * gam (TrivSqZeroExt.inr (↑d⁻¹ : A)) =
      gam DualNumber.eps
    rw [← map_mul, TrivSqZeroExt.algebraMap_eq_inl,
      TrivSqZeroExt.inl_mul_inr, smul_eq_mul, Units.mul_inv]
    rfl
  have hy : rootPoint xm (dualOver A) y = rootPoint (scaleHom (d : A) ≫ xm) (dualOver A)
      (baseScalar (dualOver A) (↑d⁻¹ : A) * y) := by
    rw [rootPoint_scaleHom, ← mul_assoc, ← map_mul, Units.mul_inv, map_one, one_mul]
  have hr := hg (dualOver A) 1 w U hu
  rw [rootPoint_scaleHom (d : A) xm (dualOver A) w, heps, mul_one] at hr
  have h2 : rootPoint (scaleHom (d : A) ≫ xm) (dualOver A)
        (baseScalar (dualOver A) (↑d⁻¹ : A) * y) *
        ((t ≫ i.hom.hom) * rootPoint xp (dualOver A) x) =
      rootPoint (scaleHom (d : A) ≫ xm) (dualOver A) ((↑U⁻¹ : Γ((dualOver A).left, ⊤)) * w) *
        ((cocharPoint nu (dualOver A) U ≫ i.hom.hom) *
          rootPoint xp (dualOver A) (↑U⁻¹ : Γ((dualOver A).left, ⊤))) := by
    rw [← hy, ← hx, hr]
  have hp := hs (dualOver A) _ _ _ _ _ _ h2
  have hp' := congrArg (Scheme.ΓSpecIso (CommRingCat.of (DualNumber A))).hom hp
  change _ = (Scheme.ΓSpecIso (CommRingCat.of (DualNumber A))).hom
    (gam (↑u₀⁻¹ : DualNumber A)) at hp'
  rw [Iso.inv_hom_id_apply] at hp'
  rw [hp']
  change (1 - TrivSqZeroExt.inr (↑d⁻¹ : A) : DualNumber A).snd = _
  simp

variable [IsLocalRing A] [DecidableEq I] [IsAffineHom G.X.hom]

/-- Over a local ring, an ambient dual-number factorization determines a unit `d` whose
rescaling of the negative root realizes the root reflection, with `ε`-coefficient `-d⁻¹`. -/
theorem exists_weylUnit_of_dualFactorization (hG : IsReductive G)
    (i : splitTorus (Spec (CommRingCat.of A)) I ⟶ G) (hi : IsClosedSubgroup i)
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
    {J : Type u} {P : RootDatum J (I → ℤ) (I → ℤ)}
    (hP : IsFibrewiseRootDatumOf I G i P) (a : J) {xp xm : Ga A ⟶ G}
    (hp : IsRootParametrization i (P.root a) xp)
    (hm : IsRootParametrization i (-P.root a) xm)
    {y : Γ((dualOver A).left, ⊤)}
    {t : dualOver A ⟶ (splitTorus (Spec (CommRingCat.of A)) I).X}
    {x : Γ((dualOver A).left, ⊤)}
    (hx : rootPoint xp (dualOver A) 1 * rootPoint xm (dualOver A) (epsSec A) =
      rootPoint xm (dualOver A) y * ((t ≫ i.hom.hom) * rootPoint xp (dualOver A) x)) :
    ∃ d : Aˣ, IsWeylPoint i (weylPoint xp (scaleHom (d : A) ≫ xm)) (P.reflection a) ∧
      ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber A))).hom x).snd = -(↑d⁻¹ : A) := by
  obtain ⟨d, hg, hs, hw⟩ := exists_unit_oppositeNormalization hG i hi hmax hP a hp hm
  exact ⟨d, hw, snd_dual_of_gauss d hg hs hx⟩

end LocalScalar

section Global

open Corepresented.RingCoordinates LocalWeylNormalization

variable {R : Type u} [CommRing R] {I : Type u} [Fintype I] [DecidableEq I]
  {G : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom G.X.hom]

set_option maxHeartbeats 800000 in
/-- An ambient dual-number factorization of `xp(1) xm(ε)` over an arbitrary ring yields a
global unit rescaling of the negative root whose Weyl product realizes the root reflection:
the scalar is a unit at every localization at a prime, and the reflection identity descends. -/
theorem exists_isWeylPoint_of_dualFactorization (hG : IsReductive G)
    (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G) (hi : IsClosedSubgroup i)
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
    {J : Type u} {P : RootDatum J (I → ℤ) (I → ℤ)}
    (hP : IsFibrewiseRootDatumOf I G i P) (a : J) {xp xm : Ga R ⟶ G}
    (hp : IsRootParametrization i (P.root a) xp)
    (hm : IsRootParametrization i (-P.root a) xm)
    {y : Γ((dualOver R).left, ⊤)}
    {t : dualOver R ⟶ (splitTorus (Spec (CommRingCat.of R)) I).X}
    {x : Γ((dualOver R).left, ⊤)}
    (hx : rootPoint xp (dualOver R) 1 * rootPoint xm (dualOver R) (epsSec R) =
      rootPoint xm (dualOver R) y * ((t ≫ i.hom.hom) * rootPoint xp (dualOver R) x)) :
    ∃ c : Rˣ, IsWeylPoint i (weylPoint xp (scaleHom (c : R) ≫ xm)) (P.reflection a) := by
  have key : ∀ (p : Ideal R) [p.IsPrime], ∃ d : (Localization.AtPrime p)ˣ,
      IsWeylPoint (splitTorus.baseChangeHom (K := Localization.AtPrime p) G I i)
        (weylPoint (baseChangeRoot (Localization.AtPrime p) xp)
          (scaleHom (d : Localization.AtPrime p) ≫
            baseChangeRoot (Localization.AtPrime p) xm)) (P.reflection a) ∧
      algebraMap R (Localization.AtPrime p) (RingRootCell.DualCell.normalizationScalar x) =
        (↑d⁻¹ : Localization.AtPrime p) := by
    intro p _
    let A := Localization.AtPrime p
    have : Smooth G.X.hom := hG.smooth
    have : IsAffineHom ((GroupScheme.baseChange (algebraBaseMap R A)).obj G).X.hom :=
      inferInstanceAs (IsAffineHom (Limits.pullback.snd G.X.hom (algebraBaseMap R A)))
    have hiA : IsClosedSubgroup (splitTorus.baseChangeHom (K := A) G I i) :=
      IsClosedSubgroup.iso_comp (splitTorus.baseChangeIso (algebraBaseMap R A) I).symm
        (hi.baseChange (algebraBaseMap R A))
    have hmaxA : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I)
        (splitTorus.baseChangeHom (K := A) G I i) :=
      splitTorus.isFibrewiseMaximalTorus_baseChangeHom I G i hmax
    obtain ⟨tA, hxA⟩ := dualFactorization_baseChange i xm xp A hx
    obtain ⟨d, hw, hsnd⟩ := exists_weylUnit_of_dualFactorization
      (hG.baseChange (algebraBaseMap R A)) (splitTorus.baseChangeHom (K := A) G I i) hiA hmaxA
      (hP.baseChange_implicit (A := A)) a
      (isRootParametrization_baseChangeRoot A i (P.root a) xp hp)
      (isRootParametrization_baseChangeRoot A i (-P.root a) xm hm) hxA
    refine ⟨d, hw, ?_⟩
    change ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber A))).hom
      ((Spec.map (CommRingCat.ofHom
        (RingRootCell.DualCell.coefficientMap (R := R) A).toRingHom)).appTop x)).snd = _ at hsnd
    rw [ΓSpecIso_hom_specMap_appTop] at hsnd
    change (RingRootCell.DualCell.coefficientMap A
      ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).hom x)).snd = _ at hsnd
    rw [RingRootCell.DualCell.snd_coefficientMap] at hsnd
    unfold RingRootCell.DualCell.normalizationScalar
    rw [map_neg, hsnd, neg_neg]
  have hunit : IsUnit (RingRootCell.DualCell.normalizationScalar x) := by
    by_contra hn
    obtain ⟨M, hM, hsM⟩ := exists_max_ideal_of_mem_nonunits hn
    have := hM.isPrime
    obtain ⟨d, -, hd⟩ := key M
    have hu : IsUnit (algebraMap R (Localization.AtPrime M)
        (RingRootCell.DualCell.normalizationScalar x)) := by
      rw [hd]
      exact Units.isUnit _
    rw [IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime M) M] at hu
    exact hu hsM
  refine ⟨hunit.unit⁻¹, isWeylPoint_of_localizations ?_⟩
  intro p _ W t'
  obtain ⟨d, hw, hd⟩ := key p
  have hc : algebraMap R (Localization.AtPrime p) ((hunit.unit⁻¹ : Rˣ) : R) = d := by
    have h1 : algebraMap R (Localization.AtPrime p) (RingRootCell.DualCell.normalizationScalar x) *
        algebraMap R (Localization.AtPrime p) ((hunit.unit⁻¹ : Rˣ) : R) = 1 := by
      rw [← map_mul, IsUnit.mul_val_inv, map_one]
    rw [hd] at h1
    calc algebraMap R (Localization.AtPrime p) ((hunit.unit⁻¹ : Rˣ) : R)
        = (d : Localization.AtPrime p) * ((↑d⁻¹ : Localization.AtPrime p) *
          algebraMap R (Localization.AtPrime p) ((hunit.unit⁻¹ : Rˣ) : R)) := by
          rw [← mul_assoc, Units.mul_inv, one_mul]
      _ = d := by rw [h1, mul_one]
  apply weylIdentity_of_baseChange (Localization.AtPrime p) ?_ W t'
  rw [LocalSplitRootBaseChange.baseChangeRoot_scaleHom, hc]
  exact hw

end Global

section GlobalCell

open Corepresented.RingCoordinates LocalWeylNormalization splitTorus.RelativeCocharacterCentralizer

variable {R : Type u} [CommRing R] {I : Type u} [Fintype I]
  {G : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom G.X.hom]

/-- Over an arbitrary ring, `xp(1) xm(ε)` factors through the ambient opposite-root cell:
it lies in the open rank-one cell of the relative cocharacter centralizer of the root. -/
theorem exists_dualFactorization (hG : IsReductive G)
    (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
    {J : Type u} {P : RootDatum J (I → ℤ) (I → ℤ)}
    (hP : IsFibrewiseRootDatumOf I G i P) (a : J) {xp xm : Ga R ⟶ G}
    (hp : IsRootParametrization i (P.root a) xp)
    (hm : IsRootParametrization i (-P.root a) xm) :
    ∃ (y : Γ((dualOver R).left, ⊤))
      (t : dualOver R ⟶ (splitTorus (Spec (CommRingCat.of R)) I).X)
      (x : Γ((dualOver R).left, ⊤)),
      rootPoint xp (dualOver R) 1 * rootPoint xm (dualOver R) (epsSec R) =
        rootPoint xm (dualOver R) y * ((t ≫ i.hom.hom) * rootPoint xp (dualOver R) x) := by
  classical
  have : Finite J := hP.finite
  have := hP.isReduced
  obtain ⟨mu, ha, hmu⟩ := LocalRootGroup.exists_kernel_exponent P (ULift.{u} ℚ) a
  have hex : ∃ j : I, P.root a j ≠ 0 := by
    by_contra! h
    apply P.ne_zero a
    ext j
    exact h j
  obtain ⟨j, hj⟩ := hex
  have hpos : 0 < ∑ k, P.root a k * P.root a k := by
    have hle := Finset.single_le_sum
      (fun k (_ : k ∈ (Finset.univ : Finset I)) => mul_self_nonneg (P.root a k))
      (Finset.mem_univ j)
    exact lt_of_lt_of_le (mul_self_pos.mpr hj) hle
  let D := splitTorus.RelativeCocharacterCentralizer.cellData i mu hG hmax hP a ha hmu
    (P.root a) hpos hp hm
  obtain ⟨y, t, x, hx⟩ := D.exists_dualFactorization
  refine ⟨y, t, x, ?_⟩
  have h := congrArg (fun g => g ≫ (inclusion I G i mu).hom.hom) hx
  change (rootPoint (rootLift i mu hp ha) (dualOver R) 1 *
      rootPoint (rootLift i mu hm (by
        simpa only [Pi.neg_apply, neg_mul, Finset.sum_neg_distrib, neg_zero] using
          congrArg Neg.neg ha)) (dualOver R) (epsSec R)) ≫ (inclusion I G i mu).hom.hom =
    (rootPoint (rootLift i mu hm (by
        simpa only [Pi.neg_apply, neg_mul, Finset.sum_neg_distrib, neg_zero] using
          congrArg Neg.neg ha)) (dualOver R) y *
      ((t ≫ (splitTorus.RelativeCocharacterCentralizer.torusHom I G i mu).hom.hom) *
        rootPoint (rootLift i mu hp ha) (dualOver R) x)) ≫ (inclusion I G i mu).hom.hom at h
  simp only [MonObj.mul_comp, ← rootPoint_comp, Category.assoc, ← Grp.comp_hom_hom] at h
  rwa [rootLift_comp, rootLift_comp, torusHom_comp] at h

end GlobalCell

section Clause1

variable {R : Type u} [CommRing R] {I : Type u} [Fintype I]

/-- An exponent automorphism of the split torus pulls back characters by its exponent map. -/
theorem prod_pointsEquiv_exponentCommIso [DecidableEq I] (f : (I → ℤ) ≃ₗ[ℤ] (I → ℤ))
    (U : Over (Spec (CommRingCat.of R)))
    (x : U ⟶ (splitTorus (Spec (CommRingCat.of R)) I).X) (m : I → ℤ) :
    ∏ j, splitTorus.pointsEquiv I U
        (x ≫ (CommGroupScheme.groupHom (splitTorus.exponentCommIso _ I f).hom).hom.hom) j ^
          m j =
      ∏ j, splitTorus.pointsEquiv I U x j ^ (f m) j := by
  rw [← splitTorus.pointsEquiv_exponentCharacter, ← splitTorus.pointsEquiv_exponentCharacter,
    Category.assoc, ← Grp.comp_hom_hom]
  change Gm.pointsEquiv _ U (x ≫ (CommGroupScheme.groupHom
    (splitTorus.exponentHom _ I I f.toLinearMap ≫ splitTorus.exponentCharacter _ I m)).hom.hom) = _
  rw [splitTorus.exponentHom_comp_exponentCharacter]
  rfl

variable {G : GroupScheme (Spec (CommRingCat.of R))} {J : Type u}
  (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G) (P : RootDatum J (I → ℤ) (I → ℤ))

/-- The point `n` induces the root-datum automorphism `w`: conjugation by `n` restricts to the
torus automorphism whose pullback on characters is `w`. -/
def Induces (n : Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶ G.X) (w : RootPairing.Aut P) : Prop :=
  ∃ σ : splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I ≅
      splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I,
    IsNormalizingPoint (T := splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I) i n σ ∧
      ∀ (U : Over (Spec (CommRingCat.of R)))
        (x : U ⟶ (splitTorus (Spec (CommRingCat.of R)) I).X) (m : I → ℤ),
        ∏ j, splitTorus.pointsEquiv I U
            (x ≫ (CommGroupScheme.groupHom σ.hom).hom.hom) j ^ m j =
          ∏ j, splitTorus.pointsEquiv I U x j ^ (w • m) j

theorem induces_one : Induces i P 1 1 :=
  ⟨Iso.refl _, IsNormalizingPoint.one, fun U x m => by
    change ∏ j, splitTorus.pointsEquiv I U (x ≫ 𝟙 _) j ^ m j = _
    rw [Category.comp_id]
    rfl⟩

/-- If `n` induces `w` and `n'` induces `w'`, then `n' n` induces `w w'`. -/
theorem Induces.mul {n n' : Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶ G.X}
    {w w' : RootPairing.Aut P} (h : Induces i P n w) (h' : Induces i P n' w') :
    Induces i P (n' * n) (w * w') := by
  obtain ⟨σ, hσ, hw⟩ := h
  obtain ⟨σ', hσ', hw'⟩ := h'
  refine ⟨σ ≪≫ σ', hσ'.mul hσ, fun U x m => ?_⟩
  change ∏ j, splitTorus.pointsEquiv I U
      ((x ≫ (CommGroupScheme.groupHom σ.hom).hom.hom) ≫
        (CommGroupScheme.groupHom σ'.hom).hom.hom) j ^ m j = _
  rw [hw', hw, mul_smul]

/-- Every element of the Weyl group is induced by a point once every reflection is. -/
theorem forall_weylGroup_induces
    (h : ∀ a : J, ∃ n : Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶ G.X,
      Induces i P n (RootPairing.Equiv.reflection P a))
    (w : RootPairing.Aut P) (hw : w ∈ P.weylGroup) :
    ∃ n : Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶ G.X, Induces i P n w := by
  induction hw using RootPairing.weylGroup.induction with
  | mem a => exact h a
  | one => exact ⟨1, induces_one i P⟩
  | mul x y _ _ hx hy =>
    obtain ⟨n, hn⟩ := hx
    obtain ⟨n', hn'⟩ := hy
    exact ⟨n' * n, hn.mul i P hn'⟩

end Clause1

section Final

open LocalSplitCell

variable {R : Type u} [CommRing R] {I : Type u} [Fintype I] [DecidableEq I]
  {G : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom G.X.hom] {J : Type u}

/-- Every root reflection is induced by a point of `G`: a suitable unit rescaling of the
negative root map makes the Weyl product of the global opposite root maps realize it. -/
theorem exists_induces_reflection (hG : IsReductive G)
    (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G) (hi : IsClosedSubgroup i)
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
    {P : RootDatum J (I → ℤ) (I → ℤ)} (hP : IsFibrewiseRootDatumOf I G i P)
    (hfree : ∀ α : J, Nonempty
      (splitTorus.exponentWeightSpace I G i (P.root α) ≃ₗ[CommRingCat.of R] CommRingCat.of R))
    (a : J) :
    ∃ n : Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶ G.X,
      Induces i P n (RootPairing.Equiv.reflection P a) := by
  let xs := LocalRootGroup.rootParametrizationsOfFreeWeights i hG hmax hP hfree
  have hxs := LocalRootGroup.isRootParametrization_rootParametrizationsOfFreeWeights
    i hG hmax hP hfree
  have hneg : P.root (P.reflectionPerm a a) = -P.root a := by
    rw [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_self]
  have hp : IsRootParametrization i (P.root a) (xs a) := hxs a
  have hm : IsRootParametrization i (-P.root a) (xs (P.reflectionPerm a a)) := by
    rw [← hneg]
    exact hxs _
  obtain ⟨y, t, x, hx⟩ := exists_dualFactorization hG i hmax hP a hp hm
  obtain ⟨c, hc⟩ := exists_isWeylPoint_of_dualFactorization hG i hi hmax hP a hp hm hx
  refine ⟨weylPoint (xs a) (scaleHom (c : R) ≫ xs (P.reflectionPerm a a)),
    splitTorus.exponentCommIso _ I (P.reflection a), hc.isNormalizingPoint, fun U z m => ?_⟩
  rw [prod_pointsEquiv_exponentCommIso]
  rfl

end Final

/-- **Clause 1 of Conrad, Example 6.4.3.** For a split reductive group over an arbitrary ring
with a closed fibrewise maximal split torus, a fibrewise root datum and free root spaces,
every element of the Weyl group is induced by a point of `G` normalizing the torus. -/
theorem weylGroup_induced (R : Type u) [CommRing R]
    (G : GroupScheme (Spec (CommRingCat.of R))) (hG : IsReductive G)
    (I : Type u) [Fintype I] (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
    (J : Type u) (P : RootDatum J (I → ℤ) (I → ℤ)) :
    haveI := hG.isAffineHom
    IsClosedSubgroup i →
    IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I) i →
    IsFibrewiseRootDatumOf I G i P →
    (∀ α : J, Nonempty
      (splitTorus.exponentWeightSpace I G i (P.root α) ≃ₗ[CommRingCat.of R] CommRingCat.of R)) →
    ∀ w ∈ P.weylGroup, ∃ n : Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶ G.X,
      ∃ σ : splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I ≅
          splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I,
        IsNormalizingPoint (T := splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I) i n σ ∧
          ∀ (U : Over (Spec (CommRingCat.of R)))
            (x : U ⟶ (splitTorus (Spec (CommRingCat.of R)) I).X) (m : I → ℤ),
            ∏ j, splitTorus.pointsEquiv I U
                (x ≫ (CommGroupScheme.groupHom σ.hom).hom.hom) j ^ m j =
              ∏ j, splitTorus.pointsEquiv I U x j ^ (w • m) j := by
  have := hG.isAffineHom
  intro hi hmax hP hfree w hw
  classical
  exact forall_weylGroup_induces i P
    (fun a => exists_induces_reflection hG i hi hmax hP hfree a) w hw

end AffineSplitReflection

end Langlands.GroupScheme
