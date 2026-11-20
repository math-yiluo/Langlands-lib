import Langlands.Geometry.FormalGroup.PolarizedOrderModule
import Langlands.Geometry.FormalGroup.CoefficientCoherence

/-! # Coherence for coefficient changes of actual polarizations -/

noncomputable section

universe u v w

namespace Langlands.FormalGroup.ModuleLaw

open CategoryTheory Opposite _root_.AlgebraicGeometry
open Langlands.GroupScheme Langlands.Shimura Hom.FiniteKernelModel
open scoped CategoryTheory.MonObj CategoryTheory.Obj

variable {O : Type u} [CommRing O]
variable {R S : Type v} [CommRing R] [CommRing S] [Algebra O R] [Algebra O S]
variable {σ τ : Type} [Finite σ] [Finite τ]
variable {M : ModuleLaw O R σ} {N : ModuleLaw O R τ} {π : O}

attribute [local instance] coefficientAlgebra coefficientScalarTower

namespace Hom.FiniteKernelModel

variable {φ : R →ₐ[O] S}
variable {f : Hom M N} {g : Hom (M.map φ) (N.map φ)}
variable (K : FiniteKernelModel f) (L : FiniteKernelModel g)

private def pullbackIsoAlongEq (e : f.map φ = g) :
    L.commGroupScheme ≅ (CommGroupScheme.baseChange (coefficientSpecMap φ)).obj K.commGroupScheme := by
  subst g
  exact K.pullbackIso φ L

private theorem pullbackIsoAlongEq_point (e : f.map φ = g) (T : Over (Spec (CommRingCat.of S)))
    (x : T ⟶ L.commGroupScheme.X) :
    (K.globalPointsEquiv ((Over.map (coefficientSpecMap φ)).obj T)
      (GroupScheme.baseChangePointsEquiv (coefficientSpecMap φ) K.commGroupScheme.toGrp T
        (x ≫ (K.pullbackIsoAlongEq L e).hom.toMul.hom.hom))).toAdd.val =
      (L.globalPointsEquiv T x).toAdd.val := by
  subst g
  change (K.globalPointsEquiv _
    (GroupScheme.baseChangePointsEquiv (coefficientSpecMap φ) K.commGroupScheme.toGrp T
      (x ≫ (K.pullbackIso φ L).hom.toMul.hom.hom))).toAdd.val = _
  erw [K.pullbackIso_hom_points φ L T x]
  let p := (GroupScheme.baseChangePointsEquiv (coefficientSpecMap φ) K.commGroupScheme.toGrp T).trans
    (K.globalPointsEquiv ((Over.map (coefficientSpecMap φ)).obj T))
  unfold pullbackPointsEquiv
  simp only [MulEquiv.trans_apply]
  change (p (p.symm _)).toAdd.val = _
  rw [p.apply_symm_apply]
  rfl

end Hom.FiniteKernelModel

namespace IsPiDivisible

/-- The coefficient point comparison preserves the actual formal coordinates
of a represented torsion point. -/
theorem torsionPointBaseChangeEquiv_globalPoints_val (hM : M.IsPiDivisible π) (φ : R →ₐ[O] S)
    (n : ℕ) (T : Over (Spec (CommRingCat.of S)))
    (x : T ⟶ ((hM.map φ).torsionSchemeInclusions.obj n).X) :
    ((hM.torsionKernelModel n).globalPointsEquiv ((Over.map (coefficientSpecMap φ)).obj T)
      (hM.torsionPointBaseChangeEquiv φ n T x)).toAdd.val =
      (((hM.map φ).torsionKernelModel n).globalPointsEquiv T x).toAdd.val :=
  (hM.torsionKernelModel n).pullbackIsoAlongEq_point ((hM.map φ).torsionKernelModel n)
    (scalarHom_map M (π ^ n) φ) T x

end IsPiDivisible

namespace Hom

variable {hM : M.IsPiDivisible π} {hN : N.IsPiDivisible π}

/-- A map of torsion schemes is the formal map evaluated on the relative global sections. -/
theorem scalarTorsionSchemeMap_globalPoints_val
    (f : Hom M N) (n : ℕ) {T : Over (Spec (CommRingCat.of R))}
    (x : T ⟶ (hM.torsionSchemeInclusions.obj n).X) :
    ((hN.torsionKernelModel n).globalPointsEquiv T
      (x ≫ (f.scalarTorsionSchemeMap hM hN n).toMul.hom.hom)).toAdd.val =
      f.onAlgebraPoints ((hM.torsionKernelModel n).globalPointsEquiv T x).toAdd.val :=
  congrArg (fun y : Multiplicative ((N.scalarHom (π ^ n)).kernelPoints (globalAlgebra T)) =>
    y.toAdd.val) ((hM.torsionKernelModel n).commGroupSchemeMap_globalPoints
      (hN.torsionKernelModel n) (f.scalarTorsionPointNatTrans π n) x)

end Hom

private theorem coefficientSpecMap_comp {B : Type v} [CommRing B] [Algebra O B]
    (φ : R →ₐ[O] S) (ψ : S →ₐ[O] B) :
    coefficientSpecMap (ψ.comp φ) = coefficientSpecMap ψ ≫ coefficientSpecMap φ := by
  change Spec.map (CommRingCat.ofHom (ψ.toRingHom.comp φ.toRingHom)) = _
  rw [CommRingCat.ofHom_comp, Spec.map_comp]

private def changeTest {B : Scheme.{v}} {a b : B ⟶ Spec (CommRingCat.of R)} (e : a = b) :
    Over.mk a ⟶ Over.mk b :=
  Over.homMk (𝟙 B) ((Category.id_comp b).trans e.symm)

private theorem globalPointsEquiv_changeTest_val {B : Scheme.{v}} {a b : B ⟶ Spec (CommRingCat.of R)}
    (e : a = b) {f : Hom M N} (K : f.FiniteKernelModel)
    (x : Over.mk b ⟶ K.commGroupScheme.X) :
    (K.globalPointsEquiv (Over.mk a) (changeTest e ≫ x)).toAdd.val =
      (K.globalPointsEquiv (Over.mk b) x).toAdd.val := by
  subst b
  have h : changeTest (rfl : a = a) = 𝟙 (Over.mk a) := by
    apply Over.OverMorphism.ext
    rfl
  rw [h, Category.id_comp]

private theorem unit_changeTest {B : Scheme.{v}} {a b : B ⟶ Spec (CommRingCat.of R)}
    (e : a = b) (x : Over.mk b ⟶ (Gm (Spec (CommRingCat.of R))).X) :
    Gm.pointsEquiv (Spec (CommRingCat.of R)) (Over.mk a) (changeTest e ≫ x) =
      Gm.pointsEquiv (Spec (CommRingCat.of R)) (Over.mk b) x := by
  subst b
  have h : changeTest (rfl : a = a) = 𝟙 (Over.mk a) := by
    apply Over.OverMorphism.ext
    rfl
  rw [h, Category.id_comp]

private theorem onAlgebraPoints_id_coordinates {N : ModuleLaw O R σ} (f : Hom M N)
    (hf : f.toHom.toCoordinateMap = CoordinateMap.id) (A : CommAlgCat.{v} R)
    (x : M.AlgebraPoint A) : f.onAlgebraPoints x = x := by
  change SeriesPoint.eval (f.toHom.toCoordinateMap.map (algebraMap R A)) x = x
  rw [hf, CoordinateMap.map_id]
  exact SeriesPoint.eval_id x

variable {B : Type v} [CommRing B] [Algebra O B]
variable (φ : R →ₐ[O] S) (ψ : S →ₐ[O] B)

private def compTestMap (T : Over (Spec (CommRingCat.of B))) :
    (Over.map (coefficientSpecMap (ψ.comp φ))).obj T ⟶
      (Over.map (coefficientSpecMap φ)).obj ((Over.map (coefficientSpecMap ψ)).obj T) :=
  changeTest (by
    change T.hom ≫ coefficientSpecMap (ψ.comp φ) =
      (T.hom ≫ coefficientSpecMap ψ) ≫ coefficientSpecMap φ
    rw [coefficientSpecMap_comp, Category.assoc])

variable {hM : M.IsPiDivisible π}

set_option maxHeartbeats 800000 in
private theorem compPointComparison (n : ℕ) (T : Over (Spec (CommRingCat.of B)))
    (x : T ⟶ (((hM.map φ).map ψ).torsionSchemeInclusions.obj n).X) :
    hM.torsionPointBaseChangeEquiv (ψ.comp φ) n T
        (x ≫ ((mapCompIso M φ ψ).hom.scalarTorsionSchemeMap
          ((hM.map φ).map ψ) (hM.map (ψ.comp φ)) n).toMul.hom.hom) =
      compTestMap φ ψ T ≫ hM.torsionPointBaseChangeEquiv φ n
        ((Over.map (coefficientSpecMap ψ)).obj T)
        ((hM.map φ).torsionPointBaseChangeEquiv ψ n T x) := by
  let K := hM.torsionKernelModel n
  let K' := ((hM.map φ).map ψ).torsionKernelModel n
  let T₁ := (Over.map (coefficientSpecMap ψ)).obj T
  let T₂ := (Over.map (coefficientSpecMap φ)).obj T₁
  let T₃ := (Over.map (coefficientSpecMap (ψ.comp φ))).obj T
  let x₁ := (hM.map φ).torsionPointBaseChangeEquiv ψ n T x
  let x₂ := hM.torsionPointBaseChangeEquiv φ n T₁ x₁
  let e := mapCompIso M φ ψ
  let ex := x ≫ (e.hom.scalarTorsionSchemeMap ((hM.map φ).map ψ)
    (hM.map (ψ.comp φ)) n).toMul.hom.hom
  apply (K.globalPointsEquiv T₃).injective
  change K.globalPointsEquiv T₃ (hM.torsionPointBaseChangeEquiv (ψ.comp φ) n T ex) =
    K.globalPointsEquiv T₃ (compTestMap φ ψ T ≫ x₂)
  apply congrArg Multiplicative.ofAdd
  apply Subtype.ext
  have h1 := hM.torsionPointBaseChangeEquiv_globalPoints_val (ψ.comp φ) n T ex
  have h2 := Hom.scalarTorsionSchemeMap_globalPoints_val (hN := hM.map (ψ.comp φ)) e.hom n x
  have h3 := onAlgebraPoints_id_coordinates e.hom rfl (globalAlgebra T)
    (K'.globalPointsEquiv T x).toAdd.val
  have h4 := (hM.map φ).torsionPointBaseChangeEquiv_globalPoints_val ψ n T x
  have h5 := hM.torsionPointBaseChangeEquiv_globalPoints_val φ n T₁ x₁
  have h6 : (K.globalPointsEquiv T₃ (compTestMap φ ψ T ≫ x₂)).toAdd.val =
      (K.globalPointsEquiv T₂ x₂).toAdd.val :=
    globalPointsEquiv_changeTest_val _ K x₂
  exact h1.trans (h2.trans (h3.trans (h4.symm.trans (h5.symm.trans h6.symm))))

set_option maxHeartbeats 800000 in
/-- Two successive coefficient extensions preserve the original polarization
under the canonical composite-coefficient isomorphism. -/
theorem mapCompIso_isometry (polarization : TorsionPrincipalPolarization hM) :
    (mapCompIso M φ ψ).hom.IsTorsionSimilitude
      ((polarization.baseChange φ).baseChange ψ) (polarization.baseChange (ψ.comp φ)) 1 := by
  intro n T x y
  let duality := polarization.toTorsionCartierDuality
  let T₁ := (Over.map (coefficientSpecMap ψ)).obj T
  let T₂ := (Over.map (coefficientSpecMap φ)).obj T₁
  let T₃ := (Over.map (coefficientSpecMap (ψ.comp φ))).obj T
  let x₁ := (hM.map φ).torsionPointBaseChangeEquiv ψ n T x
  let y₁ := (hM.map φ).torsionPointBaseChangeEquiv ψ n T y
  let x₂ := hM.torsionPointBaseChangeEquiv φ n T₁ x₁
  let y₂ := hM.torsionPointBaseChangeEquiv φ n T₁ y₁
  let e := (mapCompIso M φ ψ).hom.scalarTorsionSchemeMap ((hM.map φ).map ψ)
    (hM.map (ψ.comp φ)) n
  rw [scalarHom_one, Hom.scalarTorsionSchemeMap_id]
  change (duality.baseChange (ψ.comp φ)).pairing n (x ≫ e.toMul.hom.hom) (y ≫ e.toMul.hom.hom) =
    ((duality.baseChange φ).baseChange ψ).pairing n (x ≫ 𝟙 _) y
  rw [Category.comp_id]
  apply (Gm.pointsEquiv (Spec (CommRingCat.of B)) T).injective
  have hx := compPointComparison φ ψ (hM := hM) n T x
  have hy := compPointComparison φ ψ (hM := hM) n T y
  have h1 := duality.baseChange_pairing (ψ.comp φ) n T (x ≫ e.toMul.hom.hom) (y ≫ e.toMul.hom.hom)
  have h2 := congrArg₂ (fun u v => Gm.pointsEquiv (Spec (CommRingCat.of R)) T₃ (duality.pairing n u v))
    hx hy
  have h3 := congrArg (Gm.pointsEquiv (Spec (CommRingCat.of R)) T₃)
    (duality.pairing_restrict n (compTestMap φ ψ T) x₂ y₂)
  have h4 : Gm.pointsEquiv (Spec (CommRingCat.of R)) T₃
        (compTestMap φ ψ T ≫ duality.pairing n x₂ y₂) =
      Gm.pointsEquiv (Spec (CommRingCat.of R)) T₂ (duality.pairing n x₂ y₂) :=
    unit_changeTest _ _
  have h5 := duality.baseChange_pairing φ n T₁ x₁ y₁
  have h6 := (duality.baseChange φ).baseChange_pairing ψ n T x y
  exact h1.trans (h2.trans (h3.trans (h4.trans (h5.symm.trans h6.symm))))

private def idTestMap (T : Over (Spec (CommRingCat.of R))) :
    (Over.map (coefficientSpecMap (AlgHom.id O R))).obj T ⟶ T :=
  changeTest (by
    change T.hom ≫ Spec.map (𝟙 (CommRingCat.of R)) = T.hom
    rw [Spec.map_id, Category.comp_id])

set_option maxHeartbeats 800000 in
private theorem idPointComparison (n : ℕ) (T : Over (Spec (CommRingCat.of R)))
    (x : T ⟶ ((hM.map (AlgHom.id O R)).torsionSchemeInclusions.obj n).X) :
    hM.torsionPointBaseChangeEquiv (AlgHom.id O R) n T x =
      idTestMap (O := O) T ≫
        (x ≫ ((mapIdIso M).hom.scalarTorsionSchemeMap (hM.map (AlgHom.id O R)) hM n).toMul.hom.hom) := by
  let K := hM.torsionKernelModel n
  let K' := (hM.map (AlgHom.id O R)).torsionKernelModel n
  let T₀ := (Over.map (coefficientSpecMap (AlgHom.id O R))).obj T
  let e := mapIdIso M
  let ex := x ≫ (e.hom.scalarTorsionSchemeMap (hM.map (AlgHom.id O R)) hM n).toMul.hom.hom
  apply (K.globalPointsEquiv T₀).injective
  change K.globalPointsEquiv T₀ (hM.torsionPointBaseChangeEquiv (AlgHom.id O R) n T x) =
    K.globalPointsEquiv T₀ (idTestMap (O := O) T ≫ ex)
  apply congrArg Multiplicative.ofAdd
  apply Subtype.ext
  have h1 := hM.torsionPointBaseChangeEquiv_globalPoints_val (AlgHom.id O R) n T x
  have h2 := Hom.scalarTorsionSchemeMap_globalPoints_val (hN := hM) e.hom n x
  have h3 := onAlgebraPoints_id_coordinates e.hom rfl (globalAlgebra T)
    (K'.globalPointsEquiv T x).toAdd.val
  have h4 : (K.globalPointsEquiv T₀ (idTestMap (O := O) T ≫ ex)).toAdd.val =
      (K.globalPointsEquiv T ex).toAdd.val :=
    globalPointsEquiv_changeTest_val _ K ex
  exact h1.trans (h3.symm.trans (h2.symm.trans h4.symm))

set_option maxHeartbeats 800000 in
/-- The canonical comparison for identity coefficient extension is an isometry. -/
theorem mapIdIso_isometry (polarization : TorsionPrincipalPolarization hM) :
    (mapIdIso M).hom.IsTorsionSimilitude (polarization.baseChange (AlgHom.id O R)) polarization 1 := by
  intro n T x y
  let duality := polarization.toTorsionCartierDuality
  let T₀ := (Over.map (coefficientSpecMap (AlgHom.id O R))).obj T
  let e := (mapIdIso M).hom.scalarTorsionSchemeMap (hM.map (AlgHom.id O R)) hM n
  let ex := x ≫ e.toMul.hom.hom
  let ey := y ≫ e.toMul.hom.hom
  rw [scalarHom_one, Hom.scalarTorsionSchemeMap_id]
  change duality.pairing n ex ey = (duality.baseChange (AlgHom.id O R)).pairing n (x ≫ 𝟙 _) y
  rw [Category.comp_id]
  apply (Gm.pointsEquiv (Spec (CommRingCat.of R)) T).injective
  have hx := idPointComparison (hM := hM) n T x
  have hy := idPointComparison (hM := hM) n T y
  have h1 := duality.baseChange_pairing (AlgHom.id O R) n T x y
  have h2 := congrArg₂ (fun u v => Gm.pointsEquiv (Spec (CommRingCat.of R)) T₀ (duality.pairing n u v))
    hx hy
  have h3 := congrArg (Gm.pointsEquiv (Spec (CommRingCat.of R)) T₀)
    (duality.pairing_restrict n (idTestMap (O := O) T) ex ey)
  have h4 : Gm.pointsEquiv (Spec (CommRingCat.of R)) T₀
        (idTestMap (O := O) T ≫ duality.pairing n ex ey) =
      Gm.pointsEquiv (Spec (CommRingCat.of R)) T (duality.pairing n ex ey) :=
    unit_changeTest _ _
  exact (h1.trans (h2.trans (h3.trans h4))).symm

private def mapEqIso (φ' ψ' : R →ₐ[O] B) (h : φ' = ψ') : Iso (M.map φ') (M.map ψ') := by
  subst ψ'
  exact Iso.refl _

private theorem mapEqIso_coordinates (φ' ψ' : R →ₐ[O] B) (h : φ' = ψ') :
    (mapEqIso (M := M) φ' ψ' h).hom.toHom.toCoordinateMap = CoordinateMap.id := by
  subst ψ'
  rfl

private theorem mapEqIso_isometry (polarization : TorsionPrincipalPolarization hM)
    (φ' ψ' : R →ₐ[O] B) (h : φ' = ψ') :
    (mapEqIso φ' ψ' h).hom.IsTorsionSimilitude (polarization.baseChange φ') (polarization.baseChange ψ') 1 := by
  subst ψ'
  exact Hom.IsTorsionSimilitude.id _

set_option maxHeartbeats 800000 in
/-- A commuting coefficient square gives an actual polarized isometry. -/
theorem mapSquareIso_isometry (polarization : TorsionPrincipalPolarization hM)
    {C : Type v} [CommRing C] [Algebra O C]
    (φ' : R →ₐ[O] C) (ψ' : C →ₐ[O] B) (h : ψ.comp φ = ψ'.comp φ') :
    (mapSquareIso M φ ψ φ' ψ' h).hom.IsTorsionSimilitude
      ((polarization.baseChange φ).baseChange ψ)
      ((polarization.baseChange φ').baseChange ψ') 1 := by
  let a := mapCompIso M φ ψ
  let b := mapCompIso M φ' ψ'
  let c := mapEqIso (M := M) (ψ.comp φ) (ψ'.comp φ') h
  have he : (mapSquareIso M φ ψ φ' ψ' h).hom = b.inv.comp (c.hom.comp a.hom) := by
    apply Hom.ext
    apply CommLaw.Hom.ext
    change CoordinateMap.id = CoordinateMap.id.comp (c.hom.toHom.toCoordinateMap.comp CoordinateMap.id)
    rw [mapEqIso_coordinates, CoordinateMap.id_comp, CoordinateMap.comp_id]
  rw [he]
  have ha := mapCompIso_isometry φ ψ polarization
  have hb := (mapCompIso_isometry φ' ψ' polarization).inverse_isometry (e := b)
  have hc := mapEqIso_isometry polarization (ψ.comp φ) (ψ'.comp φ') h
  simpa only [one_mul] using hb.comp (hc.comp ha)

namespace PolarizedOrderModule

variable {D : Type w} [Ring D] [Algebra O D] {star : AlgebraInvolution O D}
variable (X : PolarizedOrderModule D star R π)

set_option maxHeartbeats 800000 in
/-- Identity coefficient change preserves the polarized order module. -/
def mapIdIso : Iso (X.map (AlgHom.id O R)) X where
  orderIso := OrderAction.Iso.ofModuleIso (ModuleLaw.mapIdIso X.law)
    (fun a => (ModuleLaw.mapIdIso_natural (X.order.action a)).symm)
  preserves := mapIdIso_isometry X.polarization

set_option maxHeartbeats 800000 in
/-- Coefficient extension composes up to the canonical polarized isometry. -/
def mapCompIso : Iso ((X.map φ).map ψ) (X.map (ψ.comp φ)) where
  orderIso := OrderAction.Iso.ofModuleIso (ModuleLaw.mapCompIso X.law φ ψ)
    (fun a => (ModuleLaw.mapCompIso_natural (X.order.action a) φ ψ).symm)
  preserves := mapCompIso_isometry φ ψ X.polarization

set_option maxHeartbeats 800000 in
/-- The canonical commuting-square comparison also preserves the order and polarization. -/
def mapSquareIso {C : Type v} [CommRing C] [Algebra O C]
    (φ' : R →ₐ[O] C) (ψ' : C →ₐ[O] B) (h : ψ.comp φ = ψ'.comp φ') :
    Iso ((X.map φ).map ψ) ((X.map φ').map ψ') where
  orderIso := OrderAction.Iso.ofModuleIso (ModuleLaw.mapSquareIso X.law φ ψ φ' ψ' h)
    (fun a => (ModuleLaw.mapSquareIso_natural (X.order.action a) φ ψ φ' ψ' h).symm)
  preserves := mapSquareIso_isometry φ ψ X.polarization φ' ψ' h

end PolarizedOrderModule

end Langlands.FormalGroup.ModuleLaw
