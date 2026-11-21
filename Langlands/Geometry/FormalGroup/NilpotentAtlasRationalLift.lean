import Langlands.Geometry.FormalGroup.NilpotentAtlasRationalHom

/-! # Lifting rational atlas maps across nilpotent reduction -/

noncomputable section

universe u v w z

namespace Langlands.FormalGroup.ModuleLaw.BasicAtlas

open CategoryTheory
open scoped TensorProduct

attribute [local instance] coefficientAlgebra coefficientScalarTower

variable {R : Type v} [CommRing R] (S : CommAlgCat.{v} R)

private abbrev quotientTestIdeal (A : CommAlgCat.{v} R) : Ideal A :=
  (RingHom.ker (algebraMap R S)).map (algebraMap R A)

private def quotientTestStructuralMap (hS : Function.Surjective (algebraMap R S))
    (A : CommAlgCat.{v} R) : S →+* (A ⧸ quotientTestIdeal S A) :=
  (algebraMap R S).liftOfSurjective hS
    ⟨(Ideal.Quotient.mk (quotientTestIdeal S A)).comp (algebraMap R A), fun _ hr =>
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ hr)⟩

private theorem quotientTestStructuralMap_apply (hS : Function.Surjective (algebraMap R S))
    (A : CommAlgCat.{v} R) (r : R) :
    quotientTestStructuralMap S hS A (algebraMap R S r) =
      Ideal.Quotient.mk (quotientTestIdeal S A) (algebraMap R A r) :=
  (algebraMap R S).liftOfSurjective_comp_apply hS _ r

/-- Reduce a coefficient test by the ideal extended from the base coefficient kernel. -/
def quotientTest (hS : Function.Surjective (algebraMap R S)) (A : CommAlgCat.{v} R) :
    CommAlgCat.{v} S :=
  letI := (quotientTestStructuralMap S hS A).toAlgebra
  CommAlgCat.of S (A ⧸ quotientTestIdeal S A)

/-- The quotient map is an actual map of R-algebra tests. -/
def quotientTestProjection (hS : Function.Surjective (algebraMap R S))
    (A : CommAlgCat.{v} R) : A ⟶ restrictTest S (quotientTest S hS A) :=
  CommAlgCat.ofHom {
    toRingHom := Ideal.Quotient.mk (quotientTestIdeal S A)
    commutes' r := (quotientTestStructuralMap_apply S hS A r).symm }

theorem quotientTestProjection_surjective (hS : Function.Surjective (algebraMap R S))
    (A : CommAlgCat.{v} R) : Function.Surjective (quotientTestProjection S hS A).hom :=
  Ideal.Quotient.mk_surjective

theorem quotientTestProjection_nilpotent (hS : Function.Surjective (algebraMap R S))
    (hI : IsNilpotent (RingHom.ker (algebraMap R S))) (A : CommAlgCat.{v} R) :
    IsNilpotent (RingHom.ker (quotientTestProjection S hS A).hom.toRingHom) := by
  change IsNilpotent (RingHom.ker (Ideal.Quotient.mk (quotientTestIdeal S A)))
  rw [Ideal.mk_ker]
  obtain ⟨n, hn⟩ := hI
  refine ⟨n, ?_⟩
  change (quotientTestIdeal S A) ^ n = ⊥
  rw [quotientTestIdeal, ← Ideal.map_pow,
    show RingHom.ker (algebraMap R S) ^ n = ⊥ from hn, Ideal.map_bot]

private theorem quotientTestIdeal_le_ker {A : CommAlgCat.{v} R} {B : CommAlgCat.{v} S}
    (g : A ⟶ restrictTest S B) :
    quotientTestIdeal S A ≤ RingHom.ker g.hom.toRingHom := by
  rw [quotientTestIdeal, Ideal.map_le_iff_le_comap]
  intro r hr
  change g.hom (algebraMap R A r) = 0
  rw [g.hom.commutes]
  change algebraMap S B (algebraMap R S r) = 0
  rw [show algebraMap R S r = 0 from hr, map_zero]

/-- A coefficient map to an S-algebra factors through the actual quotient test. -/
def quotientTestLift (hS : Function.Surjective (algebraMap R S))
    {A : CommAlgCat.{v} R} {B : CommAlgCat.{v} S} (g : A ⟶ restrictTest S B) :
    quotientTest S hS A ⟶ B := by
  letI := (quotientTestStructuralMap S hS A).toAlgebra
  exact CommAlgCat.ofHom {
    toRingHom := Ideal.Quotient.lift (quotientTestIdeal S A) g.hom.toRingHom
      (fun _ hr => quotientTestIdeal_le_ker S g hr)
    commutes' s := by
      obtain ⟨r, rfl⟩ := hS s
      change Ideal.Quotient.lift (quotientTestIdeal S A) g.hom.toRingHom _
        (quotientTestStructuralMap S hS A (algebraMap R S r)) =
          algebraMap S B (algebraMap R S r)
      rw [quotientTestStructuralMap_apply]
      exact (Ideal.Quotient.lift_mk (quotientTestIdeal S A) g.hom.toRingHom
        (fun _ hr => quotientTestIdeal_le_ker S g hr)).trans (g.hom.commutes r) }

@[simp]
theorem quotientTestProjection_lift (hS : Function.Surjective (algebraMap R S))
    {A : CommAlgCat.{v} R} {B : CommAlgCat.{v} S} (g : A ⟶ restrictTest S B) :
    quotientTestProjection S hS A ≫ restrictTestHom S (quotientTestLift S hS g) = g := by
  ext x
  exact Ideal.Quotient.lift_mk (quotientTestIdeal S A) (a := x) g.hom.toRingHom
    (fun _ hr => quotientTestIdeal_le_ker S g hr)

/-- A morphism of coefficient tests induces the actual morphism on their quotients. -/
def quotientTestMap (hS : Function.Surjective (algebraMap R S))
    {A B : CommAlgCat.{v} R} (g : A ⟶ B) :
    quotientTest S hS A ⟶ quotientTest S hS B :=
  quotientTestLift S hS (g ≫ quotientTestProjection S hS B)

@[simp]
theorem quotientTestProjection_natural (hS : Function.Surjective (algebraMap R S))
    {A B : CommAlgCat.{v} R} (g : A ⟶ B) :
    quotientTestProjection S hS A ≫ restrictTestHom S (quotientTestMap S hS g) =
      g ≫ quotientTestProjection S hS B :=
  quotientTestProjection_lift S hS _

variable {O : Type u} [CommRing O] [Algebra O R]
variable {σ τ : Type} [Finite σ] [Finite τ]
variable {X : BasicAtlas O R σ} {Y : BasicAtlas O R τ} {h : X.opens = Y.opens}

/-- A nilpotent coefficient thickening admits a finite principal subcover with distinct images. -/
theorem exists_finite_subcover_injOn (Y : BasicAtlas O R τ)
    (hS : Function.Surjective (algebraMap R S))
    (hI : IsNilpotent (RingHom.ker (algebraMap R S))) :
    ∃ s : Finset R, (s : Set R) ⊆ Y.opens ∧ Ideal.span (s : Set R) = ⊤ ∧
      Set.InjOn (algebraMap R S) (s : Set R) := by
  have hc := Y.baseSourceSubcover_covers S hS hI
  obtain ⟨s, hs, hm⟩ := Submodule.mem_span_finite_of_mem_span ((Ideal.eq_top_iff_one _).mp hc)
  refine ⟨s, hs.trans (Y.baseSourceSubcover_subset S), (Ideal.eq_top_iff_one _).mpr hm, ?_⟩
  intro a ha b hb he
  obtain ⟨x, rfl⟩ := hs ha
  obtain ⟨y, rfl⟩ := hs hb
  have hxy : x = y := Subtype.ext
    ((Y.baseSource_image S x).symm.trans (he.trans (Y.baseSource_image S y)))
  exact congrArg (fun z => (Y.baseSource S z).val) hxy

private abbrev chartHomAt (h : X.opens = Y.opens) (A : CommAlgCat.{v} R) (b : Y.opens)
    (hb : IsUnit (algebraMap R A b.val)) :=
  ModuleLaw.Hom
    ((X.chart (sourceChart h b)).map (coefficientLift (O := O) b.val A hb))
    ((Y.chart b).map (coefficientLift (O := O) b.val A hb))

private def principalMap (A : CommAlgCat.{v} R) (a : R)
    (ha : IsUnit (algebraMap R A a)) : principalChartAlgebra a ⟶ A :=
  CommAlgCat.ofHom (IsLocalization.Away.liftAlgHom a (f := Algebra.ofId R A) ha)

private theorem principalMap_natural {A B : CommAlgCat.{v} R} (g : A ⟶ B)
    (a : R) (ha : IsUnit (algebraMap R A a)) (hb : IsUnit (algebraMap R B a)) :
    principalMap A a ha ≫ g = principalMap B a hb := by
  apply CommAlgCat.hom_ext
  apply AlgHom.coe_ringHom_injective
  let φ : Localization.Away a →+* B :=
    (principalMap A a ha ≫ g).hom.toRingHom
  let ψ : Localization.Away a →+* B :=
    (principalMap B a hb).hom.toRingHom
  change φ = ψ
  apply IsLocalization.ringHom_ext (Submonoid.powers a)
  ext x
  exact ((principalMap A a ha ≫ g).hom.commutes x).trans
    ((principalMap B a hb).hom.commutes x).symm

set_option backward.isDefEq.respectTransparency false in
private def mapChartHom {A B : CommAlgCat.{v} R} (g : A ⟶ B) (b : Y.opens)
    (ha : IsUnit (algebraMap R A b.val)) (hb : IsUnit (algebraMap R B b.val))
    (f : chartHomAt h A b ha) : chartHomAt h B b hb :=
  (coefficientTriangleIso (Y.chart b) g ha hb).hom.comp
    ((f.map (g.hom.restrictScalars O)).comp
      (coefficientTriangleIso (X.chart (sourceChart h b)) g ha hb).inv)

set_option backward.isDefEq.respectTransparency false in
private theorem mapChartHom_coordinates {A B : CommAlgCat.{v} R} (g : A ⟶ B) (b : Y.opens)
    (ha : IsUnit (algebraMap R A b.val)) (hb : IsUnit (algebraMap R B b.val))
    (f : chartHomAt h A b ha) :
    (mapChartHom g b ha hb f).toHom.toCoordinateMap =
      f.toHom.toCoordinateMap.map g.hom.toRingHom := by
  change CoordinateMap.id.comp
    ((f.toHom.toCoordinateMap.map g.hom.toRingHom).comp CoordinateMap.id) = _
  simp only [CoordinateMap.id_comp, CoordinateMap.comp_id]

private theorem baseSource_imageChart_of_injOn
    (hi : Set.InjOn (algebraMap R S) Y.opens) (b : Y.opens) :
    Y.baseSource S (Y.imageChart S b) = b :=
  Subtype.ext (hi (Y.baseSource S (Y.imageChart S b)).property b.property
    (Y.baseSource_image S (Y.imageChart S b)))

private def equalChartIso {A : CommAlgCat.{v} R} {M N : ModuleLaw O A σ}
    (e : M = N) : ModuleLaw.Iso M N := by
  cases e
  exact ModuleLaw.Iso.refl M

@[simp]
private theorem equalChartIso_hom_coordinates
    {A : CommAlgCat.{v} R} {M N : ModuleLaw O A σ} (e : M = N) :
    (equalChartIso e).hom.toHom.toCoordinateMap = CoordinateMap.id := by
  cases e
  rfl

@[simp]
private theorem equalChartIso_inv_coordinates
    {A : CommAlgCat.{v} R} {M N : ModuleLaw O A σ} (e : M = N) :
    (equalChartIso e).inv.toHom.toCoordinateMap = CoordinateMap.id := by
  cases e
  rfl

namespace Hom

set_option backward.isDefEq.respectTransparency false in
/-- Interpret a reduced atlas map in the original charts on a coefficient test. -/
private def reducedChartHom (r : Hom (X.baseChange S) (Y.baseChange S) (baseOpens_eq S h))
    (hi : Set.InjOn (algebraMap R S) Y.opens) (B : CommAlgCat.{v} S)
    (b : Y.opens) (hb : IsUnit (algebraMap R (restrictTest S B) b.val)) :
    ModuleLaw.Hom
      ((X.chart (sourceChart h b)).map (coefficientLift (O := O) b.val (restrictTest S B) hb))
      ((Y.chart b).map (coefficientLift (O := O) b.val (restrictTest S B) hb)) := by
  let b' := Y.imageChart S b
  let hb' := Y.imageChart_unit S B b hb
  let a := Y.baseSource S b'
  let ha := Y.baseSource_unit S B b' hb'
  have he : a = b := baseSource_imageChart_of_injOn S hi b
  let ix := (baseSourceChartIso S h B b' hb').trans
    (equalChartIso (X.testChart_eq (restrictTest S B) (sourceChart h a)
      (sourceChart h b) ha hb (congrArg (sourceChart h) he)))
  let iy := (Y.baseChartIso S B b' hb').trans
    (equalChartIso (Y.testChart_eq (restrictTest S B) a b ha hb he))
  exact iy.hom.comp ((r.hom B b' hb').comp ix.inv)

set_option backward.isDefEq.respectTransparency false in
private theorem reducedChartHom_coordinates
    (r : Hom (X.baseChange S) (Y.baseChange S) (baseOpens_eq S h))
    (hi : Set.InjOn (algebraMap R S) Y.opens) (B : CommAlgCat.{v} S)
    (b : Y.opens) (hb : IsUnit (algebraMap R (restrictTest S B) b.val)) :
    (reducedChartHom S (h := h) r hi B b hb).toHom.toCoordinateMap =
      (r.hom B (Y.imageChart S b) (Y.imageChart_unit S B b hb)).toHom.toCoordinateMap := by
  unfold reducedChartHom
  simp only [ModuleLaw.Iso.trans, ModuleLaw.Hom.comp_toHom,
    CommLaw.Hom.comp_toCoordinateMap, equalChartIso_hom_coordinates,
    equalChartIso_inv_coordinates]
  change (CoordinateMap.id.comp CoordinateMap.id).comp
    ((r.hom B (Y.imageChart S b) (Y.imageChart_unit S B b hb)).toHom.toCoordinateMap.comp
      (CoordinateMap.id.comp CoordinateMap.id)) = _
  simp only [CoordinateMap.id_comp, CoordinateMap.comp_id]

set_option backward.isDefEq.respectTransparency false in
private theorem reducedChartHom_natural
    (r : Hom (X.baseChange S) (Y.baseChange S) (baseOpens_eq S h))
    (hi : Set.InjOn (algebraMap R S) Y.opens) {A B : CommAlgCat.{v} S} (g : A ⟶ B)
    (b : Y.opens) (ha : IsUnit (algebraMap R (restrictTest S A) b.val))
    (hb : IsUnit (algebraMap R (restrictTest S B) b.val)) :
    (reducedChartHom S (h := h) r hi A b ha).toHom.toCoordinateMap.map g.hom.toRingHom =
      (reducedChartHom S (h := h) r hi B b hb).toHom.toCoordinateMap := by
  rw [reducedChartHom_coordinates, reducedChartHom_coordinates]
  exact r.natural g (Y.imageChart S b) (Y.imageChart_unit S A b ha)
    (Y.imageChart_unit S B b hb)

set_option backward.isDefEq.respectTransparency false in
private theorem reducedChartHom_transition_coordinates
    (r : Hom (X.baseChange S) (Y.baseChange S) (baseOpens_eq S h))
    (hi : Set.InjOn (algebraMap R S) Y.opens) (B : CommAlgCat.{v} S)
    (a b : Y.opens) (ha : IsUnit (algebraMap R (restrictTest S B) a.val))
    (hb : IsUnit (algebraMap R (restrictTest S B) b.val)) :
    (Y.transition (restrictTest S B) a b ha hb).hom.toHom.toCoordinateMap.comp
      (reducedChartHom S (h := h) r hi B a ha).toHom.toCoordinateMap =
    (reducedChartHom S (h := h) r hi B b hb).toHom.toCoordinateMap.comp
      (X.transition (restrictTest S B) (sourceChart h a) (sourceChart h b)
        ha hb).hom.toHom.toCoordinateMap := by
  let a' := Y.imageChart S a
  let b' := Y.imageChart S b
  let ha' := Y.imageChart_unit S B a ha
  let hb' := Y.imageChart_unit S B b hb
  have hY := (Y.baseTransition_coordinates S B a' b' ha' hb').trans
    (Y.testTransition_coordinates_eq (restrictTest S B)
      (Y.baseSource S a') (Y.baseSource S b') a b
      (Y.baseSource_unit S B a' ha') (Y.baseSource_unit S B b' hb') ha hb
      (baseSource_imageChart_of_injOn S hi a) (baseSource_imageChart_of_injOn S hi b))
  have hX := (baseSourceTransition_coordinates S h B a' b' ha' hb').trans
    (X.testTransition_coordinates_eq (restrictTest S B)
      (sourceChart h (Y.baseSource S a')) (sourceChart h (Y.baseSource S b'))
      (sourceChart h a) (sourceChart h b)
      (Y.baseSource_unit S B a' ha') (Y.baseSource_unit S B b' hb') ha hb
      (congrArg (sourceChart h) (baseSource_imageChart_of_injOn S hi a))
      (congrArg (sourceChart h) (baseSource_imageChart_of_injOn S hi b)))
  have he := congrArg (fun f => f.toHom.toCoordinateMap) (r.transition B a' b' ha' hb')
  simp only [ModuleLaw.Hom.comp_toHom, CommLaw.Hom.comp_toCoordinateMap] at he
  change ((Y.baseTransition S B a' b' ha' hb').hom.toHom.toCoordinateMap).comp
    (r.hom B a' ha').toHom.toCoordinateMap = _ at he
  rw [hY, hX] at he
  simpa only [reducedChartHom_coordinates] using he

private abbrev principalHomAt (h : X.opens = Y.opens) (b : Y.opens) :=
  chartHomAt h (principalChartAlgebra b.val) b (principalChartAlgebra_unit b.val)

private abbrev extendsReducedHom
    (hS : Function.Surjective (algebraMap R S))
    (r : Hom (X.baseChange S) (Y.baseChange S) (baseOpens_eq S h))
    (hi : Set.InjOn (algebraMap R S) Y.opens) (b : Y.opens) (f : principalHomAt h b) : Prop :=
  let A := principalChartAlgebra b.val
  let q := quotientTestProjection S hS A
  f.toHom.toCoordinateMap.map q.hom.toRingHom =
    (reducedChartHom S (h := h) r hi (quotientTest S hS A) b
      (unit_map q (principalChartAlgebra_unit b.val))).toHom.toCoordinateMap

set_option backward.isDefEq.respectTransparency false in
private theorem mappedPrincipalHom_reduction
    (hS : Function.Surjective (algebraMap R S))
    (r : Hom (X.baseChange S) (Y.baseChange S) (baseOpens_eq S h))
    (hi : Set.InjOn (algebraMap R S) Y.opens) (b : Y.opens)
    (f : principalHomAt h b) (hf : extendsReducedHom S hS r hi b f)
    (A : CommAlgCat.{v} R) (hb : IsUnit (algebraMap R A b.val)) :
    (mapChartHom (principalMap A b.val hb) b (principalChartAlgebra_unit b.val) hb
      f).toHom.toCoordinateMap.map (quotientTestProjection S hS A).hom.toRingHom =
    (reducedChartHom S (h := h) r hi (quotientTest S hS A) b
      (unit_map (quotientTestProjection S hS A) hb)).toHom.toCoordinateMap := by
  let β := principalMap A b.val hb
  let q := quotientTestProjection S hS A
  let q₀ := quotientTestProjection S hS (principalChartAlgebra b.val)
  let β₀ := quotientTestMap S hS β
  rw [mapChartHom_coordinates, CoordinateMap.map_ringHom_comp]
  have e := congrArg (fun z => z.hom.toRingHom) (quotientTestProjection_natural S hS β)
  change β₀.hom.toRingHom.comp q₀.hom.toRingHom = q.hom.toRingHom.comp β.hom.toRingHom at e
  change f.toHom.toCoordinateMap.map (q.hom.toRingHom.comp β.hom.toRingHom) = _
  rw [← e, ← CoordinateMap.map_ringHom_comp]
  change f.toHom.toCoordinateMap.map q₀.hom.toRingHom = _ at hf
  rw [hf]
  exact reducedChartHom_natural S r hi β₀ b _ _

set_option backward.isDefEq.respectTransparency false in
private def assemblePrincipalLifts
    (hS : Function.Surjective (algebraMap R S))
    (hI : IsNilpotent (RingHom.ker (algebraMap R S))) {π : O}
    (hX : ∀ a : X.opens, (X.chart a).IsPiDivisible π)
    (hY : ∀ b : Y.opens, (Y.chart b).IsPiPowerTorsion π)
    (r : Hom (X.baseChange S) (Y.baseChange S) (baseOpens_eq S h))
    (hi : Set.InjOn (algebraMap R S) Y.opens) (f : ∀ b : Y.opens, principalHomAt h b)
    (hf : ∀ b : Y.opens, extendsReducedHom S hS r hi b (f b)) : Hom X Y h where
  hom A b hb := mapChartHom (principalMap A b.val hb) b (principalChartAlgebra_unit b.val) hb (f b)
  natural {A B} g b ha hb := by
    rw [mapChartHom_coordinates, mapChartHom_coordinates, CoordinateMap.map_ringHom_comp]
    exact congrArg (fun z => (f b).toHom.toCoordinateMap.map z.hom.toRingHom)
      (principalMap_natural g b.val ha hb)
  transition A a b ha hb := by
    let q := quotientTestProjection S hS A
    let ha₀ := unit_map q ha
    let hb₀ := unit_map q hb
    apply ModuleLaw.Hom.map_injective_of_nilpotent (q.hom.restrictScalars O)
      (quotientTestProjection_surjective S hS A) (quotientTestProjection_nilpotent S hS hI A)
      ((hX (sourceChart h a)).map (coefficientLift (O := O) a.val A ha))
      ((hY b).map (coefficientLift (O := O) b.val A hb))
    apply ModuleLaw.Hom.ext
    apply CommLaw.Hom.ext
    change ((Y.transition A a b ha hb).hom.toHom.toCoordinateMap.comp _).map q.hom.toRingHom =
      (CoordinateMap.comp _ (X.transition A (sourceChart h a) (sourceChart h b)
        ha hb).hom.toHom.toCoordinateMap).map q.hom.toRingHom
    rw [CoordinateMap.map_comp, CoordinateMap.map_comp,
      Y.transition_natural q a b ha hb ha₀ hb₀,
      X.transition_natural q (sourceChart h a) (sourceChart h b) ha hb ha₀ hb₀,
      mappedPrincipalHom_reduction S hS r hi a (f a) (hf a) A ha,
      mappedPrincipalHom_reduction S hS r hi b (f b) (hf b) A hb]
    exact reducedChartHom_transition_coordinates S r hi (quotientTest S hS A) a b ha₀ hb₀

set_option backward.isDefEq.respectTransparency false in
private theorem assemblePrincipalLifts_baseChange
    (hS : Function.Surjective (algebraMap R S))
    (hI : IsNilpotent (RingHom.ker (algebraMap R S))) {π : O}
    (hX : ∀ a : X.opens, (X.chart a).IsPiDivisible π)
    (hY : ∀ b : Y.opens, (Y.chart b).IsPiPowerTorsion π)
    (r : Hom (X.baseChange S) (Y.baseChange S) (baseOpens_eq S h))
    (hi : Set.InjOn (algebraMap R S) Y.opens) (f : ∀ b : Y.opens, principalHomAt h b)
    (hf : ∀ b : Y.opens, extendsReducedHom S hS r hi b (f b)) :
    (assemblePrincipalLifts S hS hI hX hY r hi f hf).baseChange S = r := by
  apply Hom.ext
  intro B b hb
  apply ModuleLaw.Hom.ext
  apply CommLaw.Hom.ext
  rw [baseChange_coordinates]
  let A := restrictTest S B
  let a := Y.baseSource S b
  let ha := Y.baseSource_unit S B b hb
  let q := quotientTestProjection S hS A
  let v := quotientTestLift S hS (B := B) (𝟙 A)
  have hv : v.hom.toRingHom.comp q.hom.toRingHom = RingHom.id A :=
    congrArg (fun z => z.hom.toRingHom) (quotientTestProjection_lift S hS (B := B) (𝟙 A))
  have hc := mappedPrincipalHom_reduction S hS r hi a (f a) (hf a) A ha
  have hvh := congrArg (fun z => z.map v.hom.toRingHom) hc
  change (((assemblePrincipalLifts S hS hI hX hY r hi f hf).hom A a ha).toHom.toCoordinateMap.map
    q.hom.toRingHom).map v.hom.toRingHom = _ at hvh
  rw [CoordinateMap.map_ringHom_comp, hv, CoordinateMap.map_ringHom_id,
    reducedChartHom_natural S r hi v a _ ha] at hvh
  exact hvh.trans ((reducedChartHom_coordinates S r hi B a ha).trans
    (r.hom_coordinates_eq B (Y.imageChart S a) b (Y.imageChart_unit S B a ha) hb
      (Y.imageChart_baseSource S b)))

set_option backward.isDefEq.respectTransparency false in
private def reducedPrincipalHom
    (hS : Function.Surjective (algebraMap R S))
    (r : Hom (X.baseChange S) (Y.baseChange S) (baseOpens_eq S h))
    (hi : Set.InjOn (algebraMap R S) Y.opens) (b : Y.opens) :
    let A := principalChartAlgebra b.val
    let q := (quotientTestProjection S hS A).hom.restrictScalars O
    ModuleLaw.Hom
      (((X.chart (sourceChart h b)).map (coefficientLift (O := O) b.val A
        (principalChartAlgebra_unit b.val))).map q)
      (((Y.chart b).map (coefficientLift (O := O) b.val A
        (principalChartAlgebra_unit b.val))).map q) := by
  let A := principalChartAlgebra b.val
  let B := quotientTest S hS A
  let q := quotientTestProjection S hS A
  let hb := principalChartAlgebra_unit b.val
  let hb₀ := unit_map q hb
  let ix := coefficientTriangleIso (X.chart (sourceChart h b)) q hb hb₀
  let iy := coefficientTriangleIso (Y.chart b) q hb hb₀
  exact iy.inv.comp ((reducedChartHom S (h := h) r hi B b hb₀).comp ix.hom)

set_option backward.isDefEq.respectTransparency false in
private theorem reducedPrincipalHom_coordinates
    (hS : Function.Surjective (algebraMap R S))
    (r : Hom (X.baseChange S) (Y.baseChange S) (baseOpens_eq S h))
    (hi : Set.InjOn (algebraMap R S) Y.opens) (b : Y.opens) :
    (reducedPrincipalHom S hS (h := h) r hi b).toHom.toCoordinateMap =
      (reducedChartHom S (h := h) r hi (quotientTest S hS (principalChartAlgebra b.val))
        b (unit_map (quotientTestProjection S hS (principalChartAlgebra b.val))
          (principalChartAlgebra_unit b.val))).toHom.toCoordinateMap := by
  let A := principalChartAlgebra b.val
  let B := quotientTest S hS A
  let hb := unit_map (quotientTestProjection S hS A) (principalChartAlgebra_unit b.val)
  let C := (reducedChartHom S (h := h) r hi B b hb).toHom.toCoordinateMap
  change CoordinateMap.id.comp (C.comp CoordinateMap.id) = C
  rw [CoordinateMap.id_comp, CoordinateMap.comp_id]

set_option backward.isDefEq.respectTransparency false in
private theorem reducedPrincipalHom_smul
    (hS : Function.Surjective (algebraMap R S))
    (r : Hom (X.baseChange S) (Y.baseChange S) (baseOpens_eq S h))
    (hi : Set.InjOn (algebraMap R S) Y.opens) (b : Y.opens) (t : O) :
    reducedPrincipalHom S hS (h := h) (t • r) hi b =
      t • reducedPrincipalHom S hS (h := h) r hi b := by
  unfold reducedPrincipalHom reducedChartHom
  simp only [smul_hom, ModuleLaw.Hom.comp_smul, ModuleLaw.Hom.smul_comp]

set_option backward.isDefEq.respectTransparency false in
/-- On a finite principal cover, one scalar power suffices for the entire atlas lift. -/
theorem exists_lift_smul_of_finite_of_nilpotent [Finite Y.opens]
    (hS : Function.Surjective (algebraMap R S))
    (hI : IsNilpotent (RingHom.ker (algebraMap R S))) {π : O}
    (hX : ∀ a : X.opens, (X.chart a).IsPiDivisible π)
    (hY : ∀ b : Y.opens, (Y.chart b).IsPiPowerTorsion π)
    (r : Hom (X.baseChange S) (Y.baseChange S) (baseOpens_eq S h))
    (hi : Set.InjOn (algebraMap R S) Y.opens) :
    ∃ (k : ℕ) (f : Hom X Y h), f.baseChange S = π ^ k • r := by
  classical
  let _ := Fintype.ofFinite Y.opens
  let A (b : Y.opens) := principalChartAlgebra b.val
  let q (b : Y.opens) := (quotientTestProjection S hS (A b)).hom.restrictScalars O
  have hlift (b : Y.opens) : ∃ (k : ℕ) (f : principalHomAt h b),
      f.map (q b) = π ^ k • reducedPrincipalHom S hS (h := h) r hi b :=
    ModuleLaw.Hom.exists_lift_smul_of_nilpotent (q b)
      (quotientTestProjection_surjective S hS (A b))
      (quotientTestProjection_nilpotent S hS hI (A b))
      ((hY b).map (coefficientLift (O := O) b.val (A b) (principalChartAlgebra_unit b.val)))
      (reducedPrincipalHom S hS (h := h) r hi b)
  choose n g hg using hlift
  let k := Finset.univ.sup n
  let f (b : Y.opens) : principalHomAt h b := π ^ (k - n b) • g b
  have hf (b : Y.opens) : extendsReducedHom S hS (π ^ k • r) hi b (f b) := by
    have he : (f b).map (q b) = reducedPrincipalHom S hS (h := h) (π ^ k • r) hi b := by
      change ModuleLaw.Hom.mapLinear (q b) (π ^ (k - n b) • g b) = _
      rw [map_smul, reducedPrincipalHom_smul]
      change π ^ (k - n b) • (g b).map (q b) = _
      rw [hg b, smul_smul, ← pow_add, Nat.sub_add_cancel (Finset.le_sup (Finset.mem_univ b))]
    exact (congrArg (fun z => z.toHom.toCoordinateMap) he).trans
      (reducedPrincipalHom_coordinates S hS (π ^ k • r) hi b)
  exact ⟨k, assemblePrincipalLifts S hS hI hX hY (π ^ k • r) hi f hf,
    assemblePrincipalLifts_baseChange S hS hI hX hY (π ^ k • r) hi f hf⟩

end Hom

namespace RationalHom

variable {F : Type w} [Field F] [Algebra O F] {π : O}

/-- Rationalization inverts the common scalar power in the integral atlas lifting theorem. -/
theorem baseChange_surjective_of_finite_of_nilpotent [Finite Y.opens]
    (hS : Function.Surjective (algebraMap R S))
    (hI : IsNilpotent (RingHom.ker (algebraMap R S)))
    (hX : ∀ a : X.opens, (X.chart a).IsPiDivisible π)
    (hY : ∀ b : Y.opens, (Y.chart b).IsPiPowerTorsion π)
    (hi : Set.InjOn (algebraMap R S) Y.opens) (hπ : algebraMap O F π ≠ 0) :
    Function.Surjective (baseChange (F := F) (X := X) (Y := Y) (h := h) S) := by
  intro t
  induction t using TensorProduct.inductionOn with
  | tmul a f =>
    obtain ⟨n, g, hg⟩ := Hom.exists_lift_smul_of_finite_of_nilpotent S hS hI hX hY f hi
    let c := algebraMap O F π ^ n
    refine ⟨(a / c) ⊗ₜ[O] g, ?_⟩
    rw [baseChange_tmul, hg, ← TensorProduct.smul_tmul, Algebra.smul_def, map_pow]
    change (c * (a / c)) ⊗ₜ[O] f = a ⊗ₜ[O] f
    rw [mul_comm c, div_mul_cancel₀ _ (pow_ne_zero n hπ)]
  | add t₁ t₂ h₁ h₂ =>
    obtain ⟨f₁, rfl⟩ := h₁
    obtain ⟨f₂, rfl⟩ := h₂
    exact ⟨f₁ + f₂, map_add _ _ _⟩

/-- The actual rational atlas Hom comparison on a finite cover with distinct images. -/
def finiteNilpotentBaseChangeEquiv [Module.Flat O F] [Finite Y.opens]
    (hS : Function.Surjective (algebraMap R S))
    (hI : IsNilpotent (RingHom.ker (algebraMap R S)))
    (hX : ∀ a : X.opens, (X.chart a).IsPiDivisible π)
    (hY : ∀ b : Y.opens, (Y.chart b).IsPiPowerTorsion π)
    (hi : Set.InjOn (algebraMap R S) Y.opens) (hπ : algebraMap O F π ≠ 0) :
    RationalHom F X Y h ≃ₗ[F]
      RationalHom F (X.baseChange S) (Y.baseChange S) (baseOpens_eq S h) :=
  LinearEquiv.ofBijective (baseChange S)
    ⟨baseChange_injective_of_nilpotent S hS hI hX hY,
      baseChange_surjective_of_finite_of_nilpotent S hS hI hX hY hi hπ⟩

end RationalHom

namespace OrderAction

variable {D : Type z} [Ring D] [Algebra O D]
variable {E : OrderAction D X} {G : OrderAction D Y}
variable {F : Type w} [Field F] [Algebra O F] {π : O}

set_option backward.isDefEq.respectTransparency false in
private theorem endomorphism_baseChange (E : OrderAction D X) (a : D) :
    (E.endomorphism a).baseChange S = (E.baseChange S).endomorphism a := by
  apply BasicAtlas.Hom.ext
  intro A b hb
  apply ModuleLaw.Hom.ext
  apply CommLaw.Hom.ext
  rw [BasicAtlas.Hom.baseChange_coordinates]
  exact (E.baseOrderChart_coordinates S A b hb a).symm

set_option backward.isDefEq.respectTransparency false in
private theorem commutes_iff_endomorphism [Module.Flat O F]
    (f : BasicAtlas.RationalHom F X Y h) :
    f ∈ rationalHomSubmodule F E G h ↔
      ∀ a : D, BasicAtlas.RationalHom.comp f (BasicAtlas.RationalHom.ofHom (E.endomorphism a)) =
        BasicAtlas.RationalHom.comp (BasicAtlas.RationalHom.ofHom (G.endomorphism a)) f := by
  constructor
  · intro hf a
    apply BasicAtlas.RationalHom.ext_onCharts
    intro A b hb
    rw [BasicAtlas.RationalHom.onChart_comp, BasicAtlas.RationalHom.onChart_comp,
      BasicAtlas.RationalHom.onChart_ofHom, BasicAtlas.RationalHom.onChart_ofHom]
    exact hf A b hb a
  · intro hf A b hb a
    have he := congrArg (BasicAtlas.RationalHom.onChart (X := X) (h := h) A b hb) (hf a)
    rw [BasicAtlas.RationalHom.onChart_comp, BasicAtlas.RationalHom.onChart_comp,
      BasicAtlas.RationalHom.onChart_ofHom, BasicAtlas.RationalHom.onChart_ofHom] at he
    exact he

namespace RationalHom

/-- Finite-cover lifting preserves the full order by reflecting its endomorphism equations. -/
theorem baseChange_bijective_of_finite_of_nilpotent [Module.Flat O F] [Finite Y.opens]
    (hS : Function.Surjective (algebraMap R S))
    (hI : IsNilpotent (RingHom.ker (algebraMap R S)))
    (hX : ∀ a : X.opens, (X.chart a).IsPiDivisible π)
    (hY : ∀ b : Y.opens, (Y.chart b).IsPiPowerTorsion π)
    (hi : Set.InjOn (algebraMap R S) Y.opens) (hπ : algebraMap O F π ≠ 0) :
    Function.Bijective (baseChange (F := F) (E := E) (E' := G) (h := h) S) := by
  let e := BasicAtlas.RationalHom.finiteNilpotentBaseChangeEquiv (F := F) (h := h) S
    hS hI hX hY hi hπ
  constructor
  · intro f g he
    apply ext
    apply e.injective
    change BasicAtlas.RationalHom.baseChange S f.val = BasicAtlas.RationalHom.baseChange S g.val
    exact congrArg Subtype.val he
  · intro f
    obtain ⟨g, hg⟩ := e.surjective f.val
    change BasicAtlas.RationalHom.baseChange S g = f.val at hg
    refine ⟨⟨g, (commutes_iff_endomorphism (E := E) (G := G) g).2 ?_⟩, ext hg⟩
    intro a
    apply e.injective
    change BasicAtlas.RationalHom.baseChange S _ = BasicAtlas.RationalHom.baseChange S _
    rw [BasicAtlas.RationalHom.baseChange_comp, BasicAtlas.RationalHom.baseChange_comp,
      BasicAtlas.RationalHom.baseChange_ofHom, BasicAtlas.RationalHom.baseChange_ofHom,
      endomorphism_baseChange, endomorphism_baseChange, hg]
    exact (commutes_iff_endomorphism (E := E.baseChange S) (G := G.baseChange S) f.val).1 f.property a

end RationalHom

namespace QuasiIsogeny

variable [IsDomain O] [IsFractionRing O F]

/-- On such a finite cover the lift and its rational inverse retain the entire order action. -/
theorem baseChange_bijective_of_finite_of_nilpotent [Finite Y.opens]
    (hS : Function.Surjective (algebraMap R S))
    (hI : IsNilpotent (RingHom.ker (algebraMap R S)))
    (hX : ∀ a : X.opens, (X.chart a).IsPiDivisible π)
    (hY : ∀ b : Y.opens, (Y.chart b).IsPiDivisible π)
    (hi : Set.InjOn (algebraMap R S) Y.opens) (hπ : π ≠ 0) :
    Function.Bijective (fun f : QuasiIsogeny F E G h => f.baseChange S) := by
  let _ := IsLocalization.flat F (nonZeroDivisors O)
  let _ : Finite X.opens := h.symm ▸ (inferInstance : Finite Y.opens)
  have hj : Set.InjOn (algebraMap R S) X.opens := h.symm ▸ hi
  have hc : algebraMap O F π ≠ 0 := by
    simpa only [map_zero] using (IsFractionRing.injective O F).ne hπ
  have hf := RationalHom.baseChange_bijective_of_finite_of_nilpotent
    (E := E) (G := G) (h := h) S hS hI hX (fun b => (hY b).torsion) hi hc
  have hg := RationalHom.baseChange_bijective_of_finite_of_nilpotent
    (E := G) (G := E) (h := h.symm) S hS hI hY (fun a => (hX a).torsion) hj hc
  refine ⟨fun f g he => ext_hom (hf.injective (congrArg QuasiIsogeny.hom he)), ?_⟩
  intro f₀
  obtain ⟨f, hf₀⟩ := hf.surjective f₀.hom
  obtain ⟨g, hg₀⟩ := hg.surjective f₀.inv
  refine ⟨⟨f, g, ?_, ?_⟩, ?_⟩
  · apply (RationalHom.baseChange_bijective_of_finite_of_nilpotent
      (E := E) (G := E) (h := rfl) S hS hI hX (fun a => (hX a).torsion) hj hc).injective
    rw [RationalHom.baseChange_comp, hf₀, hg₀, RationalHom.baseChange_id, f₀.inv_hom]
  · apply (RationalHom.baseChange_bijective_of_finite_of_nilpotent
      (E := G) (G := G) (h := rfl) S hS hI hY (fun b => (hY b).torsion) hi hc).injective
    rw [RationalHom.baseChange_comp, hf₀, hg₀, RationalHom.baseChange_id, f₀.hom_inv]
  · exact ext_hom hf₀

end QuasiIsogeny
end OrderAction

end Langlands.FormalGroup.ModuleLaw.BasicAtlas
