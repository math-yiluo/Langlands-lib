import Langlands.Global.AdelicIntrinsicStandardFamily
import Langlands.Global.AdelicRelativeSplitBaseChart
import Mathlib.MeasureTheory.Group.MeasurableEquiv

/-! # Product Lebesgue measure in nested relative split coordinates -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory Set
open scoped CategoryTheory.MonObj Classical NNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.StandardParabolicFamily

open GroupScheme GroupScheme.RealTorusSpace ArthurRelative ArthurTruncation
  AdelicGroupPoints PositiveRealTorus

variable {F : Type} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G)

section SplitPoints

variable (J : StandardIndex F G fam.i fam.ν)

local notation "B" => relativePositiveSubgroup (fam.l J ≫ fam.p J) (fam.a J)
local notation "X" => (fam.relativeSimpleRoots J → ℝ)

/-- The relative positive split points and their projected coroot coordinates. -/
def relativeSplitCoordinatesEquiv : B ≃ₜ X := by
  let e := (fam.relativeCorootHaar J).choose
  exact
    { toEquiv := e.toEquiv.trans Multiplicative.toAdd
      continuous_toFun := e.continuous
      continuous_invFun := e.symm.continuous }

theorem exists_measurePreserving_relativeSplitCoordinatesEquiv (da : Measure B)
    (hda : da.IsHaarMeasure) :
    ∃ c > (0 : ℝ≥0), MeasurePreserving (fam.relativeSplitCoordinatesEquiv J).symm
      (c • (volume : Measure X)) da := by
  obtain ⟨c, hc, hp⟩ := (fam.relativeCorootHaar J).choose_spec.2 da hda
  exact ⟨c, hc, hp.symm (fam.relativeSplitCoordinatesEquiv J).toMeasurableEquiv⟩

/-- A relative positive split point in the ambient adelic group, specified by its coroot
coordinates. -/
def relativeSplitAdelicPoint (x : X) : AdelicGroupPoints F G :=
  map F (fam.M J) G (fam.l J ≫ fam.p J)
    (positivePointMap F (fam.M J) (fam.A J) (fam.a J) ((fam.relativeSplitCoordinatesEquiv J).symm x).val)

theorem exists_torusPoint_relativeSplitAdelicPoint (x : X) :
    ∃ t : intrinsicSubgroup F fam.T,
      fam.relativeSplitAdelicPoint J x = map F fam.T.toGrp G fam.i t.val ∧
      characterLog F fam.T.toGrp t.val = cocharacterFunctional (fam.relativeSplitVector J x) := by
  let e := fam.relativeSplitCoordinatesEquiv J
  obtain ⟨t, he, ht⟩ := ((fam.relativeCorootHaar J).choose_spec.1 (e.symm x)).1
  have hx : ((fam.relativeCorootHaar J).choose (e.symm x)).toAdd = x := e.apply_symm_apply x
  rw [hx, ← fam.relativeSplitVector_apply J x] at ht
  exact ⟨t, he, ht⟩

end SplitPoints

variable
  {I Q : StandardIndex F G fam.i fam.ν} (hIQ : I ≤ Q)

local instance : IsAffineHom (fam.M Q).X.hom := (fam.isCompatible Q).levi.isConnectedReductive.isAffineHom
local notation "low" => fam.intrinsicStandardFamily Q
local notation "L" => fam.intrinsicStandardIndex Q I hIQ
local notation "T" => fam.T
local notation "D" => fam.coroots
local notation "Δ" => simpleRelativeRoots fam.i fam.ν
local notation "R" => fam.relativeSimpleRoots I
local notation "A" => fam.relativeSimpleRoots Q
set_option quotPrecheck false in
local notation "B" => (low).relativeSimpleRoots L
set_option quotPrecheck false in
local notation "S" => ({α : R | α.val ∈ Q.val} : Set R)
set_option quotPrecheck false in
local notation "VC" => aSpace T I.val ⊓ (D).realCorootSpan
local notation "w" => weight fam.connectedReductive fam.maximalSplit fam.ν D Δ

omit [NumberField F] in
private theorem mem_relativeSimpleRoots {H : GroupScheme (Spec (CommRingCat.of F))}
    [IsAffineHom H.X.hom] [IsAffine H.X.left] [LocallyOfFiniteType H.X.hom]
    (f : StandardParabolicFamily F H) (J : StandardIndex F H f.i f.ν) (α : characterLattice f.T) :
    α ∈ f.relativeSimpleRoots J ↔ α ∈ simpleRelativeRoots f.i f.ν \ J.val := by
  rw [relativeSimpleRoots, Finset.mem_filter, ArthurTruncation.mem_simpleFinset]
  rfl

omit [NumberField F] in
private theorem weightCoordinate_formula (J : StandardIndex F G fam.i fam.ν)
    (y : V T) (α : fam.relativeSimpleRoots J) :
    fam.weightCoordinate J y α = w α.val y := by
  have he : (simpleFinset fam.ν fam.connectedReductive fam.maximalSplit : Set (characterLattice T)) = Δ :=
    Set.ext fun _ => mem_simpleFinset _ _
  unfold weightCoordinate
  rw [he]

private def outerCoordinate : {α : R // α ∉ S} ≃ A where
  toFun a := ⟨a.val.val, (mem_relativeSimpleRoots fam Q _).mpr
    ⟨((mem_relativeSimpleRoots fam I _).mp a.val.property).1, a.property⟩⟩
  invFun a := by
    have h := (mem_relativeSimpleRoots fam Q _).mp a.property
    exact ⟨⟨a.val, (mem_relativeSimpleRoots fam I _).mpr ⟨h.1, fun ha => h.2 (hIQ ha)⟩⟩, h.2⟩
  left_inv a := Subtype.ext (Subtype.ext rfl)
  right_inv a := Subtype.ext rfl

private def innerCoordinate : S ≃ B where
  toFun a := by
    have h := (mem_relativeSimpleRoots fam I _).mp a.val.property
    have hr : simpleRelativeRoots (low).i (low).ν = Q.val := (fam.intrinsicStandardRootData Q).2.2.1
    have ha : a.val.val ∈ simpleRelativeRoots (low).i (low).ν := by
      rw [hr]
      exact a.property
    exact ⟨a.val.val, (mem_relativeSimpleRoots (low) L _).mpr ⟨ha, h.2⟩⟩
  invFun a := by
    have h := (mem_relativeSimpleRoots (low) L _).mp a.property
    have hr : simpleRelativeRoots (low).i (low).ν = Q.val := (fam.intrinsicStandardRootData Q).2.2.1
    have ha : a.val ∈ Q.val := hr ▸ h.1
    exact ⟨⟨a.val, (mem_relativeSimpleRoots fam I _).mpr ⟨Q.property ha, h.2⟩⟩, ha⟩
  left_inv a := Subtype.ext (Subtype.ext rfl)
  right_inv a := Subtype.ext rfl

omit [NumberField F] in
private theorem innerProjectedSimpleCoroot (β : B) :
    ((low).projectedSimpleCoroot L β).val =
      (fam.projectedSimpleCoroot I ((fam.innerCoordinate hIQ).symm β).val).val := by
  let g := low
  let α := ((fam.innerCoordinate hIQ).symm β).val
  let βr : relativeRoots g.i := ⟨β.val, g.mem_relativeRoots_of_mem_relativeSimpleRoots L β⟩
  let αr : relativeRoots fam.i := ⟨α.val, fam.mem_relativeRoots_of_mem_relativeSimpleRoots I α⟩
  have hc : g.i ≫ fam.l Q ≫ fam.p Q = fam.i := fam.torus_comp Q
  change levelProjection g.connectedReductive g.maximalSplit g.ν g.coroots I.val (g.coroots.realCoroot βr) =
    levelProjection fam.connectedReductive fam.maximalSplit fam.ν D I.val ((D).realCoroot αr)
  exact (nestedProjectedCoroots fam.connectedReductive fam.maximalSplit g.connectedReductive
    g.maximalSplit (fam.l Q ≫ fam.p Q) D g.coroots hc fam.generic g.generic
    I.val I.property (L).property).2 βr αr rfl

omit [NumberField F] in
include hIQ in
private theorem outer_relativeSplitVector_mem (x : A → ℝ) :
    fam.relativeSplitVector Q x ∈ VC := by
  have hv := fam.relativeSplitVector_mem Q x
  refine ⟨?_, hv.2⟩
  exact (mem_rootAnnihilator _ _).mpr fun α hα => (mem_rootAnnihilator _ _).mp hv.1 α (hIQ hα)

omit [NumberField F] in
private theorem inner_relativeSplitVector_mem (y : B → ℝ) :
    (low).relativeSplitVector L y ∈ VC := by
  rw [relativeSplitVector_apply]
  apply Submodule.sum_mem
  intro β _
  rw [fam.innerProjectedSimpleCoroot hIQ β]
  exact (VC).smul_mem _ (fam.projectedSimpleCoroot I ((fam.innerCoordinate hIQ).symm β).val).property

omit [NumberField F] in
private theorem inner_weightCoordinate (y : B → ℝ) (a : R) :
    fam.weightCoordinate I ((low).relativeSplitVector L y) a =
      ∑ β : B, y β * if a = ((fam.innerCoordinate hIQ).symm β).val then 1 else 0 := by
  rw [relativeSplitVector_apply, fam.weightCoordinate_formula, map_sum]
  apply Finset.sum_congr rfl
  intro β _
  rw [fam.innerProjectedSimpleCoroot hIQ β, map_smul, smul_eq_mul]
  congr 1
  let b := ((fam.innerCoordinate hIQ).symm β).val
  let br : relativeRoots fam.i := ⟨b.val, fam.mem_relativeRoots_of_mem_relativeSimpleRoots I b⟩
  have ha := (mem_relativeSimpleRoots fam I _).mp a.property
  have hb := (mem_relativeSimpleRoots fam I _).mp b.property
  change w a.val (levelProjection fam.connectedReductive fam.maximalSplit fam.ν D I.val ((D).realCoroot br)) = _
  rw [weight_levelProjection_outside fam.connectedReductive fam.maximalSplit D fam.generic
    I.property ha.1 ha.2, weight_coroot fam.connectedReductive fam.maximalSplit D fam.generic
    subset_rfl ha.1 br hb.1]
  simp only [Subtype.ext_iff, br, b]

omit [NumberField F] in
private theorem inner_weightCoordinate_inside (y : B → ℝ) (a : S) :
    fam.weightCoordinate I ((low).relativeSplitVector L y) a.val = y (fam.innerCoordinate hIQ a) := by
  let e := fam.innerCoordinate hIQ
  rw [fam.inner_weightCoordinate hIQ]
  have hzero (b : B) (hba : b ≠ e a) :
      y b * (if a.val = (e.symm b).val then 1 else 0) = 0 := by
    have hne : a.val ≠ (e.symm b).val := by
      intro h
      exact hba (e.symm_apply_eq.mp (Subtype.ext h.symm))
    rw [ite_eq_right hne, mul_zero]
  rw [Finset.sum_eq_single (e a) (fun b _ hb => hzero b hb) (fun h => (h (Finset.mem_univ _)).elim)]
  change y (e a) * (if a.val = (e.symm (e a)).val then 1 else 0) = y (e a)
  rw [e.symm_apply_apply, ite_eq_left rfl, mul_one]

omit [NumberField F] in
private theorem inner_weightCoordinate_outside (y : B → ℝ) (a : {α : R // α ∉ S}) :
    fam.weightCoordinate I ((low).relativeSplitVector L y) a.val = 0 := by
  rw [fam.inner_weightCoordinate hIQ]
  apply Finset.sum_eq_zero
  intro β _
  have hne : a.val ≠ ((fam.innerCoordinate hIQ).symm β).val := by
    intro h
    exact a.property (h.symm ▸ ((fam.innerCoordinate hIQ).symm β).property)
  rw [ite_eq_right hne, mul_zero]

omit [NumberField F] in
private theorem outer_weightCoordinate_outside (x : A → ℝ) (a : {α : R // α ∉ S}) :
    fam.weightCoordinate I (fam.relativeSplitVector Q x) a.val = x (fam.outerCoordinate hIQ a) := by
  rw [← fam.relativeSplitVector_weight Q x (fam.outerCoordinate hIQ a),
    fam.weightCoordinate_formula, fam.weightCoordinate_formula]
  rfl

omit [NumberField F] in
private theorem measurable_outerWeight (a : R) :
    Measurable (fun x : A → ℝ => fam.weightCoordinate I (fam.relativeSplitVector Q x) a) := by
  simp only [fam.weightCoordinate_formula, relativeSplitVector_apply, map_sum, map_smul, smul_eq_mul]
  exact Finset.measurable_sum _ fun b _ => (measurable_pi_apply b).mul_const _

/-- The coordinates of the sum of the outer split vector and the intrinsic inner split
vector, both in the common maximal split torus. -/
def nestedRelativeSplitAdd (z : (A → ℝ) × (B → ℝ)) : R → ℝ :=
  fun a => fam.weightCoordinate I
    (fam.relativeSplitVector Q z.1 + (show V T from (low).relativeSplitVector L z.2)) a

/-- Coroot-coordinate Lebesgue measures for nested split factors multiply exactly. -/
def NestedSplitHaarCoordinatesStatement : Prop :=
  MeasurePreserving (fam.nestedRelativeSplitAdd hIQ) (volume.prod volume) volume ∧
    (∀ z : (A → ℝ) × (B → ℝ),
      fam.relativeSplitVector I (fam.nestedRelativeSplitAdd hIQ z) =
        fam.relativeSplitVector Q z.1 + (show V T from (low).relativeSplitVector L z.2)) ∧
    (∀ z : (A → ℝ) × (B → ℝ),
      fam.relativeSplitAdelicPoint I (fam.nestedRelativeSplitAdd hIQ z) =
        fam.relativeSplitAdelicPoint Q z.1 *
          map F (fam.M Q) G (fam.l Q ≫ fam.p Q) ((low).relativeSplitAdelicPoint L z.2))

set_option maxHeartbeats 2700000 in
theorem nestedSplitHaarCoordinates : fam.NestedSplitHaarCoordinatesStatement hIQ := by
  have hVector (z : (A → ℝ) × (B → ℝ)) :
      fam.relativeSplitVector I (fam.nestedRelativeSplitAdd hIQ z) =
        fam.relativeSplitVector Q z.1 + (show V T from (low).relativeSplitVector L z.2) :=
    fam.relativeSplitVector_weightCoordinate I
      ((VC).add_mem (fam.outer_relativeSplitVector_mem hIQ z.1)
        (fam.inner_relativeSplitVector_mem hIQ z.2))
  refine ⟨?_, hVector, fun z => ?_⟩
  · let e₁ := fam.outerCoordinate hIQ
    let e₂ := fam.innerCoordinate hIQ
    let u := MeasurableEquiv.piCongrLeft (fun _ : {a : R // a ∉ S} => ℝ) e₁.symm
    let v := MeasurableEquiv.piCongrLeft (fun _ : S => ℝ) e₂.symm
    let b := fun (x : {a : R // a ∉ S} → ℝ) (a : S) =>
      fam.weightCoordinate I (fam.relativeSplitVector Q (u.symm x)) a.val
    let shear := fun z : ({a : R // a ∉ S} → ℝ) × (S → ℝ) => (z.1, z.2 + b z.1)
    have hu := volume_measurePreserving_piCongrLeft (fun _ : {a : R // a ∉ S} => ℝ) e₁.symm
    have hv := volume_measurePreserving_piCongrLeft (fun _ : S => ℝ) e₂.symm
    have hb : Measurable b := Measurable.of_eval fun (a : S) =>
      (fam.measurable_outerWeight a.val).comp u.symm.measurable
    have hs : MeasurePreserving shear (volume.prod volume) (volume.prod volume) := by
      refine MeasurePreserving.skew_product (MeasurePreserving.id volume)
        (g := fun x y => y + b x) ?_
        (Filter.Eventually.of_forall fun x => (measurePreserving_add_right volume (b x)).map_eq)
      exact measurable_snd.add (hb.comp measurable_fst)
    let i := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : R => ℝ) (· ∈ S)
    have hi := volume_preserving_piEquivPiSubtypeProd (fun _ : R => ℝ) (· ∈ S)
    have hm := (hi.symm _).comp
      (Measure.measurePreserving_swap.comp (hs.comp (hu.prod hv)))
    convert hm using 1
    funext z
    apply i.injective
    change i (fam.nestedRelativeSplitAdd hIQ z) = i (i.symm ((v z.2 + b (u z.1)), u z.1))
    rw [i.apply_symm_apply]
    apply Prod.ext
    · funext a
      change fam.weightCoordinate I
          (fam.relativeSplitVector Q z.1 + (show V T from (low).relativeSplitVector L z.2)) a.val =
        v z.2 a + fam.weightCoordinate I (fam.relativeSplitVector Q (u.symm (u z.1))) a.val
      rw [u.symm_apply_apply, fam.weightCoordinate_formula, map_add, ← fam.weightCoordinate_formula,
        ← fam.weightCoordinate_formula, fam.inner_weightCoordinate_inside hIQ, add_comm]
      have hv' := MeasurableEquiv.piCongrLeft_apply_apply e₂.symm
        (β := fun _ : S => ℝ) z.2 (e₂ a)
      rw [e₂.symm_apply_apply] at hv'
      exact congrArg (· + fam.weightCoordinate I (fam.relativeSplitVector Q z.1) a.val) hv'.symm
    · funext a
      change fam.weightCoordinate I
          (fam.relativeSplitVector Q z.1 + (show V T from (low).relativeSplitVector L z.2)) a.val =
        u z.1 a
      rw [fam.weightCoordinate_formula, map_add, ← fam.weightCoordinate_formula,
        ← fam.weightCoordinate_formula, fam.inner_weightCoordinate_outside hIQ, add_zero,
        fam.outer_weightCoordinate_outside hIQ]
      have hu' := MeasurableEquiv.piCongrLeft_apply_apply e₁.symm
        (β := fun _ : {a : R // a ∉ S} => ℝ) z.1 (e₁ a)
      rw [e₁.symm_apply_apply] at hu'
      exact hu'.symm
  · obtain ⟨t, ht, htLog⟩ := fam.exists_torusPoint_relativeSplitAdelicPoint I
      (fam.nestedRelativeSplitAdd hIQ z)
    obtain ⟨t₁, ht₁, ht₁Log⟩ := fam.exists_torusPoint_relativeSplitAdelicPoint Q z.1
    obtain ⟨t₂, ht₂, ht₂Log⟩ := (low).exists_torusPoint_relativeSplitAdelicPoint L z.2
    let t₂' : intrinsicSubgroup F fam.T := t₂
    have hc : (low).i ≫ fam.l Q ≫ fam.p Q = fam.i := fam.torus_comp Q
    rw [ht, ht₁, ht₂, ← map_comp_apply_of_hom, hc]
    change map F fam.T.toGrp G fam.i t.val =
      map F fam.T.toGrp G fam.i t₁.val * map F fam.T.toGrp G fam.i t₂'.val
    rw [← map_mul]
    suffices h : t = t₁ * t₂' by
      exact congrArg (fun x : intrinsicSubgroup F T => map F fam.T.toGrp G fam.i x.val) h
    obtain ⟨C, hC, ⟨e⟩⟩ := fam.maximalSplit.isSplitSubtorus.1
    let : Fintype C := Fintype.ofFinite C
    apply (positiveLogEquiv F T C e).injective
    change characterLog F fam.T.toGrp t.val = characterLog F fam.T.toGrp (t₁.val * t₂'.val)
    change characterLog F fam.T.toGrp t₂'.val =
      cocharacterFunctional (show V T from (low).relativeSplitVector L z.2) at ht₂Log
    rw [characterLog_mul, htLog, ht₁Log, ht₂Log, hVector]
    exact (cocharacterFunctionalEquiv fam.maximalSplit.isSplitSubtorus.1).map_add _ _

end Langlands.Global.StandardParabolicFamily
