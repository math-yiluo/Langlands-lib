import Langlands.Geometry.FormalGroup.AtlasRationalHeight
import Langlands.Geometry.FormalGroup.AtlasLocalTests
import Langlands.Geometry.FormalGroup.TensorQuasiIsogenyHeight

/-! # The signed kernel-rank height of an atlas quasi-isogeny -/

noncomputable section

universe u v

namespace Langlands.FormalGroup.ModuleLaw.BasicAtlas.QuasiIsogeny

open CategoryTheory TopologicalSpace

attribute [local instance] coefficientAlgebra coefficientScalarTower

variable {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable [Finite (IsLocalRing.ResidueField O)]
variable {F : Type v} [Field F] [Algebra O F] [IsFractionRing O F]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {σ τ : Type} [Finite σ] [Finite τ]
variable {X : BasicAtlas O R σ} {Y : BasicAtlas O R τ} {h : X.opens = Y.opens}
variable (e : QuasiIsogeny F X Y h) {π : O} (hπ : Irreducible π)

local notation "q" => Nat.card (IsLocalRing.ResidueField O)

variable {d j : ℕ} (hX : ∀ b : X.opens, (X.chart b).HasPiHeight π (Nat.card (IsLocalRing.ResidueField O)) d)
variable (hY : ∀ b : Y.opens, (Y.chart b).HasPiHeight π (Nat.card (IsLocalRing.ResidueField O)) j)
variable (B : CommAlgCat.{v} R) (b : Y.opens) (hb : IsUnit (algebraMap R B b.val))

/-- The actual chart section has its unique signed kernel-rank height. -/
def heightOnChart : (⊤ : Opens (PrimeSpectrum B)) → ℤ :=
  (e.onChart B b hb).heightFunction hπ ((hX (sourceChart h b)).map _) ((hY b).map _)

/-- The chart function is witnessed by local integral numerator and scalar kernels. -/
theorem hasHeightOnChart :
    RationalSection.HasHeightFunction π q (RationalSection.ofGlobal (e.onChart B b hb).hom)
      (e.heightOnChart hπ hX hY B b hb) :=
  (e.onChart B b hb).hasHeightFunction hπ ((hX (sourceChart h b)).map _) ((hY b).map _)

/-- The actual local rank witnesses determine the chart function uniquely. -/
theorem heightOnChart_eq {k : (⊤ : Opens (PrimeSpectrum B)) → ℤ}
    (hk : RationalSection.HasHeightFunction π q (RationalSection.ofGlobal (e.onChart B b hb).hom) k) :
    e.heightOnChart hπ hX hY B b hb = k :=
  (e.onChart B b hb).heightFunction_eq hπ ((hX (sourceChart h b)).map _) ((hY b).map _) hk

omit [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)]
  [IsFractionRing O F] in
private theorem eq_isoTransport_of_square {S : Type v} [CommRing S] [Algebra O S]
    {M M' : ModuleLaw O S σ} {N N' : ModuleLaw O S τ}
    (a : ModuleLaw.Iso M M') (b : ModuleLaw.Iso N N') (f : ModuleLaw.RationalHom F M N)
    (g : ModuleLaw.RationalHom F M' N')
    (hh : ModuleLaw.RationalHom.comp g (ModuleLaw.RationalHom.ofHom a.hom) =
      ModuleLaw.RationalHom.comp (ModuleLaw.RationalHom.ofHom b.hom) f) :
    g = ModuleLaw.RationalHom.isoTransport a b f := by
  rw [ModuleLaw.RationalHom.isoTransport_eq_comp, ← ModuleLaw.RationalHom.comp_assoc, ← hh,
    ModuleLaw.RationalHom.comp_assoc, ← ModuleLaw.RationalHom.ofHom_comp, a.hom_inv,
    ModuleLaw.RationalHom.ofHom_id, ModuleLaw.RationalHom.comp_id]

/-- The chart height pulls back along an actual coefficient map. -/
theorem heightOnChart_natural {A : CommAlgCat.{v} R} (φ : A ⟶ B)
    (ha : IsUnit (algebraMap R A b.val)) :
    e.heightOnChart hπ hX hY B b hb = e.heightOnChart hπ hX hY A b ha ∘
      coefficientOpenPoint (φ.hom.restrictScalars O) ⊤ := by
  let ψ := φ.hom.restrictScalars O
  let z := e.onChart A b ha
  let w := e.onChart B b hb
  let a := coefficientTriangleIso (X.chart (sourceChart h b)) φ ha hb
  let g := coefficientTriangleIso (Y.chart b) φ ha hb
  let hM := (hX (sourceChart h b)).map (coefficientLift (O := O) b.val A ha)
  let hN := (hY b).map (coefficientLift (O := O) b.val A ha)
  have he : w.hom = ModuleLaw.RationalHom.isoTransport a g (z.map ψ).hom :=
    eq_isoTransport_of_square a g _ _ (e.hom.onChart_natural φ b ha hb)
  have ht := (z.map ψ).heightFunction_eq_of_isoTransport hπ (hM.map ψ) (hN.map ψ) a g (e' := w) he
  have hm := z.heightFunction_eq_of_map hπ hM hN ψ (z.map ψ) rfl
  exact ht.trans hm

/-- The actual chart transition preserves the height over a common test algebra. -/
theorem heightOnChart_transition (c : Y.opens) (hc : IsUnit (algebraMap R B c.val)) :
    e.heightOnChart hπ hX hY B c hc = e.heightOnChart hπ hX hY B b hb := by
  let z := e.onChart B b hb
  let w := e.onChart B c hc
  let a := X.transition B (sourceChart h b) (sourceChart h c) hb hc
  let g := Y.transition B b c hb hc
  let hM := (hX (sourceChart h b)).map (coefficientLift (O := O) b.val B hb)
  let hN := (hY b).map (coefficientLift (O := O) b.val B hb)
  have he : w.hom = ModuleLaw.RationalHom.isoTransport a g z.hom :=
    eq_isoTransport_of_square a g _ _ (e.hom.onChart_transition B b c hb hc).symm
  exact z.heightFunction_eq_of_isoTransport hπ hM hN a g w he


omit [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] in
private theorem exists_chart_at (Y : BasicAtlas O R τ) (x : PrimeSpectrum R) :
    ∃ b : Y.opens, b.val ∉ x.asIdeal := by
  by_contra! he
  have hh : Ideal.span Y.opens ≤ x.asIdeal := Ideal.span_le.mpr (fun a ha => he ⟨a, ha⟩)
  rw [Y.covers] at hh
  exact x.isPrime.ne_top (top_unique hh)

private def chartAt (Y : BasicAtlas O R τ) (x : PrimeSpectrum R) : Y.opens :=
  (exists_chart_at Y x).choose

omit [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] in
private theorem chartAt_notMem (Y : BasicAtlas O R τ) (x : PrimeSpectrum R) :
    (chartAt Y x).val ∉ x.asIdeal :=
  (exists_chart_at Y x).choose_spec

private theorem exists_away_lift {S : Type v} [CommRing S] {r : S} {x : PrimeSpectrum S}
    (hx : r ∉ x.asIdeal) : ∃ y : PrimeSpectrum (Localization.Away r),
      y.comap (algebraMap S (Localization.Away r)) = x := by
  change x ∈ Set.range (PrimeSpectrum.comap (algebraMap S (Localization.Away r)))
  rw [PrimeSpectrum.localization_away_comap_range (Localization.Away r) r]
  exact (PrimeSpectrum.mem_basicOpen r x).mpr hx

private def primeOnChart (Y : BasicAtlas O R τ) (x : PrimeSpectrum R) :
    PrimeSpectrum (Localization.Away (chartAt Y x).val) :=
  (exists_away_lift (chartAt_notMem Y x)).choose

omit [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] in
private theorem primeOnChart_comap (Y : BasicAtlas O R τ) (x : PrimeSpectrum R) :
    (primeOnChart Y x).comap (algebraMap R (Localization.Away (chartAt Y x).val)) = x :=
  (exists_away_lift (chartAt_notMem Y x)).choose_spec

/-- The signed height on the actual base spectrum, computed on any chart containing the point. -/
def heightFunction (x : PrimeSpectrum R) : ℤ :=
  let c := chartAt Y x
  e.heightOnChart hπ hX hY (CommAlgCat.of R (Localization.Away c.val)) c
    (IsLocalization.Away.algebraMap_isUnit c.val) ⟨primeOnChart Y x, by trivial⟩

private theorem comap_to_base {A C : CommAlgCat.{v} R} (φ : A ⟶ C) (y : PrimeSpectrum C) :
    (y.comap φ.hom.toRingHom).comap (algebraMap R A) = y.comap (algebraMap R C) := by
  have he : φ.hom.toRingHom.comp (algebraMap R A) = algebraMap R C := RingHom.ext φ.hom.commutes
  rw [← PrimeSpectrum.comap_comp_apply, he]

/-- Every test chart reads the same height after mapping its prime to the base. -/
theorem heightOnChart_eq_heightFunction (x : (⊤ : Opens (PrimeSpectrum B))) :
    e.heightOnChart hπ hX hY B b hb x =
      e.heightFunction hπ hX hY (x.val.comap (algebraMap R B)) := by
  let p := x.val.comap (algebraMap R B)
  let c := chartAt Y p
  let C := CommAlgCat.of R (Localization.Away c.val)
  let hc : IsUnit (algebraMap R C c.val) := IsLocalization.Away.algebraMap_isUnit c.val
  let E := Y.localAlgebra B c
  let φ := Y.localizationMap B c
  let hc' := Y.localUnit B c
  let hb' := unit_map φ hb
  let ψ : C ⟶ E := CommAlgCat.ofHom
    (IsLocalization.Away.liftAlgHom c.val (f := Algebra.ofId R E) hc')
  have hunit : algebraMap R B c.val ∉ x.val.asIdeal := chartAt_notMem Y p
  obtain ⟨y, hy⟩ := exists_away_lift hunit
  let y' : (⊤ : Opens (PrimeSpectrum E)) := ⟨y, by trivial⟩
  have hx : coefficientOpenPoint (φ.hom.restrictScalars O) ⊤ y' = x := Subtype.ext hy
  have hw : coefficientOpenPoint (ψ.hom.restrictScalars O) ⊤ y' =
      (⟨primeOnChart Y p, by trivial⟩ : (⊤ : Opens (PrimeSpectrum C))) := by
    apply Subtype.ext
    apply (PrimeSpectrum.localization_away_isOpenEmbedding (Localization.Away c.val) c.val).injective
    change (y.comap ψ.hom.toRingHom).comap (algebraMap R C) =
      (primeOnChart Y p).comap (algebraMap R C)
    rw [comap_to_base ψ y, primeOnChart_comap, ← comap_to_base φ y]
    exact congrArg (PrimeSpectrum.comap (algebraMap R B)) hy
  have ha := congrFun (e.heightOnChart_natural hπ hX hY E b hb' φ hb) y'
  have hd := congrFun (e.heightOnChart_transition hπ hX hY E b hb' c hc') y'
  have he := congrFun (e.heightOnChart_natural hπ hX hY E c hc' ψ hc) y'
  change _ = e.heightOnChart hπ hX hY B b hb (coefficientOpenPoint (φ.hom.restrictScalars O) ⊤ y') at ha
  change _ = e.heightOnChart hπ hX hY C c hc (coefficientOpenPoint (ψ.hom.restrictScalars O) ⊤ y') at he
  rw [hx] at ha
  rw [hw] at he
  exact ha.symm.trans (hd.symm.trans he)

/-- The signed height of an atlas rigidifier is locally constant on its base spectrum. -/
theorem isLocallyConstant_heightFunction : IsLocallyConstant (e.heightFunction hπ hX hY) := by
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  let c := chartAt Y x
  let C := CommAlgCat.of R (Localization.Away c.val)
  let hc : IsUnit (algebraMap R C c.val) := IsLocalization.Away.algebraMap_isUnit c.val
  let y := primeOnChart Y x
  let ι := PrimeSpectrum.comap (algebraMap R C)
  have hι := PrimeSpectrum.localization_away_isOpenEmbedding (Localization.Away c.val) c.val
  have hy : ι y = x := primeOnChart_comap Y x
  let : Algebra O C := coefficientAlgebra C
  let topPoint : PrimeSpectrum C → (⊤ : Opens (PrimeSpectrum C)) := fun z => ⟨z, by trivial⟩
  have ht : Continuous topPoint := continuous_id.subtype_mk (fun _ => by trivial)
  let k := e.heightOnChart hπ hX hY C c hc ∘ topPoint
  have hlocal : IsLocallyConstant (e.heightOnChart hπ hX hY C c hc) :=
    (e.hasHeightOnChart hπ hX hY C c hc).isLocallyConstant
  have hk : IsLocallyConstant k := hlocal.comp_continuous ht
  rw [IsLocallyConstant.iff_exists_open] at hk
  obtain ⟨V, hV, hyV, hconst⟩ := hk y
  refine ⟨ι '' V, hι.isOpenMap _ hV, ⟨y, hyV, hy⟩, ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  have hz' : k z = e.heightFunction hπ hX hY (ι z) :=
    e.heightOnChart_eq_heightFunction hπ hX hY C c hc ⟨z, by trivial⟩
  have hy' : k y = e.heightFunction hπ hX hY x :=
    (e.heightOnChart_eq_heightFunction hπ hX hY C c hc ⟨y, by trivial⟩).trans
      (congrArg (e.heightFunction hπ hX hY) hy)
  exact hz'.symm.trans ((hconst z hz).trans hy')


/-- On a chart test the pulled-back base height is verified by the actual local rank witnesses. -/
theorem hasHeightFunction_onChart :
    RationalSection.HasHeightFunction π q (RationalSection.ofGlobal (e.onChart B b hb).hom)
      (fun x => e.heightFunction hπ hX hY (x.val.comap (algebraMap R B))) := by
  have he := funext (e.heightOnChart_eq_heightFunction hπ hX hY B b hb)
  exact he ▸ e.hasHeightOnChart hπ hX hY B b hb

/-- A constant value for the base height is equivalent to that verified value on all test charts. -/
theorem hasConstantChartHeight_iff (n : ℤ) :
    e.hom.HasConstantChartHeight π q n ↔ ∀ x, e.heightFunction hπ hX hY x = n := by
  constructor
  · intro hh x
    let c := chartAt Y x
    let C := CommAlgCat.of R (Localization.Away c.val)
    let hc : IsUnit (algebraMap R C c.val) := IsLocalization.Away.algebraMap_isUnit c.val
    let y : (⊤ : Opens (PrimeSpectrum C)) := ⟨primeOnChart Y x, by trivial⟩
    exact congrFun (e.heightOnChart_eq hπ hX hY C c hc (hh C c hc)) y
  · intro hh B b hb
    have hs := e.hasHeightFunction_onChart hπ hX hY B b hb
    have he : (fun x : (⊤ : Opens (PrimeSpectrum B)) => e.heightFunction hπ hX hY
      (x.val.comap (algebraMap R B))) = (fun _ => n) := funext fun x => hh _
    exact he ▸ hs

end Langlands.FormalGroup.ModuleLaw.BasicAtlas.QuasiIsogeny
