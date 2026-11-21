import Langlands.Geometry.FormalGroup.TensorQuasiIsogenyHeight
import Langlands.Geometry.FormalGroup.AtlasRationalHeightBaseChange
import Langlands.Geometry.FormalGroup.NilpotentAtlasRationalLift
import Mathlib.RingTheory.Spectrum.Prime.RingHom

/-! # The height of a quasi-isogeny reflected by nilpotent reduction -/

noncomputable section

universe u v w

namespace Langlands.FormalGroup.ModuleLaw

open CategoryTheory TopologicalSpace

attribute [local instance] coefficientAlgebra coefficientScalarTower

variable {O : Type u} [CommRing O]
variable {R S : Type v} [CommRing R] [CommRing S] [Algebra O R] [Algebra O S]
variable {F : Type v} [Field F] [Algebra O F]
variable {σ τ : Type} [Finite σ] [Finite τ]
variable {M M' : ModuleLaw O R σ} {N N' : ModuleLaw O R τ}

private theorem coefficientSpectrumMap_surjective (φ : R →ₐ[O] S)
    (hφ : Function.Surjective φ) (hI : IsNilpotent (RingHom.ker φ.toRingHom)) :
    Function.Surjective (coefficientSpectrumMap φ) := by
  rw [← Set.range_eq_univ]
  change Set.range (PrimeSpectrum.comap φ.toRingHom) = Set.univ
  rw [range_comap_of_surjective _ _ hφ, PrimeSpectrum.zeroLocus_eq_univ_iff]
  intro a ha
  obtain ⟨n, hn⟩ := hI
  have hp := Ideal.pow_mem_pow ha n
  rw [show RingHom.ker φ.toRingHom ^ n = ⊥ from hn, Ideal.mem_bot] at hp
  exact mem_nilradical.mpr ⟨n, hp⟩

namespace RationalHom

variable {f : RationalHom F M N} {g : RationalHom F M' N'}

private theorem eq_isoTransport_of_comp_eq (a : Iso M M') (b : Iso N N')
    (h : comp g (ofHom a.hom) = comp (ofHom b.hom) f) :
    g = isoTransport a b f := by
  calc
    g = comp g (comp (ofHom a.hom) (ofHom a.inv)) := by
      rw [← ofHom_comp, a.hom_inv, ofHom_id, comp_id]
    _ = isoTransport a b f := by
      rw [← comp_assoc, h, comp_assoc, isoTransport_eq_comp]

private theorem isoTransport_symm_cancel (a : Iso M M') (b : Iso N N') (f : RationalHom F M N) :
    isoTransport a.symm b.symm (isoTransport a b f) = f := by
  rw [isoTransport_eq_comp, isoTransport_eq_comp]
  change comp (ofHom b.inv) (comp (comp (ofHom b.hom) (comp f (ofHom a.inv)))
    (ofHom a.hom)) = f
  rw [comp_assoc (ofHom b.hom), ← comp_assoc (ofHom b.inv), comp_assoc f,
    ← ofHom_comp, ← ofHom_comp, b.inv_hom, a.inv_hom, ofHom_id, ofHom_id, id_comp, comp_id]

end RationalHom

namespace RationalSection.HasHeightFunction

private theorem ofGlobal_isoTransport_iff {f : RationalHom F M N}
    {π : O} {q : ℕ} {k : (⊤ : Opens (PrimeSpectrum R)) → ℤ}
    (a : Iso M M') (b : Iso N N') :
    HasHeightFunction π q (ofGlobal (RationalHom.isoTransport a b f)) k ↔
      HasHeightFunction π q (ofGlobal f) k := by
  refine ⟨fun hf => ?_, fun hf => hf.ofGlobal_isoTransport a b⟩
  have hh := hf.ofGlobal_isoTransport a.symm b.symm
  rw [RationalHom.isoTransport_symm_cancel] at hh
  exact hh

end RationalSection.HasHeightFunction

namespace QuasiIsogeny

variable [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)]
variable [IsFractionRing O F]
variable {π : O} {d j : ℕ} {n : ℤ}

local notation "q" => Nat.card (IsLocalRing.ResidueField O)

/-- The actual signed height of an invertible tensor is constant if its nilpotent reduction has that height. -/
theorem hasHeightFunction_of_map_of_nilpotent (e : QuasiIsogeny F M N) (hπ : Irreducible π)
    (hM : M.HasPiHeight π q d) (hN : N.HasPiHeight π q j) (φ : R →ₐ[O] S)
    (hφ : Function.Surjective φ) (hI : IsNilpotent (RingHom.ker φ.toRingHom))
    (hz : RationalSection.HasHeightFunction π q
      (RationalSection.ofGlobal (RationalHom.map φ e.hom)) (fun _ => n)) :
    RationalSection.HasHeightFunction π q (RationalSection.ofGlobal e.hom) (fun _ => n) := by
  let e' := e.map φ
  have he := e.heightFunction_eq_of_map hπ hM hN φ e' rfl
  have hh := e'.heightFunction_eq hπ (hM.map φ) (hN.map φ) hz
  have hk : e.heightFunction hπ hM hN = fun _ => n := by
    funext x
    obtain ⟨y, hy⟩ := coefficientSpectrumMap_surjective φ hφ hI x.val
    let p : (coefficientOpenMap φ).obj ⊤ := ⟨y, trivial⟩
    have hp : coefficientOpenPoint φ ⊤ p = x := Subtype.ext hy
    have ht := congrFun (he.symm.trans hh) p
    change e.heightFunction hπ hM hN (coefficientOpenPoint φ ⊤ p) = n at ht
    rwa [hp] at ht
  rw [← hk]
  exact e.hasHeightFunction hπ hM hN

end QuasiIsogeny

namespace BasicAtlas.QuasiIsogeny

variable [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)]
variable [IsFractionRing O F] {π : O} {d j : ℕ} {n : ℤ}
variable {X : BasicAtlas O R σ} {Y : BasicAtlas O R τ} {h : X.opens = Y.opens}

local notation "q" => Nat.card (IsLocalRing.ResidueField O)

set_option backward.isDefEq.respectTransparency false in
/-- Height is reflected on the actual atlas, including when image generators coincide. -/
theorem hasConstantChartHeight_of_baseChange_of_nilpotent (e : BasicAtlas.QuasiIsogeny F X Y h)
    (hπ : Irreducible π) (T : CommAlgCat.{v} R)
    (hT : Function.Surjective (algebraMap R T))
    (hI : IsNilpotent (RingHom.ker (algebraMap R T)))
    (hX : ∀ a : X.opens, (X.chart a).HasPiHeight π q d)
    (hY : ∀ b : Y.opens, (Y.chart b).HasPiHeight π q j)
    (hz : (e.baseChange T).hom.HasConstantChartHeight π q n) :
    e.hom.HasConstantChartHeight π q n := by
  intro A b hb
  let B := quotientTest T hT A
  let A' := restrictTest T B
  let β := quotientTestProjection T hT A
  let hb' := unit_map β hb
  let b₀ := Y.imageChart T b
  let hb₀ := Y.imageChart_unit T B b hb'
  let c := Y.baseSource T b₀
  let hc := Y.baseSource_unit T B b₀ hb₀
  have he := hz B b₀ hb₀
  change RationalSection.HasHeightFunction π q (RationalSection.ofGlobal
    (BasicAtlas.RationalHom.onChart (X := X.baseChange T) (h := baseOpens_eq T h)
      B b₀ hb₀ (BasicAtlas.RationalHom.baseChange T e.hom))) (fun _ => n) at he
  rw [BasicAtlas.RationalHom.onChart_baseChange e.hom T B b₀ hb₀] at he
  have hc_height : RationalSection.HasHeightFunction π q (RationalSection.ofGlobal
      (BasicAtlas.RationalHom.onChart (X := X) (h := h) A' c hc e.hom)) (fun _ => n) := by
    apply (RationalSection.HasHeightFunction.ofGlobal_isoTransport_iff
      (baseSourceChartIso T h B b₀ hb₀).symm (Y.baseChartIso T B b₀ hb₀).symm).mp
    rw [ModuleLaw.RationalHom.isoTransport_eq_comp]
    exact he
  have hb_height : RationalSection.HasHeightFunction π q (RationalSection.ofGlobal
      (BasicAtlas.RationalHom.onChart (X := X) (h := h) A' b hb' e.hom)) (fun _ => n) := by
    let a := X.transition A' (sourceChart h c) (sourceChart h b) hc hb'
    let t := Y.transition A' c b hc hb'
    rw [ModuleLaw.RationalHom.eq_isoTransport_of_comp_eq a t
      (e.hom.onChart_transition A' c b hc hb').symm]
    exact hc_height.ofGlobal_isoTransport a t
  let ix := coefficientTriangleIso (X.chart (sourceChart h b)) β hb hb'
  let iy := coefficientTriangleIso (Y.chart b) β hb hb'
  let eA := e.onChart A b hb
  have hmap : RationalSection.HasHeightFunction π q (RationalSection.ofGlobal
      (ModuleLaw.RationalHom.map (β.hom.restrictScalars O) eA.hom)) (fun _ => n) := by
    apply (RationalSection.HasHeightFunction.ofGlobal_isoTransport_iff ix iy).mp
    change RationalSection.HasHeightFunction π q (RationalSection.ofGlobal
      (ModuleLaw.RationalHom.isoTransport ix iy (ModuleLaw.RationalHom.map (β.hom.restrictScalars O)
        (BasicAtlas.RationalHom.onChart (X := X) (h := h) A b hb e.hom)))) (fun _ => n)
    rw [← ModuleLaw.RationalHom.eq_isoTransport_of_comp_eq ix iy
      (e.hom.onChart_natural β b hb hb')]
    exact hb_height
  exact eA.hasHeightFunction_of_map_of_nilpotent hπ
    ((hX (sourceChart h b)).map (coefficientLift (O := O) b.val A hb))
    ((hY b).map (coefficientLift (O := O) b.val A hb))
    (β.hom.restrictScalars O) (quotientTestProjection_surjective T hT A)
    (quotientTestProjection_nilpotent T hT hI A) hmap

end BasicAtlas.QuasiIsogeny

namespace BasicAtlas.OrderAction.QuasiIsogeny

variable [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)]
variable [IsFractionRing O F] {π : O} {d j : ℕ} {n : ℤ}
variable {X : BasicAtlas O R σ} {Y : BasicAtlas O R τ} {h : X.opens = Y.opens}
variable {D : Type w} [Ring D] [Algebra O D]
variable {E : BasicAtlas.OrderAction D X} {G : BasicAtlas.OrderAction D Y}

local notation "q" => Nat.card (IsLocalRing.ResidueField O)

/-- The constant kernel-rank height of a full-order quasi-isogeny is equivalent to its reduced height. -/
theorem hasConstantChartHeight_baseChange_iff_of_nilpotent
    (e : BasicAtlas.OrderAction.QuasiIsogeny F E G h) (hπ : Irreducible π)
    (T : CommAlgCat.{v} R) (hT : Function.Surjective (algebraMap R T))
    (hI : IsNilpotent (RingHom.ker (algebraMap R T)))
    (hX : ∀ a : X.opens, (X.chart a).HasPiHeight π q d)
    (hY : ∀ b : Y.opens, (Y.chart b).HasPiHeight π q j) :
    (e.baseChange T).hom.val.HasConstantChartHeight π q n ↔
      e.hom.val.HasConstantChartHeight π q n :=
  ⟨e.toAtlasQuasiIsogeny.hasConstantChartHeight_of_baseChange_of_nilpotent hπ T hT hI hX hY,
    fun hh => hh.baseChange T⟩

set_option backward.isDefEq.respectTransparency false in
/-- Nilpotent reduction on the finite principal cover lifts full-order framings with their exact height. -/
def finiteNilpotentHeightEquiv [Finite Y.opens] (hπ : Irreducible π)
    (T : CommAlgCat.{v} R) (hT : Function.Surjective (algebraMap R T))
    (hI : IsNilpotent (RingHom.ker (algebraMap R T)))
    (hX : ∀ a : X.opens, (X.chart a).HasPiHeight π q d)
    (hY : ∀ b : Y.opens, (Y.chart b).HasPiHeight π q j)
    (hi : Set.InjOn (algebraMap R T) Y.opens) (n : ℤ) :
    {e : BasicAtlas.OrderAction.QuasiIsogeny F E G h //
      e.hom.val.HasConstantChartHeight π q n} ≃
    {e : BasicAtlas.OrderAction.QuasiIsogeny F (E.baseChange T) (G.baseChange T)
      (baseOpens_eq T h) // e.hom.val.HasConstantChartHeight π q n} := by
  let reduce (e : {e : BasicAtlas.OrderAction.QuasiIsogeny F E G h //
      e.hom.val.HasConstantChartHeight π q n}) :
      {f : BasicAtlas.OrderAction.QuasiIsogeny F (E.baseChange T) (G.baseChange T)
        (baseOpens_eq T h) // f.hom.val.HasConstantChartHeight π q n} :=
    ⟨e.val.baseChange T, e.property.baseChange T⟩
  have he := baseChange_bijective_of_finite_of_nilpotent (F := F) (E := E) (G := G) (h := h)
    T hT hI (fun a => (hX a).piDivisible) (fun b => (hY b).piDivisible) hi hπ.ne_zero
  refine Equiv.ofBijective reduce ⟨?_, ?_⟩
  · intro f g efg
    exact Subtype.ext (he.injective (congrArg Subtype.val efg))
  · intro g
    obtain ⟨f, hf⟩ := he.surjective g.val
    change f.baseChange T = g.val at hf
    have hz : (f.baseChange T).hom.val.HasConstantChartHeight π q n := by
      rw [hf]
      exact g.property
    refine ⟨⟨f, (f.hasConstantChartHeight_baseChange_iff_of_nilpotent hπ T hT hI hX hY).mp hz⟩, ?_⟩
    exact Subtype.ext hf

end BasicAtlas.OrderAction.QuasiIsogeny

end Langlands.FormalGroup.ModuleLaw
