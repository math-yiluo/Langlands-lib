import Langlands.Geometry.FormalGroup.CentralOrderAtlasHom
import Langlands.Geometry.FormalGroup.DivisionImageAtlasHom
import Langlands.Geometry.FormalGroup.FieldScalarIsogenyPresentation
import Langlands.Geometry.FormalGroup.AtlasOrderRationalMorphism

/-! # The central tensor quasi-isogeny of a split primal image atlas -/

noncomputable section

universe u v w c s t

namespace Langlands.FormalGroup.ModuleLaw.IdempotentImageCover

open CategoryTheory BasicAtlas

attribute [local instance] coefficientAlgebra coefficientScalarTower

set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

variable {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {D : Type w} [Ring D] [Algebra O D]
variable {C : Type c} [CommRing C] [IsDomain C] [Algebra C D] [Algebra C R]
variable {F : Type s} [Field F] [Algebra O F] [IsFractionRing O F]
variable {K : Type t} [Field K] [Algebra C K] [IsFractionRing C K]
variable {σ τ σ' τ' : Type} [Finite σ] [Finite τ] [Finite σ'] [Finite τ']
variable {M : ModuleLaw O R σ} {N : ModuleLaw O R τ}
variable {E : ModuleLaw.OrderAction (Dᵐᵒᵖ × D) M} {G : ModuleLaw.OrderAction (Dᵐᵒᵖ × D) N}
variable (I : IdempotentImageCover E.divisionProjector σ') (J : IdempotentImageCover G.divisionProjector τ')
variable {h : I.atlas.opens = J.atlas.opens}
variable (hs : ∀ (b : I.atlas.opens) (a : C) (x : σ' → Localization.Away b.val),
  ((I.divisionOrder E).chart b).fiberTangent (RingHom.id _) (algebraMap C D a) x =
    algebraMap C (Localization.Away b.val) a • x)
variable (ht : ∀ (b : J.atlas.opens) (a : C) (x : τ' → Localization.Away b.val),
  ((J.divisionOrder G).chart b).fiberTangent (RingHom.id _) (algebraMap C D a) x =
    algebraMap C (Localization.Away b.val) a • x)

omit [IsDomain O] [IsDiscreteValuationRing O] in
private theorem restrictDivisionHom_scalar (f : ModuleLaw.OrderAction.Hom E E) (a : O)
    (hf : f.val = M.scalarHom a) :
    I.restrictDivisionHom I (h := rfl) f = BasicAtlas.OrderAction.Hom.scalarHom (I.divisionOrder E) a := by
  apply Subtype.ext
  apply BasicAtlas.Hom.ext
  intro B b hb
  let φ := IsScalarTower.toAlgHom O R B
  let j := (I.image b).2.overChartTest B hb
  change j.restrictHom j (f.val.map φ) =
    ((I.atlas.chart b).map (coefficientLift (O := O) b.val B hb)).scalarHom a
  rw [hf, scalarHom_map, scalarHom, ModuleLaw.Hom.IdempotentImage.restrictHom,
    ModuleLaw.Hom.smul_comp, ModuleLaw.Hom.comp_smul, ModuleLaw.Hom.id_comp,
    j.projection_inclusion]
  rfl

private def numeratorOfClearing {A : Type w} [Ring A] [Algebra O A]
    {U : ModuleLaw.OrderAction A M} {V : ModuleLaw.OrderAction A N}
    (z : ModuleLaw.OrderAction.RationalHom F U V) {a : O} (ha : Irreducible a)
    (hM : M.IsPiDivisible a) {n : ℕ} (f : ModuleLaw.Hom M N)
    (hf : (algebraMap O F a) ^ n • z.val = ModuleLaw.RationalHom.ofHom f) :
    ModuleLaw.OrderAction.Hom U V :=
  ⟨f, fun x => by
    apply ModuleLaw.RationalHom.ofHom_injective_of_piDivisible (F := F) ha hM
    rw [ModuleLaw.RationalHom.ofHom_comp, ModuleLaw.RationalHom.ofHom_comp, ← hf,
      ModuleLaw.RationalHom.smul_comp, ModuleLaw.RationalHom.comp_smul, z.commutes]⟩

omit [IsDomain C] [IsFractionRing C K] in
private theorem rationalize_scalar {X : BasicAtlas C R σ'} {A : BasicAtlas.OrderAction D X} (a : C) :
    BasicAtlas.OrderAction.RationalHom.ofHom (F := K) (BasicAtlas.OrderAction.Hom.scalarHom A a) =
      algebraMap C K a • BasicAtlas.OrderAction.RationalHom.id A := by
  apply BasicAtlas.OrderAction.RationalHom.ext
  change BasicAtlas.RationalHom.ofHom (F := K) (a • BasicAtlas.Hom.id X) =
    algebraMap C K a • BasicAtlas.RationalHom.ofHom (BasicAtlas.Hom.id X)
  rw [map_smul, IsScalarTower.algebraMap_smul]

/-- Restrict the two globally cleared integral numerators to the actual division-image
atlases, change their central scalars, and divide by the same natural-number powers. -/
def restrictCentralQuasiIsogeny (z : ModuleLaw.OrderAction.QuasiIsogeny F E G) {p : ℕ}
    (hp : Irreducible (p : O)) (hpK : (p : K) ≠ 0)
    (hM : M.IsPiDivisible (p : O)) (hN : N.IsPiDivisible (p : O)) :
    BasicAtlas.OrderAction.QuasiIsogeny K
      ((I.divisionOrder E).centralAtlasOrder hs) ((J.divisionOrder G).centralAtlasOrder ht) h := by
  let hf := ModuleLaw.RationalHom.exists_uniformizerPower_ofHom hp z.hom.val
  let hg := ModuleLaw.RationalHom.exists_uniformizerPower_ofHom hp z.inv.val
  let n := hf.choose
  let m := hg.choose
  let f := numeratorOfClearing z.hom hp hM hf.choose_spec.choose hf.choose_spec.choose_spec
  let g := numeratorOfClearing z.inv hp hN hg.choose_spec.choose hg.choose_spec.choose_spec
  let fC := (I.restrictDivisionHom J (h := h) f).centralScalars hs ht
  let gC := (J.restrictDivisionHom I (h := h.symm) g).centralScalars ht hs
  have hfg := z.toModuleQuasiIsogeny.scalarComposites hp hM hN
    hf.choose_spec.choose_spec hg.choose_spec.choose_spec
  have hleft : gC.comp fC = BasicAtlas.OrderAction.Hom.scalarHom
      ((I.divisionOrder E).centralAtlasOrder hs) ((p : C) ^ (m + n)) := by
    dsimp only [fC, gC]
    rw [← BasicAtlas.OrderAction.Hom.centralScalars_comp, ← restrictDivisionHom_comp,
      restrictDivisionHom_scalar I (g.comp f) _ hfg.1,
      ← Nat.cast_pow (α := O), BasicAtlas.OrderAction.Hom.centralScalars_scalarNatCast, Nat.cast_pow]
  have hright : fC.comp gC = BasicAtlas.OrderAction.Hom.scalarHom
      ((J.divisionOrder G).centralAtlasOrder ht) ((p : C) ^ (m + n)) := by
    dsimp only [fC, gC]
    rw [← BasicAtlas.OrderAction.Hom.centralScalars_comp, ← restrictDivisionHom_comp,
      restrictDivisionHom_scalar J (f.comp g) _ hfg.2,
      ← Nat.cast_pow (α := O), BasicAtlas.OrderAction.Hom.centralScalars_scalarNatCast, Nat.cast_pow]
  let a := (p : K) ^ m
  let b := (p : K) ^ n
  have ha : a ≠ 0 := pow_ne_zero _ hpK
  have hb : b ≠ 0 := pow_ne_zero _ hpK
  have hn : algebraMap C K ((p : C) ^ (m + n)) = a * b := by
    rw [map_pow, map_natCast, pow_add]
  refine ⟨b⁻¹ • BasicAtlas.OrderAction.RationalHom.ofHom fC,
    a⁻¹ • BasicAtlas.OrderAction.RationalHom.ofHom gC, ?_, ?_⟩
  · rw [BasicAtlas.OrderAction.RationalHom.smul_comp, BasicAtlas.OrderAction.RationalHom.comp_smul,
      ← BasicAtlas.OrderAction.RationalHom.ofHom_comp, hleft, rationalize_scalar, hn,
      smul_smul, smul_smul]
    rw [show a⁻¹ * b⁻¹ * (a * b) = 1 by field_simp, one_smul]
  · rw [BasicAtlas.OrderAction.RationalHom.smul_comp, BasicAtlas.OrderAction.RationalHom.comp_smul,
      ← BasicAtlas.OrderAction.RationalHom.ofHom_comp, hright, rationalize_scalar, hn,
      smul_smul, smul_smul]
    rw [show b⁻¹ * a⁻¹ * (a * b) = 1 by field_simp, one_smul]

/-- The forward atlas tensor and the ambient tensor have a common integral presentation
under restriction to the image and change of scalars. -/
theorem restrictCentralQuasiIsogeny_forwardPresentation (z : ModuleLaw.OrderAction.QuasiIsogeny F E G)
    {p : ℕ} (hp : Irreducible (p : O)) (hpK : (p : K) ≠ 0)
    (hM : M.IsPiDivisible (p : O)) (hN : N.IsPiDivisible (p : O)) :
    ∃ (n : ℕ) (f : ModuleLaw.OrderAction.Hom E G),
      (algebraMap O F (p : O)) ^ n • z.hom.val = ModuleLaw.RationalHom.ofHom f.val ∧
      (I.restrictCentralQuasiIsogeny J (h := h) hs ht z hp hpK hM hN).hom =
        ((p : K) ^ n)⁻¹ • BasicAtlas.OrderAction.RationalHom.ofHom
          ((I.restrictDivisionHom J (h := h) f).centralScalars hs ht) := by
  let hf := ModuleLaw.RationalHom.exists_uniformizerPower_ofHom hp z.hom.val
  exact ⟨hf.choose, numeratorOfClearing z.hom hp hM hf.choose_spec.choose hf.choose_spec.choose_spec,
    hf.choose_spec.choose_spec, rfl⟩

end Langlands.FormalGroup.ModuleLaw.IdempotentImageCover
