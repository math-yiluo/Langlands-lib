import Langlands.AbelianScheme.PolarizedFiniteLevel.PolarizationIsoTransport
import Langlands.AbelianScheme.PolarizedFiniteLevel.PolarizationRayPositivityStatement
import Langlands.AbelianScheme.Tate.PrimitiveHom

/-! # Transport of primitive polarization factors along isomorphisms -/

universe u

open CategoryTheory AlgebraicGeometry

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

open Langlands.AlgebraicGeometry.FiniteEtale

variable (P : Prerequisites.{u}) {S : Scheme.{u}} {A B : AbelianScheme S}

/-- Transport along an isomorphism is additive in the transported map. -/
theorem DualWitness.transportMap_nsmul (e : A ≅ B) (WA : DualWitness A) (WB : DualWitness B)
    (k : ℕ) (lam : B ⟶ WB.dual P) :
    DualWitness.transportMap P e WA WB (k • lam) = k • DualWitness.transportMap P e WA WB lam := by
  simp only [DualWitness.transportMap, Preadditive.nsmul_comp, Preadditive.comp_nsmul]

/-- Transport along an isomorphism is additive in the transported map, for integer
multiples. -/
theorem DualWitness.transportMap_zsmul (e : A ≅ B) (WA : DualWitness A) (WB : DualWitness B)
    (k : ℤ) (lam : B ⟶ WB.dual P) :
    DualWitness.transportMap P e WA WB (k • lam) = k • DualWitness.transportMap P e WA WB lam := by
  simp only [DualWitness.transportMap, Preadditive.zsmul_comp, Preadditive.comp_zsmul]

/-- Transporting back along the inverse isomorphism recovers the original map. -/
theorem DualWitness.transportMap_symm_transportMap (e : A ≅ B) (WA : DualWitness A)
    (WB : DualWitness B) (lam : B ⟶ WB.dual P) :
    DualWitness.transportMap P e.symm WB WA (DualWitness.transportMap P e WA WB lam) = lam := by
  simp only [DualWitness.transportMap, Iso.symm_hom, Category.assoc]
  rw [← DualWitness.map_comp P WB WA WB e.inv e.hom, e.inv_hom_id, DualWitness.map_id,
    Category.comp_id, e.inv_hom_id_assoc]

/-- Transport along an isomorphism, as an additive equivalence between the groups of
actual maps to the constructed duals. -/
def DualWitness.transportAddEquiv (e : A ≅ B) (WA : DualWitness A) (WB : DualWitness B) :
    (B ⟶ WB.dual P) ≃+ (A ⟶ WA.dual P) where
  toFun := DualWitness.transportMap P e WA WB
  invFun := DualWitness.transportMap P e.symm WB WA
  left_inv := DualWitness.transportMap_symm_transportMap P e WA WB
  right_inv := DualWitness.transportMap_symm_transportMap P e.symm WB WA
  map_add' f g := by
    simp only [DualWitness.transportMap, Preadditive.add_comp, Preadditive.comp_add]

@[simp] theorem DualWitness.transportAddEquiv_apply (e : A ≅ B) (WA : DualWitness A)
    (WB : DualWitness B) (lam : B ⟶ WB.dual P) :
    DualWitness.transportAddEquiv P e WA WB lam = DualWitness.transportMap P e WA WB lam := rfl

/-- Transport along an isomorphism preserves primitivity. -/
theorem DualWitness.isPrimitiveHom_transportMap (e : A ≅ B) (WA : DualWitness A)
    (WB : DualWitness B) {lam : B ⟶ WB.dual P} (hlam : Tate.IsPrimitiveHom lam) :
    Tate.IsPrimitiveHom (DualWitness.transportMap P e WA WB lam) := by
  intro j g hg
  apply hlam j (DualWitness.transportMap P e.symm WB WA g)
  rw [← DualWitness.transportMap_nsmul, hg, DualWitness.transportMap_symm_transportMap]

variable (hpos : PolarizationRayPositivityStatement.{u})
  (htor : TorsionFiniteEtaleStatement.{u}) [IsLocallyNoetherian S] [ConnectedSpace S]
  (hu : ∀ k : GroupScheme.Tate.Index (fun _ => True), IsUnit (k.val : Γ(S, ⊤)))
  {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)

include hpos htor hu s in
/-- Let `lamA` and `lamB` be polarizations, positive multiples of primitive maps `mA`
and `mB`. If the transport of `lamB` along an isomorphism is integrally proportional to
`lamA`, then the transport of `mB` equals `mA`. -/
theorem DualWitness.transportMap_eq_of_primitive (e : A ≅ B) (WA : DualWitness A)
    (WB : DualWitness B) (g : ℕ) (hg : 0 < g) (hdim : A.HasRelativeDimension g)
    {lamA : A ⟶ WA.dual P} {lamB : B ⟶ WB.dual P}
    (hA : WA.IsPolarization P lamA) (hB : WB.IsPolarization P lamB)
    {a b : ℤ} (ha : a ≠ 0) (hab : a • DualWitness.transportMap P e WA WB lamB = b • lamA)
    {mA : A ⟶ WA.dual P} {mB : B ⟶ WB.dual P} (hmA : Tate.IsPrimitiveHom mA)
    (hmB : Tate.IsPrimitiveHom mB) {kA kB : ℕ} (hkA : 0 < kA) (hkB : 0 < kB)
    (hlamA : kA • mA = lamA) (hlamB : kB • mB = lamB) :
    DualWitness.transportMap P e WA WB mB = mA := by
  have hpol := hpos P S ⟨(s.base (Classical.arbitrary _))⟩ A g hg hdim WA lamA
    (DualWitness.transportMap P e WA WB lamB) hA
    (DualWitness.isPolarization_transportMap P e WA WB lamB hB) a b ha hab
  -- Rewrite the proportionality with the primitive factors.
  have hmul : (a * kB) • DualWitness.transportMap P e WA WB mB = (b * kA) • mA := by
    rw [mul_smul, mul_smul, natCast_zsmul, natCast_zsmul, ← DualWitness.transportMap_nsmul,
      hlamB, hlamA, hab]
  have hsign : (a * kB) * (b * kA) > 0 := by
    have : (0 : ℤ) < kB * kA := by positivity
    nlinarith
  -- Reduce to equal positive natural multiples.
  have hnat : ((a * kB).natAbs) • DualWitness.transportMap P e WA WB mB =
      ((b * kA).natAbs) • mA := by
    rcases lt_or_gt_of_ne (show a * kB ≠ 0 by intro h0; rw [h0] at hsign; simp at hsign) with
      hneg | hposa
    · have hbneg : b * kA < 0 := by
        by_contra hcon
        have hcon := not_lt.mp hcon
        nlinarith
      rw [← natCast_zsmul, ← natCast_zsmul, Int.ofNat_natAbs_of_nonpos hneg.le,
        Int.ofNat_natAbs_of_nonpos hbneg.le, neg_smul, neg_smul, hmul]
    · have hbpos : 0 < b * kA := by
        by_contra hcon
        have hcon := not_lt.mp hcon
        nlinarith
      rw [← natCast_zsmul, ← natCast_zsmul, Int.natAbs_of_nonneg hposa.le,
        Int.natAbs_of_nonneg hbpos.le, hmul]
  have h1 : 0 < (a * kB).natAbs := Int.natAbs_pos.mpr (by intro h0; rw [h0] at hsign; simp at hsign)
  have h2 : 0 < (b * kA).natAbs := Int.natAbs_pos.mpr (by intro h0; rw [h0] at hsign; simp at hsign)
  exact (Tate.eq_of_nsmul_eq_nsmul_of_isPrimitiveHom htor hu s h1 h2
    (DualWitness.isPrimitiveHom_transportMap P e WA WB hmB) hmA hnat).2

end Langlands.AbelianScheme.PolarizedFiniteLevel
