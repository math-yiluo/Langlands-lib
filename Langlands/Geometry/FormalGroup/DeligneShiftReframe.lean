import Langlands.Geometry.FormalGroup.DeligneReframeAdmissible
import Langlands.Geometry.FormalGroup.DeligneShiftCoherence

/-! # Determinant-corrected shifts and reframes of actual Deligne data -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.DeligneFormalSpace

open CategoryTheory _root_.AlgebraicGeometry TopologicalSpace

variable {O : Type u} [CommRing O] {d : ℕ} [NeZero d] {π : O}
  {F : Type u} [Field F] [Algebra O F] {X : TopCat.{u}}

namespace FramedLatticePiSheaf

variable (M : FramedLatticePiSheaf d π X F) (hπ : algebraMap O F π ≠ 0)
  (g : (Fin d → F) ≃ₗ[F] (Fin d → F)) (k : ℤ)

/-- Shifting and precomposing the actual rational frame commute. -/
theorem shiftInt_reframe :
    (M.reframe F g).shiftInt F hπ k = (M.shiftInt F hπ k).reframe F g := by
  dsimp only [shiftInt, reframe]
  congr 1

/-- The combined frame determinant has the literal correction det(g) times pi^k. -/
theorem normalizedFrameDeterminant_shiftInt_reframe (i : ℤ) (x : X) :
    ((M.shiftInt F hπ k).reframe F g).normalizedFrameDeterminant F hπ i x =
      scaleStalkLattice F (LinearMap.det g.toLinearMap * algebraMap O F π ^ k) _
        (M.normalizedFrameDeterminant F hπ (i + k) x) := by
  rw [normalizedFrameDeterminant_reframe, normalizedFrameDeterminant_shiftInt,
    scaleStalkLattice_mul]

/-- An integral-unit corrected determinant identifies the actual normalized lattices. -/
theorem normalizedFrameDeterminant_shiftInt_reframe_of_unit (a : Oˣ)
    (hdet : algebraMap O F π ^ k * LinearMap.det g.toLinearMap =
      algebraMap O F (a : O)) (i : ℤ) (x : X) :
    ((M.shiftInt F hπ k).reframe F g).normalizedFrameDeterminant F hπ i x =
      M.normalizedFrameDeterminant F hπ (i + k) x := by
  rw [M.normalizedFrameDeterminant_shiftInt_reframe hπ g k,
    mul_comm (LinearMap.det g.toLinearMap), hdet, scaleStalkLattice_algebraMap_unit]

end FramedLatticePiSheaf

variable {S : Scheme.{u}} {φ : O →+* Γ(S, ⊤)}

namespace SheafPreDatum

variable (D : SheafPreDatum d π F φ) (hπ : algebraMap O F π ≠ 0)
  (g h : (Fin d → F) ≃ₗ[F] (Fin d → F)) (k l : ℤ)

/-- The complete four-data constructions commute, including the specified u components. -/
theorem shiftInt_reframe :
    (D.reframe g).shiftInt hπ k = (D.shiftInt hπ k).reframe g := by
  cases D
  dsimp only [shiftInt, reframe]
  congr 1

/-- Simultaneously shift the grading and precompose the actual rational frame. -/
def shiftReframe : SheafPreDatum d π F φ := (D.shiftInt hπ k).reframe g

/-- The actual combined operation is the composite of the two genuine functors. -/
def shiftReframeFunctor : SheafPreDatum d π F φ ⥤ SheafPreDatum d π F φ :=
  shiftIntFunctor hπ k ⋙ reframeFunctor g

/-- The combined operation transports genuine frame- and u-preserving isomorphisms. -/
def shiftReframeIso {D E : SheafPreDatum d π F φ} (e : D ≅ E) :
    D.shiftReframe hπ g k ≅ E.shiftReframe hπ g k :=
  (shiftReframeFunctor hπ g k).mapIso e

/-- Condition (a) survives the simultaneous component translation. -/
theorem constantOnPiZeroLoci_shiftReframe_iff :
    (D.shiftReframe hπ g k).ConstantOnPiZeroLoci ↔ D.ConstantOnPiZeroLoci := by
  rw [shiftReframe, constantOnPiZeroLoci_reframe_iff, constantOnPiZeroLoci_shiftInt_iff]

/-- The total quotient-to-residue-fibre map is unchanged by the combined operation. -/
@[simp]
theorem piQuotientResidueMap_shiftReframe (x : S) :
    (D.shiftReframe hπ g k).piQuotientResidueMap x = D.piQuotientResidueMap x := rfl

/-- Condition (b) is unchanged because its actual total map is unchanged. -/
theorem residueFibreInjective_shiftReframe_iff :
    (D.shiftReframe hπ g k).ResidueFibreInjective ↔ D.ResidueFibreInjective := Iff.rfl

/-- Correcting the determinant by an integral unit preserves condition (c). -/
theorem determinantNormalized_shiftReframe_iff_of_unit (a : Oˣ)
    (hdet : algebraMap O F π ^ k * LinearMap.det g.toLinearMap =
      algebraMap O F (a : O)) :
    (D.shiftReframe hπ g k).DeterminantNormalized hπ ↔ D.DeterminantNormalized hπ := by
  have heq (i : ℤ) (x : S) :
      (D.shiftReframe hπ g k).eta.normalizedFrameDeterminant F hπ i x =
        D.eta.normalizedFrameDeterminant F hπ (i + k) x :=
    D.eta.normalizedFrameDeterminant_shiftInt_reframe_of_unit hπ g k a hdet i x
  have hz (i : ℤ) :
      (D.shiftReframe hπ g k).tangent.graded.piZeroLocus (i : ZMod d) =
        D.tangent.graded.piZeroLocus ((i + k : ℤ) : ZMod d) := by
    change (D.shiftInt hπ k).tangent.graded.piZeroLocus (i : ZMod d) = _
    simpa only [Int.cast_add] using D.piZeroLocus_shiftInt hπ k (i : ZMod d)
  have hc (i : ℤ) (x : S) :
      (D.shiftReframe hπ g k).componentDeterminant (i : ZMod d) x =
        D.componentDeterminant ((i + k : ℤ) : ZMod d) x := by
    change (D.shiftInt hπ k).componentDeterminant (i : ZMod d) x = _
    simpa only [Int.cast_add] using D.componentDeterminant_shiftInt hπ k (i : ZMod d) x
  unfold DeterminantNormalized
  simp only [heq, hz, hc]
  constructor
  · intro H j x hx
    simpa only [sub_add_cancel] using H (j - k) x (by
      simpa only [sub_add_cancel] using hx)
  · intro H i x hx
    exact H (i + k) x hx

/-- All three actual conditions are invariant under an integral-unit correction. -/
theorem admissible_shiftReframe_iff_of_unit (a : Oˣ)
    (hdet : algebraMap O F π ^ k * LinearMap.det g.toLinearMap =
      algebraMap O F (a : O)) :
    (D.shiftReframe hπ g k).Admissible hπ ↔ D.Admissible hπ := by
  unfold Admissible
  rw [D.constantOnPiZeroLoci_shiftReframe_iff hπ g k,
    D.residueFibreInjective_shiftReframe_iff hπ g k,
    D.determinantNormalized_shiftReframe_iff_of_unit hπ g k a hdet]

namespace IsoClass

/-- Shift and reframe preliminary classes through the actual four-data functors. -/
def shiftReframe (hπ : algebraMap O F π ≠ 0)
    (g : (Fin d → F) ≃ₗ[F] (Fin d → F)) (k : ℤ)
    (q : IsoClass (d := d) (π := π) (F := F) (φ := φ)) :
    IsoClass (d := d) (π := π) (F := F) (φ := φ) :=
  reframe g (shiftInt hπ k q)

@[simp]
theorem shiftReframe_mk :
    shiftReframe hπ g k (mk D) = mk (D.shiftReframe hπ g k) := rfl

/-- The actual commutation equality descends to preliminary classes. -/
theorem shiftInt_reframe
    (q : IsoClass (d := d) (π := π) (F := F) (φ := φ)) :
    shiftInt hπ k (reframe g q) = reframe g (shiftInt hπ k q) := by
  induction q using Quotient.inductionOn with
  | h D => exact congrArg mk (D.shiftInt_reframe hπ g k)

/-- The identity frame and zero shift act identically on preliminary classes. -/
@[simp]
theorem shiftReframe_one_zero
    (q : IsoClass (d := d) (π := π) (F := F) (φ := φ)) :
    shiftReframe hπ 1 0 q = q := by
  rw [shiftReframe, shiftInt_zero, reframe_one]

/-- The combined preliminary operation follows the right product and integer addition. -/
theorem shiftReframe_mul_add
    (q : IsoClass (d := d) (π := π) (F := F) (φ := φ)) :
    shiftReframe hπ h l (shiftReframe hπ g k q) =
      shiftReframe hπ (g * h) (k + l) q := by
  unfold shiftReframe
  rw [shiftInt_reframe, reframe_mul, shiftInt_add]

end IsoClass

end SheafPreDatum

omit [NeZero d] in
/-- The actual corrected determinant of a linear frame change and an integer shift. -/
def shiftReframeDeterminantHom (hπ : algebraMap O F π ≠ 0) :
    (((Fin d → F) ≃ₗ[F] (Fin d → F)) × Multiplicative ℤ) →* Fˣ where
  toFun p := Units.mk0 (algebraMap O F π) hπ ^ p.2.toAdd * LinearEquiv.det p.1
  map_one' := by simp
  map_mul' p q := by
    change
      Units.mk0 (algebraMap O F π) hπ ^ (p.2.toAdd + q.2.toAdd) *
          LinearEquiv.det (p.1 * q.1) =
        (Units.mk0 (algebraMap O F π) hπ ^ p.2.toAdd * LinearEquiv.det p.1) *
          (Units.mk0 (algebraMap O F π) hπ ^ q.2.toAdd * LinearEquiv.det q.1)
    rw [zpow_add, map_mul]
    ac_rfl

omit [NeZero d] in
/-- Corrected pairs are those whose actual corrected determinant is an integral unit. -/
def shiftReframeSubgroup (hπ : algebraMap O F π ≠ 0) :
    Subgroup (((Fin d → F) ≃ₗ[F] (Fin d → F)) × Multiplicative ℤ) :=
  ((⊤ : Subgroup Oˣ).map (Units.map (algebraMap O F).toMonoidHom)).comap
    (shiftReframeDeterminantHom (d := d) hπ)

omit [NeZero d] in
/-- Subgroup membership supplies precisely the previously proved unit correction. -/
theorem mem_shiftReframeSubgroup_iff (hπ : algebraMap O F π ≠ 0)
    (p : ((Fin d → F) ≃ₗ[F] (Fin d → F)) × Multiplicative ℤ) :
    p ∈ shiftReframeSubgroup hπ ↔
      ∃ a : Oˣ, algebraMap O F π ^ p.2.toAdd * LinearMap.det p.1.toLinearMap =
        algebraMap O F (a : O) := by
  change (∃ a : Oˣ, a ∈ (⊤ : Subgroup Oˣ) ∧
    Units.map (algebraMap O F).toMonoidHom a =
      shiftReframeDeterminantHom hπ p) ↔ _
  constructor
  · rintro ⟨a, _, ha⟩
    exact ⟨a, by simpa [shiftReframeDeterminantHom] using
      (congrArg Units.val ha).symm⟩
  · rintro ⟨a, ha⟩
    exact ⟨a, Subgroup.mem_top a, Units.ext (by
      simpa [shiftReframeDeterminantHom] using ha.symm)⟩

namespace SheafPreDatum

/-- Arithmetic subgroup membership proves preservation of all actual conditions. -/
theorem admissible_shiftReframe_iff (D : SheafPreDatum d π F φ)
    (hπ : algebraMap O F π ≠ 0) (p : shiftReframeSubgroup (d := d) hπ) :
    (D.shiftReframe hπ p.val.1 p.val.2.toAdd).Admissible hπ ↔ D.Admissible hπ := by
  obtain ⟨a, ha⟩ := (mem_shiftReframeSubgroup_iff hπ p.val).mp p.property
  exact D.admissible_shiftReframe_iff_of_unit hπ p.val.1 p.val.2.toAdd a ha

end SheafPreDatum

namespace SheafDatum

variable (hπ : algebraMap O F π ≠ 0)

/-- Construct the actual corrected admissible datum, deriving its conditions arithmetically. -/
def shiftReframe (p : shiftReframeSubgroup (d := d) hπ)
    (D : SheafDatum (d := d) (π := π) (φ := φ) hπ) :
    SheafDatum (d := d) (π := π) (φ := φ) hπ :=
  ⟨D.val.shiftReframe hπ p.val.1 p.val.2.toAdd,
    (D.val.admissible_shiftReframe_iff hπ p).mpr D.property⟩

@[simp]
theorem shiftReframe_val (p : shiftReframeSubgroup (d := d) hπ)
    (D : SheafDatum (d := d) (π := π) (φ := φ) hπ) :
    (shiftReframe hπ p D).val = D.val.shiftReframe hπ p.val.1 p.val.2.toAdd := rfl

namespace IsoClass

/-- Forgetting the admissibility proof is injective on genuine isomorphism classes. -/
theorem toPreliminary_injective :
    Function.Injective (toPreliminary (d := d) (π := π) (φ := φ) hπ) := by
  intro x y
  refine Quotient.inductionOn₂ x y ?_
  intro D E h
  exact Quotient.sound ((SheafPreDatum.IsoClass.mk_eq_mk_iff D.val E.val).mp h)

/-- Corrected pairs act on admissible classes by genuine four-data isomorphism transport. -/
def shiftReframe (p : shiftReframeSubgroup (d := d) hπ) :
    IsoClass (d := d) (π := π) (φ := φ) hπ →
      IsoClass (d := d) (π := π) (φ := φ) hπ :=
  Quotient.map (SheafDatum.shiftReframe hπ p)
    (fun _ _ ⟨e⟩ => ⟨SheafPreDatum.shiftReframeIso hπ p.val.1 p.val.2.toAdd e⟩)

@[simp]
theorem shiftReframe_mk (p : shiftReframeSubgroup (d := d) hπ)
    (D : SheafDatum (d := d) (π := π) (φ := φ) hπ) :
    shiftReframe hπ p (mk hπ D) = mk hπ (SheafDatum.shiftReframe hπ p D) := rfl

/-- Forgetting admissibility commutes with the constructed corrected operation. -/
@[simp]
theorem toPreliminary_shiftReframe (p : shiftReframeSubgroup (d := d) hπ)
    (q : IsoClass (d := d) (π := π) (φ := φ) hπ) :
    toPreliminary hπ (shiftReframe hπ p q) =
      SheafPreDatum.IsoClass.shiftReframe hπ p.val.1 p.val.2.toAdd
        (toPreliminary hπ q) := by
  induction q using Quotient.inductionOn with
  | h D => rfl

/-- The identity corrected pair acts identically on actual admissible classes. -/
@[simp]
theorem shiftReframe_one (q : IsoClass (d := d) (π := π) (φ := φ) hπ) :
    shiftReframe hπ 1 q = q := by
  apply toPreliminary_injective hπ
  rw [toPreliminary_shiftReframe]
  exact SheafPreDatum.IsoClass.shiftReframe_one_zero hπ _

/-- Multiplication of corrected pairs gives the actual right-action law. -/
theorem shiftReframe_mul (p r : shiftReframeSubgroup (d := d) hπ)
    (q : IsoClass (d := d) (π := π) (φ := φ) hπ) :
    shiftReframe hπ r (shiftReframe hπ p q) = shiftReframe hπ (p * r) q := by
  apply toPreliminary_injective hπ
  rw [toPreliminary_shiftReframe, toPreliminary_shiftReframe, toPreliminary_shiftReframe]
  exact SheafPreDatum.IsoClass.shiftReframe_mul_add hπ p.val.1 r.val.1
    p.val.2.toAdd r.val.2.toAdd _

/-- The inverse corrected pair undoes the constructed action. -/
@[simp]
theorem shiftReframe_inv_shiftReframe (p : shiftReframeSubgroup (d := d) hπ)
    (q : IsoClass (d := d) (π := π) (φ := φ) hπ) :
    shiftReframe hπ p⁻¹ (shiftReframe hπ p q) = q := by
  rw [shiftReframe_mul, mul_inv_cancel, shiftReframe_one]

/-- The corrected action also undoes the action of its inverse. -/
@[simp]
theorem shiftReframe_shiftReframe_inv (p : shiftReframeSubgroup (d := d) hπ)
    (q : IsoClass (d := d) (π := π) (φ := φ) hπ) :
    shiftReframe hπ p (shiftReframe hπ p⁻¹ q) = q := by
  rw [shiftReframe_mul, inv_mul_cancel, shiftReframe_one]

/-- A corrected pair gives a bijection, with inverse the opposite corrected pair. -/
def shiftReframeEquiv (p : shiftReframeSubgroup (d := d) hπ) :
    IsoClass (d := d) (π := π) (φ := φ) hπ ≃
      IsoClass (d := d) (π := π) (φ := φ) hπ where
  toFun := shiftReframe hπ p
  invFun := shiftReframe hπ p⁻¹
  left_inv := shiftReframe_inv_shiftReframe hπ p
  right_inv := shiftReframe_shiftReframe_inv hπ p

/-- Encode the proved right action as a left action of the opposite corrected subgroup. -/
instance shiftReframeRightAction :
    MulAction (shiftReframeSubgroup (d := d) hπ)ᵐᵒᵖ
      (IsoClass (d := d) (π := π) (φ := φ) hπ) where
  smul p q := shiftReframe hπ p.unop q
  one_smul := shiftReframe_one hπ
  mul_smul p r q := (shiftReframe_mul hπ r.unop p.unop q).symm

end IsoClass

end SheafDatum

end Langlands.DeligneFormalSpace
