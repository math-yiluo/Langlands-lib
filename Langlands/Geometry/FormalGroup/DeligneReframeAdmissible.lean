import Langlands.Geometry.FormalGroup.DeligneFrameDeterminant
import Langlands.Geometry.FormalGroup.DeligneIsomorphism
import Mathlib.Algebra.Group.Subgroup.Map

/-! # Determinant-unit frame changes of actual admissible Deligne data -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.DeligneFormalSpace

open CategoryTheory _root_.AlgebraicGeometry TopologicalSpace

variable {O : Type u} [CommRing O] {d : ℕ} [NeZero d] {π : O}
  {F : Type u} [Field F] [Algebra O F] {X : TopCat.{u}}

namespace FramedLatticePiSheaf

omit [NeZero d] in
/-- The identity linear automorphism leaves the actual framed lattice unchanged. -/
@[simp]
theorem reframe_one (M : FramedLatticePiSheaf d π X F) :
    M.reframe F 1 = M := by
  cases M with
  | mk lattice frame =>
    dsimp only [reframe]
    congr 1
    apply Iso.ext
    change (constantSheaf (Opens.grothendieckTopology X) (ModuleCat.{u} F)).map
      (𝟙 (ModuleCat.of F (Fin d → F))) ≫ frame.hom = frame.hom
    simp

omit [NeZero d] in
/-- Reframing successively by g and h precomposes the original frame by g * h. -/
theorem reframe_mul (M : FramedLatticePiSheaf d π X F)
    (g h : (Fin d → F) ≃ₗ[F] (Fin d → F)) :
    (M.reframe F g).reframe F h = M.reframe F (g * h) := by
  dsimp only [reframe]
  congr 1
  apply Iso.ext
  change
    (constantSheaf (Opens.grothendieckTopology X) (ModuleCat.{u} F)).map
        h.toModuleIso.hom ≫
      ((constantSheaf (Opens.grothendieckTopology X) (ModuleCat.{u} F)).map
        g.toModuleIso.hom ≫ M.frame.hom) =
    (constantSheaf (Opens.grothendieckTopology X) (ModuleCat.{u} F)).map
        (h.toModuleIso.hom ≫ g.toModuleIso.hom) ≫ M.frame.hom
  rw [Functor.map_comp, Category.assoc]

/-- Reframing both objects retains the original genuine lattice morphism. -/
def reframeMap (g : (Fin d → F) ≃ₗ[F] (Fin d → F))
    {M N : FramedLatticePiSheaf d π X F} (f : M ⟶ N) :
    M.reframe F g ⟶ N.reframe F g where
  lattice := f.lattice
  frame := by
    change (_ ≫ M.frame.hom) ≫ _ = _ ≫ N.frame.hom
    rw [Category.assoc, f.frame]

/-- Changing the rational frame is functorial for genuine framed lattice maps. -/
def reframeFunctor (g : (Fin d → F) ≃ₗ[F] (Fin d → F)) :
    FramedLatticePiSheaf d π X F ⥤ FramedLatticePiSheaf d π X F where
  obj M := M.reframe F g
  map f := reframeMap g f
  map_id _ := Hom.ext rfl
  map_comp _ _ := Hom.ext rfl

end FramedLatticePiSheaf

variable {S : Scheme.{u}} {φ : O →+* Γ(S, ⊤)}

namespace SheafPreDatum

/-- Change the rational frame of the actual four data, retaining eta, T and u. -/
def reframe (D : SheafPreDatum d π F φ)
    (g : (Fin d → F) ≃ₗ[F] (Fin d → F)) : SheafPreDatum d π F φ where
  eta := D.eta.reframe F g
  tangent := D.tangent
  u := D.u
  uPi := D.uPi
  uComponent := D.uComponent
  uComponent_inclusion := D.uComponent_inclusion
  locallyGenerates := D.locallyGenerates

variable (D : SheafPreDatum d π F φ)
  (g h : (Fin d → F) ≃ₗ[F] (Fin d → F))

/-- The constant-locus condition uses only the unchanged lattice and tangent data. -/
@[simp]
theorem constantOnPiZeroLoci_reframe_iff :
    (D.reframe g).ConstantOnPiZeroLoci ↔ D.ConstantOnPiZeroLoci := Iff.rfl

/-- The actual quotient-to-residue-fibre map is unchanged by a rational reframe. -/
@[simp]
theorem piQuotientResidueMap_reframe (x : S) :
    (D.reframe g).piQuotientResidueMap x = D.piQuotientResidueMap x := rfl

/-- The total residue-fibre injectivity condition is unchanged. -/
@[simp]
theorem residueFibreInjective_reframe_iff :
    (D.reframe g).ResidueFibreInjective ↔ D.ResidueFibreInjective := Iff.rfl

/-- An integral-unit determinant preserves condition (c) in both directions. -/
theorem determinantNormalized_reframe_iff_of_det_unit
    (a : Oˣ) (hdet : LinearMap.det g.toLinearMap = algebraMap O F (a : O))
    (hπ : algebraMap O F π ≠ 0) :
    (D.reframe g).DeterminantNormalized hπ ↔ D.DeterminantNormalized hπ := by
  have heq (n : ℤ) (x : S) :
      (D.reframe g).eta.normalizedFrameDeterminant F hπ n x =
        D.eta.normalizedFrameDeterminant F hπ n x :=
    D.eta.normalizedFrameDeterminant_reframe_of_det_unit F g a hdet hπ n x
  change (∀ (n : ℤ) (x : S), x ∈ D.tangent.graded.piZeroLocus (n : ZMod d) →
      D.componentDeterminant (n : ZMod d) x =
        (D.reframe g).eta.normalizedFrameDeterminant F hπ n x) ↔ _
  simp only [heq]
  rfl

/-- All three actual admissibility conditions are preserved by determinant-unit frames. -/
theorem admissible_reframe_iff_of_det_unit
    (a : Oˣ) (hdet : LinearMap.det g.toLinearMap = algebraMap O F (a : O))
    (hπ : algebraMap O F π ≠ 0) :
    (D.reframe g).Admissible hπ ↔ D.Admissible hπ := by
  unfold Admissible
  rw [D.constantOnPiZeroLoci_reframe_iff g, D.residueFibreInjective_reframe_iff g,
    D.determinantNormalized_reframe_iff_of_det_unit g a hdet hπ]

/-- The identity frame change preserves the complete actual datum. -/
@[simp]
theorem reframe_one : D.reframe 1 = D := by
  cases D
  dsimp only [reframe]
  congr 1
  exact FramedLatticePiSheaf.reframe_one _

/-- The order of successive frame changes is the ordinary linear-composition product. -/
theorem reframe_mul : (D.reframe g).reframe h = D.reframe (g * h) := by
  cases D
  dsimp only [reframe]
  congr 1
  exact FramedLatticePiSheaf.reframe_mul _ g h

/-- Reframe a genuine four-data morphism using the same lattice, tangent and u square. -/
def reframeMap {D E : SheafPreDatum d π F φ} (f : D ⟶ E)
    (g : (Fin d → F) ≃ₗ[F] (Fin d → F)) : D.reframe g ⟶ E.reframe g where
  eta := FramedLatticePiSheaf.reframeMap g f.eta
  tangent := f.tangent
  u := f.u

/-- Rational reframing is functorial on the actual category of four data. -/
def reframeFunctor (g : (Fin d → F) ≃ₗ[F] (Fin d → F)) :
    SheafPreDatum d π F φ ⥤ SheafPreDatum d π F φ where
  obj D := D.reframe g
  map f := reframeMap f g
  map_id _ := Hom.ext (FramedLatticePiSheaf.Hom.ext rfl) rfl
  map_comp _ _ := Hom.ext (FramedLatticePiSheaf.Hom.ext rfl) rfl

/-- The induced isomorphism still preserves all four actual data. -/
def reframeIso {D E : SheafPreDatum d π F φ} (e : D ≅ E)
    (g : (Fin d → F) ≃ₗ[F] (Fin d → F)) : D.reframe g ≅ E.reframe g :=
  (reframeFunctor g).mapIso e

namespace IsoClass

/-- Change the rational frame on preliminary classes using genuine isomorphism transport. -/
def reframe (g : (Fin d → F) ≃ₗ[F] (Fin d → F)) :
    IsoClass (d := d) (π := π) (F := F) (φ := φ) →
      IsoClass (d := d) (π := π) (F := F) (φ := φ) :=
  Quotient.map (fun D => D.reframe g) (fun _ _ ⟨e⟩ => ⟨reframeIso e g⟩)

@[simp]
theorem reframe_mk (D : SheafPreDatum d π F φ)
    (g : (Fin d → F) ≃ₗ[F] (Fin d → F)) :
    reframe g (mk D) = mk (D.reframe g) := rfl

/-- The identity change of frame is the identity on preliminary classes. -/
@[simp]
theorem reframe_one (x : IsoClass (d := d) (π := π) (F := F) (φ := φ)) :
    reframe 1 x = x := by
  induction x using Quotient.inductionOn with
  | h D => exact congrArg mk D.reframe_one

/-- Frame precomposition is a right action on preliminary classes. -/
theorem reframe_mul (g h : (Fin d → F) ≃ₗ[F] (Fin d → F))
    (x : IsoClass (d := d) (π := π) (F := F) (φ := φ)) :
    reframe h (reframe g x) = reframe (g * h) x := by
  induction x using Quotient.inductionOn with
  | h D => exact congrArg mk (D.reframe_mul g h)

end IsoClass

end SheafPreDatum

omit [NeZero d] in
/-- The subgroup whose actual determinant is the image of an integral unit. -/
def determinantUnitSubgroup (O : Type u) [CommRing O] (d : ℕ)
    (F : Type u) [Field F] [Algebra O F] :
    Subgroup ((Fin d → F) ≃ₗ[F] (Fin d → F)) :=
  ((⊤ : Subgroup Oˣ).map (Units.map (algebraMap O F).toMonoidHom)).comap
    LinearEquiv.det

omit [NeZero d] in
/-- Membership is exactly the determinant-unit hypothesis of the lattice calculation. -/
theorem mem_determinantUnitSubgroup_iff
    (g : (Fin d → F) ≃ₗ[F] (Fin d → F)) :
    g ∈ determinantUnitSubgroup O d F ↔
      ∃ a : Oˣ, LinearMap.det g.toLinearMap = algebraMap O F (a : O) := by
  change (∃ a : Oˣ, a ∈ (⊤ : Subgroup Oˣ) ∧
    Units.map (algebraMap O F).toMonoidHom a = LinearEquiv.det g) ↔ _
  constructor
  · rintro ⟨a, _, ha⟩
    exact ⟨a, by simpa using
      (congrArg Units.val ha).symm⟩
  · rintro ⟨a, ha⟩
    exact ⟨a, Subgroup.mem_top a, Units.ext (by
      simpa using ha.symm)⟩

namespace SheafPreDatum

/-- The subgroup's membership supplies preservation of the actual three conditions. -/
theorem admissible_reframe_iff (D : SheafPreDatum d π F φ)
    (g : determinantUnitSubgroup O d F) (hπ : algebraMap O F π ≠ 0) :
    (D.reframe g.val).Admissible hπ ↔ D.Admissible hπ := by
  obtain ⟨a, ha⟩ := (mem_determinantUnitSubgroup_iff g.val).mp g.property
  exact D.admissible_reframe_iff_of_det_unit g.val a ha hπ

end SheafPreDatum

namespace SheafDatum

variable (hπ : algebraMap O F π ≠ 0)

/-- An actual admissible reframe, with all conditions proved from subgroup membership. -/
def reframe (g : determinantUnitSubgroup O d F)
    (D : SheafDatum (d := d) (π := π) (φ := φ) hπ) :
    SheafDatum (d := d) (π := π) (φ := φ) hπ :=
  ⟨D.val.reframe g.val, (D.val.admissible_reframe_iff g hπ).mpr D.property⟩

@[simp]
theorem reframe_val (g : determinantUnitSubgroup O d F)
    (D : SheafDatum (d := d) (π := π) (φ := φ) hπ) :
    (reframe hπ g D).val = D.val.reframe g.val := rfl

/-- The identity frame leaves the entire admissible datum unchanged. -/
@[simp]
theorem reframe_one (D : SheafDatum (d := d) (π := π) (φ := φ) hπ) :
    reframe hπ 1 D = D :=
  Subtype.ext D.val.reframe_one

/-- Successive admissible reframes follow the same right-action product. -/
theorem reframe_mul (g h : determinantUnitSubgroup O d F)
    (D : SheafDatum (d := d) (π := π) (φ := φ) hπ) :
    reframe hπ h (reframe hπ g D) = reframe hπ (g * h) D :=
  Subtype.ext (D.val.reframe_mul g.val h.val)

namespace IsoClass

/-- Reframe admissible classes by transporting genuine four-data isomorphisms. -/
def reframe (g : determinantUnitSubgroup O d F) :
    IsoClass (d := d) (π := π) (φ := φ) hπ →
      IsoClass (d := d) (π := π) (φ := φ) hπ :=
  Quotient.map (SheafDatum.reframe hπ g)
    (fun _ _ ⟨e⟩ => ⟨SheafPreDatum.reframeIso e g.val⟩)

@[simp]
theorem reframe_mk (g : determinantUnitSubgroup O d F)
    (D : SheafDatum (d := d) (π := π) (φ := φ) hπ) :
    reframe hπ g (mk hπ D) = mk hπ (SheafDatum.reframe hπ g D) := rfl

/-- Forgetting admissibility commutes with the actual frame change on classes. -/
@[simp]
theorem toPreliminary_reframe (g : determinantUnitSubgroup O d F)
    (x : IsoClass (d := d) (π := π) (φ := φ) hπ) :
    toPreliminary hπ (reframe hπ g x) =
      SheafPreDatum.IsoClass.reframe g.val (toPreliminary hπ x) := by
  induction x using Quotient.inductionOn with
  | h D => rfl

/-- The identity frame change acts trivially on actual admissible classes. -/
@[simp]
theorem reframe_one (x : IsoClass (d := d) (π := π) (φ := φ) hπ) :
    reframe hπ 1 x = x := by
  induction x using Quotient.inductionOn with
  | h D => exact congrArg (mk hπ) (SheafDatum.reframe_one hπ D)

/-- Successive frame changes define a right action on actual admissible classes. -/
theorem reframe_mul (g h : determinantUnitSubgroup O d F)
    (x : IsoClass (d := d) (π := π) (φ := φ) hπ) :
    reframe hπ h (reframe hπ g x) = reframe hπ (g * h) x := by
  induction x using Quotient.inductionOn with
  | h D => exact congrArg (mk hπ) (SheafDatum.reframe_mul hπ g h D)

/-- Reframing by the group inverse undoes the original frame change. -/
@[simp]
theorem reframe_inv_reframe (g : determinantUnitSubgroup O d F)
    (x : IsoClass (d := d) (π := π) (φ := φ) hπ) :
    reframe hπ g⁻¹ (reframe hπ g x) = x := by
  rw [reframe_mul, mul_inv_cancel, reframe_one]

/-- The inverse frame change is undone by the original one as well. -/
@[simp]
theorem reframe_reframe_inv (g : determinantUnitSubgroup O d F)
    (x : IsoClass (d := d) (π := π) (φ := φ) hπ) :
    reframe hπ g (reframe hπ g⁻¹ x) = x := by
  rw [reframe_mul, inv_mul_cancel, reframe_one]

/-- Each determinant-unit frame change is a genuine equivalence of admissible classes. -/
def reframeEquiv (g : determinantUnitSubgroup O d F) :
    IsoClass (d := d) (π := π) (φ := φ) hπ ≃
      IsoClass (d := d) (π := π) (φ := φ) hπ where
  toFun := reframe hπ g
  invFun := reframe hπ g⁻¹
  left_inv := reframe_inv_reframe hπ g
  right_inv := reframe_reframe_inv hπ g

/-- Encode the proved right action as a left action of the opposite subgroup. -/
instance reframeRightAction :
    MulAction (determinantUnitSubgroup O d F)ᵐᵒᵖ
      (IsoClass (d := d) (π := π) (φ := φ) hπ) where
  smul g x := reframe hπ g.unop x
  one_smul := reframe_one hπ
  mul_smul g h x := (reframe_mul hπ h.unop g.unop x).symm

end IsoClass

end SheafDatum

end Langlands.DeligneFormalSpace
