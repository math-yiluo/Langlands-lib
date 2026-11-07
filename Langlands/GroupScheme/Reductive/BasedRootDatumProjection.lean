import Langlands.GroupScheme.Reductive.PinnedAutomorphismLift
import Langlands.GroupScheme.Reductive.PinnedDynamicTransport
import Langlands.GroupScheme.Reductive.RootDatumGaloisSimpleRoots
import Langlands.GroupScheme.Reductive.RootDatumWeylComparison
import Langlands.GroupScheme.Torus.WeylImageFinite
import Langlands.GroupScheme.Rational.PositiveRootStabilizerAveraging
import Langlands.LinearAlgebra.RootDatumBasedCorrection

/-! # Based representatives modulo the full integral Weyl group -/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SplitPinning

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (p : SplitPinning G)

/-- The Weyl group of the full supplied integral root datum is finite. -/
theorem finite_rootDatum_weylGroup : Finite p.rootDatum.weylGroup := by
  let : IsClosedImmersion p.inclusion.hom.hom.left := p.isMaximalTorus.2.1
  have := p.isConnectedReductive.smooth
  let : Finite (weylImage p.inclusion) :=
    splitTorusWeylImageFinite k G p.torus p.isSplitTorus p.inclusion
      p.isMaximalTorus.2.1
  let f : p.rootDatum.weylGroup → weylImage p.inclusion := fun w =>
    ⟨w.val.weightEquiv, p.isRootDatum.abstractWeylImage_le
      ⟨w.val, w.property, rfl⟩⟩
  apply Finite.of_injective f
  intro a b hab
  apply Subtype.ext
  exact RootPairing.Equiv.weightHom_injective p.rootDatum (congrArg Subtype.val hab)

/-- Every full root-datum automorphism admits a based representative in its
left Weyl coset. -/
theorem exists_basedRootDatum_correction (δ : p.rootDatum.Aut) :
    ∃ w : p.rootDatum.weylGroup, w.val * δ ∈ p.basedRootDatumAut := by
  classical
  let := Fintype.ofFinite p.rootIndex
  let := p.finite_rootDatum_weylGroup
  have hf (i : p.rootIndex) : p.rootDatum.root' i p.positiveCocharacter ≠ 0 := by
    change p.rootDatum.toLinearMap (p.rootDatum.root i) p.positiveCocharacter ≠ 0
    rw [p.isRootDatum.1]
    exact p.latticePairing_root_positiveCocharacter_ne_zero i
  obtain ⟨w, hpos, -⟩ :=
    Langlands.LinearAlgebra.RootDatumBasedCorrection.exists_positive_correction
      p.rootDatum 0 p.positiveCocharacter hf
      (fun i hi => False.elim (hi (map_zero _))) δ (map_zero _)
  refine ⟨⟨w.val, Langlands.LinearAlgebra.RootDatumWeylChambers.reflectionSubgroup_le
    p.rootDatum _ w.property⟩, fun i => ?_⟩
  apply (p.base.mem_support_equiv_iff_of_isPos p.rootDatum
    (w.val * δ).indexEquiv (w.val * δ).weightEquiv
    (fun j => ((w.val * δ).root_weightMap_apply p.rootDatum p.rootDatum j).symm) ?_ i).symm
  intro j
  have h := hpos j
  change (0 < p.rootDatum.toLinearMap (p.rootDatum.root j) p.positiveCocharacter) ↔
    (0 < p.rootDatum.toLinearMap
      (p.rootDatum.root ((w.val * δ).indexEquiv j)) p.positiveCocharacter) at h
  rw [p.isRootDatum.1, p.latticePairing_root_positiveCocharacter_pos_iff,
    p.latticePairing_root_positiveCocharacter_pos_iff] at h
  exact h.symm

/-- A Weyl element preserving the supplied base is the identity on both full
lattices, including their central directions. -/
theorem eq_one_of_weyl_of_based (w : p.rootDatum.Aut)
    (hw : w ∈ p.rootDatum.weylGroup) (hb : w ∈ p.basedRootDatumAut) : w = 1 := by
  let : IsClosedImmersion p.inclusion.hom.hom.left := p.isMaximalTorus.2.1
  obtain ⟨n, hn⟩ := p.isRootDatum.abstractWeylImage_le ⟨w, hw, rfl⟩
  change weylAction p.inclusion n = w.weightEquiv at hn
  have hpos (a : p.rootIndex) : p.base.IsPos (w.indexEquiv a) ↔ p.base.IsPos a := by
    have h := (p.isoOfBasedRootDatumAut ⟨w, hb⟩).isPos_iff a
    simpa only [isoOfBasedRootDatumAut, isoOfRootDatumEquiv_indexEquiv] using h
  have hn1 : (QuotientGroup.mk n : relativeWeylGroup p.inclusion) = 1 := by
    apply hasTrivialPositiveRootStabilizer p.inclusion p.isConnectedReductive
      (p.isMaximalTorus.isMaximalSplitTorus p.isSplitTorus)
      p.isGenericCocharacter_positiveCocharacter
    intro α hα
    obtain ⟨a, rfl⟩ : ∃ a, p.rootDatum.root a = α := by
      rw [← Set.mem_range, p.isRootDatum.2.1]
      exact hα
    rw [relativeWeylCharacterAction_mk, hn]
    change (0 < latticePairing p.torus (w.weightEquiv (p.rootDatum.root a))
      p.positiveCocharacter) ↔ _
    have hroot : w.weightEquiv (p.rootDatum.root a) =
        p.rootDatum.root (w.indexEquiv a) :=
      w.root_weightMap_apply p.rootDatum p.rootDatum a
    rw [hroot,
      p.latticePairing_root_positiveCocharacter_pos_iff,
      p.latticePairing_root_positiveCocharacter_pos_iff]
    exact hpos a
  apply RootPairing.Equiv.weightHom_injective p.rootDatum
  rw [map_one]
  change w.weightEquiv = 1
  rw [← hn, ← relativeWeylCharacterAction_mk, hn1, map_one]

/-- Conjugating a root reflection by any full root-datum automorphism gives the
reflection at the transported root. -/
theorem conjugate_rootDatum_reflection (δ : p.rootDatum.Aut) (i : p.rootIndex) :
    δ * RootPairing.Equiv.reflection p.rootDatum i * δ⁻¹ =
      RootPairing.Equiv.reflection p.rootDatum (δ.indexEquiv i) := by
  apply RootPairing.Equiv.weightHom_injective p.rootDatum
  ext x
  change δ.weightEquiv (p.rootDatum.reflection i (δ.weightEquiv.symm x)) =
    p.rootDatum.reflection (δ.indexEquiv i) x
  rw [δ.weightEquiv_reflection, LinearEquiv.apply_symm_apply]

/-- The full integral Weyl subgroup is stable under arbitrary root-datum
conjugation. -/
theorem conjugate_mem_rootDatum_weylGroup (δ w : p.rootDatum.Aut)
    (hw : w ∈ p.rootDatum.weylGroup) :
    δ * w * δ⁻¹ ∈ p.rootDatum.weylGroup := by
  induction hw using RootPairing.weylGroup.induction with
  | mem i =>
    rw [p.conjugate_rootDatum_reflection]
    exact p.rootDatum.reflection_mem_weylGroup _
  | one => simp
  | mul a b ha hb ia ib =>
    have he : δ * (a * b) * δ⁻¹ = (δ * a * δ⁻¹) * (δ * b * δ⁻¹) := by group
    rw [he]
    exact p.rootDatum.weylGroup.mul_mem ia ib

/-- A based automorphism in a specified left Weyl coset exists. -/
theorem exists_basedRootDatum_representative (δ : p.rootDatum.Aut) :
    ∃ θ : p.basedRootDatumAut, θ.val * δ⁻¹ ∈ p.rootDatum.weylGroup := by
  obtain ⟨w, hw⟩ := p.exists_basedRootDatum_correction δ
  refine ⟨⟨w.val * δ, hw⟩, ?_⟩
  simpa only [mul_inv_cancel_right] using w.property

/-- There is only one based automorphism in a given left Weyl coset. -/
theorem basedRootDatum_representative_unique (δ : p.rootDatum.Aut)
    (θ φ : p.basedRootDatumAut)
    (hθ : θ.val * δ⁻¹ ∈ p.rootDatum.weylGroup)
    (hφ : φ.val * δ⁻¹ ∈ p.rootDatum.weylGroup) : θ = φ := by
  have he : (θ.val * δ⁻¹) * (φ.val * δ⁻¹)⁻¹ = θ.val * φ.val⁻¹ := by group
  have hw : θ.val * φ.val⁻¹ ∈ p.rootDatum.weylGroup := by
    rw [← he]
    exact p.rootDatum.weylGroup.mul_mem hθ (p.rootDatum.weylGroup.inv_mem hφ)
  have hb : θ.val * φ.val⁻¹ ∈ p.basedRootDatumAut :=
    p.basedRootDatumAut.mul_mem θ.property (p.basedRootDatumAut.inv_mem φ.property)
  exact Subtype.ext (mul_inv_eq_one.mp (p.eq_one_of_weyl_of_based _ hw hb))

/-- The unique based representative of each full root-datum automorphism,
packaged as a multiplicative projection. -/
def basedRootDatumProjection : p.rootDatum.Aut →* p.basedRootDatumAut where
  toFun δ := Classical.choose (p.exists_basedRootDatum_representative δ)
  map_one' := by
    apply p.basedRootDatum_representative_unique 1
    · exact Classical.choose_spec (p.exists_basedRootDatum_representative 1)
    · simp
  map_mul' δ ε := by
    apply p.basedRootDatum_representative_unique (δ * ε)
    · exact Classical.choose_spec (p.exists_basedRootDatum_representative (δ * ε))
    · let θ := Classical.choose (p.exists_basedRootDatum_representative δ)
      let φ := Classical.choose (p.exists_basedRootDatum_representative ε)
      have hθ : θ.val * δ⁻¹ ∈ p.rootDatum.weylGroup :=
        Classical.choose_spec (p.exists_basedRootDatum_representative δ)
      have hφ : φ.val * ε⁻¹ ∈ p.rootDatum.weylGroup :=
        Classical.choose_spec (p.exists_basedRootDatum_representative ε)
      change (θ.val * φ.val) * (δ * ε)⁻¹ ∈ p.rootDatum.weylGroup
      have he : (θ.val * φ.val) * (δ * ε)⁻¹ =
          (θ.val * δ⁻¹) * (δ * (φ.val * ε⁻¹) * δ⁻¹) := by group
      rw [he]
      exact p.rootDatum.weylGroup.mul_mem hθ
        (p.conjugate_mem_rootDatum_weylGroup δ _ hφ)

/-- The projection has a full integral Weyl correction. -/
theorem basedRootDatumProjection_correction (δ : p.rootDatum.Aut) :
    (p.basedRootDatumProjection δ).val * δ⁻¹ ∈ p.rootDatum.weylGroup :=
  Classical.choose_spec (p.exists_basedRootDatum_representative δ)

/-- The projection restricts to the identity on based automorphisms. -/
@[simp]
theorem basedRootDatumProjection_of_based (θ : p.basedRootDatumAut) :
    p.basedRootDatumProjection θ.val = θ := by
  apply p.basedRootDatum_representative_unique θ.val
    _ θ (p.basedRootDatumProjection_correction θ.val)
  simp

/-- The kernel of the projection is exactly the full integral Weyl subgroup. -/
theorem basedRootDatumProjection_eq_one_iff (δ : p.rootDatum.Aut) :
    p.basedRootDatumProjection δ = 1 ↔ δ ∈ p.rootDatum.weylGroup := by
  constructor
  · intro h
    have hw := p.basedRootDatumProjection_correction δ
    rw [h] at hw
    change 1 * δ⁻¹ ∈ p.rootDatum.weylGroup at hw
    simpa using p.rootDatum.weylGroup.inv_mem hw
  · intro h
    apply p.basedRootDatum_representative_unique δ
      _ 1 (p.basedRootDatumProjection_correction δ)
    simpa using p.rootDatum.weylGroup.inv_mem h

/-- The original automorphism and its based projection differ by a specified
left Weyl factor. -/
theorem exists_weyl_mul_eq_basedRootDatumProjection (δ : p.rootDatum.Aut) :
    ∃ w : p.rootDatum.weylGroup,
      w.val * δ = (p.basedRootDatumProjection δ).val := by
  refine ⟨⟨_, p.basedRootDatumProjection_correction δ⟩, ?_⟩
  exact inv_mul_cancel_right _ _

/-- Lift the based projection to an actual field-group automorphism action. -/
def rootDatumAutPinnedLift : p.rootDatum.Aut →* CategoryTheory.Aut G :=
  p.basedRootDatumAutLift.comp p.basedRootDatumProjection

end Langlands.GroupScheme.SplitPinning
