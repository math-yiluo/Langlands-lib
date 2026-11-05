import Langlands.GroupScheme.Reductive.RootDatumStatement
import Langlands.GroupScheme.Rational.CocharacterCentralizer
import Langlands.GroupScheme.Rational.PositiveRootStabilizerReduction
import Langlands.GroupScheme.Rational.GenericCentralizerProof
import Mathlib.LinearAlgebra.RootSystem.Finite.CanonicalBilinear

/-! # A fixed regular integral character forces torus centralization -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {i : T.toGrp ⟶ G} [IsAffineHom G.X.hom]
    {J : Type v} [Fintype J]
    (P : RootDatum J (characterLattice T) (cocharacterLattice T))

private theorem integral_rootForm_root_pos (a : J) :
    0 < P.RootForm (P.root a) (P.root a) := by
  rw [P.rootForm_apply_apply]
  apply Finset.sum_pos'
  · intro b _
    exact mul_self_nonneg _
  · exact ⟨a, Finset.mem_univ _, by simp⟩

private theorem integral_rootForm_coroot (x : characterLattice T) (a : J) :
    2 * P.RootForm x (P.root a) =
      P.RootForm (P.root a) (P.root a) * P.coroot' a x := by
  have h := congrArg (fun y : cocharacterLattice T => P.toLinearMap x y)
    (P.rootForm_self_smul_coroot a)
  have hs : P.RootForm (P.root a) x = P.RootForm x (P.root a) :=
    P.rootForm_symmetric.eq _ _
  simp only [map_smul, map_nsmul, smul_eq_mul, nsmul_eq_mul] at h
  rw [P.toLinearMap_apply_apply_Polarization, hs] at h
  exact h.symm

/-- The integral polarization of a coroot-regular actual character is generic.
No extension of scalars or existence of root data is used. -/
theorem polarization_isGenericCocharacter (hP : IsRootDatumOf i P)
    (x : characterLattice T) (hx : ∀ a, P.coroot' a x ≠ 0) :
    IsGenericCocharacter i (P.Polarization x) := by
  intro α hα hz
  obtain ⟨a, rfl⟩ : ∃ a : J, P.root a = α := by
    rw [← Set.mem_range, hP.2.1]
    exact hα
  have hf : P.RootForm x (P.root a) = 0 := by
    rw [← P.toLinearMap_apply_apply_Polarization, hP.1]
    exact hz
  have he := integral_rootForm_coroot P x a
  rw [hf, mul_zero] at he
  exact (mul_ne_zero (ne_of_gt (integral_rootForm_root_pos P a)) (hx a)) he.symm

/-- An actual generic cocharacter, with its certificate, constructed integrally
from a supplied root datum and a character regular on its coroots. -/
def genericCocharacterOfRegularWeight (hP : IsRootDatumOf i P)
    (x : characterLattice T) (hx : ∀ a, P.coroot' a x ≠ 0) :
    {ν : cocharacterLattice T // IsGenericCocharacter i ν} :=
  ⟨P.Polarization x, polarization_isGenericCocharacter P hP x hx⟩

theorem genericCocharacterOfRegularWeight_coe (hP : IsRootDatumOf i P)
    (x : characterLattice T) (hx : ∀ a, P.coroot' a x ≠ 0) :
    (genericCocharacterOfRegularWeight P hP x hx).val = P.Polarization x :=
  rfl

variable [Mono i.hom.hom.left]

/-- A Weyl representative fixing the weight fixes its integral polarization
under the inverse normalizing automorphism. -/
theorem polarization_comp_normalizingAut_inv_eq
    (hP : IsRootDatumOf i P) (x : characterLattice T)
    (n : normalizerPoints i) (w : P.weylGroup)
    (hw : weylAction i n = RootPairing.Equiv.weightHom P w.val)
    (hfixed : weylAction i n x = x) :
    P.Polarization x ≫ (normalizingAut i n).inv = P.Polarization x := by
  have hfixed' : w • x = x := by
    change RootPairing.Equiv.weightHom P w.val x = x
    rw [← hw]
    exact hfixed
  let B : P.InvariantForm :=
    { form := P.RootForm
      symm := P.rootForm_symmetric
      ne_zero := fun a => ne_of_gt (integral_rootForm_root_pos P a)
      isOrthogonal_reflection := P.rootForm_reflection_reflection_apply }
  apply P.flip.toPerfPair.injective
  apply LinearMap.ext
  intro y
  change P.toLinearMap y (P.Polarization x ≫ (normalizingAut i n).inv) =
    P.toLinearMap y (P.Polarization x)
  have he := RootPairing.InvariantForm.apply_weylGroup_smul P (B := B) w x y
  rw [hfixed'] at he
  calc
    P.toLinearMap y (P.Polarization x ≫ (normalizingAut i n).inv) =
        latticePairing T y (P.Polarization x ≫ (normalizingAut i n).inv) := by
      rw [hP.1]
    _ = latticePairing T (weylAction i n y) (P.Polarization x) :=
      (latticePairing_weylAction i n y (P.Polarization x)).symm
    _ = P.toLinearMap (w • y) (P.Polarization x) := by
      rw [← hP.1, hw]
      rfl
    _ = P.RootForm x (w • y) := P.toLinearMap_apply_apply_Polarization x (w • y)
    _ = P.RootForm x y := he
    _ = P.toLinearMap y (P.Polarization x) :=
      (P.toLinearMap_apply_apply_Polarization x y).symm

/-- Given the actual Weyl representative, a normalizing point fixing a
coroot-regular integral character lies in the actual torus centralizer. -/
theorem mem_centralizerPoints_of_fixed_regular_weight_of_weyl
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hP : IsRootDatumOf i P) (x : characterLattice T)
    (hx : ∀ a, P.coroot' a x ≠ 0)
    (n : normalizerPoints i) (w : P.weylGroup)
    (hw : weylAction i n = RootPairing.Equiv.weightHom P w.val)
    (hfixed : weylAction i n x = x) :
    n.val ∈ centralizerPoints i := by
  have hinv := polarization_comp_normalizingAut_inv_eq P hP x n w hw hfixed
  have hforward : cocharacterAut (normalizingAut i n) (P.Polarization x) =
      P.Polarization x := by
    rw [cocharacterAut_apply]
    have he := congrArg
      (fun ν : cocharacterLattice T => ν ≫ (normalizingAut i n).hom) hinv
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using he.symm
  have hn := (normalizerPoint_mem_dynamicCentralizer_iff i n (P.Polarization x)).mpr
    hforward
  rw [genericCentralizer k G hG T i hi (P.Polarization x)
    (polarization_isGenericCocharacter P hP x hx), torusCentralizer_carrier_base] at hn
  exact hn

/-- The exact actual Weyl-image comparison supplies the representative needed
by the regular-character centralizer criterion. Its equality is explicit input. -/
theorem mem_centralizerPoints_of_fixed_regular_weight
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hP : IsRootDatumOf i P)
    (himage : weylImage i = P.weylGroup.map (RootPairing.Equiv.weightHom P))
    (x : characterLattice T) (hx : ∀ a, P.coroot' a x ≠ 0)
    (n : normalizerPoints i) (hfixed : weylAction i n x = x) :
    n.val ∈ centralizerPoints i := by
  have hn : weylAction i n ∈ P.weylGroup.map (RootPairing.Equiv.weightHom P) := by
    rw [← himage]
    exact ⟨n, rfl⟩
  obtain ⟨w, hw, he⟩ := hn
  exact mem_centralizerPoints_of_fixed_regular_weight_of_weyl P hG hi hP x hx
    n ⟨w, hw⟩ he.symm hfixed

end Langlands.GroupScheme
