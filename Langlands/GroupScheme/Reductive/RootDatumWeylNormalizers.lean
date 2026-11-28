import Langlands.GroupScheme.Reductive.RootDatum
import Langlands.GroupScheme.Torus.CocharacterAction
import Langlands.GroupScheme.Dynamic.Functoriality
import Mathlib.LinearAlgebra.RootSystem.WeylGroup

/-! # Weyl elements of an actual root datum act on cocharacters through normalizing points -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k] {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

/-- A torus automorphism acting on characters by a root reflection acts on cocharacters by the
corresponding coreflection. -/
theorem IsRootDatumOf.cocharacterAut_eq_coreflection (i : T.toGrp ⟶ G) {J : Type*}
    {P : RootDatum J (characterLattice T) (cocharacterLattice T)}
    (hP : IsRootDatumOf i P) (a : J) (σ : T ≅ T)
    (hσ : characterAut σ = P.reflection a) (ν : cocharacterLattice T) :
    RealTorusSpace.cocharacterAut σ ν = P.coreflection a ν := by
  apply P.flip.toPerfPair.injective
  apply LinearMap.ext
  intro χ
  change P.toLinearMap χ (RealTorusSpace.cocharacterAut σ ν) =
    P.toLinearMap χ (P.coreflection a ν)
  rw [hP.1]
  have h := RealTorusSpace.latticePairing_aut σ (P.reflection a χ) ν
  rw [hσ, P.reflection_same] at h
  rw [h, RootPairing.reflection_apply, RootPairing.coreflection_apply]
  simp only [map_sub, LinearMap.sub_apply, map_zsmul, LinearMap.smul_apply, smul_eq_mul]
  rw [← hP.1]
  change P.toLinearMap χ ν - P.toLinearMap χ (P.coroot a) * P.toLinearMap (P.root a) ν =
    P.toLinearMap χ ν - P.toLinearMap (P.root a) ν * P.toLinearMap χ (P.coroot a)
  ring

/-- Every element of the Weyl group of an actual root datum acts on cocharacters as
postcomposition with a torus automorphism through which some rational point normalizes. -/
theorem IsRootDatumOf.exists_isNormalizingPoint_coweightEquiv (i : T.toGrp ⟶ G) {J : Type*}
    {P : RootDatum J (characterLattice T) (cocharacterLattice T)}
    (hP : IsRootDatumOf i P) (w : P.Aut) (hw : w ∈ P.weylGroup) :
    ∃ (n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) (σ : T ≅ T),
      IsNormalizingPoint i n σ ∧ ∀ ν, w.coweightEquiv ν = ν ≫ σ.hom := by
  induction hw using RootPairing.weylGroup.induction with
  | mem a =>
    obtain ⟨n, σ, hn, hσ⟩ := hP.2.2 a
    refine ⟨n, σ, hn, fun ν => ?_⟩
    rw [RootPairing.Equiv.reflection_coweightEquiv]
    exact (hP.cocharacterAut_eq_coreflection i a σ hσ ν).symm
  | one =>
    exact ⟨1, Iso.refl T, IsNormalizingPoint.one, fun ν => by simp⟩
  | mul a b _ _ ia ib =>
    obtain ⟨na, σa, hna, ha⟩ := ia
    obtain ⟨nb, σb, hnb, hb⟩ := ib
    refine ⟨nb * na, σa ≪≫ σb, hnb.mul hna, fun ν => ?_⟩
    rw [RootPairing.Equiv.mul_eq_comp, RootPairing.Equiv.coweightEquiv_comp_toLin,
      LinearEquiv.trans_apply, ha, hb, Iso.trans_hom, Category.assoc]

/-- Weyl elements of an actual root datum move dynamic parabolics of cocharacters by
conjugation with rational points. -/
theorem IsRootDatumOf.exists_parabolic_coweightEquiv (i : T.toGrp ⟶ G) {J : Type*}
    {P : RootDatum J (characterLattice T) (cocharacterLattice T)}
    (hP : IsRootDatumOf i P) (w : P.Aut) (hw : w ∈ P.weylGroup) :
    ∃ n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X, ∀ ν : cocharacterLattice T,
      Dynamic.parabolic (CommGroupScheme.groupHom (w.coweightEquiv ν) ≫ i) =
        Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i ≫ (G.innerIso n).hom) := by
  obtain ⟨n, σ, hn, hσ⟩ := hP.exists_isNormalizingPoint_coweightEquiv i w hw
  refine ⟨n, fun ν => ?_⟩
  rw [hσ, hn, ← Category.assoc]
  rfl

end Langlands.GroupScheme
