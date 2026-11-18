import Langlands.GroupScheme.Torus.Relative
import Langlands.GroupScheme.Torus.RelativeMultiplicativeType
import Langlands.GroupScheme.Torus.DiagonalizableBaseChange
import Langlands.GroupScheme.Torus.DiagonalizableCharacterProof
import Langlands.GroupScheme.Torus.DiagonalizablePower

/-! # Splitting diagonalizable relative tori -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

namespace Diagonalizable

private theorem restrictMap_id (R : CommRingCat.{u}) (M : Type u) [AddCommGroup M] :
    restrictMap R (AddMonoidHom.id M) = 𝟙 (groupScheme R M).toGrp := by
  simpa only [one_smul, powerHom, pow_one] using
    (restrictMap_nsmul_id R (A := M) 1)

/-- Over a field, an actual isomorphism of diagonalizable groups identifies their full
character groups, including possible torsion. -/
def characterGroupEquivOfIso (k : Type u) [Field k] {M N : Type u}
    [AddCommGroup M] [AddCommGroup N]
    (e : (groupScheme (CommRingCat.of k) M).toGrp ≅
      (groupScheme (CommRingCat.of k) N).toGrp) : M ≃+ N := by
  let f := Classical.choose ((DiagonalizableCharacter.restrictMap_bijective k M N).2 e.hom)
  have hf : restrictMap (CommRingCat.of k) f = e.hom :=
    Classical.choose_spec ((DiagonalizableCharacter.restrictMap_bijective k M N).2 e.hom)
  let g := Classical.choose ((DiagonalizableCharacter.restrictMap_bijective k N M).2 e.inv)
  have hg : restrictMap (CommRingCat.of k) g = e.inv :=
    Classical.choose_spec ((DiagonalizableCharacter.restrictMap_bijective k N M).2 e.inv)
  have hfg : f.comp g = AddMonoidHom.id M := by
    apply (DiagonalizableCharacter.restrictMap_bijective k M M).1
    change restrictMap (CommRingCat.of k) (f.comp g) =
      restrictMap (CommRingCat.of k) (AddMonoidHom.id M)
    rw [← restrictMap_comp, hf, hg, e.hom_inv_id, restrictMap_id]
  have hgf : g.comp f = AddMonoidHom.id N := by
    apply (DiagonalizableCharacter.restrictMap_bijective k N N).1
    change restrictMap (CommRingCat.of k) (g.comp f) =
      restrictMap (CommRingCat.of k) (AddMonoidHom.id N)
    rw [← restrictMap_comp, hg, hf, e.inv_hom_id, restrictMap_id]
  exact
    { toFun := g
      invFun := f
      left_inv := fun x => DFunLike.congr_fun hfg x
      right_inv := fun x => DFunLike.congr_fun hgf x
      map_add' := g.map_add }

/-- A splitting of a diagonalizable group over one field recovers finite free coordinates
for its full character group. -/
def characterEquivOfSplitIso (k : Type u) [Field k] {M I : Type u}
    [AddCommGroup M] [Finite I]
    (e : (groupScheme (CommRingCat.of k) M).toGrp ≅
      splitTorus (Spec (CommRingCat.of k)) I) : M ≃+ (I → ℤ) := by
  classical
  letI := Fintype.ofFinite I
  exact characterGroupEquivOfIso k
    (e ≪≫ (splitIso (CommRingCat.of k) (AddEquiv.refl (I → ℤ))).symm)

end Diagonalizable

namespace RelativeMultiplicativeType

/-- Finite free coordinates for the fixed character group split its relative
model over the original, arbitrary base scheme. -/
def diagonalizableSplitIso (S : Scheme.{u}) {M I : Type u} [AddCommGroup M] [Finite I]
    (b : M ≃+ (I → ℤ)) : diagonalizable S M ≅ splitTorus S I := by
  classical
  letI := Fintype.ofFinite I
  exact (GroupScheme.baseChange (Gm.toSpecZ S)).mapIso
    (Diagonalizable.splitIso (CommRingCat.of (ULift.{u} ℤ)) b) ≪≫
      splitTorus.baseChangeIso (Gm.toSpecZ S) I

end RelativeMultiplicativeType

namespace RelativeTorus

variable {S : Scheme.{u}} {T : GroupScheme S}

/-- A relative torus which is diagonalizable over a nonempty base is split over that base.
A single residue field in a split chart determines the fixed character group's coordinates. -/
theorem IsTorus.isSplitTorus_of_isDiagonalizable [Nonempty S]
    (hT : IsTorus T) (hdiag : RelativeMultiplicativeType.IsDiagonalizable T) :
    IsSplitTorus T := by
  obtain ⟨M, hM, _, ⟨e⟩⟩ := hdiag
  let : AddCommGroup M := hM
  obtain ⟨𝒰, h𝒰⟩ := hT
  obtain ⟨s⟩ := ‹Nonempty S›
  obtain ⟨i, y, _⟩ := 𝒰.exists_eq s
  let K := (𝒰.X i).residueField y
  let a := (𝒰.X i).fromSpecResidueField y
  let c := a ≫ 𝒰.f i
  have hsplit : IsSplitTorus ((GroupScheme.baseChange c).obj T) :=
    IsSplitTorus.of_iso (baseChangeCompIso (𝒰.f i) a T) ((h𝒰 i).baseChange a)
  let d : ((GroupScheme.baseChange c).obj T) ≅
      (Diagonalizable.groupScheme K M).toGrp :=
    (GroupScheme.baseChange c).mapIso e ≪≫
      RelativeMultiplicativeType.diagonalizableBaseChangeIso c M ≪≫
      Diagonalizable.baseChangeIso (Gm.toSpecZ (Spec K)) M
  obtain ⟨I, hI, ⟨f⟩⟩ := IsSplitTorus.of_iso d.symm hsplit
  let : Finite I := hI
  let b : M ≃+ (I → ℤ) := Diagonalizable.characterEquivOfSplitIso K f
  exact ⟨I, hI, ⟨e ≪≫ RelativeMultiplicativeType.diagonalizableSplitIso S b⟩⟩

end RelativeTorus

end Langlands.GroupScheme
