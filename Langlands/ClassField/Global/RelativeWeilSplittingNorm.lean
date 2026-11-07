import Langlands.ClassField.Global.RelativeWeilSplittingTateInput
import Langlands.ClassField.Global.IdeleClassGaloisDescentProof
import Langlands.GroupTheory.CocycleSplittingInvariants

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits NumberField
open scoped NumberField
open Langlands.Global.AdelicFunctoriality

namespace Langlands.ClassField.Global

set_option backward.isDefEq.respectTransparency false

attribute [local instance] relativeIdeleClassAction

variable (F E : Type u) [Field F] [NumberField F] [Field E] [NumberField E]
  [Algebra F E] [IsGalois F E]

/-- The actual idele-class inclusion, with codomain the invariant vectors. -/
def ideleClassInclusionInvariants :
    Additive (IdeleClassGroup (𝓞 F) F) →+
      (relativeIdeleClassRepresentation F E).ρ.invariants where
  toFun a := ⟨Additive.ofMul (ideleClassInclusion (K := F) (L := E) a.toMul), by
    intro σ
    exact congrArg Additive.ofMul
      (((ideleClassGaloisDescent F E).2 _).mpr ⟨a.toMul, rfl⟩ σ)⟩
  map_zero' := Subtype.ext (congrArg Additive.ofMul (map_one
    (ideleClassInclusion (K := F) (L := E))))
  map_add' a b := Subtype.ext (congrArg Additive.ofMul (map_mul
    (ideleClassInclusion (K := F) (L := E)) a.toMul b.toMul))

/-- Galois descent identifies the actual coefficient invariants with the
base idele classes, written additively. -/
def ideleClassInvariantsEquiv :
    Additive (IdeleClassGroup (𝓞 F) F) ≃+
      (relativeIdeleClassRepresentation F E).ρ.invariants :=
  AddEquiv.ofBijective (ideleClassInclusionInvariants F E) ⟨by
    intro a b h
    have hab : a.toMul = b.toMul := (ideleClassGaloisDescent F E).1
      (congrArg (fun x : (relativeIdeleClassRepresentation F E).ρ.invariants =>
        x.val.toMul) h)
    exact congrArg Additive.ofMul hab, by
    intro x
    obtain ⟨a, ha⟩ := ((ideleClassGaloisDescent F E).2 x.val.toMul).mp
      (fun σ => congrArg Additive.toMul (x.property σ))
    exact ⟨Additive.ofMul a, Subtype.ext (congrArg Additive.ofMul ha)⟩⟩

@[simp] lemma ideleClassInvariantsEquiv_val
    (a : Additive (IdeleClassGroup (𝓞 F) F)) :
    (ideleClassInvariantsEquiv F E a).val =
      Additive.ofMul (ideleClassInclusion (K := F) (L := E) a.toMul) := rfl

lemma ideleClassInvariantsEquiv_symm_inclusion
    (x : (relativeIdeleClassRepresentation F E).ρ.invariants) :
    ideleClassInclusion (K := F) (L := E)
        ((ideleClassInvariantsEquiv F E).symm x).toMul =
      x.val.toMul :=
  congrArg (fun y : (relativeIdeleClassRepresentation F E).ρ.invariants =>
    y.val.toMul) ((ideleClassInvariantsEquiv F E).apply_symm_apply x)

namespace RelativeWeilGroup

variable (c : FundamentalClass.ClassFamily.{u})

/-- The actual norm from chosen splitting coinvariants, descended to base
idele classes by Galois descent. -/
def splittingNormToBase :
    (splittingRepresentation c F E).ρ.Coinvariants →+
      Additive (IdeleClassGroup (𝓞 F) F) := by
  let := Fintype.ofFinite (E ≃ₐ[F] E)
  exact (ideleClassInvariantsEquiv F E).symm.toAddMonoidHom.comp
    (NormalizedTwoCocycle.SplittingModule.splittingNorm
      (ClassExtension.representative (c F E))).toAddMonoidHom

/-- Inclusion to `C_E` characterizes the descended splitting norm. -/
lemma ideleClassInclusion_splittingNormToBase
    (x : (splittingRepresentation c F E).ρ.Coinvariants) :
    letI := Fintype.ofFinite (E ≃ₐ[F] E)
    ideleClassInclusion (K := F) (L := E) (splittingNormToBase F E c x).toMul =
      (NormalizedTwoCocycle.SplittingModule.splittingNorm
        (ClassExtension.representative (c F E)) x).val.toMul := by
  let := Fintype.ofFinite (E ≃ₐ[F] E)
  exact ideleClassInvariantsEquiv_symm_inclusion F E _

/-- The descended splitting norm is bijective at a generating,
restriction-compatible global class family. -/
lemma splittingNormToBase_bijective
    (hgen : FundamentalClass.Generates c) (hres : FundamentalClass.Restriction c) :
    Function.Bijective (splittingNormToBase F E c) := by
  let := Fintype.ofFinite (E ≃ₐ[F] E)
  have hn : Function.Bijective
      (NormalizedTwoCocycle.SplittingModule.splittingNorm
        (ClassExtension.representative (c F E))) := by
    apply NormalizedTwoCocycle.SplittingModule.splittingNorm_bijective
    intro n
    rw [show NormalizedTwoCocycle.cohomologyClass
        (ClassExtension.representative (c F E)) = c F E from
      ClassExtension.cohomologyClass_representative (c F E)]
    exact fundamentalClass_tateCup_bijective F E c hgen hres n
  exact (ideleClassInvariantsEquiv F E).symm.bijective.comp hn

end RelativeWeilGroup

end Langlands.ClassField.Global
