import Langlands.GroupScheme.Torus.EndomorphismDichotomy
import Langlands.GroupScheme.Torus.HomKernelDiagonalizable
import Langlands.GroupScheme.Torus.ExponentCharacters

/-! # Full kernels of collections of exponent characters over arbitrary rings -/

noncomputable section

universe u

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Diagonalizable

variable (R : CommRingCat.{u}) (I : Type u) [Fintype I] [DecidableEq I]
  (N : AddSubgroup (I → ℤ))

/-- The full quotient of the exponent lattice; no saturation is taken. -/
abbrev exponentKernelLattice := (I → ℤ) ⧸ N

/-- The diagonalizable group killing every exponent in `N`. -/
abbrev exponentKernel : CommGroupScheme (Spec R) :=
  groupScheme R (exponentKernelLattice I N)

/-- The inclusion of the full exponent kernel into the coordinate split torus. -/
def exponentKernelHom : (exponentKernel R I N).toGrp ⟶ splitTorus (Spec R) I :=
  restrictMap R (QuotientAddGroup.mk' N) ≫
    (splitIso R (AddEquiv.refl (I → ℤ))).hom

/-- The exponent kernel is a closed subgroup over every commutative ring. -/
theorem isClosedSubgroup_exponentKernelHom :
    IsClosedSubgroup (exponentKernelHom R I N) := by
  have := isClosedImmersion_restrictMap R (QuotientAddGroup.mk' N)
    (QuotientAddGroup.mk'_surjective N)
  have : IsIso (splitIso R (AddEquiv.refl (I → ℤ))).hom.hom.hom.left :=
    Functor.map_isIso (Grp.forget _ ⋙ Over.forget _)
      (splitIso R (AddEquiv.refl (I → ℤ))).hom
  change IsClosedImmersion
    ((restrictMap R (QuotientAddGroup.mk' N)).hom.hom.left ≫
      (splitIso R (AddEquiv.refl (I → ℤ))).hom.hom.hom.left)
  infer_instance

/-- The character group of the full kernel is finitely generated, retaining torsion. -/
instance fg_exponentKernelLattice : AddGroup.FG (exponentKernelLattice I N) :=
  inferInstanceAs (AddGroup.FG ((I → ℤ) ⧸ N))

variable {R I N}

/-- Evaluating an exponent after the split-diagonalizable comparison evaluates
the corresponding character of the exponent lattice. -/
theorem exponentValue_splitIso {U : Over (Spec R)}
    (x : U ⟶ (groupScheme R (I → ℤ)).X) (m : I → ℤ) :
    splitTorus.exponentValue I
        (splitTorus.pointsEquiv I U
          (x ≫ (splitIso R (AddEquiv.refl (I → ℤ))).hom.hom.hom))
        (.ofAdd m) =
      characterPointsEquiv R (I → ℤ) U x (.ofAdd m) := by
  have h := isoOfPointModels_hom
    (fun T : Over (Spec R) => I → (Γ(T.left, ⊤))ˣ)
    (fun a => splitTorus.unitsRestrict I a)
    (splitPointsEquiv R (AddEquiv.refl (I → ℤ)))
    (fun T => splitTorus.pointsEquiv I T)
    (splitPointsEquiv_naturality R (AddEquiv.refl (I → ℤ)))
    (fun a y => splitTorus.pointsEquiv_naturality I a y) U x
  change splitTorus.pointsEquiv I U
      (x ≫ (splitIso R (AddEquiv.refl (I → ℤ))).hom.hom.hom) =
    charEquiv (AddEquiv.refl (I → ℤ)) _ (characterPointsEquiv R (I → ℤ) U x) at h
  rw [h]
  exact congrArg (fun χ : Multiplicative (I → ℤ) →* (Γ(U.left, ⊤))ˣ =>
    χ (.ofAdd m))
      ((charEquiv (AddEquiv.refl (I → ℤ)) _).symm_apply_apply _)

/-- Every exponent evaluates on the kernel at its full quotient class. -/
theorem exponentValue_exponentKernelHom {U : Over (Spec R)}
    (x : U ⟶ (exponentKernel R I N).X) (m : I → ℤ) :
    splitTorus.exponentValue I
        (splitTorus.pointsEquiv I U (x ≫ (exponentKernelHom R I N).hom.hom))
        (.ofAdd m) =
      characterPointsEquiv R (exponentKernelLattice I N) U x
        (.ofAdd (QuotientAddGroup.mk' N m)) := by
  rw [exponentKernelHom, Grp.comp_hom_hom, ← Category.assoc,
    exponentValue_splitIso]
  exact pointsEquiv_restrictMap R (QuotientAddGroup.mk' N) x m

/-- Each imposed relation is killed scheme-theoretically on every test scheme. -/
theorem exponentValue_exponentKernelHom_eq_one {U : Over (Spec R)}
    (x : U ⟶ (exponentKernel R I N).X) {m : I → ℤ} (hm : m ∈ N) :
    splitTorus.exponentValue I
        (splitTorus.pointsEquiv I U (x ≫ (exponentKernelHom R I N).hom.hom))
        (.ofAdd m) = 1 := by
  have hzero : QuotientAddGroup.mk' N m = 0 :=
    (QuotientAddGroup.eq_zero_iff m).mpr hm
  rw [exponentValue_exponentKernelHom, hzero]
  exact map_one _

/-- The image is exactly the intersection of all the specified character
kernels, on every scheme over the base. -/
theorem mem_range_exponentKernelHom_iff {U : Over (Spec R)}
    (t : U ⟶ (splitTorus (Spec R) I).X) :
    t ∈ (SubgroupFunctor.range (exponentKernelHom R I N)).carrier U ↔
      ∀ m ∈ N, splitTorus.exponentValue I (splitTorus.pointsEquiv I U t)
        (.ofAdd m) = 1 := by
  constructor
  · rintro ⟨x, rfl⟩ m hm
    exact exponentValue_exponentKernelHom_eq_one x hm
  · intro ht
    let χ : subgroupAnnihilator N (Γ(U.left, ⊤))ˣ :=
      ⟨(charEquiv (AddEquiv.refl (I → ℤ)) _).symm
        (splitTorus.pointsEquiv I U t), ht⟩
    let ψ := (subgroupQuotientCharactersEquiv N _).symm χ
    let x := (characterPointsEquiv R (exponentKernelLattice I N) U).symm ψ
    refine ⟨x, ?_⟩
    apply (splitTorus.pointsEquiv I U).injective
    apply (charEquiv (AddEquiv.refl (I → ℤ)) _).symm.injective
    apply MonoidHom.ext
    intro m
    change splitTorus.exponentValue I
        (splitTorus.pointsEquiv I U (x ≫ (exponentKernelHom R I N).hom.hom))
        (.ofAdd m.toAdd) =
      splitTorus.exponentValue I (splitTorus.pointsEquiv I U t) (.ofAdd m.toAdd)
    rw [exponentValue_exponentKernelHom]
    change ((characterPointsEquiv R (exponentKernelLattice I N) U)
      ((characterPointsEquiv R (exponentKernelLattice I N) U).symm ψ))
        (.ofAdd (subgroupQuotientMap N m.toAdd)) = χ.val (.ofAdd m.toAdd)
    rw [MulEquiv.apply_symm_apply]
    exact subgroupQuotientCharactersEquiv_symm_apply N _ χ m.toAdd

end Langlands.GroupScheme.Diagonalizable
