import Langlands.GroupScheme.Lie.WeightImagePullback
import Langlands.GroupScheme.Reductive.RootReducednessReduction

/-! # Weight spaces in actual cocharacter centralizers -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace Lie

variable {R : CommRingCat.{u}} {T : CommGroupScheme (Spec R)}
  {M G : GroupScheme (Spec R)} [IsAffineHom M.X.hom] [IsAffineHom G.X.hom]

/-- If a monomorphic subgroup contains an entire ambient weight space in its
Lie image, its differential identifies the two intrinsic weight spaces. -/
def weightSpaceEquivOfLeRange (s : M ⟶ G) [Mono s.hom.hom]
    (t : T.toGrp ⟶ M) (χ : characterLattice T)
    (hχ : weightSpace (t ≫ s) χ ≤ LinearMap.range (targetMapLinear s R)) :
    weightSpace t χ ≃ₗ[R] weightSpace (t ≫ s) χ :=
  LinearEquiv.ofBijective (weightSpaceMap s t χ) ⟨weightSpaceMap_injective s t χ, by
    intro X
    obtain ⟨Y, hY⟩ := hχ X.property
    refine ⟨⟨Y, (lieKernelHomLinear_mem_weightSpace_iff s t χ Y).mp ?_⟩, ?_⟩
    · rw [hY]
      exact X.property
    · exact Subtype.ext hY⟩

@[simp] theorem weightSpaceEquivOfLeRange_coe (s : M ⟶ G) [Mono s.hom.hom]
    (t : T.toGrp ⟶ M) (χ : characterLattice T)
    (hχ : weightSpace (t ≫ s) χ ≤ LinearMap.range (targetMapLinear s R))
    (X : weightSpace t χ) :
    (weightSpaceEquivOfLeRange s t χ hχ X : Additive (lieKernel G R)) =
      targetMapLinear s R X := rfl

end Lie

namespace Dynamic

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G L : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [IsAffineHom L.X.hom] [LocallyOfFiniteType G.X.hom]
  (i : T.toGrp ⟶ G) (ζ : cocharacterLattice T) {j : L ⟶ G}
  (hj : (centralizer (CommGroupScheme.groupHom ζ ≫ i)).IsRepresentedBy j)

/-- A weight annihilating the cocharacter has the same intrinsic weight
space in its actual centralizer as in the ambient group. -/
def weightSpaceEquiv_torusFactor (χ : characterLattice T)
    (hχ : latticePairing T χ ζ = 0) :
    weightSpace (torusFactor i (CommGroupScheme.groupHom ζ) hj) χ ≃ₗ[k]
      weightSpace i χ := by
  letI : Mono j.hom.hom := hj.1
  have hχ' :
      weightSpace (torusFactor i (CommGroupScheme.groupHom ζ) hj ≫ j) χ ≤
        LinearMap.range (Lie.targetMapLinear j k) := by
    rw [torusFactor_comp]
    exact RootReducedness.weightSpace_le_range_centralizer i ζ hj hχ
  exact (Lie.weightSpaceEquivOfLeRange j
    (torusFactor i (CommGroupScheme.groupHom ζ) hj) χ hχ').trans
      (LinearEquiv.ofEq _ _ (congrArg (fun t => weightSpace t χ)
        (torusFactor_comp i (CommGroupScheme.groupHom ζ) hj)))

/-- The line property for a weight annihilating a cocharacter is equivalent
in the centralizer and in the ambient group. -/
theorem nonempty_line_torusFactor_iff (χ : characterLattice T)
    (hχ : latticePairing T χ ζ = 0) :
    Nonempty (k ≃ₗ[k] weightSpace (torusFactor i (CommGroupScheme.groupHom ζ) hj) χ) ↔
      Nonempty (k ≃ₗ[k] weightSpace i χ) := by
  let e := weightSpaceEquiv_torusFactor i ζ hj χ hχ
  constructor
  · rintro ⟨f⟩
    exact ⟨f.trans e⟩
  · rintro ⟨f⟩
    exact ⟨f.trans e.symm⟩

end Dynamic

end Langlands.GroupScheme
