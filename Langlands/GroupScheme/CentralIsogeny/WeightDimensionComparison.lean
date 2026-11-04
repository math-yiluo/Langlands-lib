import Langlands.GroupScheme.CentralIsogeny.NonzeroWeights
import Langlands.GroupScheme.Lie.DimensionInduction
import Langlands.GroupScheme.Torus.WeightDecomposition
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # Nonzero weight comparison from total and zero-weight dimensions -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj DirectSum

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

private theorem block_surjective_of_dimensions
    {K : Type*} [Field K] {V W : Type*} [AddCommGroup V] [AddCommGroup W]
    [Module K V] [Module K W] [FiniteDimensional K V] [FiniteDimensional K W]
    {I : Type*} [Zero I] [DecidableEq I] (A : I → Submodule K V) (B : I → Submodule K W)
    (hA : DirectSum.IsInternal A) (hB : DirectSum.IsInternal B)
    (f : ∀ a, A a →ₗ[K] B a) (hf : ∀ a, a ≠ 0 → Function.Injective (f a))
    (hdim : Module.finrank K V = Module.finrank K W)
    (hzero : Module.finrank K (A 0) = Module.finrank K (B 0))
    {a : I} (ha : a ≠ 0) : Function.Surjective (f a) := by
  classical
  let eV := LinearEquiv.ofBijective (DirectSum.coeLinearMap A) hA
  let eW := LinearEquiv.ofBijective (DirectSum.coeLinearMap B) hB
  have : FiniteDimensional K (⨁ b, A b) := eV.symm.finiteDimensional
  have : FiniteDimensional K (⨁ b, B b) := eW.symm.finiteDimensional
  obtain ⟨e0⟩ := FiniteDimensional.nonempty_linearEquiv_of_finrank_eq hzero
  let g (b : I) : A b →ₗ[K] B b :=
    if hb : b = 0 then by subst b; exact e0.toLinearMap else f b
  have hg (b : I) : Function.Injective (g b) := by
    by_cases hb : b = 0
    · subst b
      simpa only [g, dite_eq_left rfl, LinearEquiv.coe_toLinearMap] using e0.injective
    · simpa only [g, dite_eq_right hb] using hf b hb
  have hsum : Module.finrank K (⨁ b, A b) = Module.finrank K (⨁ b, B b) :=
    eV.finrank_eq.trans (hdim.trans eW.finrank_eq.symm)
  have hsurj : Function.Surjective (DirectSum.lmap g) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hsum).mp
      ((DirectSum.lmap_injective g).mpr hg)
  simpa only [g, dite_eq_right ha] using (DirectSum.lmap_surjective g).mp hsurj a

variable {k : Type u} [Field k]
  {G H : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
  [LocallyOfFiniteType G.X.hom] [LocallyOfFiniteType H.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}

/-- Equal total and zero-weight dimensions force surjectivity of the actual
differential on every nonzero weight space when the full kernel is central. -/
theorem Lie.weightSpaceMap_surjective_of_dimensions (q : G ⟶ H)
    (hq : IsCentral (kernelι q)) (i : T.toGrp ⟶ G) (hT : IsSplitTorus T.toGrp)
    (hdim : Lie.dimension G = Lie.dimension H)
    (hzero : Module.finrank k (weightSpace i 0) =
      Module.finrank k (weightSpace (i ≫ q) 0))
    {χ : characterLattice T} (hχ : χ ≠ 0) :
    Function.Surjective (Lie.weightSpaceMap q i χ) := by
  classical
  exact block_surjective_of_dimensions (K := k) (weightSpace i) (weightSpace (i ≫ q))
    (isInternal_weightSpace_of_isSplitTorus k G T hT i)
    (isInternal_weightSpace_of_isSplitTorus k H T hT (i ≫ q))
    (Lie.weightSpaceMap q i)
    (fun ψ hψ => Lie.weightSpaceMap_injective_of_central_kernel q hq i hT hψ)
    hdim hzero hχ

/-- Under equal total and zero-weight dimensions, the actual differential
identifies each nonzero weight space with the corresponding target space. -/
def Lie.nonzeroWeightSpaceEquivOfDimensions (q : G ⟶ H)
    (hq : IsCentral (kernelι q)) (i : T.toGrp ⟶ G) (hT : IsSplitTorus T.toGrp)
    (hdim : Lie.dimension G = Lie.dimension H)
    (hzero : Module.finrank k (weightSpace i 0) =
      Module.finrank k (weightSpace (i ≫ q) 0))
    {χ : characterLattice T} (hχ : χ ≠ 0) :
    weightSpace i χ ≃ₗ[k] weightSpace (i ≫ q) χ :=
  LinearEquiv.ofBijective (Lie.weightSpaceMap q i χ)
    ⟨Lie.weightSpaceMap_injective_of_central_kernel q hq i hT hχ,
      Lie.weightSpaceMap_surjective_of_dimensions q hq i hT hdim hzero hχ⟩

@[simp]
theorem Lie.nonzeroWeightSpaceEquivOfDimensions_coe (q : G ⟶ H)
    (hq : IsCentral (kernelι q)) (i : T.toGrp ⟶ G) (hT : IsSplitTorus T.toGrp)
    (hdim : Lie.dimension G = Lie.dimension H)
    (hzero : Module.finrank k (weightSpace i 0) =
      Module.finrank k (weightSpace (i ≫ q) 0))
    {χ : characterLattice T} (hχ : χ ≠ 0) (X : weightSpace i χ) :
    (Lie.nonzeroWeightSpaceEquivOfDimensions q hq i hT hdim hzero hχ X :
      Additive (lieKernel H k)) = Lie.targetMapLinear q k X := rfl

/-- A central full kernel and equal total and zero-weight dimensions give
equality of actual root supports for the same split torus acting through the map. -/
theorem roots_comp_eq_of_central_kernel_of_dimensions (q : G ⟶ H)
    (hq : IsCentral (kernelι q)) (i : T.toGrp ⟶ G) (hT : IsSplitTorus T.toGrp)
    (hdim : Lie.dimension G = Lie.dimension H)
    (hzero : Module.finrank k (weightSpace i 0) =
      Module.finrank k (weightSpace (i ≫ q) 0)) :
    roots (i ≫ q) = roots i := by
  apply Set.Subset.antisymm
  · intro χ hχ
    refine ⟨hχ.1, ?_⟩
    intro hbot
    apply hχ.2
    apply eq_bot_iff.mpr
    intro Y hY
    obtain ⟨X, hXY⟩ :=
      Lie.weightSpaceMap_surjective_of_dimensions q hq i hT hdim hzero hχ.1 ⟨Y, hY⟩
    have hX : X = 0 := by
      apply Subtype.ext
      simpa only [Submodule.mem_bot, Submodule.coe_zero] using (eq_bot_iff.mp hbot) X.property
    rw [hX, map_zero] at hXY
    exact congrArg Subtype.val hXY.symm
  · exact roots_subset_comp_of_central_kernel q hq i hT

end Langlands.GroupScheme
