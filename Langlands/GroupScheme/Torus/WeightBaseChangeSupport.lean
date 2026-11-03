import Langlands.GroupScheme.Torus.WeightBaseChange
import Langlands.GroupScheme.Rational.GenericLieWeights
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-! # Weight support under scalar extension -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false

section Span

variable {k K : Type u} [Field k] [CommRing K] [Algebra k K]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

local notation "G_K" => Functor.obj (GroupScheme.baseChange (algebraBaseMap k K)) G

local instance : IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k K)).obj G).X.hom := by
  change IsAffineHom (pullback.snd G.X.hom (algebraBaseMap k K))
  infer_instance

/-- The scalar-extended span of one actual weight space, in the actual pullback Lie kernel. -/
def extendedWeightSpace (i : T.toGrp ⟶ G) (χ : characterLattice T) :
    Submodule K (Additive (lieKernel G_K K)) :=
  Submodule.span K ((fun x => Lie.schemeScalarExtension (K := K) G (1 ⊗ₜ[k] x)) ''
    (weightSpace i χ : Set (Additive (lieKernel G k))))

/-- Every scalar-extended weight span lies in the corresponding actual pullback weight space. -/
theorem extendedWeightSpace_le (i : T.toGrp ⟶ G) (χ : characterLattice T) :
    extendedWeightSpace (K := K) i χ ≤
      weightSpace ((GroupScheme.baseChange (algebraBaseMap k K)).map i)
        (characterLattice.baseChange (algebraBaseMap k K) T χ) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨x, hx, rfl⟩
  exact weightSpace_baseChange_mem G i χ hx

/-- Scalar extension into a nontrivial algebra preserves nonvanishing of the weight span. -/
theorem extendedWeightSpace_ne_bot_iff [Nontrivial K]
    (i : T.toGrp ⟶ G) (χ : characterLattice T) :
    extendedWeightSpace (K := K) i χ ≠ ⊥ ↔ weightSpace i χ ≠ ⊥ := by
  constructor
  · intro h hbot
    apply h
    apply bot_unique
    apply Submodule.span_le.mpr
    rintro _ ⟨x, hx, rfl⟩
    change x ∈ weightSpace i χ at hx
    have hx0 : x = 0 := by simpa only [hbot, Submodule.mem_bot] using hx
    change Lie.schemeScalarExtension (K := K) G (1 ⊗ₜ[k] x) = 0
    rw [hx0, TensorProduct.tmul_zero, LinearEquiv.map_zero]
  · intro h hbot
    apply h
    apply bot_unique
    intro x hx
    have he : Lie.schemeScalarExtension (K := K) G (1 ⊗ₜ[k] x) ∈
        extendedWeightSpace (K := K) i χ := Submodule.subset_span ⟨x, hx, rfl⟩
    rw [hbot, Submodule.mem_bot] at he
    have hz : (1 : K) ⊗ₜ[k] x = 0 :=
      (Lie.schemeScalarExtension (K := K) G).injective
        (by simpa only [LinearEquiv.map_zero] using he)
    change x = 0
    simpa only [Module.FaithfullyFlat.one_tmul_eq_zero_iff] using hz

/-- If the original weight spaces span, so do their scalar-extended spans. -/
theorem iSup_extendedWeightSpace_eq_top (i : T.toGrp ⟶ G)
    (hi : iSup (weightSpace i) = ⊤) :
    iSup (extendedWeightSpace (K := K) i) = ⊤ := by
  apply top_unique
  intro y hy
  clear hy
  obtain ⟨z, rfl⟩ := (Lie.schemeScalarExtension (K := K) G).surjective y
  induction z using TensorProduct.inductionOn with
  | tmul c x =>
    have hx : x ∈ iSup (weightSpace i) := by rw [hi]; trivial
    have he : Lie.schemeScalarExtension (K := K) G (1 ⊗ₜ[k] x) ∈
        iSup (extendedWeightSpace (K := K) i) := by
      refine Submodule.iSup_induction (weightSpace i)
        (motive := fun x => Lie.schemeScalarExtension (K := K) G (1 ⊗ₜ[k] x) ∈
          iSup (extendedWeightSpace (K := K) i)) hx ?_ ?_ ?_
      · intro χ x hx
        exact Submodule.mem_iSup_of_mem χ (Submodule.subset_span ⟨x, hx, rfl⟩)
      · simpa only [TensorProduct.tmul_zero, LinearEquiv.map_zero] using
          (iSup (extendedWeightSpace (K := K) i)).zero_mem
      · intro x y hx hy
        simpa only [TensorProduct.tmul_add, LinearEquiv.map_add] using
          (iSup (extendedWeightSpace (K := K) i)).add_mem hx hy
    have hc := (iSup (extendedWeightSpace (K := K) i)).smul_mem c he
    simpa only [Lie.schemeScalarExtension_tmul, one_smul] using hc
  | add x y hx hy =>
    simpa only [LinearEquiv.map_add] using
      (iSup (extendedWeightSpace (K := K) i)).add_mem hx hy

end Span

end Langlands.GroupScheme
