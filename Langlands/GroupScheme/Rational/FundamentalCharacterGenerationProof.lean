import Langlands.GroupScheme.Rational.TorusClassFunctionRestriction
import Langlands.GroupScheme.Rational.DominantWeightTriangularity
import Langlands.GroupScheme.Reductive.SplitSemisimpleRootSpanNecessity
import Langlands.GroupScheme.Rational.ClassFunctionsTorusDensity

/-! # Free generation of class functions by fundamental trace characters -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.SplitPinning

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (p : SplitPinning G) {r : ℕ}

/-- The torus restriction of the fundamental character map is evaluation at the restricted
fundamental characters. -/
theorem torusRestriction_comp_fundamentalCharacterMap (e : Fin r ≃ p.base.support)
    (F : ∀ a : p.base.support, p.FundamentalRepresentation a) :
    p.torusRestriction.comp (p.fundamentalCharacterMap e F) =
      MvPolynomial.aeval fun j => p.torusRestriction (F (e j)).character :=
  MvPolynomial.comp_aeval _ _

/-- The fundamental character map is bijective once torus restriction is injective and the
restricted fundamental characters freely generate the reflection-invariant elements. -/
theorem fundamentalCharacterMap_bijective_of_torus (e : Fin r ≃ p.base.support)
    (F : ∀ a : p.base.support, p.FundamentalRepresentation a)
    (hinj : Function.Injective p.torusRestriction)
    (hindep : Function.Injective
      (MvPolynomial.aeval (R := k) fun j => p.torusRestriction (F (e j)).character))
    (hgen : ∀ g : AddMonoidAlgebra k (characterLattice p.torus),
      (∀ α ν, g.coeff (p.rootDatum.reflection α ν) = g.coeff ν) →
        g ∈ (MvPolynomial.aeval (R := k)
          fun j => p.torusRestriction (F (e j)).character).range) :
    Function.Bijective (p.fundamentalCharacterMap e F) := by
  have hcomp := p.torusRestriction_comp_fundamentalCharacterMap e F
  refine ⟨fun q₁ q₂ h => hindep ?_, fun f => ?_⟩
  · rw [← hcomp, AlgHom.comp_apply, AlgHom.comp_apply, h]
  · obtain ⟨q, hq⟩ := hgen (p.torusRestriction f)
      (fun α ν => p.torusRestriction_coeff_reflection f α ν)
    refine ⟨q, hinj ?_⟩
    rw [← AlgHom.comp_apply, hcomp]
    exact hq

/-- For a semisimple group, a character of the supplied torus pairing to zero with every
simple coroot is zero. -/
theorem eq_zero_of_forall_simple_coroot_of_isSemisimple (hG : IsSemisimple G)
    {x : characterLattice p.torus}
    (hx : ∀ a ∈ p.base.support, p.rootDatum.toLinearMap x (p.rootDatum.coroot a) = 0) :
    x = 0 := by
  let _ := Fintype.ofFinite p.rootIndex
  exact Langlands.RootDatum.Triangular.eq_zero_of_forall_simple_coroot
    (hG.finite_quotient_rootSpan p.isSplitTorus p.isMaximalTorus.2.1 p.isRootDatum) hx

/-- The fundamental character map of a simply connected pinned group is bijective as soon as
torus restriction of class functions is injective. -/
theorem fundamentalCharacterMap_bijective_of_torusRestriction_injective
    (hG : IsSimplyConnected G) (e : Fin r ≃ p.base.support)
    (F : ∀ a : p.base.support, p.FundamentalRepresentation a)
    (hinj : Function.Injective p.torusRestriction) :
    Function.Bijective (p.fundamentalCharacterMap e F) := by
  classical
  let _ := Fintype.ofFinite p.rootIndex
  have hlam1 : ∀ j, p.rootDatum.toLinearMap (F (e j)).highestWeight
      (p.rootDatum.coroot (e j)) = 1 := by
    intro j
    simpa using (F (e j)).isFundamentalWeight (e j)
  have hlam0 : ∀ j (a : p.base.support), a ≠ e j →
      p.rootDatum.toLinearMap (F (e j)).highestWeight (p.rootDatum.coroot a) = 0 := by
    intro j a ha
    simpa [ha] using (F (e j)).isFundamentalWeight a
  have hc : ∀ j, Langlands.RootDatum.Triangular.IsTopWeight p.rootDatum p.base
      (F (e j)).highestWeight (p.torusRestriction (F (e j)).character) := fun j =>
    ⟨p.torusRestriction_character_coeff_highestWeight (F (e j)),
      fun _ hν => p.sub_mem_positiveRootMonoid_of_mem_support (F (e j)) hν⟩
  have hinv : ∀ q, Langlands.RootDatum.Triangular.IsReflectionInvariant p.rootDatum
      (MvPolynomial.aeval (R := k) (fun j => p.torusRestriction (F (e j)).character) q) := by
    intro q i x
    rw [← p.torusRestriction_comp_fundamentalCharacterMap e F, AlgHom.comp_apply]
    exact p.torusRestriction_coeff_reflection _ i x
  exact p.fundamentalCharacterMap_bijective_of_torus e F hinj
    (Langlands.RootDatum.Triangular.aeval_injective hlam1 hlam0 hc)
    (fun g hg => Langlands.RootDatum.Triangular.mem_range_aeval hlam1 hlam0 hc hinv
      (fun _ hx => p.eq_zero_of_forall_simple_coroot_of_isSemisimple hG.isSemisimple hx) g
      (fun i x => hg i x))

/-- Over an algebraically closed field, restriction of class functions to the split maximal
torus of a pinning is injective. -/
theorem torusRestriction_injective [IsAlgClosed k] :
    Function.Injective p.torusRestriction :=
  (injective_iff_map_eq_zero _).2 fun f hf =>
    TorusConjugation.classFunction_eq_zero p.inclusion p.isConnectedReductive p.isMaximalTorus
      p.isSplitTorus f fun _ _ _ s => p.pointCoordinates_torusPoint_eq_zero hf s

end Langlands.GroupScheme.SplitPinning

namespace Langlands.GroupScheme

/-- **Free generation by fundamental trace characters.** For a simply connected pinned group
over an algebraically closed field, the fundamental trace characters freely generate the
algebra of actual class functions. -/
theorem splitFundamentalCharacterGeneration : SplitFundamentalCharacterGenerationStatement.{u} :=
  fun _ _ _ _ _ p hG _ e F =>
    p.fundamentalCharacterMap_bijective_of_torusRestriction_injective hG e F
      p.torusRestriction_injective

end Langlands.GroupScheme
