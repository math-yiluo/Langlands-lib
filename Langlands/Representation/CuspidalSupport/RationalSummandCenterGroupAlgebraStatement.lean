import Langlands.Representation.CuspidalSupport.RationalUniversalSmallProgeneratorStatement
import Langlands.Representation.Induction.OpenAdjunction

/-! Renard VI.4.4, Proposition: the center of the endomorphism ring of the
compact induction of one irreducible summand ρ of the restriction of an
irreducible cuspidal π to the common norm kernel H⁰ is isomorphic to the group
algebra of T/H⁰, the class of t going to an element supported on H⁰t⁻¹ that acts
by ω(t) on every Hom space into an unramified twist π ⊗ ω. -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology Langlands.Plancherel
open scoped CategoryTheory.MonObj

namespace Langlands.CuspidalSupport

universe uF uV

open Aubert.General Aubert.General.RationalPointFamily GroupScheme Induction

/-- VI.4.4, Proposition: let π be irreducible cuspidal, ρ an irreducible smooth
representation of the common norm kernel H⁰ with an injective equivariant map
into the restriction of π, and T the intersection of the kernels of the
unramified characters ω with π ⊗ ω ≅ π. There is an isomorphism of ℂ-algebras
from the group algebra ℂ[T/H⁰] onto the center of the endomorphism ring of
ind_{H⁰}^G ρ such that, for t ∈ T, the image ψ_t of the class of t has every
ψ_t(f_w) supported in H⁰t⁻¹ and acts on every map ind ρ → π ⊗ ω, by
precomposition, as multiplication by ω(t). -/
def RationalSummandCenterGroupAlgebraStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G)
    (S : CommGroupScheme (Spec (CommRingCat.of F))) (i : S.toGrp ⟶ G)
    (hi : IsMaximalSplitTorus i),
    haveI := hG.isAffineHom
    haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    haveI := hG.smooth
    haveI := hi.isSplitSubtorus.mono
    letI : TopologicalSpace (GroupScheme.rationalPoints G) := rationalPointTopology F G.X
    haveI : IsTopologicalGroup (GroupScheme.rationalPoints G) :=
      rationalPoint_isTopologicalGroup F G
    ∀ [LocallyCompactSpace (GroupScheme.rationalPoints G)]
      [NonarchimedeanGroup (GroupScheme.rationalPoints G)]
      [T2Space (GroupScheme.rationalPoints G)]
      (ν : cocharacterLattice S) (hν : IsGenericCocharacter i ν)
      (hStandard : StandardCocharacterStatement.{uF})
      (hRoots : HasRelativeRootSystem i)
      (hU : ∀ I, IsClosed (unipotent i ν I : Set (GroupScheme.rationalPoints G))),
      letI := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
      let h := isSemidirectDecomposition_of_standardCocharacterStatement
        i ν hStandard hG hi hν
      ∀ π : SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G),
        π.IsIrreducible →
        IsCuspidal (parabolic i ν) (levi i ν) (unipotent i ν) h hU π →
        ∀ ρ : SmoothRep.{0, uF, uV} ℂ (rationalCommonNormKernel G),
          ρ.IsIrreducible →
          ∀ j : ρ ⟶ SmoothRep.restrictSubgroup (rationalCommonNormKernel G) π,
            Function.Injective (SmoothRep.hom j) →
            let T : Subgroup (GroupScheme.rationalPoints G) :=
              ⨅ (ω : unramifiedCharacters (fun χ => (rationalNormCharacters G χ).toMul))
                (_ : Nonempty (rationalUnramifiedTwist G ω π ≅ π)),
                ω.val.toMonoidHom.ker
            let I := (compactInductionFunctor (rationalCommonNormKernel G)).obj
              (SmoothRep.toRep.obj ρ)
            let f : ρ → I := fun w => unitFunction (rationalCommonNormKernel G)
              (isOpen_rationalCommonNormKernel G) ρ.representation ρ.isSmooth w
            ∃ e : MonoidAlgebra ℂ (T ⧸ (rationalCommonNormKernel G).subgroupOf T) ≃ₐ[ℂ]
                Subalgebra.center ℂ (End I),
              ∀ t : T,
                let ψ : End I := e (MonoidAlgebra.of ℂ _ (QuotientGroup.mk t))
                (∀ (w : ρ) (g : GroupScheme.rationalPoints G),
                  g * (t : GroupScheme.rationalPoints G) ∉ rationalCommonNormKernel G →
                    eval (rationalCommonNormKernel G) ρ.representation
                      (SmoothRep.hom ψ (f w)).1 g = 0) ∧
                ∀ (ω : unramifiedCharacters (fun χ => (rationalNormCharacters G χ).toMul))
                  (φ : I ⟶ rationalUnramifiedTwist G ω (rationalInertiaBaseLift G π)),
                  ψ ≫ φ = ((ω.val (t : GroupScheme.rationalPoints G) : ℂˣ) : ℂ) • φ

end Langlands.CuspidalSupport
