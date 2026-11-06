import Langlands.Representation.CuspidalSupport.RationalUniversalSmallProgeneratorStatement
import Langlands.Representation.Induction.OpenAdjunction

/-! Renard VI.4.4, Theorem: the center of the endomorphism ring of the compact
induction of one irreducible summand ρ of the restriction of an irreducible
cuspidal π to the common norm kernel consists of the elements supported in the
group T, and the ring is free of rank m² over its center. -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology Langlands.Plancherel
open scoped CategoryTheory.MonObj

namespace Langlands.CuspidalSupport

universe uF uV

open Aubert.General Aubert.General.RationalPointFamily GroupScheme Induction

/-- VI.4.4, Theorem: let π be irreducible cuspidal, ρ an irreducible smooth
representation of the common norm kernel H⁰ with an injective equivariant map
into the restriction of π, and T the intersection of the kernels of the
unramified characters ω with π ⊗ ω ≅ π. An endomorphism α of ind_{H⁰}^G ρ is
central if and only if every function α(f_w) vanishes outside T, where f_w is
supported on H⁰ with f_w(h) = ρ(h) w. Moreover the multiplicity m of ρ in the
restriction of π is finite, and the ring is free of rank m² over its center. -/
def RationalSummandEndCenterStatement : Prop :=
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
            (∀ α : End I, α ∈ Subalgebra.center ℂ (End I) ↔
              ∀ (w : ρ) (g : GroupScheme.rationalPoints G), g ∉ T →
                eval (rationalCommonNormKernel G) ρ.representation
                  (SmoothRep.hom α (f w)).1 g = 0) ∧
            ∃ m : ℕ,
              Module.rank ℂ
                  (ρ ⟶ SmoothRep.restrictSubgroup (rationalCommonNormKernel G) π) = m ∧
                Nonempty (Module.Basis (Fin (m ^ 2)) (Subalgebra.center ℂ (End I)) (End I))

end Langlands.CuspidalSupport
