import Langlands.AlgebraicGeometry.FiniteEtale.Statements
import Langlands.AlgebraicGeometry.FiniteEtale.GeometricFiniteLimitsCoproductsProof
import Langlands.AlgebraicGeometry.FiniteEtale.GeometricMonoEpiConservativeProof
import Langlands.AlgebraicGeometry.FiniteEtale.GeometricFiniteGroupQuotientsProof

open CategoryTheory CategoryTheory.Limits

universe u

namespace Langlands.AlgebraicGeometry.FiniteEtale

open _root_.AlgebraicGeometry

/-- The actual finite étale category is Galois, with the specified geometric
fibre functor satisfying all fibre-functor axioms. -/
theorem geometricGaloisFiberFunctor
    {S : Scheme.{u}} [ConnectedSpace S] [IsLocallyNoetherian S]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) (hfin : ∀ Y : Cover S, Finite (Fiber s Y)) :
    GeometricGaloisFiberFunctor s hfin := by
  rcases geometricFiniteLimitsCoproducts s hfin with ⟨ht, hp, hc, hpt, hpp, hpc⟩
  rcases geometricMonoEpiConservative s hfin with ⟨hmono, hepi, hiso⟩
  have hquot := geometricFiniteGroupQuotients s hfin
  let : PreGaloisCategory (Cover S) :=
    { hasTerminal := ht
      hasPullbacks := hp
      hasFiniteCoproducts := hc
      hasQuotientsByFiniteGroups := fun G => (hquot G).1
      monoInducesIsoOnDirectSummand := hmono }
  let : PreGaloisCategory.FiberFunctor (fiberFunctor s hfin) :=
    { preservesTerminalObjects := hpt
      preservesPullbacks := hpp
      preservesFiniteCoproducts := hpc
      preservesEpis := hepi
      preservesQuotientsByFiniteGroups := fun G => (hquot G).2
      reflectsIsos := hiso }
  let hG : GaloisCategory (Cover S) :=
    { toPreGaloisCategory := inferInstance
      hasFiberFunctor := ⟨fiberFunctor s hfin, inferInstance⟩ }
  exact ⟨hG, inferInstance⟩

end Langlands.AlgebraicGeometry.FiniteEtale
