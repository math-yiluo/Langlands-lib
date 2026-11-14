import Langlands.GroupScheme.Reductive.SplitIsogenyGraph
import Langlands.AbelianScheme.IsogenyStability

/-! # Ambient homomorphisms recovered from local-isogeny graph projections -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.RootDatumIsogenyRealization

variable {k : Type u} [Field k]
    {G G' : GroupScheme (Spec (CommRingCat.of k))}
    {T T' : CommGroupScheme (Spec (CommRingCat.of k))}
    {I : Type v} {i : T.toGrp ⟶ G} {i' : T'.toGrp ⟶ G'} {t : T ⟶ T'}
    {ν : I → cocharacterLattice T} {ν' : I → cocharacterLattice T'}
    {C : ∀ j, LocalIsogeny i i' t (ν j) (ν' j)}

namespace LocalIsogenyGraphEnvelope

variable (D : LocalIsogenyGraphEnvelope C) [IsIso D.first]

/-- The actual ambient map recovered by inverting the first graph projection.
Invertibility is an explicit hypothesis, not a consequence of this definition. -/
def realizationHom : G ⟶ G' := inv D.first ≫ D.second

/-- The recovered homomorphism has the original second graph projection. -/
@[reassoc (attr := simp)]
theorem first_realizationHom : D.first ≫ D.realizationHom = D.second := by
  simp only [realizationHom, IsIso.hom_inv_id_assoc]

/-- The recovered homomorphism restricts to the prescribed actual torus map. -/
theorem torus_realizationHom :
    i ≫ D.realizationHom = CommGroupScheme.groupHom t ≫ i' := by
  calc
    i ≫ D.realizationHom = (D.torusLift ≫ D.first) ≫ D.realizationHom :=
      congrArg (fun a => a ≫ D.realizationHom) D.torusLift_first.symm
    _ = CommGroupScheme.groupHom t ≫ i' := by
      rw [Category.assoc, D.first_realizationHom, D.torusLift_second]

/-- The recovered ambient map retains every supplied local isogeny. -/
theorem local_realizationHom (j : I) :
    (C j).leftInclusion ≫ D.realizationHom = (C j).hom ≫ (C j).rightInclusion := by
  calc
    (C j).leftInclusion ≫ D.realizationHom =
        (D.localLift j ≫ D.first) ≫ D.realizationHom :=
      congrArg (fun a => a ≫ D.realizationHom) (D.localLift_first j).symm
    _ = (C j).hom ≫ (C j).rightInclusion := by
      rw [Category.assoc, D.first_realizationHom, D.localLift_second]

/-- Finite-flat-surjective geometry of the second projection transfers to the
ambient map, including its full scheme-theoretic kernel. -/
theorem realizationHom_isIsogeny (hs : IsIsogeny D.second) :
    IsIsogeny D.realizationHom :=
  (isCentralIsogeny_of_isIso (inv D.first)).isIsogeny.comp hs

/-- The projection identity uniquely specifies the recovered ambient map. -/
theorem realizationHom_unique (φ : G ⟶ G') (hφ : D.first ≫ φ = D.second) :
    φ = D.realizationHom := by
  apply (cancel_epi D.first).mp
  rw [hφ, D.first_realizationHom]

end LocalIsogenyGraphEnvelope

section PrescribedLattices

variable {J J' : Type u} [Finite J] [Finite J']
    [Module.Finite ℤ (characterLattice T)] [Module.Finite ℤ (cocharacterLattice T)]
    [Module.Finite ℤ (characterLattice T')] [Module.Finite ℤ (cocharacterLattice T')]
    {P : RootDatum J (characterLattice T) (cocharacterLattice T)}
    {P' : RootDatum J' (characterLattice T') (cocharacterLattice T')}
    [P.IsReduced] [P'.IsReduced] {p : ℕ}

/-- A graph with invertible first projection and isogeny second projection
realizes both specified lattice maps over the original field. The graph's
geometric projection assertions remain explicit hypotheses. -/
theorem exists_realization_of_graph_projections
    (hT : IsSplitTorus T.toGrp) (hT' : IsSplitTorus T'.toGrp)
    (hP : P.toLinearMap = latticePairing T)
    (hP' : P'.toLinearMap = latticePairing T')
    (f : Langlands.LinearAlgebra.RootDatumIsogeny p P' P)
    {C : ∀ j, LocalIsogeny i i' (torusMap hT' f) (ν j) (ν' j)}
    (D : LocalIsogenyGraphEnvelope C) [IsIso D.first]
    (hs : IsIsogeny D.second) :
    ∃ φ : G ⟶ G', IsIsogeny φ ∧
      IsIsogeny (CommGroupScheme.groupHom (torusMap hT' f)) ∧
      i ≫ φ = CommGroupScheme.groupHom (torusMap hT' f) ≫ i' ∧
      (∀ χ : characterLattice T', f.weightMap χ = torusMap hT' f ≫ χ) ∧
      (∀ μ : cocharacterLattice T, f.coweightMap μ = μ ≫ torusMap hT' f) :=
  ⟨D.realizationHom, D.realizationHom_isIsogeny hs,
    torusMap_isIsogeny hT hT' hP hP' f, D.torus_realizationHom,
    fun χ => (torusMap_comp hT' f χ).symm,
    fun μ => (comp_torusMap hT' hP hP' f μ).symm⟩

end PrescribedLattices

end Langlands.GroupScheme.RootDatumIsogenyRealization
