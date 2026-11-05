import Langlands.GroupScheme.Rational.MaximalTorusParameter
import Langlands.AlgebraicGeometry.AlgebraicSpace.FppfQuotientRepresentability

/-! # Identification of actual maximal-torus parameter schemes -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace IsMaximalTorusParameter

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {T₀ : CommGroupScheme (Spec (CommRingCat.of k))} {j₀ : T₀.toGrp ⟶ G}
  {Q Q' : Over (Spec (CommRingCat.of k))} {q : G.X ⟶ Q} {q' : G.X ⟶ Q'}

/-- Actual parameter schemes for the same torus inclusion are isomorphic over
the field, compatibly with their supplied projections. -/
theorem exists_iso (hq : IsMaximalTorusParameter j₀ q)
    (hq' : IsMaximalTorusParameter j₀ q') :
    ∃ e : Q ≅ Q', q ≫ e.hom = q' := by
  have : Smooth q.left := hq.smooth_map
  have : Surjective q.left := hq.surjective_map
  have : Smooth q'.left := hq'.smooth_map
  have : Surjective q'.left := hq'.surjective_map
  let S := Spec (CommRingCat.of k)
  let Y := Langlands.AlgebraicGeometry.AlgebraicSpace.schemeYoneda S
  obtain ⟨e, he⟩ :=
    Langlands.AlgebraicGeometry.AlgebraicSpace.exists_iso_of_locallySurjective_of_same_kernel
      (F := (Langlands.AlgebraicGeometry.AlgebraicSpace.schemeSheaf S).obj Q')
      (Y.map q') q
      (Langlands.AlgebraicGeometry.AlgebraicSpace.isLocallySurjective_schemeYoneda_map q')
      (Langlands.AlgebraicGeometry.AlgebraicSpace.isLocallySurjective_schemeYoneda_map q)
      (by
        intro U g h
        constructor
        · intro heq
          apply (hq.fiber_iff U g h).mpr
          apply (hq'.fiber_iff U g h).mp
          exact congrArg ULift.down heq
        · intro heq
          apply ULift.ext
          exact (hq'.fiber_iff U g h).mpr ((hq.fiber_iff U g h).mp heq))
  let d : Q ≅ Q' := (ULiftYoneda.fullyFaithful (Over S)).preimageIso e
  refine ⟨d, ?_⟩
  apply Y.map_injective
  simpa [d, Y, Functor.map_comp, Functor.FullyFaithful.preimageIso] using! he

end IsMaximalTorusParameter

/-- A chosen actual isomorphism between two parameter schemes for the same
torus inclusion. Its defining property is `maximalTorusParameterIso_fac`. -/
def maximalTorusParameterIso
    {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    {T₀ : CommGroupScheme (Spec (CommRingCat.of k))} {j₀ : T₀.toGrp ⟶ G}
    {Q Q' : Over (Spec (CommRingCat.of k))} {q : G.X ⟶ Q} {q' : G.X ⟶ Q'}
    (hq : IsMaximalTorusParameter j₀ q) (hq' : IsMaximalTorusParameter j₀ q') :
    Q ≅ Q' :=
  (hq.exists_iso hq').choose

/-- The chosen isomorphism carries the original supplied projection to the
other supplied projection. -/
theorem maximalTorusParameterIso_fac
    {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    {T₀ : CommGroupScheme (Spec (CommRingCat.of k))} {j₀ : T₀.toGrp ⟶ G}
    {Q Q' : Over (Spec (CommRingCat.of k))} {q : G.X ⟶ Q} {q' : G.X ⟶ Q'}
    (hq : IsMaximalTorusParameter j₀ q) (hq' : IsMaximalTorusParameter j₀ q') :
    q ≫ (maximalTorusParameterIso hq hq').hom = q' :=
  (hq.exists_iso hq').choose_spec

end Langlands.GroupScheme
