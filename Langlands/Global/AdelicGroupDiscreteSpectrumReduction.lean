import Langlands.Global.AdelicGroupParabolicSpectrumReduction
import Langlands.Representation.Unitary.DiscretePartCriteria

/-! # The discrete spectrum and the square-integrable automorphic forms: reduction to two inputs

`GroupSquareIntegrableFormSpectrumStatement` (module
`Langlands.Global.AdelicGroupParabolicSpectrumReduction`) says that, for a presented parabolic
`p : P → G` that is an isomorphism, the closure in `L²([G])` of the span of the classes of
finite linear combinations of elements of Lapid's `A²_P` is the discrete spectrum. It follows
from two propositions, one for each inclusion:

* `SquareIntegrableFormFiniteProjectionStatement` (the finite discrete content of a
  square-integrable automorphic form; Getz–Hahn 2024, Theorems 6.2.4 and 6.3.4, after
  Harish-Chandra; Borel–Jacquet 1979, §4.3 (i)): the orthogonal projections of such a class onto
  the closed `G(𝔸)`-invariant subspaces of `L²([G])` lie in one finite-dimensional subspace;
* `IrreducibleSubrepresentationFormSpectrumStatement` (the density and automorphy of the
  `K`-finite vectors of a discrete summand; Getz–Hahn 2024, Lemma 9.7.2 and Theorem 6.6.4):
  every irreducible closed invariant subspace of `L²([G])` lies in that closed span.

The theorem `groupSquareIntegrableFormSpectrum_of_reduction` derives
`GroupSquareIntegrableFormSpectrumStatement` from the two, by the abstract criteria of
`Langlands.Representation.Unitary.DiscretePartCriteria`; `groupParabolicSpectrum_of_reduction`
derives `GroupParabolicSpectrumStatement`. -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints

section Action

variable {F : Type} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

/-- The canonical right regular representation on `L²([G])` preserves norms. -/
theorem norm_canonicalL2RightAction (hG : IsConnectedReductive G) (g : AdelicGroupPoints F G)
    (f : Lp ℂ 2 (RestrictionSplitCentre.canonicalMeasure F G)) :
    ‖RestrictionSplitCentre.canonicalL2RightAction F G centralSplitTorusCharacter.{0} hG g f‖ =
      ‖f‖ :=
  (RestrictionSplitCentre.rationalQuotientL2RightTranslate F G _
    (RestrictionSplitCentre.canonicalMeasure_rightInvariant F G centralSplitTorusCharacter.{0} hG)
    g).norm_map f

end Action

section Statements

/-- The finite discrete content of square-integrable automorphic forms (derived from
Harish-Chandra's finiteness theorem, Getz–Hahn 2024, Theorem 6.3.4, p.164, and Borel–Jacquet
1979, §4.3 (i), p.195: the automorphic forms of a fixed type form a finite-dimensional space).
Getz–Hahn, Theorem 6.2.4, p.160, allows archimedean smoothing; that the projections are
automorphic forms of the same type also needs a finite-level adelic convolution, which gives
continuous representatives, and a growth estimate for these on `[G]`. For a presented parabolic `p : P → G` of a connected reductive group
that is an isomorphism, let `f ∈ L²([G])` be the class of a finite linear combination
`∑ j, c j · v j` of elements of Lapid's `A²_P` (`IsSquareIntegrableInducedForm`). There is a
finite-dimensional subspace of `L²([G])` containing the orthogonal projection of `f` onto every
closed subspace that is invariant under the right regular representation of `G(𝔸)`. -/
def SquareIntegrableFormFiniteProjectionStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    (hG : IsConnectedReductive G)
    (K : Subgroup (AdelicGroupPoints F G)) {N d : ℕ}
    (rho : MatrixRepresentation G (Fin N))
    (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (hcalc : AdelicDifferentialCommutator F G hsmooth),
    IsMaximalCompactSubgroup F G K → IsClosedSubgroup rho →
    ∀ (P M U : GroupScheme (Spec (CommRingCat.of F)))
      (A : CommGroupScheme (Spec (CommRingCat.of F)))
      [IsAffine P.X.left] [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom] [IsAffine U.X.left]
      (p : P ⟶ G) [IsClosedImmersion p.hom.hom.left] (iU : U ⟶ P) (l : M ⟶ P)
      (a : A.toGrp ⟶ M), ParabolicRootPresentation p l a →
      haveI : LocallyOfFiniteType P.X.hom :=
        IsClosedSubgroup.locallyOfFiniteType (j := p) ‹IsClosedImmersion p.hom.hom.left›
      LeviSubgroup.IsGeometricUnipotentRadical iU →
      ∀ hK : IsIwasawaCompact p K, IsIso p →
      ∀ (f : Lp ℂ 2 (RestrictionSplitCentre.canonicalMeasure F G)) (k : ℕ)
        (v : Fin k → AdelicGroupPoints F G → ℂ) (c : Fin k → ℂ),
        (∀ j, IsSquareIntegrableInducedForm K hK.isCompact rho hsmooth hcalc p iU l (v j)) →
        f =ᵐ[RestrictionSplitCentre.canonicalMeasure F G] (fun y => ∑ j, c j * v j y.out) →
        ∃ W : Submodule ℂ (Lp ℂ 2 (RestrictionSplitCentre.canonicalMeasure F G)),
          FiniteDimensional ℂ W ∧
          ∀ (V : Submodule ℂ (Lp ℂ 2 (RestrictionSplitCentre.canonicalMeasure F G)))
            [V.HasOrthogonalProjection],
            (∀ (g : AdelicGroupPoints F G), ∀ x ∈ V,
              RestrictionSplitCentre.canonicalL2RightAction F G centralSplitTorusCharacter.{0} hG
                g x ∈ V) →
            V.starProjection f ∈ W

/-- The irreducible subrepresentations of `L²([G])` are spanned by square-integrable
automorphic forms (Getz–Hahn 2024, Theorem 6.6.4, p.172, and Lemma 9.7.2, p.264: the `K`-finite
vectors of an irreducible closed invariant subspace are dense in it and, through the adelic
convolution identity of Lemma 9.7.2, have representatives that are automorphic forms; for a
disconnected `K_∞` the `𝔷`-finiteness uses the adjoint invariance of the centre of the
enveloping algebra instead of the printed Corollary 4.6.3). For a presented parabolic `p : P → G` of a connected reductive group that
is an isomorphism, every irreducible subrepresentation of the right regular representation of
`G(𝔸)` on `L²([G])` lies in `squareIntegrableFormSpectrum`, the closure of the span of the
classes of finite linear combinations of elements of Lapid's `A²_P`. -/
def IrreducibleSubrepresentationFormSpectrumStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    (hG : IsConnectedReductive G)
    (K : Subgroup (AdelicGroupPoints F G)) {N d : ℕ}
    (rho : MatrixRepresentation G (Fin N))
    (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (hcalc : AdelicDifferentialCommutator F G hsmooth),
    IsMaximalCompactSubgroup F G K → IsClosedSubgroup rho →
    ∀ (P M U : GroupScheme (Spec (CommRingCat.of F)))
      (A : CommGroupScheme (Spec (CommRingCat.of F)))
      [IsAffine P.X.left] [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom] [IsAffine U.X.left]
      (p : P ⟶ G) [IsClosedImmersion p.hom.hom.left] (iU : U ⟶ P) (l : M ⟶ P)
      (a : A.toGrp ⟶ M), ParabolicRootPresentation p l a →
      haveI : LocallyOfFiniteType P.X.hom :=
        IsClosedSubgroup.locallyOfFiniteType (j := p) ‹IsClosedImmersion p.hom.hom.left›
      LeviSubgroup.IsGeometricUnipotentRadical iU →
      ∀ hK : IsIwasawaCompact p K, IsIso p →
      ∀ V : Submodule ℂ (Lp ℂ 2 (RestrictionSplitCentre.canonicalMeasure F G)),
        Langlands.Analysis.IsIrreducibleSubrepresentation
          (RestrictionSplitCentre.canonicalL2RightAction F G centralSplitTorusCharacter.{0} hG)
          V →
        V ≤ squareIntegrableFormSpectrum K hK.isCompact rho hsmooth hcalc p iU l

end Statements

/-- The two inputs give the equality of the closed span of the square-integrable automorphic
forms with the discrete spectrum. -/
theorem groupSquareIntegrableFormSpectrum_of_reduction
    (hF : SquareIntegrableFormFiniteProjectionStatement)
    (hD : IrreducibleSubrepresentationFormSpectrumStatement) :
    GroupSquareIntegrableFormSpectrumStatement := by
  intro F _ _ G _ _ _ hG K N d rho hsmooth hcalc hKmax hrho P M U A _ _ _ _ p _ iU l a r hU hK hp
  have : LocallyOfFiniteType P.X.hom :=
    IsClosedSubgroup.locallyOfFiniteType (j := p) ‹IsClosedImmersion p.hom.hom.left›
  refine le_antisymm ?_ ?_
  · refine Submodule.topologicalClosure_minimal _ ?_ (Submodule.isClosed_topologicalClosure _)
    refine Submodule.span_le.2 fun f ⟨k, v, c, hv, hf⟩ => ?_
    obtain ⟨W, hWfin, hW⟩ := hF F G hG K rho hsmooth hcalc hKmax hrho P M U A p iU l a r hU hK
      hp f k v c hv hf
    exact Langlands.Analysis.mem_discretePart_of_starProjection_mem _
      (norm_canonicalL2RightAction hG) f W hW
  · exact Langlands.Analysis.discretePart_le_of_forall_le _
      (Submodule.isClosed_topologicalClosure _)
      (hD F G hG K rho hsmooth hcalc hKmax hrho P M U A p iU l a r hU hK hp)

/-- `GroupParabolicSpectrumStatement` from the finite discrete content of square-integrable
automorphic forms and the automorphy of the irreducible subrepresentations of `L²([G])`. -/
theorem groupParabolicSpectrum_of_reduction
    (hF : SquareIntegrableFormFiniteProjectionStatement)
    (hD : IrreducibleSubrepresentationFormSpectrumStatement) :
    GroupParabolicSpectrumStatement :=
  groupParabolicSpectrum_of_squareIntegrableFormSpectrum
    (groupSquareIntegrableFormSpectrum_of_reduction hF hD)

end Langlands.Global
