import Langlands.Geometry.Building.KPMoyPrasadLieLattices
import Langlands.Geometry.Building.KPLieGradedAction
import Langlands.Geometry.Building.KPLieGradedResidue
import Langlands.BruhatTits.IntegralModels.ReductiveQuotientLie
import Langlands.BruhatTits.IntegralModels.DepthZeroReduction
import Langlands.GroupScheme.MatrixRepresentationRationalPoints

/-! # KP 13.3.2 and 13.3.4 for the constructed lattices `𝔤_{x,r} = Lie(𝒢_{x,r})`

For the models `𝒢_{x,r}` and lattices `𝔤_{x,r} = P.moyPrasadLie hG hP h x r` chosen in
`KPMoyPrasadLieLattices`, and for the constructed `LieFiltrationData`
`P.lieFiltrationData hZ hU hOrder hP`, this module states

* `MoyPrasadReductiveQuotientLieStatement` (KP 13.3.2): for every reductive quotient `Ḡ_x` of
  the special fibre of `𝒢_{x,0}`, reduction followed by the projection to `Ḡ_x` identifies
  `𝔤_{x,0}/𝔤_{x,0+}` with `Lie(Ḡ_x)`;
* `MoyPrasadLieGradedActionStatement` (KP 13.3.4): `P_{x,0}` stabilizes every `𝔤_{x,r}`,
  `P_{x,0+}` is normal in `P_{x,0}`, and `P_{x,0+}` acts trivially on every graded piece
  `𝔤_{x,r}/𝔤_{x,r+}` and on every dual graded piece `𝔤*_{x,r}/𝔤*_{x,r+}`;
* `MoyPrasadReductiveQuotientGradedRepresentationStatement` (KP 13.2.6 and the algebraic form of
  KP 13.3.4): the kernel of reduction on `P_{x,0}` is `P_{x,0+}`, and the action of `P_{x,0}` on
  each graded piece is, through reduction, the action of the `𝔣`-points of a representation of
  the reductive quotient `Ḡ_x`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal ValuativeRel Matrix
open Langlands.GroupScheme Langlands.BruhatTits.IntegralModels

namespace Langlands.Geometry.Building

/-- **KP 13.3.2 for the constructed lattices.** Let `D` be relative-component model data whose
neutral model is the chosen depth-zero model `𝒢_{x,0}`, and let `Q` be a reductive quotient of
its special fibre (`SpecialFibreQuotientData` with `IsReductiveQuotient`): `R_u ⟶ 𝒢̄_{x,0}` the
unipotent radical and `𝒢̄_{x,0} ⟶ Ḡ_x` the quotient by it. Then the map
`𝔤_{x,0} → Lie(Ḡ_x)`, reduction followed by the differential of the projection
(`Q.latticeReductiveLieMap`), induces an isomorphism `𝔤_{x,0}/𝔤_{x,0+} ≃ Lie(Ḡ_x)` of
`𝒪[F]`-modules, where `𝔤_{x,0+} = P.moyPrasadLiePlus hG hP h x 0`. -/
def MoyPrasadReductiveQuotientLieStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    (P : ParahoricBuildingData G) (hG : MoyPrasadModelStatement.{u})
    (hP : P.SatisfiesApartmentAxioms) (h : P.MinimalCongruentCentralizerOrder)
    (x : P.Apartment) (D : RelativeComponentModelData ↥𝒪[F] F G),
    D.neutral = P.moyPrasadModel hG hP h x 0 →
    ∀ Q : SpecialFibreQuotientData D, Q.IsReductiveQuotient →
      ∃ e : (D.neutral.lieLattice ⧸
          (P.moyPrasadLiePlus hG hP h x 0).comap D.neutral.lieLattice.subtype) ≃ₗ[↥𝒪[F]]
            GenericLie ↥𝒪[F] Q.quotient,
        ∀ X : D.neutral.lieLattice, e (Submodule.Quotient.mk X) = Q.latticeReductiveLieMap X

/-- **KP 13.3.4 for the constructed lattices.** Let `L = P.lieFiltrationData hZ hU hOrder hP`.
Then

* `P_{x,0} ⊆ L.filtrationStabilizer x`: `Ad(g)` maps every `𝔤_{x,r}`, `r ≥ 0`, into itself for
  `g ∈ P_{x,0}`;
* `P_{x,0+}` is a normal subgroup of `P_{x,0}` (KP Proposition 13.2.5 (2));
* for every real `r`, `P_{x,0+}` acts trivially on `𝔤_{x,r}/𝔤_{x,r+}`
  (`L.ActsTriviallyOnGraded x r`) and on `𝔤*_{x,r}/𝔤*_{x,r+}`
  (`L.ActsTriviallyOnDualGraded x r`).

Hence `P_{x,0}/P_{x,0+}` acts on both graded pieces (`quotientGradedAdjoint`,
`quotientDualGradedAdjoint`). -/
def MoyPrasadLieGradedActionStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    (P : ParahoricBuildingData G) (hZ : CentralizerModelStatement.{u})
    (hU : AffineRootGroupModelStatement.{u}) (hOrder : MinimalCongruentOrderStatement.{u})
    (hP : P.SatisfiesApartmentAxioms) (h : P.MinimalCongruentCentralizerOrder)
    (x : P.Apartment),
    P.minimalCongruentMoyPrasad h x 0 ≤
        (P.lieFiltrationData hZ hU hOrder hP).filtrationStabilizer x ∧
      ((P.minimalCongruentMoyPrasadPlus h x 0).subgroupOf
        (P.minimalCongruentMoyPrasad h x 0)).Normal ∧
      ∀ r : ℝ,
        (P.lieFiltrationData hZ hU hOrder hP).ActsTriviallyOnGraded x r
            (P.minimalCongruentMoyPrasadPlus h x 0) ∧
          (P.lieFiltrationData hZ hU hOrder hP).ActsTriviallyOnDualGraded x r
            (P.minimalCongruentMoyPrasadPlus h x 0)

/-- **KP 13.2.6 and the algebraic form of KP 13.3.4 for the constructed lattices.** Let `D` be
relative-component model data with neutral model `𝒢_{x,0}` and `Q` a reductive quotient
`𝒢̄_{x,0} ⟶ Ḡ_x` of its special fibre, and let `L = P.lieFiltrationData hZ hU hOrder hP`. Then

* the kernel of reduction to `Ḡ_x(𝔣)` on `P_{x,0} = 𝒢_{x,0}(𝒪)` is `P_{x,0+}`:
  `Q.positivePoints = P_{x,0+}` (KP 13.2.6; with `ker_parahoricReduction` and
  `depthZeroQuotientEquiv` this identifies `P_{x,0}/P_{x,0+}` with `Ḡ_x(𝔣)`);
* `L` is periodic, and for every real `r` the residue-field vector spaces `𝔤_{x,r}/𝔤_{x,r+}`
  (`gradedLieResidueModule`) and `𝔤*_{x,r}/𝔤*_{x,r+}` (`dualGradedLieResidueModule`) have
  finite `𝔣`-linear coordinates `e` and a representation `ρ : Ḡ_x ⟶ GL_n` of the `𝔣`-group
  `Ḡ_x` such that, for `g ∈ P_{x,0}`, the action of `g` on the graded piece is, in these
  coordinates, the matrix of the `𝔣`-point `ρ(ḡ)`, where `ḡ = Q.parahoricReduction g`. -/
def MoyPrasadReductiveQuotientGradedRepresentationStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    (P : ParahoricBuildingData G) (hG : MoyPrasadModelStatement.{u})
    (hZ : CentralizerModelStatement.{u}) (hU : AffineRootGroupModelStatement.{u})
    (hOrder : MinimalCongruentOrderStatement.{u}) (hP : P.SatisfiesApartmentAxioms)
    (h : P.MinimalCongruentCentralizerOrder) (x : P.Apartment)
    (D : RelativeComponentModelData ↥𝒪[F] F G),
    D.neutral = P.moyPrasadModel hG hP h x 0 →
    ∀ Q : SpecialFibreQuotientData D, Q.IsReductiveQuotient →
      Q.positivePoints = P.minimalCongruentMoyPrasadPlus h x 0 ∧
      ∃ hL : (P.lieFiltrationData hZ hU hOrder hP).IsPeriodic, ∀ r : ℝ,
        (letI := (P.lieFiltrationData hZ hU hOrder hP).gradedLieResidueModule hL x r
          ∃ (n : ℕ) (e : (P.lieFiltrationData hZ hU hOrder hP).gradedLie x r ≃ₗ[𝓀[F]]
              (Fin n → 𝓀[F])) (ρ : MatrixRepresentation Q.quotient (Fin n)),
            ∀ (g : (P.lieFiltrationData hZ hU hOrder hP).filtrationStabilizer x)
              (g' : D.neutral.integralPoints), (g : rationalPoints G) = g' →
              ∀ Y : (P.lieFiltrationData hZ hU hOrder hP).gradedLie x r,
                e ((P.lieFiltrationData hZ hU hOrder hP).gradedAdjoint x r g Y) =
                  (ρ.rationalMatrix (Q.parahoricReduction g') : Matrix (Fin n) (Fin n) 𝓀[F]) *ᵥ
                    e Y) ∧
        (letI := (P.lieFiltrationData hZ hU hOrder hP).dualGradedLieResidueModule hL x r
          ∃ (n : ℕ) (e : ↥((P.lieFiltrationData hZ hU hOrder hP).dualGradedLie x r) ≃ₗ[𝓀[F]]
              (Fin n → 𝓀[F])) (ρ : MatrixRepresentation Q.quotient (Fin n)),
            ∀ (g : (P.lieFiltrationData hZ hU hOrder hP).filtrationStabilizer x)
              (g' : D.neutral.integralPoints), (g : rationalPoints G) = g' →
              ∀ Y : ↥((P.lieFiltrationData hZ hU hOrder hP).dualGradedLie x r),
                e ((P.lieFiltrationData hZ hU hOrder hP).dualGradedAdjoint x r g Y) =
                  (ρ.rationalMatrix (Q.parahoricReduction g') : Matrix (Fin n) (Fin n) 𝓀[F]) *ᵥ
                    e Y)

end Langlands.Geometry.Building
