import Langlands.Geometry.Building.KPMoyPrasadIsomorphismStatement
import Langlands.Geometry.Building.KPMoyPrasadLieLatticeStatements
import Langlands.Geometry.Building.KPMinimalCongruentCentralizerStatements
import Langlands.GroupScheme.IntegralModel.LieLatticeBaseChange

/-! # KP Theorem 13.5.1 (1) for the constructed groups `P_{x,r}` and lattices `𝔤_{x,r}`

For the Moy–Prasad groups `P_{x,r} = P.minimalCongruentMoyPrasad h x r` of the minimal
congruent filtration and the lattices `𝔤_{x,r} = P.moyPrasadLie hG hP h x r = Lie(𝒢_{x,r})`
of the chosen models, this module states

* `MinimalCongruentMoyPrasadIsomorphismStatement`: KP Theorem 13.5.1 (1), the Moy–Prasad
  isomorphism `P_{x,r}/P_{x,s} ≅ 𝔤_{x,r}/𝔤_{x,s}` under each of the three alternatives;
* `MinimalCongruentMoyPrasadUnramifiedIsomorphismStatement`: the same with an isomorphism
  `G(K)_{x,r}/G(K)_{x,s} ≅ 𝔤(K)_{x,r}/𝔤(K)_{x,s}` over the maximal unramified extension `K`
  compatible with it;
* `MinimalCongruentCentralizerIsomorphismStatement`: the isomorphism
  `Z(F)_r/Z(F)_s ≅ 𝔷_r/𝔷_s` for the centralizer `Z` of the maximal split torus;
* `MoyPrasadRootBlockIsomorphismStatement`: the isomorphism of the quotients of the root blocks
  `U_{a,x,r}U_{2a,x,r}` and of their lattices, for non-multipliable `a` at all depths and for
  multipliable `a` when `s ≤ 2r`;
* `MinimalCongruentMoyPrasadIsomorphismReductionStatement`: these component statements and the
  statements on the constructed filtrations imply `MinimalCongruentMoyPrasadIsomorphismStatement`
  through the supplied-data `MoyPrasadIsomorphismStatement`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal ValuativeRel
open Langlands.GroupScheme Langlands.LocalGalois.Separable
open Langlands.GroupScheme.GaloisPointComparison

namespace Langlands.Geometry.Building

/-- **KP Theorem 13.5.1 (1) for the constructed data.** Let `P` satisfy the apartment axioms,
`x` be a point of its apartment and `0 < r ≤ s` satisfy one of the three alternatives of
KP §13.5 (`MoyPrasadAlternative`). Then `P_{x,r}/P_{x,s} ≅ 𝔤_{x,r}/𝔤_{x,s}` as abstract
groups, where `P_{x,r}` is the Moy–Prasad group of the minimal congruent filtration and
`𝔤_{x,r} = Lie(𝒢_{x,r})` the Lie lattice of the model chosen from `hG`. -/
def MinimalCongruentMoyPrasadIsomorphismStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    (P : ParahoricBuildingData G) (hG : MoyPrasadModelStatement.{u})
    (hP : P.SatisfiesApartmentAxioms) (h : P.MinimalCongruentCentralizerOrder)
    (x : P.Apartment) (r s : ℝ≥0), 0 < r → r ≤ s → MoyPrasadAlternative F G r s →
      HasMoyPrasadQuotientIso (P.minimalCongruentMoyPrasad h x r)
        (P.minimalCongruentMoyPrasad h x s)
        (P.moyPrasadLie hG hP h x r).toAddSubgroup (P.moyPrasadLie hG hP h x s).toAddSubgroup

/-- **KP Theorem 13.5.1 (1) with its compatibility with the maximal unramified extension.**
Let `K = inertiaFixedField F`, let `L = P.unramifiedApartmentLift.2` be the chosen apartment
lift, `G(K)_{x,t}` its Moy–Prasad group at `x` with the minimal congruent torus filtration, and
`𝔤(K)_{x,t}` the Lie lattice of the base change of `𝒢_{x,t}` to the integers of `K`. Under one
of the three alternatives for `0 < r ≤ s`:

* `g ↦ g_K` maps `P_{x,t}` into `G(K)_{x,t}` and the base change map
  `GenericLie.baseChangeMap : Lie(G) → Lie(G_K)` maps `𝔤_{x,t}` into `𝔤(K)_{x,t}`, for every
  `t ≥ 0`;
* there are surjective homomorphisms `φ_K : G(K)_{x,r} → 𝔤(K)_{x,r}/𝔤(K)_{x,s}` with kernel
  `G(K)_{x,s}` and `φ : P_{x,r} → 𝔤_{x,r}/𝔤_{x,s}` with kernel `P_{x,s}` such that, whenever
  `φ(g)` is the class of `X`, `φ_K(g_K)` is the class of the base change of `X`. -/
def MinimalCongruentMoyPrasadUnramifiedIsomorphismStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    (P : ParahoricBuildingData G) (hG : MoyPrasadModelStatement.{u})
    (hP : P.SatisfiesApartmentAxioms) (h : P.MinimalCongruentCentralizerOrder)
    (x : P.Apartment) (r s : ℝ≥0), 0 < r → r ≤ s → MoyPrasadAlternative F G r s →
      let GK : ℝ≥0 → Subgroup (rationalPoints (baseChanged F (inertiaFixedField F) G)) :=
        fun t => P.unramifiedApartmentLift.2.buildingData.minimalCongruentMoyPrasad
          P.unramifiedApartmentLift.2.centralizer_isTorus (P.unramifiedApartmentLift.2.e x) t
      let gK : ℝ≥0 → AddSubgroup (GenericLie (fixedFieldIntegers F)
          (baseChanged F (inertiaFixedField F) G)) :=
        fun t => (P.moyPrasadModel hG hP h x t).baseChangeUnramified.lieLattice.toAddSubgroup
      let gF : ℝ≥0 → AddSubgroup (GenericLie ↥𝒪[F] G) :=
        fun t => (P.moyPrasadLie hG hP h x t).toAddSubgroup
      (∀ (t : ℝ≥0), ∀ g ∈ P.minimalCongruentMoyPrasad h x t,
        rationalExtend F (inertiaFixedField F) G g ∈ GK t) ∧
      (∀ (t : ℝ≥0), ∀ X ∈ gF t,
        GenericLie.baseChangeMap ↥𝒪[F] (fixedFieldIntegers F) (inertiaFixedField F) G X ∈
          gK t) ∧
      ∃ (φK : GK r →* Multiplicative (gK r ⧸ (gK s).addSubgroupOf (gK r)))
        (φ : P.minimalCongruentMoyPrasad h x r →* Multiplicative (gF r ⧸ (gF s).addSubgroupOf (gF r))),
        Function.Surjective φK ∧ φK.ker = (GK s).subgroupOf (GK r) ∧
        Function.Surjective φ ∧
        φ.ker = (P.minimalCongruentMoyPrasad h x s).subgroupOf (P.minimalCongruentMoyPrasad h x r) ∧
        ∀ (g : P.minimalCongruentMoyPrasad h x r) (g' : GK r),
          (g' : rationalPoints (baseChanged F (inertiaFixedField F) G)) =
            rationalExtend F (inertiaFixedField F) G g →
          ∀ (X : gF r) (Y : gK r),
            (Y : GenericLie (fixedFieldIntegers F) (baseChanged F (inertiaFixedField F) G)) =
              GenericLie.baseChangeMap ↥𝒪[F] (fixedFieldIntegers F) (inertiaFixedField F) G X →
            φ g = Multiplicative.ofAdd (QuotientAddGroup.mk X) →
              φK g' = Multiplicative.ofAdd (QuotientAddGroup.mk Y)

/-- **The centralizer component (KP Propositions B.6.9, B.10.16, B.10.17 with descent).** Let
`Z = Z_G(S)` be the centralizer of the maximal split torus of `P`, `Z(F)_r` the minimal congruent
centralizer subgroups of KP §9.8 and `𝔷_r = Lie(𝒵_r)` the Lie lattices of the centralizer
models chosen from `hZ`. For `0 < r ≤ s` satisfying one of the three alternatives,
`Z(F)_r/Z(F)_s ≅ 𝔷_r/𝔷_s` as abstract groups. -/
def MinimalCongruentCentralizerIsomorphismStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    (P : ParahoricBuildingData G) (hZ : CentralizerModelStatement.{u})
    (r s : ℝ≥0), 0 < r → r ≤ s → MoyPrasadAlternative F G r s →
      HasMoyPrasadQuotientIso (P.minimalCongruentCentralizerPoints r)
        (P.minimalCongruentCentralizerPoints s)
        (P.centralizerModelLie hZ r).toAddSubgroup (P.centralizerModelLie hZ s).toAddSubgroup

/-- **The root-block component (KP Propositions C.5.1 and A.5.19, and §C.4).** Let `a` be a
relative root of `P` that is not twice a relative root, and `0 < r ≤ s`. Assume that `2a` is not a
relative root, or that `s ≤ 2r`. Then the quotient of the block `U_{a,x,r}U_{2a,x,r}` by
`U_{a,x,s}U_{2a,x,s}` is isomorphic to the quotient of `u_{a,x,r} + u_{2a,x,r}` by
`u_{a,x,s} + u_{2a,x,s}`, the lattices of the constructed `LieFiltrationData`. Each of the three
alternatives of KP §13.5 implies `s ≤ 2r`. -/
def MoyPrasadRootBlockIsomorphismStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    (P : ParahoricBuildingData G) (hZ : CentralizerModelStatement.{u})
    (hU : AffineRootGroupModelStatement.{u}) (hOrder : MinimalCongruentOrderStatement.{u})
    (hP : P.SatisfiesApartmentAxioms) (x : P.Apartment) (α : relativeRoots P.i),
    (∀ β : relativeRoots P.i, α.1 ≠ 2 • β.1) →
    ∀ (r s : ℝ≥0), 0 < r → r ≤ s →
      (2 • α.1 ∉ relativeRoots P.i ∨ s ≤ 2 * r) →
      HasMoyPrasadQuotientIso
        (Subgroup.closure (P.apartment.filtrationBlock x (fun _ => (r : ℝ)) α.1))
        (Subgroup.closure (P.apartment.filtrationBlock x (fun _ => (s : ℝ)) α.1))
        ((P.lieFiltrationData hZ hU hOrder hP).rootBlockLie x α r).toAddSubgroup
        ((P.lieFiltrationData hZ hU hOrder hP).rootBlockLie x α s).toAddSubgroup

/-- **Reduction of KP Theorem 13.5.1 (1) to the supplied-data theorem.** The supplied-data
`MoyPrasadIsomorphismStatement`, the filtration axioms and the double-root condition for the
minimal congruent centralizer filtration, the description `MoyPrasadLieSpanStatement` of
`𝔤_{x,r}`, and the two component statements, together with the model statements from which the
`LieFiltrationData` is built, imply `MinimalCongruentMoyPrasadIsomorphismStatement`. -/
def MinimalCongruentMoyPrasadIsomorphismReductionStatement : Prop :=
  MoyPrasadIsomorphismStatement.{u} → MinimalCongruentCentralizerAxiomsStatement.{u} →
    MinimalCongruentCentralizerDoubleRootStatement.{u} → MoyPrasadLieSpanStatement.{u} →
    MinimalCongruentCentralizerIsomorphismStatement.{u} →
    MoyPrasadRootBlockIsomorphismStatement.{u} →
    CentralizerModelStatement.{u} → AffineRootGroupModelStatement.{u} →
    MinimalCongruentOrderStatement.{u} →
    MinimalCongruentMoyPrasadIsomorphismStatement.{u}

end Langlands.Geometry.Building
