import Langlands.GroupScheme.Rational.LeviCocenterRootModelStatement
import Langlands.GroupScheme.Rational.SplitTorusCentralizerReduction
import Langlands.GroupScheme.Torus.FundamentalWeightPermutation
import Langlands.GroupScheme.SimplyConnected.FieldExtensionStatement
import Langlands.GroupScheme.SimplyConnected.SplitNecessityStatement

/-! # Conditional fundamental-weight proof for split-torus centralizer cocenters -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- The root-descent data and integral coroot generation construct a basis of
the actual cocenter character lattice permuted by the ordinary Galois action. -/
theorem isInducedTorus_of_cocenterRootDescent
    (k E : Type u) [Field k] [Field E] [Algebra k E]
    [FiniteDimensional k E] [IsGalois k E]
    {T Q : CommGroupScheme (Spec (CommRingCat.of k))} (g : T ⟶ Q)
    {J : Type u}
    (P : RootDatum J
      (characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k E)).obj T))
      (cocharacterLattice ((CommGroupScheme.baseChange (algebraBaseMap k E)).obj T)))
    (B : P.Base) (s : Set B.support) (hspan : P.corootSpan ℤ = ⊤)
    (hsplit : IsSplitTorus (GaloisPointComparison.baseChanged k E Q.toGrp))
    (hdesc : CocenterRootDescentData k E g P B s) :
    IsInducedTorus Q := by
  obtain ⟨hf, hrange, w, v, e, hfix, hpair, hperm, hstable⟩ := hdesc
  let b := Langlands.RootDatum.fundamentalWeightBasis P B hspan
  let f := characterLattice.baseChangePullback k E g
  have hrange' : f.range = Langlands.PermutationBasis.complementSpan b s := by
    ext x
    exact (hrange x).trans
      (Langlands.RootDatum.mem_fundamentalWeight_complement_iff P B hspan s x).symm
  apply isInducedTorus_of_twisted_complement Q E hsplit b s f hf hrange'
    (characterLattice.galoisRepresentation k E T) w
    (characterLattice.baseChangePullback_galois k E g) hfix
  intro σ i
  let j : {i : B.support // i ∉ s} :=
    ⟨e σ i, fun h => i.property ((hstable σ i).mpr h)⟩
  refine ⟨j, ?_⟩
  exact Langlands.RootDatum.fundamentalWeightBasis_permutation P B hspan
    ((w σ).comp (characterLattice.galoisRepresentation k E T σ))
    ((v σ).comp (cocharacterLattice.galoisRepresentation k E T σ))
    (e σ) (hpair σ) (hperm σ) i

/-- The five structural propositions used by the conditional fundamental-weight
proof. None is assumed to have a proof merely by inclusion in this package. -/
def SplitTorusCentralizerCocenterInducedInputsStatement : Prop :=
  DynamicCentralizerReductiveStatement.{u} ∧
  CocenterQuotientExistenceStatement.{u} ∧
  IsSimplyConnectedFieldExtensionStatement.{u} ∧
  SplitSimplyConnectedCorootSpanStatement.{u} ∧
  SplitTorusCentralizerCocenterRootModelStatement.{u}

/-- These five precise structural inputs imply the exact arbitrary-universe
split-torus-centralizer cocenter proposition. -/
theorem splitTorusCentralizerCocenterInduced_of_inputs
    (h : SplitTorusCentralizerCocenterInducedInputsStatement.{u}) :
    SplitTorusCentralizerCocenterInducedStatement.{u} := by
  obtain ⟨hred, hexists, hfield, hspan, hmodel⟩ := h
  intro k _ G hG A a ha M j hj D d hd Q q hq
  have hGred := hG.isSemisimple.isConnectedReductive
  have hM : IsConnectedReductive M :=
    splitTorusCentralizerReductive_of_dynamic hred k G hGred A a ha.1 M j hj
  have hQ : IsTorus Q.toGrp :=
    suppliedCocenterTorus_of_existence hexists k M D d hM hd Q q hq
  have := hGred.isAffineHom
  obtain ⟨T, t, _, E, hE, hAlg, hfin, hGal, hTE, hQE, hiE,
    J, hJ, P, hP, hPred, B, s, hdesc⟩ :=
    hmodel k G hGred A a ha M j hj hM D d hd Q q hq hQ
  let : Field E := hE
  let : Algebra k E := hAlg
  let : FiniteDimensional k E := hfin
  let : IsGalois k E := hGal
  let : Finite J := hJ
  have hGE := hfield k E G hG
  have hPspan : P.corootSpan ℤ = ⊤ :=
    hspan E ((GroupScheme.baseChange (algebraBaseMap k E)).obj G) hGE
      ((CommGroupScheme.baseChange (algebraBaseMap k E)).obj T) hTE
      ((GroupScheme.baseChange (algebraBaseMap k E)).map (t ≫ j)) hiE J P hP hPred
  exact isInducedTorus_of_cocenterRootDescent k E
    (Additive.ofMul (t ≫ q) : T ⟶ Q) P B s hPspan hQE hdesc

end Langlands.GroupScheme
