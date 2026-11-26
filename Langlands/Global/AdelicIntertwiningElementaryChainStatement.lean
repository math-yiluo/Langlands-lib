import Langlands.Global.AdelicLeadingCuspidalComponents
import Langlands.Global.AdelicRootHyperplaneStatement

/-! # Standardization and elementary decomposition of intertwining operators

Two structural inputs for the root factorization of continued intertwining operators
(Bernstein–Lapid §8.6, number field case), neither of which involves analytic continuation.

* `IntertwiningStandardizationStatement`: an intertwining operator `M(w, λ)φ` for an arbitrary
  presented parabolic `P`, an arbitrary target parabolic `Q` and an arbitrary maximal compact
  Iwasawa subgroup `K` is, for `Re λ` sufficiently regular, a finite combination with
  coefficients entire in `λ` of operators for one standard parabolic family and a maximal
  compact subgroup with Iwasawa coverage `P_J(𝔸)K₀ = G(𝔸)` for every standard parabolic `P_J`,
  evaluated at transformed points.
* `IntertwiningElementaryChainStatement`: for a standard parabolic family and a maximal compact
  subgroup Iwasawa for every standard parabolic, every element of `W(P_I, P_I')` is, on the
  regular region, the composite of a chain of elementary steps, and the operator of each step
  is invariant under translation of its parameter by the kernel of one root form, which pulls
  back to the kernel of a root form of `P_I`. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints

/-- The root presentation of the standard parabolic `P_J` given by a standard parabolic family:
its maximal split torus, generic cocharacter and integral data are those of the family, and its
set of simple roots is `J`. -/
abbrev StandardParabolicFamily.rootPresentation {F : Type u} [Field F] [NumberField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] [IsAffine G.X.left]
    [LocallyOfFiniteType G.X.hom] (fam : StandardParabolicFamily F G)
    (J : StandardIndex F G fam.i fam.ν) :
    ParabolicRootPresentation (fam.p J) (fam.l J) (fam.a J) :=
  ⟨⟨fam.T, fam.i, fam.ν, J.val, fam.f J⟩, fam.isCompatible J⟩

/-- **Standardization of intertwining operators** (derived from Bernstein–Lapid §2.1–§2.2 and
Mœglin–Waldspurger I.1.4, II.1.6). In the setting of `IntertwiningRootFactorizationStatement`
there are a standard parabolic family `fam` with indices `I`, `I'`, a maximal compact subgroup
`K₀` with `P_J(𝔸)K₀ = G(𝔸)` for every standard index `J`, an element `(w₀, c₀)` of
`W(P_I, P_I')` with a retraction `π₀` of the Levi of `P_I'`, a complex linear isomorphism `iota`
of parameter spaces, and finitely many coefficients `E j` entire in linear coordinates,
functions `h j` on `G(𝔸)`, maps `τ j` of `G(𝔸)` and automorphic functions `φ₀ j` on
`U_I(𝔸) M_I(F) \ G(𝔸)` for `K₀`, together with the three instances used to form the standard
operators, such that:

* `iota` maps sufficiently regular parameters for `r` to regular parameters of the standard
  presentation of `P_I`; and for every root `β₀` of the standard presentation in the unipotent
  radical of `P_I` there is a root `β` of `r` in the unipotent radical of `P` such that `iota`
  maps the kernel of the root form of `β` into the kernel of the root form of `β₀`;
* for `Re λ` sufficiently regular and every `g`,
  `M(w, λ)φ (g) = ∑ j, E j λ · h j g · M₀(w₀, iota λ)(φ₀ j)(τ j g)`, where `M₀` is formed with
  `K₀` for the source `P_I` and the target `P_I'`. -/
def IntertwiningStandardizationStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G P M U Q M' V : GroupScheme (Spec (CommRingCat.of F)))
    (A : CommGroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    [IsAffine P.X.left] [IsAffine Q.X.left] [IsAffine V.X.left]
    (p : P ⟶ G) [IsClosedImmersion p.hom.hom.left] (iU : U ⟶ P) (l : M ⟶ P)
    (a : A.toGrp ⟶ M) (r : ParabolicRootPresentation p l a)
    [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
    [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
    (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus r.data.T.toGrp)
    (q : Q ⟶ G) [IsClosedImmersion q.hom.hom.left] (iV : V ⟶ Q) (l' : M' ⟶ Q)
    [IsClosedImmersion (iV ≫ q).hom.hom.left] (π' : Q ⟶ M')
    (w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X) (c : M' ⟶ M),
    IsConnectedReductive G → LeviSubgroup.IsGeometricUnipotentRadical iU →
    IsParabolicSubgroup q → LeviSubgroup.IsGeometricUnipotentRadical iV →
    IsRationalLeviSubgroup l' → IsIso (subgroupMultiplication l' iV) → l' ≫ π' = 𝟙 M' →
    IsWeylConjugation p l q l' w c →
    ∀ (K : Subgroup (AdelicGroupPoints F G)) (hK : IsIwasawaCompact p K)
      (hK' : IsIwasawaCompact q K) {N d : ℕ}
      (rho : MatrixRepresentation G (Fin N))
      (hsmooth : SmoothOfRelativeDimension d G.X.hom)
      (hcalc : AdelicDifferentialCommutator F G hsmooth) (φ : AdelicGroupPoints F G → ℂ),
      IsMaximalCompactSubgroup F G K → IsClosedSubgroup rho →
      IsAutomorphicFunctionOn F G hsmooth hcalc (parabolicQuotientSubgroup F p iU l)
        (K.comap (ofInfinite F G).toMonoidHom) rho φ →
      ∃ (fam : StandardParabolicFamily F G) (I I' : StandardIndex F G fam.i fam.ν)
        (K₀ : Subgroup (AdelicGroupPoints F G)) (hK₀ : ∀ J, IsIwasawaCompact (fam.p J) K₀)
        (w₀ : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X) (c₀ : fam.M I' ⟶ fam.M I)
        (π₀ : fam.P I' ⟶ fam.M I')
        (iota : ComplexCharacterParameter F P ≃ₗ[ℂ] ComplexCharacterParameter F (fam.P I))
        (m : ℕ) (E : Fin m → ComplexCharacterParameter F P → ℂ)
        (h : Fin m → AdelicGroupPoints F G → ℂ)
        (τ : Fin m → AdelicGroupPoints F G → AdelicGroupPoints F G)
        (φ₀ : Fin m → AdelicGroupPoints F G → ℂ),
        IsMaximalCompactSubgroup F G K₀ ∧
        IsWeylConjugation (fam.p I) (fam.l I) (fam.p I') (fam.l I') w₀ c₀ ∧
        fam.l I' ≫ π₀ = 𝟙 (fam.M I') ∧
        (∀ j, IsAutomorphicFunctionOn F G hsmooth hcalc
          (parabolicQuotientSubgroup F (fam.p I) (fam.iU I) (fam.l I))
          (K₀.comap (ofInfinite F G).toMonoidHom) rho (φ₀ j)) ∧
        (∀ j, ∀ (n : ℕ) (e : (Fin n → ℂ) ≃ₗ[ℂ] ComplexCharacterParameter F P),
          Differentiable ℂ (E j ∘ e)) ∧
        ∃ (_ : Fintype (relativeWeylGroup fam.i))
          (_ : ∀ J, IsClosedImmersion (fam.p J).hom.hom.left)
          (_ : ∀ J, Mono (CommGroupScheme.groupHom (fam.f J)).hom.hom.left),
          (∀ R : ℝ, ∃ R' : ℝ, ∀ lam : ComplexCharacterParameter F P,
            r.IsRegularParameter hA hT R' lam →
              (fam.rootPresentation I).IsRegularParameter
                (fam.isCompatible I).splitComponent.isCentralSplitTorus.1.1
                fam.maximalSplit.isSplitSubtorus.1 R (iota lam)) ∧
          (∀ β₀ ∈ (fam.rootPresentation I).unipotentRoots, ∃ β ∈ r.unipotentRoots,
            ∀ ν : ComplexCharacterParameter F P, r.rootFunctional hA hT β ν = 0 →
              (fam.rootPresentation I).rootFunctional
                (fam.isCompatible I).splitComponent.isCentralSplitTorus.1.1
                fam.maximalSplit.isSplitSubtorus.1 β₀ (iota ν) = 0) ∧
          ∃ R : ℝ, ∀ lam : ComplexCharacterParameter F P, r.IsRegularParameter hA hT R lam →
            ∀ g : AdelicGroupPoints F G,
              hK.intertwiningOperator hK' iU l iV c π' w φ lam g =
                ∑ j, E j lam * h j g *
                  (hK₀ I).intertwiningOperator (hK₀ I') (fam.iU I) (fam.l I) (fam.iU I') c₀ π₀
                    w₀ (φ₀ j) (iota lam) (τ j g)

/-- **Decomposition into elementary symmetries** (derived from Bernstein–Lapid §8.6 and
Mœglin–Waldspurger I.1.8, II.1.6). Let `fam` be a standard parabolic family, `K` a maximal
compact subgroup with `P_J(𝔸)K = G(𝔸)` for every standard index `J`, and `(w, c)` an element of
`W(P_I, P_I')` with a retraction `π` of the Levi of `P_I'`. Then there are `n`, standard indices
`J' 0 = I, J' 1, …, J' n` (written `Fin.cons I J`), steps `(ws t, cs t) ∈ W(P_{J' t}, P_{J' (t+1)})`,
their partial composites `(W t, C t) ∈ W(P_I, P_{J' t})` (with `W 0 = 1`, `C 0 = 𝟙`,
`W (t+1) = ws t · W t` and `C (t+1) = cs t ≫ C t`) and retractions `πs t` of the Levis of the
`P_{J' t}`, with `M_{J' t} × U_{J' t} ≅ P_{J' t}` by multiplication, such that:

* every step `t` has a root `α` of the split component of `P_{J' t}` in its unipotent radical
  such that, on the regular region of `P_{J' t}`, the operator of the step does not change when
  its parameter is translated by an element of the kernel of the root form of `α`; and the
  kernel of some root form of `P_I` is carried into the kernel of the root form of `α` by the
  Weyl parameter map of `(W t, C t)`;
* on the regular region of `P_I`, the operator of `(w, c)` agrees with the operator of the
  composite `(W n, C n)` on every function left invariant under `U_I(𝔸) M_I(F)`. -/
def IntertwiningElementaryChainStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    (fam : StandardParabolicFamily F G) [Fintype (relativeWeylGroup fam.i)]
    [∀ J, IsClosedImmersion (fam.p J).hom.hom.left]
    [∀ J, Mono (CommGroupScheme.groupHom (fam.f J)).hom.hom.left]
    (K : Subgroup (AdelicGroupPoints F G)) (hK : ∀ J, IsIwasawaCompact (fam.p J) K)
    (I I' : StandardIndex F G fam.i fam.ν)
    (w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X) (c : fam.M I' ⟶ fam.M I)
    (π : fam.P I' ⟶ fam.M I'),
    IsMaximalCompactSubgroup F G K →
    IsWeylConjugation (fam.p I) (fam.l I) (fam.p I') (fam.l I') w c →
    fam.l I' ≫ π = 𝟙 (fam.M I') →
    ∃ (n : ℕ) (J : Fin n → StandardIndex F G fam.i fam.ν)
      (ws : Fin n → (Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X))
      (cs : ∀ t : Fin n,
        fam.M ((Fin.cons I J : Fin (n + 1) → StandardIndex F G fam.i fam.ν) t.succ) ⟶
          fam.M ((Fin.cons I J : Fin (n + 1) → StandardIndex F G fam.i fam.ν) t.castSucc))
      (W : Fin (n + 1) → (Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X))
      (C : ∀ t : Fin (n + 1),
        fam.M ((Fin.cons I J : Fin (n + 1) → StandardIndex F G fam.i fam.ν) t) ⟶ fam.M I)
      (πs : ∀ t : Fin (n + 1),
        fam.P ((Fin.cons I J : Fin (n + 1) → StandardIndex F G fam.i fam.ν) t) ⟶
          fam.M ((Fin.cons I J : Fin (n + 1) → StandardIndex F G fam.i fam.ν) t)),
      W 0 = 1 ∧ C 0 = 𝟙 (fam.M I) ∧
      (∀ t : Fin n, W t.succ = ws t * W t.castSucc ∧ C t.succ = cs t ≫ C t.castSucc) ∧
      (∀ t, fam.l ((Fin.cons I J : Fin (n + 1) → StandardIndex F G fam.i fam.ν) t) ≫ πs t =
        𝟙 _) ∧
      (∀ t, IsIso (subgroupMultiplication
        (fam.l ((Fin.cons I J : Fin (n + 1) → StandardIndex F G fam.i fam.ν) t))
        (fam.iU ((Fin.cons I J : Fin (n + 1) → StandardIndex F G fam.i fam.ν) t)))) ∧
      (∀ t : Fin n, IsWeylConjugation
        (fam.p ((Fin.cons I J : Fin (n + 1) → StandardIndex F G fam.i fam.ν) t.castSucc))
        (fam.l ((Fin.cons I J : Fin (n + 1) → StandardIndex F G fam.i fam.ν) t.castSucc))
        (fam.p ((Fin.cons I J : Fin (n + 1) → StandardIndex F G fam.i fam.ν) t.succ))
        (fam.l ((Fin.cons I J : Fin (n + 1) → StandardIndex F G fam.i fam.ν) t.succ))
        (ws t) (cs t)) ∧
      (∀ t : Fin n,
        ∃ α ∈ (fam.rootPresentation
            ((Fin.cons I J : Fin (n + 1) → StandardIndex F G fam.i fam.ν) t.castSucc)).unipotentRoots,
          (∃ R : ℝ, ∀ mu nu : ComplexCharacterParameter F
              (fam.P ((Fin.cons I J : Fin (n + 1) → StandardIndex F G fam.i fam.ν) t.castSucc)),
            (fam.rootPresentation _).IsRegularParameter
              (fam.isCompatible _).splitComponent.isCentralSplitTorus.1.1
              fam.maximalSplit.isSplitSubtorus.1 R mu →
            (fam.rootPresentation _).IsRegularParameter
              (fam.isCompatible _).splitComponent.isCentralSplitTorus.1.1
              fam.maximalSplit.isSplitSubtorus.1 R (mu + nu) →
            (fam.rootPresentation _).rootFunctional
              (fam.isCompatible _).splitComponent.isCentralSplitTorus.1.1
              fam.maximalSplit.isSplitSubtorus.1 α nu = 0 →
            ∀ (ψ : AdelicGroupPoints F G → ℂ) (g : AdelicGroupPoints F G),
              (hK _).intertwiningOperator (hK _) (fam.iU _) (fam.l _) (fam.iU _) (cs t)
                  (πs t.succ) (ws t) ψ (mu + nu) g =
                (hK _).intertwiningOperator (hK _) (fam.iU _) (fam.l _) (fam.iU _) (cs t)
                  (πs t.succ) (ws t) ψ mu g) ∧
          ∃ β ∈ (fam.rootPresentation I).unipotentRoots,
            ∀ nu : ComplexCharacterParameter F (fam.P I),
              (fam.rootPresentation I).rootFunctional
                (fam.isCompatible I).splitComponent.isCentralSplitTorus.1.1
                fam.maximalSplit.isSplitSubtorus.1 β nu = 0 →
              (fam.rootPresentation _).rootFunctional
                (fam.isCompatible _).splitComponent.isCentralSplitTorus.1.1
                fam.maximalSplit.isSplitSubtorus.1 α
                (weylParameter (fam.l I) (C t.castSucc) (πs t.castSucc) nu) = 0) ∧
      ∃ R : ℝ, ∀ mu : ComplexCharacterParameter F (fam.P I),
        (fam.rootPresentation I).IsRegularParameter
          (fam.isCompatible I).splitComponent.isCentralSplitTorus.1.1
          fam.maximalSplit.isSplitSubtorus.1 R mu →
        ∀ ψ : AdelicGroupPoints F G → ℂ,
          IsLeftInvariantUnder F G (parabolicQuotientSubgroup F (fam.p I) (fam.iU I) (fam.l I))
            ψ →
          ∀ g : AdelicGroupPoints F G,
            (hK I).intertwiningOperator (hK I') (fam.iU I) (fam.l I) (fam.iU I') c π w ψ mu g =
              (hK I).intertwiningOperator (hK _) (fam.iU I) (fam.l I) (fam.iU _)
                (C (Fin.last n)) (πs (Fin.last n)) (W (Fin.last n)) ψ mu g

end Langlands.Global
