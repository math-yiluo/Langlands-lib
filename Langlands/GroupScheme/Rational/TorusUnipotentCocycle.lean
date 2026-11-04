import Langlands.GroupScheme.AutomorphicAction.CocycleExactSequence
import Langlands.GroupScheme.Rational.TorusVectorCocycle
import Langlands.GroupScheme.Rational.SplitUnipotentStableVectorStatement
import Langlands.GroupScheme.Rational.TorusVectorLinearizationStatement
import Langlands.GroupScheme.Rational.SplitUnipotentSurjectiveImage
import Langlands.GroupScheme.Chevalley.UnipotentQuotientDescent
import Langlands.GroupScheme.UnipotentAffineOrbitClosedProof
import Langlands.GroupScheme.Unipotent.BaseChange
import Langlands.GroupScheme.SplitUnipotentQuotientSection
import Langlands.GroupScheme.Torus.Geometry
import Langlands.GroupScheme.Torus.CentralMaximalBaseChangeReduction

/-! # Torus cocycles in split unipotent groups from structural inputs -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace AutomorphicAction.Cocycle

variable {S : Scheme.{u}} {H U : GroupScheme S}
    {a : AutomorphicAction H U} {T : Over S}

/-- The cocycle in an all-test trivial group is trivial. -/
theorem eq_trivial_of_range_id_eq_bot
    (hU : SubgroupFunctor.range (𝟙 U) = ⊥) (c : a.Cocycle T) :
    c = trivial T := by
  apply ext
  have hc : c.hom ∈ (SubgroupFunctor.range (𝟙 U)).carrier (T ⊗ H.X) :=
    SubgroupFunctor.mem_range.mpr ⟨c.hom, by
      change c.hom ≫ 𝟙 U.X = c.hom
      exact Category.comp_id _⟩
  rw [hU, SubgroupFunctor.bot_carrier, Subgroup.mem_bot] at hc
  exact hc

end AutomorphicAction.Cocycle

namespace RelativeRoot

section LocalLifts

variable {B : Scheme.{u}} {U Q : GroupScheme B} {N : SubgroupFunctor U}
    {q : U ⟶ Q} (hq : IsFppfQuotient N q)

include hq

/-- Every point of a represented fppf quotient lifts after an actual fppf
pullback cover of its test scheme. -/
theorem IsFppfQuotient.local_lifts (T : Over B) (y : T ⟶ Q.X) :
    ∃ (V : Over B) (v : V ⟶ T),
      Flat v.left ∧ Surjective v.left ∧ LocallyOfFinitePresentation v.left ∧
        ∃ x : V ⟶ U.X, x ≫ q.hom.hom = v ≫ y := by
  let : Flat q.hom.hom.left := hq.1
  let : Surjective q.hom.hom.left := hq.2.1
  let : LocallyOfFinitePresentation q.hom.hom.left := hq.2.2.1
  let V : Over B := Over.mk (pullback.fst y.left q.hom.hom.left ≫ T.hom)
  let v : V ⟶ T := Over.homMk (pullback.fst y.left q.hom.hom.left) rfl
  let x : V ⟶ U.X := Over.homMk (pullback.snd y.left q.hom.hom.left) (by
    rw [← Over.w q.hom.hom, ← Category.assoc, ← pullback.condition,
      Category.assoc, Over.w y]
    rfl)
  refine ⟨V, v, ?_, ?_, ?_, x, Over.OverMorphism.ext pullback.condition.symm⟩
  · change Flat (pullback.fst y.left q.hom.hom.left)
    infer_instance
  · change Surjective (pullback.fst y.left q.hom.hom.left)
    infer_instance
  · change LocallyOfFinitePresentation (pullback.fst y.left q.hom.hom.left)
    infer_instance

end LocalLifts

section VectorKernel

variable {k : Type u} [Field k]
    {H V U Q : GroupScheme (Spec (CommRingCat.of k))}
    {aV : AutomorphicAction H V} {a : AutomorphicAction H U}
    {aQ : AutomorphicAction H Q}
    (z : V ⟶ U) (hz : aV.IsEquivariant a z) [Mono z.hom.hom]
    [IsAffineHom V.X.hom]
    (q : U ⟶ Q) (hq : a.IsEquivariant aQ q)
    (hker : SubgroupFunctor.range z = SubgroupFunctor.range (kernelι q))
    (hH : IsTorus H) {n : ℕ}
    (e : ∀ T : Over (Spec (CommRingCat.of k)),
      (T ⟶ V.X) ≃* Multiplicative (Fin n → Γ(T.left, ⊤)))
    (he : IsLinearVectorCoordinates aV e)
    (c : a.Cocycle (Over.mk (𝟙 (Spec (CommRingCat.of k)))))

include hz hq hker hH he

/-- A lift of a quotient coboundary can be corrected through an equivariant
linear vector kernel for any torus, including nonsplit tori. -/
theorem exists_coboundary_of_isTorus_vector_kernel
    (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ U.X)
    (hc : c.map q hq = aQ.coboundary (g ≫ q.hom.hom)) :
    ∃ v : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ V.X,
      c = a.coboundary (g * (v ≫ z.hom.hom)) :=
  AutomorphicAction.Cocycle.exists_coboundary_of_map_eq_coboundary
    z hz c q hq hker g hc
    (exists_coboundary_of_isTorus aV e he hH)

end VectorKernel

section Induction

variable
    (hstable : SplitUnipotentStableVectorSubgroupStatement.{u})
    (hlinear : TorusVectorActionLinearizationStatement.{u})
    (htorsor : SplitUnipotentAffineTorsorStatement.{u})
    {k : Type u} [Field k]
    (H : GroupScheme (Spec (CommRingCat.of k))) (hH : IsTorus H)

include hstable hlinear htorsor hH

/-- Dimension induction for actual rational torus cocycles. The three
structural propositions remain explicit inputs. Quotient existence,
affineness, equivariance and strict dimension decrease are constructed. -/
theorem exists_coboundary_of_split_unipotent_of_structuralStatements
    (U : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth U.X.hom] [IsAffineHom U.X.hom] [ConnectedSpace U.X.left]
    (hU : IsUnipotent U) (hUsplit : IsSplitUnipotent U)
    (a : AutomorphicAction H U)
    (c : a.Cocycle (Over.mk (𝟙 (Spec (CommRingCat.of k))))) :
    ∃ g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ U.X, c = a.coboundary g := by
  have : IsAffine H.X.left := SplittingAssembly.isAffine_of_isTorus H hH
  let : IsAffineHom H.X.hom := inferInstance
  let : Smooth H.X.hom := hH.smooth
  have hind : ∀ d : ℕ,
      ∀ (U : GroupScheme (Spec (CommRingCat.of k)))
        (hsm : Smooth U.X.hom) (haff : IsAffineHom U.X.hom)
        (hconn : ConnectedSpace U.X.left),
        IsUnipotent U → IsSplitUnipotent U →
        ∀ (a : AutomorphicAction H U)
          (c : a.Cocycle (Over.mk (𝟙 (Spec (CommRingCat.of k))))),
          SmoothOfRelativeDimension d U.X.hom →
            ∃ g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ U.X,
              c = a.coboundary g := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro U hsm haff hconn hU hUsplit a c hd
      let : Smooth U.X.hom := hsm
      let : IsAffineHom U.X.hom := haff
      let : ConnectedSpace U.X.left := hconn
      by_cases htriv : SubgroupFunctor.range (𝟙 U) = ⊥
      · refine ⟨1, ?_⟩
        rw [c.eq_trivial_of_range_id_eq_bot htriv, AutomorphicAction.coboundary,
          AutomorphicAction.Cocycle.conjugate_one]
      · obtain ⟨V, z, aV, n, e, hz, hVsm, hVaff, hVconn, hV, hVsplit,
          hcentral, hstableV, _hnontriv, hpos, hn, he, heq⟩ :=
          hstable k U hsm haff hconn hU hUsplit htriv H
            inferInstance inferInstance a
        let : IsAffineHom V.X.hom := hVaff
        let : Smooth V.X.hom := hVsm
        let : IsClosedImmersion z.hom.hom.left := hz
        let : Mono z.hom.hom := Over.mono_of_mono_left _
        have hzact : aV.IsEquivariant a z := fun {T} h v => heq T h v
        obtain ⟨Q, q, b, m, hQaff, hQsm, hQconn, hQ, hquot, _hqsm, _hnq,
            hm, _hdim, hlt, hb⟩ :=
          Chevalley.exists_unipotentNormalQuotientOfFieldExtension
            unipotentAffineOrbitClosed k (AlgebraicClosure k) U V H hU z hz
            hU.baseChange hV.baseChange hcentral.range_isNormal
            a hstableV hd hn hpos
        let : IsAffineHom Q.X.hom := hQaff
        let : Smooth Q.X.hom := hQsm
        let : ConnectedSpace Q.X.left := hQconn
        let : Surjective q.hom.hom.left := hquot.2.1
        have hQsplit : IsSplitUnipotent Q :=
          hUsplit.of_surjective_to_smooth_affine q
        have hqact : a.IsEquivariant b q := fun {T} h u => (hb T h u).symm
        obtain ⟨y, hy⟩ := ih m hlt Q hQsm hQaff hQconn hQ hQsplit b
          (c.map q hqact) hm
        obtain ⟨s, hs⟩ :=
          HomogeneousQuotient.fppf_section_of_split_unipotent_torsors
            U V z htorsor hz hVsplit Q q hquot
        let g := y ≫ s
        have hg : g ≫ q.hom.hom = y := by
          simp only [g, Category.assoc, hs, Category.comp_id]
        obtain ⟨e', he'⟩ := hlinear k H V n hH ⟨e, he⟩ aV
        obtain ⟨v, hv⟩ :=
          exists_coboundary_of_isTorus_vector_kernel z hzact q hqact
            hquot.2.2.2.symm hH e' he' c g (by rw [hg]; exact hy)
        exact ⟨g * (v ≫ z.hom.hom), hv⟩
  obtain ⟨d, hd⟩ := Langlands.AlgebraicGeometry.smoothConnectedRelativeDimension
    U.X.left _ U.X.hom inferInstance inferInstance
  exact hind d U inferInstance inferInstance inferInstance hU hUsplit a c hd

variable (U : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth U.X.hom] [IsAffineHom U.X.hom] [ConnectedSpace U.X.left]
    (hU : IsUnipotent U) (hUsplit : IsSplitUnipotent U)
    (a : AutomorphicAction H U)
    (c : a.Cocycle (Over.mk (𝟙 (Spec (CommRingCat.of k)))))

/-- A chosen actual rational coboundary point, conditional on the three named
structural propositions used by the dimension induction. -/
def torusUnipotentCocycleConjugator :
    Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ U.X :=
  (exists_coboundary_of_split_unipotent_of_structuralStatements
    hstable hlinear htorsor H hH U hU hUsplit a c).choose

/-- The constructed rational point gives equality of actual cocycle morphisms. -/
theorem cocycle_eq_coboundary_of_split_unipotent_of_structuralStatements :
    c = a.coboundary
      (torusUnipotentCocycleConjugator hstable hlinear htorsor H hH
        U hU hUsplit a c) :=
  (exists_coboundary_of_split_unipotent_of_structuralStatements
    hstable hlinear htorsor H hH U hU hUsplit a c).choose_spec

end Induction

end RelativeRoot

end Langlands.GroupScheme
