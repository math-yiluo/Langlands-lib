import Langlands.Representation.CuspidalSupport.RationalNormKernelOrbitTwistStatement

/-! Renard VI.3.1, Lemma: the action of `G` on `Irr(⁰G)` by conjugation has finite
orbits, and `π(g)` carries the `σ`-isotypic part of the restriction of `π` to `⁰G`
onto the `σ^g`-isotypic part. -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.CuspidalSupport

universe u uV uW

/-- VI.3.1, Lemma. Write `⁰G = rationalCommonNormKernel G` and
`σ^g = σ ∘ (h ↦ g⁻¹ h g)` for a representation `σ` of `⁰G` and `g ∈ G(F)`.

(i) For every irreducible smooth representation `σ` of `⁰G`, the conjugates `σ^g`,
`g ∈ G(F)`, fall into finitely many isomorphism classes: there is a finite set `S`
with every `σ^g` equivalent to some `σ^s`, `s ∈ S`.

(ii) For every smooth representation `π` of `G(F)`, every irreducible smooth `σ` of
`⁰G` and every `g`, `π(g)` maps the `σ`-isotypic part `V(σ)` of `π|_{⁰G}` onto
`V(σ^g)`. Here `V(σ)` is the span of the images of all `⁰G`-intertwining maps from
`σ` to `π|_{⁰G}`. -/
def RationalNormKernelConjugationLemmaStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : GroupScheme.IsConnectedReductive G),
    haveI := hG.isAffineHom
    haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    haveI := hG.smooth
    letI : TopologicalSpace (GroupScheme.rationalPoints G) := rationalPointTopology F G.X
    letI : IsTopologicalGroup (GroupScheme.rationalPoints G) :=
      rationalPoint_isTopologicalGroup F G
    let conj := fun g : GroupScheme.rationalPoints G =>
      (MulAut.conjNormal (H := Plancherel.rationalCommonNormKernel G) g⁻¹).toMonoidHom
    (∀ σ : SmoothRep.{0, u, uW} ℂ (Plancherel.rationalCommonNormKernel G),
      σ.IsIrreducible →
      ∃ S : Finset (GroupScheme.rationalPoints G), ∀ g : GroupScheme.rationalPoints G,
        ∃ s ∈ S, Nonempty (Representation.Equiv
          (σ.representation.comp (conj g)) (σ.representation.comp (conj s)))) ∧
    ∀ (π : SmoothRep.{0, u, uV} ℂ (GroupScheme.rationalPoints G))
      (σ : SmoothRep.{0, u, uW} ℂ (Plancherel.rationalCommonNormKernel G)),
      σ.IsIrreducible →
      let res := π.representation.comp (Plancherel.rationalCommonNormKernel G).subtype
      let iso := fun τ : Representation ℂ (Plancherel.rationalCommonNormKernel G) σ =>
        Submodule.span ℂ {x : π | ∃ (f : Representation.IntertwiningMap τ res) (w : σ),
          f w = x}
      ∀ g : GroupScheme.rationalPoints G,
        (iso σ.representation).map (π.representation g) =
          iso (σ.representation.comp (conj g))

end Langlands.CuspidalSupport
