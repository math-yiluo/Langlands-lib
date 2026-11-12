import Langlands.Representation.CuspidalSupport.RationalSummandEndCenterStatement

/-! Renard VI.4.4, Lemma: for a copy `W` of the irreducible summand `ρ` inside an
irreducible cuspidal `π`, chosen so that its stabilizer `H` is the normalizer of the
representation `ρ_H` of `H` on `W`, one has `T ⊂ H ⊂ N` with `[N : H] = [H : T] = m`,
every irreducible component of the restriction of `π` to `T` whose restriction to `⁰G`
contains `ρ` is isomorphic to `ρ_T`, and restriction
`Hom_T(ρ_T, Res_T π) → Hom_{⁰G}(ρ, Res_{⁰G} π)` is an isomorphism. -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology Langlands.Plancherel
open scoped CategoryTheory.MonObj

namespace Langlands.CuspidalSupport

universe uF uV

open Aubert.General Aubert.General.RationalPointFamily GroupScheme Induction

/-- VI.4.4, Lemma. Setting of the Theorem of VI.4.4: `π` irreducible cuspidal, `ρ` an
irreducible smooth representation of the common norm kernel `⁰G` occurring in the
restriction of `π`, `T` the intersection of the kernels of the unramified characters
`ω` with `π ⊗ ω ≅ π`, `N` the stabilizer of the isomorphism class of `ρ`, and `m` the
dimension of `Hom_{⁰G}(ρ, Res π)`. For an injective `j : ρ → Res π` with image `W`, let
`H = {g | π(g) W = W}`; `j` is *good* when every `g` with `ρ_H^g ≅ ρ_H` lies in `H`
(Renard's choice `H = H̃`). Then a good `j` exists, and for every good `j`:
`T ≤ H ≤ N`, `[N : H] = [H : T] = m`, every `⁰G`-map `ρ → Res π` is `T`-equivariant
for `ρ_T` (so restriction `Hom_T(ρ_T, Res_T π) → Hom_{⁰G}(ρ, Res π)` is bijective), and
every irreducible `T`-stable subspace of `π` receiving a nonzero `⁰G`-map from `ρ` is
isomorphic to `ρ_T`. -/
def RationalSummandStabilizerLemmaStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G)
    (S : CommGroupScheme (Spec (CommRingCat.of F))) (i : S.toGrp ⟶ G)
    (hi : IsMaximalSplitTorus i),
    haveI := hG.isAffineHom
    haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    haveI := hG.smooth
    haveI := hi.isSplitSubtorus.mono
    letI : TopologicalSpace (GroupScheme.rationalPoints G) := rationalPointTopology F G.X
    haveI : IsTopologicalGroup (GroupScheme.rationalPoints G) :=
      rationalPoint_isTopologicalGroup F G
    ∀ [LocallyCompactSpace (GroupScheme.rationalPoints G)]
      [NonarchimedeanGroup (GroupScheme.rationalPoints G)]
      [T2Space (GroupScheme.rationalPoints G)]
      (ν : cocharacterLattice S) (hν : IsGenericCocharacter i ν)
      (hStandard : StandardCocharacterStatement.{uF})
      (hRoots : HasRelativeRootSystem i)
      (hU : ∀ I, IsClosed (unipotent i ν I : Set (GroupScheme.rationalPoints G))),
      letI := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
      let h := isSemidirectDecomposition_of_standardCocharacterStatement
        i ν hStandard hG hi hν
      ∀ π : SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G),
        π.IsIrreducible →
        IsCuspidal (parabolic i ν) (levi i ν) (unipotent i ν) h hU π →
        ∀ ρ : SmoothRep.{0, uF, uV} ℂ (rationalCommonNormKernel G),
          ρ.IsIrreducible →
          (∃ j : ρ ⟶ SmoothRep.restrictSubgroup (rationalCommonNormKernel G) π,
            Function.Injective (SmoothRep.hom j)) →
          let Res := SmoothRep.restrictSubgroup (rationalCommonNormKernel G) π
          let T : Subgroup (GroupScheme.rationalPoints G) :=
            ⨅ (ω : unramifiedCharacters (fun χ => (rationalNormCharacters G χ).toMul))
              (_ : Nonempty (rationalUnramifiedTwist G ω π ≅ π)),
              ω.val.toMonoidHom.ker
          -- `g` stabilizes the isomorphism class of `ρ`: `ρ^g ≅ ρ`, `ρ^g(x) = ρ(g⁻¹ x g)`.
          let InN : GroupScheme.rationalPoints G → Prop := fun g =>
            ∃ A : ρ ≃ₗ[ℂ] ρ, ∀ x y : rationalCommonNormKernel G,
              (y : GroupScheme.rationalPoints G) = g⁻¹ * x * g →
                ∀ w : ρ, A (ρ.representation y w) = ρ.representation x (A w)
          -- `g ∈ H`: `π(g) W = W` for `W` the image of `j`.
          let InH : (ρ ⟶ Res) → GroupScheme.rationalPoints G → Prop := fun j g =>
            ∀ v : π, (∃ w : ρ, SmoothRep.hom j w = v) ↔
              ∃ w : ρ, SmoothRep.hom j w = π.representation g v
          -- `g ∈ H̃`: `ρ_H^g ≅ ρ_H`, read on `ρ` through `j`.
          let InHtilde : (ρ ⟶ Res) → GroupScheme.rationalPoints G → Prop := fun j g =>
            ∃ A : ρ ≃ₗ[ℂ] ρ, ∀ k : GroupScheme.rationalPoints G, InH j k →
              ∀ w w' : ρ,
                SmoothRep.hom j w' = π.representation (g⁻¹ * k * g) (SmoothRep.hom j w) →
                  π.representation k (SmoothRep.hom j (A w)) = SmoothRep.hom j (A w')
          let Good : (ρ ⟶ Res) → Prop := fun j =>
            Function.Injective (SmoothRep.hom j) ∧ ∀ g, InHtilde j g → InH j g
          -- `T`-stable subspaces of the carrier of `π`.
          let TStable : Submodule ℂ π → Prop := fun E =>
            ∀ t ∈ T, ∀ v ∈ E, π.representation t v ∈ E
          (∃ j : ρ ⟶ Res, Good j) ∧
          ∀ j : ρ ⟶ Res, Good j →
            ∃ (m : ℕ) (H N : Subgroup (GroupScheme.rationalPoints G)),
              Module.rank ℂ (ρ ⟶ Res) = m ∧
              (∀ g, g ∈ H ↔ InH j g) ∧ (∀ g, g ∈ N ↔ InN g) ∧
              T ≤ H ∧ H ≤ N ∧ H.relIndex N = m ∧ T.relIndex H = m ∧
              -- (VI.4.4.3): every `⁰G`-map `ρ → Res π` is `T`-equivariant for `ρ_T`.
              (∀ ψ : ρ ⟶ Res, ∀ t ∈ T, ∀ w w' : ρ,
                SmoothRep.hom j w' = π.representation t (SmoothRep.hom j w) →
                  SmoothRep.hom ψ w' = π.representation t (SmoothRep.hom ψ w)) ∧
              -- irreducible components of `Res_T π` containing `ρ` are isomorphic to `ρ_T`.
              ∀ E : Submodule ℂ π, TStable E → E ≠ ⊥ →
                (∀ E' : Submodule ℂ π, E' ≤ E → TStable E' → E' = ⊥ ∨ E' = E) →
                (∃ ψ : ρ ⟶ Res, ψ ≠ 0 ∧ ∀ w : ρ, SmoothRep.hom ψ w ∈ E) →
                ∃ A : ρ ≃ₗ[ℂ] E, ∀ t ∈ T, ∀ w w' : ρ,
                  SmoothRep.hom j w' = π.representation t (SmoothRep.hom j w) →
                    ((A w' : E) : π) = π.representation t (A w)

end Langlands.CuspidalSupport
