import Langlands.Representation.CuspidalSupport.RationalNormKernelHeckeStatement

/-! Renard VI.4.2, after the Proposition: the right action of `H(G, ρ)` on
`Hom_{⁰G}(ρ, Res τ)` and the compatibility of the adjunction
`Hom_G(Π, τ) ≃ Hom_{⁰G}(ρ, Res τ)` with the right actions. -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology Langlands.Plancherel
open scoped CategoryTheory.MonObj

namespace Langlands.CuspidalSupport

universe uF uV

open GroupScheme Induction

/-- Renard VI.4.2, the paragraphs after the Proposition. Let `ρ` be an irreducible smooth
representation of the common norm kernel `⁰G`, `Π = ind_{⁰G}^G ρ`, `f_w ∈ Π` the function
supported on `⁰G` with `f_w(1) = w`, and `τ` a smooth representation of `G(F)` (carriers in
`Type (max uF uV)`, those of `Π`). For a `⁰G`-map `ψ : ρ → τ` and `φ ∈ H(G, ρ)` put
`(ψ · φ)(w) = ∑_{g ∈ G/⁰G} τ(g) ψ(φ(g⁻¹) w)`. Then:

1. `ψ · φ` is again a `⁰G`-map;
2. this is a right action: `(ψ · φ) · φ' = ψ · (φ ∗ φ')`, and the unit `φ_e` of `H(G, ρ)`
   (`φ_e(h) = ρ(h)` on `⁰G`, `0` elsewhere) acts trivially;
3. for the identification `e : End Π ≃ H(G, ρ)`, `e(α)(g)(w) = α(f_w)(g)`, of the published
   VI.4.2 Proposition, the adjunction map `s ↦ ψ_s`, `ψ_s(w) = s(f_w)`, from `Hom_G(Π, τ)` to
   `⁰G`-maps carries the transported right action `s · φ = s ∘ e⁻¹(φ)` to `ψ_s · φ`;
4. the adjunction map is bijective, with inverse (VI.4.2.6):
   `ψ ↦ (f ↦ ∑_{g ∈ ⁰G\G} τ(g) ψ(f(g⁻¹)))`. -/
def RationalNormKernelHeckeModuleStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    haveI := hG.smooth
    letI : TopologicalSpace (GroupScheme.rationalPoints G) := rationalPointTopology F G.X
    haveI : IsTopologicalGroup (GroupScheme.rationalPoints G) :=
      rationalPoint_isTopologicalGroup F G
    ∀ ρ : SmoothRep.{0, uF, uV} ℂ (rationalCommonNormKernel G),
      ρ.IsIrreducible →
      let I := (compactInductionFunctor (rationalCommonNormKernel G)).obj (SmoothRep.toRep.obj ρ)
      let f : ρ → I := fun w => unitFunction (rationalCommonNormKernel G)
        (isOpen_rationalCommonNormKernel G) ρ.representation ρ.isSmooth w
      ∀ τ : SmoothRep.{0, uF, max uF uV} ℂ (GroupScheme.rationalPoints G),
        let Rτ := SmoothRep.restrictSubgroup (rationalCommonNormKernel G) τ
        let act : ρ.representation.IntertwiningMap Rτ.representation →
            (GroupScheme.rationalPoints G → Module.End ℂ ρ) → ρ → τ := fun ψ φ w =>
          ∑ᶠ q : GroupScheme.rationalPoints G ⧸ rationalCommonNormKernel G,
            τ.representation q.out (ψ (φ q.out⁻¹ w))
        (∀ (ψ : ρ.representation.IntertwiningMap Rτ.representation)
            (φ : rationalNormKernelHecke G ρ),
          ∃ ψ' : ρ.representation.IntertwiningMap Rτ.representation,
            ∀ w, ψ' w = act ψ φ w) ∧
        (∀ (ψ ψ' : ρ.representation.IntertwiningMap Rτ.representation)
            (φ φ' : rationalNormKernelHecke G ρ),
          (∀ w, ψ' w = act ψ φ w) →
            ∀ w, act ψ' φ' w = act ψ (rationalNormKernelConvolution G ρ φ φ') w) ∧
        (∀ (ψ : ρ.representation.IntertwiningMap Rτ.representation)
            (φe : rationalNormKernelHecke G ρ),
          (∀ h : rationalCommonNormKernel G,
            (φe : GroupScheme.rationalPoints G → Module.End ℂ ρ) h = ρ.representation h) →
          (∀ g : GroupScheme.rationalPoints G, g ∉ rationalCommonNormKernel G →
            (φe : GroupScheme.rationalPoints G → Module.End ℂ ρ) g = 0) →
          ∀ w, act ψ φe w = ψ w) ∧
        (∀ e : End I ≃ₗ[ℂ] rationalNormKernelHecke G ρ,
          (∀ (α : End I) (g : GroupScheme.rationalPoints G) (w : ρ),
            (e α : GroupScheme.rationalPoints G → Module.End ℂ ρ) g w =
              eval (rationalCommonNormKernel G) ρ.representation
                (SmoothRep.hom α (f w)).1 g) →
          ∀ (s : I ⟶ τ) (φ : rationalNormKernelHecke G ρ) (ψ : ρ.representation.IntertwiningMap
              Rτ.representation),
            (∀ w, ψ w = SmoothRep.hom s (f w)) →
            ∀ w, SmoothRep.hom (e.symm φ ≫ s) (f w) = act ψ φ w) ∧
        ∀ ψ : ρ.representation.IntertwiningMap Rτ.representation,
          ∃! s : I ⟶ τ, (∀ w, SmoothRep.hom s (f w) = ψ w) ∧
            ∀ v : I, SmoothRep.hom s v =
              ∑ᶠ q : LeftQuotient (rationalCommonNormKernel G),
                τ.representation q.out
                  (ψ (eval (rationalCommonNormKernel G) ρ.representation v.1 q.out⁻¹))

end Langlands.CuspidalSupport
