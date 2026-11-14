import Langlands.Representation.Exponents.MaximalLeviBlockStatements
import Langlands.Representation.Exponents.LeviInductionDualityAdjunction

/-! # The functor `r_D` of a non-self-associate supercuspidal block of a maximal Levi

Renard 2026, VII.1.3, Corollary (ii)–(iii) (printed p.226/PDF p.232), for the functor
`r_D` itself: `r_D` is `r_P^G` followed by the projection onto the factor `M(M)_D`; it is
faithful from `M(G)_Ω` to `M(M)_D`, the natural morphism `π → i_P^G r_D(π)` is an
isomorphism for every `π` in `M(G)_Ω`, and `r_D` is an equivalence with inverse `i_P^G`.
The setting and the encodings of `D`, `M(M)_D` and `M(G)_Ω` are those of the published
`MaximalLeviBlockStatements`.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- Renard VII.1.3, Corollary, parts (ii) and (iii) for the functor `r_D`, in the setting
and encoding of `MaximalLeviBlockStatements` (an actual maximal proper rational parabolic,
an irreducible supercuspidal `ρ` of `M(F)` whose inertial class `D` is not fixed by the
nontrivial element of `W(M, *)`, the block `InBlockM` of `D` in `M(M)` and the block
`InBlockG` of `G(F)`; carriers in `Type (max u v)`):

* (a) the inclusion of `InBlockM` has a left adjoint, that is, the projection of `M(M)`
  onto `M(M)_D` exists;
* for every left adjoint `L` of that inclusion, with adjunction `adjL`, put
  `r_D := InBlockG.ι ⋙ r_P^G ⋙ L`. Then
  (ii) `r_D` is faithful;
  (iii) for every object `Y` of `InBlockG`, the unit at `Y` of the composite adjunction
  `r_P^G ⋙ L ⊣ InBlockM.ι ⋙ i_P^G` (first adjointness followed by `adjL`), a morphism
  `Y → i_P^G r_D(Y)`, is an isomorphism; and some equivalence `InBlockG ≌ InBlockM` has
  functor `r_D` and an inverse whose composite with the inclusion of `InBlockG` is
  isomorphic to `i_P^G` on `InBlockM`. -/
def MaximalLeviBlockProjectionEquivalenceStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (P M U : GroupScheme (Spec (CommRingCat.of k)))
      (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
      (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
      (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
      (hmul : IsIso (subgroupMultiplication l r)),
      ¬ IsIso p →
      (∀ (Q : GroupScheme (Spec (CommRingCat.of k))) (q : Q ⟶ G) (j : P ⟶ Q),
        IsParabolicSubgroup q → j ≫ q = p → IsIso j ∨ IsIso q) →
      haveI := hl.isConnectedReductive.isAffineHom
      letI : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
      haveI : LocallyCompactSpace (rationalPoints M) := leviPoints_locallyCompactSpace p l hp hl
      haveI : NonarchimedeanGroup (rationalPoints M) := leviPoints_nonarchimedeanGroup p l hp hl
      ∀ ρ : SmoothRep.{0, u, max u v} ℂ (rationalPoints M), ρ.IsIrreducible →
        (∀ (P' M' U' : GroupScheme (Spec (CommRingCat.of k)))
          (p' : P' ⟶ M) (l' : M' ⟶ P') (r' : U' ⟶ P')
          (hp' : IsParabolicSubgroup p') (hl' : IsRationalLeviSubgroup l')
          (hr' : LeviSubgroup.IsGeometricUnipotentRadical r')
          (hmul' : IsIso (subgroupMultiplication l' r')),
          ¬ IsIso p' → Subsingleton ((jacquetFunctor p' l' r' hp' hr' hl' hmul').obj ρ)) →
        (¬ ∃ (g : rationalPoints G) (φ : M ≅ M),
          φ.hom ≫ l ≫ p = l ≫ p ≫ (G.innerIso g).hom ∧ g ∉ pointImage (l ≫ p) ∧
          ∃ ψ : Plancherel.unramifiedCharacters
              (fun χ : rationalCharacters M => (Plancherel.rationalNormCharacters M χ).toMul),
            ∃ T : ρ ≃ₗ[ℂ] ρ, ∀ (m : rationalPoints M) (x : ρ),
              T (ρ.representation m x) =
                (((ψ : rationalPoints M →ₜ* ℂˣ) (rationalPoints.map φ.hom m) : ℂˣ) : ℂ) •
                  ρ.representation (rationalPoints.map φ.hom m) (T x)) →
        let IsTwist : SmoothRep.{0, u, max u v} ℂ (rationalPoints M) → Prop := fun σ =>
          ∃ ψ : Plancherel.unramifiedCharacters
              (fun χ : rationalCharacters M => (Plancherel.rationalNormCharacters M χ).toMul),
            ∃ T : ρ ≃ₗ[ℂ] σ, ∀ (m : rationalPoints M) (x : ρ),
              (((ψ : rationalPoints M →ₜ* ℂˣ) m : ℂˣ) : ℂ) • T (ρ.representation m x) =
                σ.representation m (T x)
        let InBlockM : ObjectProperty (SmoothRep.{0, u, max u v} ℂ (rationalPoints M)) :=
          fun X => ∀ σ : SmoothRep.{0, u, max u v} ℂ (rationalPoints M),
            σ.IsIrreducible → SmoothRep.IsSubquotient σ X → IsTwist σ
        let InBlockG : ObjectProperty (SmoothRep.{0, u, max u v} ℂ (rationalPoints G)) :=
          fun Y => ∀ τ : SmoothRep.{0, u, max u v} ℂ (rationalPoints G),
            τ.IsIrreducible → SmoothRep.IsSubquotient τ Y →
              ∃ σ : SmoothRep.{0, u, max u v} ℂ (rationalPoints M), IsTwist σ ∧
                SmoothRep.IsSubquotient τ ((leviInductionFunctor p l r hp hr hl hmul).obj σ)
        InBlockM.ι.IsRightAdjoint ∧
        ∀ (L : SmoothRep.{0, u, max u v} ℂ (rationalPoints M) ⥤ InBlockM.FullSubcategory)
          (adjL : L ⊣ InBlockM.ι),
          let rD : InBlockG.FullSubcategory ⥤ InBlockM.FullSubcategory :=
            InBlockG.ι ⋙ leviJacquetFunctor.{u, max u v} p l r hp hr hl hmul ⋙ L
          let adj := (leviFirstAdjointnessAdjunction.{u, v} p l r hp hl hr hmul).comp adjL
          rD.Faithful ∧
          (∀ Y : InBlockG.FullSubcategory, IsIso (adj.unit.app Y.obj)) ∧
          ∃ E : InBlockG.FullSubcategory ≌ InBlockM.FullSubcategory,
            E.functor = rD ∧
            Nonempty (E.inverse ⋙ InBlockG.ι ≅
              InBlockM.ι ⋙ leviInductionFunctor.{u, max u v} p l r hp hr hl hmul)

end Langlands.Aubert.General.RepresentedParabolic
