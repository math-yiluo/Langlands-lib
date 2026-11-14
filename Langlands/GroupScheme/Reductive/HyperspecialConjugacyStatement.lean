import Langlands.GroupScheme.Adjoint.InnerAction
import Langlands.GroupScheme.Reductive.FibrewiseRootDatum
import Langlands.GroupScheme.Reductive.Basic
import Langlands.GroupScheme.Torus.FieldPointMaximality
import Mathlib.NumberTheory.LocalField.Basic

/-! # Statement: conjugacy of hyperspecial subgroups of split groups -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped ValuativeRel CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- **Conjugacy classes of the adjoint translates of `G(R)`** (Conrad, *Reductive group
schemes* (2014), Proposition 7.2.14). Let `F` be a nonarchimedean local field with valuation
ring `R = 𝒪[F]`, let `G` be a split reductive group scheme over `R`, and let `p : G ⟶ Gad` be
its adjoint central quotient over `R` (a flat, surjective homomorphism of finite presentation
onto a reductive group, whose kernel is the scheme-theoretic centre of `G`). The points of
`G` and `Gad` over `F` are their points over the `R`-scheme `Spec F`; the subgroup `G(R)` of
`G(F)` consists of the restrictions of the sections of `G` over `Spec R`. `Gad` acts on `G` by
the conjugation action descended along `p`. For `x ∈ Gad(F)`, the translate `x · G(R)` is
`G(F)`-conjugate to `G(R)` if and only if `x ∈ p(G(F)) · Gad(R)`. -/
def ReductiveHyperspecialConjugacyStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G Gad : GroupScheme (Spec (CommRingCat.of ↥𝒪[F])))
    (hG : IsReductive G) (hGad : IsReductive Gad) (p : G ⟶ Gad),
    (∃ (I : Type u) (_ : Fintype I) (i : splitTorus (Spec (CommRingCat.of ↥𝒪[F])) I ⟶ G)
        (J : Type u) (P : RootDatum J (I → ℤ) (I → ℤ)),
      haveI := hG.isAffineHom
      IsClosedSubgroup i ∧
        IsFibrewiseMaximalTorus
          (T := splitTorus.commGroupScheme (Spec (CommRingCat.of ↥𝒪[F])) I) i ∧
        IsFibrewiseRootDatumOf I G i P ∧
        ∀ α : J, Nonempty (splitTorus.exponentWeightSpace I G i (P.root α) ≃ₗ[CommRingCat.of ↥𝒪[F]]
          CommRingCat.of ↥𝒪[F])) →
    ∀ (hflat : Flat p.hom.hom.left) (hsurj : Surjective p.hom.hom.left),
    LocallyOfFinitePresentation p.hom.hom.left →
    ∀ (hker : IsSchemeTheoreticCenter (kernelι p)),
    haveI := hflat
    haveI := hsurj
    haveI := hG.isAffineHom
    haveI := hGad.isAffineHom
    haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    haveI : IsAffine Gad.X.left := isAffine_of_isAffineHom Gad.X.hom
    let a : AutomorphicAction Gad G :=
      (AutomorphicAction.conjugation (𝟙 G)).quotientAction p
        (AutomorphicAction.conjugation_kernelActsTrivially hker)
    let T : Over (Spec (CommRingCat.of ↥𝒪[F])) := Over.mk (Spec.algebraMap ↥𝒪[F] F)
    let res : T ⟶ Over.mk (𝟙 (Spec (CommRingCat.of ↥𝒪[F]))) := Over.homMk T.hom
    ∀ x : T ⟶ Gad.X,
      (∃ h : T ⟶ G.X, ∀ g : T ⟶ G.X,
          (∃ y : Over.mk (𝟙 (Spec (CommRingCat.of ↥𝒪[F]))) ⟶ G.X, g = a.act x (res ≫ y)) ↔
            ∃ y : Over.mk (𝟙 (Spec (CommRingCat.of ↥𝒪[F]))) ⟶ G.X,
              g = h * (res ≫ y) * h⁻¹) ↔
        ∃ (h : T ⟶ G.X) (y : Over.mk (𝟙 (Spec (CommRingCat.of ↥𝒪[F]))) ⟶ Gad.X),
          x = (h ≫ p.hom.hom) * (res ≫ y)

end Langlands.GroupScheme
