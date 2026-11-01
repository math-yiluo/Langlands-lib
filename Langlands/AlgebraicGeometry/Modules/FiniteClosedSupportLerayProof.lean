import Langlands.AlgebraicGeometry.Modules.FiniteClosedSupportLerayStatement
import Langlands.AlgebraicGeometry.Modules.FiniteClosedSupportCohomologyProof
import Langlands.AlgebraicGeometry.Modules.PushforwardComparison
import Langlands.AlgebraicGeometry.Modules.PushforwardInjectiveAcyclicProof
import Langlands.Cohomology.AcyclicResolution.AcyclicTermsHomologyComparisonProof

/-!
# A finite-support Leray comparison for actual scheme modules: proof

Let `I` be the chosen injective resolution of `M : X.Modules` and `K` its termwise pushforward
along `f`. The terms of `K` are pushforwards of injective modules, hence acyclic for the
`R`-module global sections `F` along `g`, and the homology objects of `K` are the higher direct
images `Rᵠ f_* M`. If these are `F`-acyclic, the generic acyclic-terms comparison identifies
`Hⁿ(F K)` with `F (Hⁿ K) ≅ Γ(Y, Rⁿ f_* M)`, while `F K` is the global sections along `f ≫ g` of
`I`, whose homology is `Hⁿ(X, M)`. Finite closed support makes the higher direct images
`F`-acyclic.
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Modules

namespace FiniteClosedSupportLeray

variable {X Y : Scheme.{u}} {R : CommRingCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Spec R) (M : X.Modules)

/-- `R`-module global sections along `g` applied termwise to the direct-image complex of `M`
is `R`-module global sections along `f ≫ g` applied termwise to the chosen injective
resolution of `M`. -/
noncomputable def mapDirectImageComplexIso :
    ((DerivedSections.relativeGlobalSections g).mapHomologicalComplex _).obj
        (DerivedSections.directImageComplex f M) ≅
      DerivedSections.relativeComplex (f ≫ g) M :=
  (Functor.mapHomologicalComplexCompIso (DerivedSections.relativeGlobalSectionsCompIso f g)
    (ComplexShape.up ℕ)).app (injectiveResolution M).cocomplex

/-- If every higher direct image `Rᵠ f_* M` is acyclic for the `R`-module global sections along
`g`, then the `R`-module cohomology of `M` along `f ≫ g` is the `R`-module global sections of
the higher direct images. -/
theorem nonempty_iso_of_isZero (hM : ∀ q r : ℕ, IsZero
      ((DerivedSections.relativeCohomology g (r + 1)).obj
        ((DerivedSections.higherDirectImage f q).obj M)))
    (n : ℕ) :
    Nonempty
      (((DerivedSections.relativeCohomology (f ≫ g) n).obj M) ≅
        (DerivedSections.relativeGlobalSections g).obj
          ((DerivedSections.higherDirectImage f n).obj M)) := by
  let F := DerivedSections.relativeGlobalSections g
  let K := DerivedSections.directImageComplex f M
  have hX : ∀ i r : ℕ, IsZero ((F.rightDerived (r + 1)).obj (K.X i)) := fun i r =>
    (pushforwardInjectiveAcyclic X Y f ((injectiveResolution M).cocomplex.X i)
      inferInstance r).2 R g
  have hH : ∀ i r : ℕ, IsZero ((F.rightDerived (r + 1)).obj (K.homology i)) := fun i r =>
    (hM i r).of_iso
      ((F.rightDerived (r + 1)).mapIso (DerivedSections.higherDirectImageIso f M i).symm)
  obtain ⟨e⟩ := Langlands.Cohomology.acyclicTermsHomologyComparisonStatement
    Y.Modules (ModuleCat.{u} R) F K hX hH n
  exact ⟨DerivedSections.relativeCohomologyIso (f ≫ g) M n ≪≫
    (HomologicalComplex.homologyFunctor _ _ n).mapIso (mapDirectImageComplexIso f g M).symm ≪≫
    e ≪≫ F.mapIso (DerivedSections.higherDirectImageIso f M n).symm⟩

end FiniteClosedSupportLeray

/-- When all higher direct images have finite closed support, total cohomology is isomorphic to
global sections of the higher direct images in every degree. -/
theorem finiteClosedSupportLeray : FiniteClosedSupportLerayStatement.{u} := by
  intro X Y R f g M hM n
  refine FiniteClosedSupportLeray.nonempty_iso_of_isZero f g M (fun q r => ?_) n
  exact ((finiteClosedSupportCohomology Y _ (hM q)).2.2 R g).1 r

end Langlands.AlgebraicGeometry.Modules
