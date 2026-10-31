import Langlands.AlgebraicGeometry.Modules.PushforwardComparison
import Langlands.AlgebraicGeometry.Modules.PushforwardInjectiveAcyclicProof
import Langlands.AlgebraicGeometry.Modules.ClosedImmersionHigherDirectImageVanishingProof
import Mathlib.CategoryTheory.Adjunction.FullyFaithful

/-! # Relative cohomology and scheme isomorphisms -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Modules

variable {X Y : Scheme.{u}}

/-- Pushforward along a scheme isomorphism is an equivalence of module categories. -/
def pushforwardEquivalence (e : X ≅ Y) : X.Modules ≌ Y.Modules :=
  CategoryTheory.Equivalence.mk (Scheme.Modules.pushforward e.hom) (Scheme.Modules.pushforward e.inv)
    (Scheme.Modules.pushforwardComp e.hom e.inv ≪≫
      Scheme.Modules.pushforwardCongr e.hom_inv_id ≪≫ Scheme.Modules.pushforwardId X).symm
    (Scheme.Modules.pushforwardComp e.inv e.hom ≪≫
      Scheme.Modules.pushforwardCongr e.inv_hom_id ≪≫ Scheme.Modules.pushforwardId Y)

namespace DerivedSections

/-- Relative cohomology of a pulled-back module is invariant under a scheme isomorphism. -/
def relativeCohomologyPullbackIso (e : X ≅ Y) {R : CommRingCat.{u}}
    (g : Y ⟶ Spec R) (M : Y.Modules) (n : ℕ) :
    (relativeCohomology (e.hom ≫ g) n).obj ((Scheme.Modules.pullback e.hom).obj M) ≅
      (relativeCohomology g n).obj M := by
  letI : (Scheme.Modules.pushforward e.hom).IsEquivalence :=
    (pushforwardEquivalence e).isEquivalence_functor
  let hM : ∀ q : ℕ, IsZero ((higherDirectImage e.hom (q + 1)).obj
      ((Scheme.Modules.pullback e.hom).obj M)) := fun q =>
    closedImmersionHigherDirectImageVanishing X Y e.hom inferInstance _ q
  haveI := isIso_pushforwardComparison e.hom g _ hM
    (fun J hJ q => (pushforwardInjectiveAcyclic X Y e.hom J hJ q).2 R g) n
  exact asIso (pushforwardComparison e.hom g _ hM n) ≪≫
    (relativeCohomology g n).mapIso
      (asIso ((Scheme.Modules.pullbackPushforwardAdjunction e.hom).unit.app M)).symm

end DerivedSections

end Langlands.AlgebraicGeometry.Modules
