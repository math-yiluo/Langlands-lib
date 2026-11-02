import Langlands.AlgebraicGeometry.Modules.ProperAmplePairSerreVanishingStatement
import Langlands.AlgebraicGeometry.Modules.CoherentEulerSequence

/-! # Multiplication by a section of a line bundle, and the section-killing interface -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.Scheme.Modules Langlands.SchemeModule Langlands.AlgebraicGeometry.Picard

namespace Langlands.AlgebraicGeometry.Modules.SerreVanishing

/-- Multiplication by a global section `s` of `N`, as the map `G ⟶ G ⊗ N`,
`g ↦ g ⊗ s`. -/
def twistMul {X : Scheme.{u}} (N : X.Modules) (s : GlobalSections N) (G : X.Modules) :
    G ⟶ tensorObj G N :=
  (tensorRightUnitor G).inv ≫ tensorMap (𝟙 G) (sectionHom N s)

/-- Section killing on a proper scheme over a field (after Stacks 01XR): if `s` is a
global section of a line bundle `N` whose trivialization locus is affine, and the
kernel and cokernel of multiplication by `s` on a coherent `G` have vanishing
cohomology in degrees `i + 1` and `i` after every twist `N^(m+k)` and a further twist
by a line bundle `P`, then `Hⁱ((G ⊗ N^(m+t)) ⊗ P)` vanishes for some `t`. -/
def SectionKillingStatement : Prop :=
  ∀ (K : Type u) [Field K] (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of K)),
    IsProper f →
      ∀ (N : X.Modules), IsLocallyFreeRankOne N → ∀ s : GlobalSections N,
        IsAffineOpen (trivializationOpen N s) →
          ∀ (P : X.Modules), IsLocallyFreeRankOne P →
            ∀ (G : X.Modules), G.IsQuasicoherent → HasFiniteAffineSections G →
              ∀ m i : ℕ, 0 < i →
                (∀ k : ℕ, IsZero ((DerivedSections.relativeCohomology f (i + 1)).obj
                  (tensorObj (tensorObj (kernel (twistMul N s G)) (tensorPow N (m + k))) P))) →
                (∀ k : ℕ, IsZero ((DerivedSections.relativeCohomology f i).obj
                  (tensorObj (tensorObj (cokernel (twistMul N s G)) (tensorPow N (m + k)))
                    P))) →
                ∃ t : ℕ, IsZero ((DerivedSections.relativeCohomology f i).obj
                  (tensorObj (tensorObj G (tensorPow N (m + t))) P))

end Langlands.AlgebraicGeometry.Modules.SerreVanishing
