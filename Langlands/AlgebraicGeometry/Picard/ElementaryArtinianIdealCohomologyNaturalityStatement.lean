import Langlands.AlgebraicGeometry.Picard.StructureKernelModule
import Langlands.AlgebraicGeometry.Modules.CohomologyPullback
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Artinian.Ring
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-! # Naturality of elementary ideal cohomology with residue coordinates -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing

namespace Langlands.AlgebraicGeometry.Picard.ElementaryArtinianIdealCohomology

open StructureKernelModule Langlands.Scheme.Modules
  Langlands.AlgebraicGeometry.Modules.DerivedSections

variable {R S : Type u} [CommRing R] [CommRing S]
  (φ : R →+* S)

/-- The actual closed-fibre ideal, formed before any coordinate comparison. -/
abbrev ideal (X : Over (Spec (CommRingCat.of R))) :=
  kernelModule (pullback.fst X.hom (Spec.map (CommRingCat.ofHom φ)))

/-- Relative cohomology of the actual closed-fibre ideal. -/
abbrev idealCohomology (X : Over (Spec (CommRingCat.of R))) (n : ℕ) :=
  (relativeCohomology X.hom n).obj (ideal φ X)

/-- Compatibility with the actual ideal inclusions. -/
def Compatible {X Y : Over (Spec (CommRingCat.of R))} (f : Y ⟶ X)
    (k : ideal φ X ⟶ (Scheme.Modules.pushforward f.left).obj (ideal φ Y)) : Prop :=
  k ≫ (Scheme.Modules.pushforward f.left).map
      (kernelModuleι (pullback.fst Y.hom (Spec.map (CommRingCat.ofHom φ)))) =
    kernelModuleι (pullback.fst X.hom (Spec.map (CommRingCat.ofHom φ))) ≫
      unitToPushforwardUnit f.left

/-- The coefficient pullback used in the Artinian reduced-coproduct target. -/
def idealPull {X Y : Over (Spec (CommRingCat.of R))} (f : Y ⟶ X)
    (k : ideal φ X ⟶ (Scheme.Modules.pushforward f.left).obj (ideal φ Y)) (n : ℕ) :
    idealCohomology φ X n →ₗ[R] idealCohomology φ Y n :=
  (relativeCohomologyPullback f (ideal φ X) n ≫
    (relativeCohomology Y.hom n).map
      (((Scheme.Modules.pullbackPushforwardAdjunction f.left).homEquiv _ _).symm k)).hom

variable {K : Type u} [Field K]

/-- Actual relative structure-module cohomology over a field. -/
abbrev structureCohomology (X : Over (Spec (CommRingCat.of K))) (n : ℕ) :=
  (relativeCohomology X.hom n).obj (SheafOfModules.unit X.left.ringCatSheaf)

/-- Structure-module pullback, with its canonical coefficient comparison. -/
def structurePull {X Y : Over (Spec (CommRingCat.of K))} (f : Y ⟶ X) (n : ℕ) :
    structureCohomology X n →ₗ[K] structureCohomology Y n :=
  (relativeCohomologyPullback f (SheafOfModules.unit X.left.ringCatSheaf) n ≫
    (relativeCohomology Y.hom n).map (pullbackUnitIso f.left).hom).hom

variable [IsLocalRing S]

/-- The residue immersion into the original affine source base. -/
abbrev residueBaseMap :=
  Spec.map (CommRingCat.ofHom ((residue S).comp φ))

/-- Base change to the actual target residue field. -/
abbrev residuePullback :=
  Over.pullback (residueBaseMap φ)

/-- For a fixed pair of flat proper schemes and every degree, one common finite
coordinate system identifies their elementary ideal cohomology with residue
structure cohomology and commutes with every compatible coefficient pullback.
This proposition records the missing comparison; it proves no injectivity. -/
def NaturalityStatement : Prop :=
  ∀ (R S : Type u) [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    [IsArtinianRing R] [IsArtinianRing S] (φ : R →+* S),
    Function.Surjective φ → maximalIdeal R * RingHom.ker φ = ⊥ →
      ∀ (X Y : Over (Spec (CommRingCat.of R)))
        [Flat X.hom] [IsProper X.hom] [Flat Y.hom] [IsProper Y.hom] (n : ℕ),
        ∃ (d : ℕ)
          (eX : idealCohomology φ X n ≃+
            (Fin d → structureCohomology ((residuePullback φ).obj X) n))
          (eY : idealCohomology φ Y n ≃+
            (Fin d → structureCohomology ((residuePullback φ).obj Y) n)),
          ∀ (f : Y ⟶ X)
            (k : ideal φ X ⟶ (Scheme.Modules.pushforward f.left).obj (ideal φ Y)),
            Compatible φ f k →
              ∀ (x : idealCohomology φ X n) (j : Fin d),
                eY (idealPull φ f k n x) j =
                  structurePull ((residuePullback φ).map f) n (eX x j)

end Langlands.AlgebraicGeometry.Picard.ElementaryArtinianIdealCohomology
