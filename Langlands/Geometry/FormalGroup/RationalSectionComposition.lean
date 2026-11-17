import Langlands.Geometry.FormalGroup.RationalHomSheaf
import Langlands.Geometry.SheafifyPairing
import Mathlib.Topology.Sheaves.LocallySurjective
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-! # Composition on actual rational formal Hom sheaf sections -/

noncomputable section

universe u v

namespace Langlands.FormalGroup.ModuleLaw

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

attribute [local instance] coefficientAlgebra coefficientScalarTower

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {F : Type v} [Field F] [Algebra O F]
variable {σ τ υ ω : Type} [Finite σ] [Finite τ] [Finite υ] [Finite ω]
variable {M : ModuleLaw O R σ} {N : ModuleLaw O R τ}
variable {P : ModuleLaw O R υ} {Q : ModuleLaw O R ω}

/-- The underlying type presheaf of the actual rational Hom presheaf. -/
abbrev rationalHomTypePresheaf (F : Type v) [Field F] [Algebra O F]
    (M : ModuleLaw O R σ) (N : ModuleLaw O R τ) :=
  rationalHomPresheaf F M N ⋙ forget (ModuleCat.{v} F)

/-- The underlying sheaf of types of the rational Hom module sheaf. -/
abbrev rationalHomTypeSheaf (F : Type v) [Field F] [Algebra O F]
    (M : ModuleLaw O R σ) (N : ModuleLaw O R τ) :
    TopCat.Sheaf (Type v) (PrimeSpectrum.Top R) :=
  (sheafCompose (Opens.grothendieckTopology (PrimeSpectrum.Top R))
    (forget (ModuleCat.{v} F))).obj (rationalHomSheaf F M N)

/-- The genuine module sheafification unit, with its scalar structure forgotten. -/
abbrev rationalHomTypeUnit (F : Type v) [Field F] [Algebra O F]
    (M : ModuleLaw O R σ) (N : ModuleLaw O R τ) :
    rationalHomTypePresheaf F M N ⟶ (rationalHomTypeSheaf F M N).obj :=
  Functor.whiskerRight
    (CategoryTheory.toSheafify (Opens.grothendieckTopology (PrimeSpectrum.Top R))
      (rationalHomPresheaf F M N)) (forget (ModuleCat.{v} F))

/-- Forgetting scalar structure preserves local injectivity of the genuine unit. -/
instance rationalHomTypeUnit_isLocallyInjective :
    Presheaf.IsLocallyInjective (Opens.grothendieckTopology (PrimeSpectrum.Top R))
      (rationalHomTypeUnit F M N) := by
  change Presheaf.IsLocallyInjective _ (Functor.whiskerRight
    (CategoryTheory.toSheafify (Opens.grothendieckTopology (PrimeSpectrum.Top R))
      (rationalHomPresheaf F M N)) (forget (ModuleCat.{v} F)))
  infer_instance

/-- Forgetting scalar structure preserves local surjectivity of the genuine unit. -/
instance rationalHomTypeUnit_isLocallySurjective :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology (PrimeSpectrum.Top R))
      (rationalHomTypeUnit F M N) := by
  change Presheaf.IsLocallySurjective _ (Functor.whiskerRight
    (CategoryTheory.toSheafify (Opens.grothendieckTopology (PrimeSpectrum.Top R))
      (rationalHomPresheaf F M N)) (forget (ModuleCat.{v} F)))
  infer_instance

/-- Tensor composition before sheafification, natural for the actual restrictions. -/
def rationalHomCompositionPresheaf :
    SheafifyPairing.pairs (rationalHomTypePresheaf F N P)
      (rationalHomTypePresheaf F M N) ⟶ rationalHomTypePresheaf F M P where
  app U := TypeCat.ofHom fun s => RationalHom.comp s.1 s.2
  naturality U V i := by
    apply ConcreteCategory.hom_ext
    intro s
    change RationalHom.comp
      (RationalHom.algebraMapLinear ((coefficientStructurePresheaf R).map i) s.1)
      (RationalHom.algebraMapLinear ((coefficientStructurePresheaf R).map i) s.2) =
        RationalHom.algebraMapLinear ((coefficientStructurePresheaf R).map i)
          (RationalHom.comp s.1 s.2)
    exact (RationalHom.algebraMapLinear_hom_comp _ _ _).symm

/-- Canonical natural composition on the sheafifications, obtained by local descent. -/
def rationalSectionComposition :
    SheafifyPairing.pairs (rationalHomTypeSheaf F N P).obj
      (rationalHomTypeSheaf F M N).obj ⟶ (rationalHomTypeSheaf F M P).obj :=
  SheafifyPairing.extend (Opens.grothendieckTopology (PrimeSpectrum.Top R))
    (rationalHomTypeUnit F N P) (rationalHomTypeUnit F M N)
    (rationalHomTypeSheaf F M P)
    (rationalHomCompositionPresheaf ≫ rationalHomTypeUnit F M P)

namespace RationalSection

/-- Compose actual rational Hom sheaf sections. -/
def comp {U : Opens (PrimeSpectrum R)}
    (g : RationalSection F N P U) (f : RationalSection F M N U) :
    RationalSection F M P U :=
  (rationalSectionComposition (F := F) (M := M) (N := N) (P := P)).app (op U) (g, f)

/-- On tensor representatives, section composition is the existing rational composition. -/
@[simp]
theorem comp_ofRational {U : Opens (PrimeSpectrum R)}
    (g : (rationalHomPresheaf F N P).obj (op U))
    (f : (rationalHomPresheaf F M N).obj (op U)) :
    comp (ofRational U g) (ofRational U f) =
      ofRational U (RationalHom.comp g f) := by
  exact SheafifyPairing.extend_apply
    (Opens.grothendieckTopology (PrimeSpectrum.Top R))
    (rationalHomTypeUnit F N P) (rationalHomTypeUnit F M N)
    (rationalHomTypeSheaf F M P)
    (rationalHomCompositionPresheaf ≫ rationalHomTypeUnit F M P) (op U) g f

/-- Composition commutes with restriction to every smaller open set. -/
@[simp]
theorem restrict_comp_hom {U V : Opens (PrimeSpectrum R)} (i : V ⟶ U)
    (g : RationalSection F N P U) (f : RationalSection F M N U) :
    restrict i (comp g f) = comp (restrict i g) (restrict i f) := by
  exact (congrArg (fun k => k (g, f))
    ((rationalSectionComposition (F := F) (M := M) (N := N) (P := P)).naturality
      i.op)).symm

end RationalSection

end Langlands.FormalGroup.ModuleLaw
