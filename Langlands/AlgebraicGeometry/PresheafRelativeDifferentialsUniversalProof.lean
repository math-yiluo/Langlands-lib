import Langlands.AlgebraicGeometry.PresheafRelativeDifferentialsStatement

/-!
# Universality of the constructed relative derivation

We prove `Langlands.PresheafDifferentials.DerivationUniversalStatement φ` for every
`φ : S ⟶ F.op ⋙ R`. The derivation `derivation φ` is Mathlib's universal derivation
`DifferentialsConstruction.derivation' (pullbackRingι φ)` read as a `φ`-derivation,
and `φ`-derivations and `pullbackRingι φ`-derivations correspond by `derivationEquiv`
compatibly with postcomposition, so Mathlib's `isUniversal'` transfers.
-/

universe u v₁ v₂ u₁ u₂

open CategoryTheory

namespace Langlands.PresheafDifferentials

open PresheafOfModulesOfCommRing

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {S : Cᵒᵖ ⥤ CommRingCat.{u}} {F : C ⥤ D} {R : Dᵒᵖ ⥤ CommRingCat.{u}}
  (φ : S ⟶ F.op ⋙ R)

/-- The universal property of `derivation φ`, obtained from Mathlib's
`DifferentialsConstruction.isUniversal' (pullbackRingι φ)`. -/
noncomputable def derivationUniversal : (derivation φ).Universal where
  desc d' := (DifferentialsConstruction.isUniversal' (pullbackRingι φ)).desc
    (toPullbackDerivation d')
  fac d' := congrArg ofPullbackDerivation
    ((DifferentialsConstruction.isUniversal' (pullbackRingι φ)).fac (toPullbackDerivation d'))
  postcomp_injective α β h :=
    (DifferentialsConstruction.isUniversal' (pullbackRingι φ)).postcomp_injective α β
      (congrArg toPullbackDerivation h)

/-- The constructed derivation `derivation φ` is universal. -/
theorem derivationUniversalStatement : DerivationUniversalStatement φ :=
  ⟨derivationUniversal φ⟩

end Langlands.PresheafDifferentials
