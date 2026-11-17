import Langlands.AlgebraicGeometry.Modules.AffineDirectImageRank
import Langlands.AlgebraicGeometry.Modules.DirectImageAffineCriterion
import Langlands.AlgebraicGeometry.Modules.FieldGlobalFunctionsSheaf
import Langlands.AlgebraicGeometry.Picard.FiniteLocallyFreeDeterminant

/-! # Finite local bases from finite projective affine sections -/

noncomputable section
universe u

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace Langlands.AlgebraicGeometry.Modules

namespace DerivedSections

/-- A finite projective affine module has an actual finite free sheaf chart
around each point; the chart rank may depend on the point. -/
theorem exists_freeNeighborhood_of_finite_projective {R : CommRingCat.{u}}
    (P : (Spec R).Modules) [P.IsQuasicoherent]
    [Module.Finite R (moduleSpecΓFunctor.obj P)]
    [Module.Projective R (moduleSpecΓFunctor.obj P)] (x : Spec R) :
    ∃ (n : ℕ) (U : (Spec R).Opens), x ∈ U ∧ Nonempty
      (P.restrict U.ι ≅ SheafOfModules.free
        (R := U.toScheme.ringCatSheaf) (ULift.{u} (Fin n))) := by
  let N := moduleSpecΓFunctor.obj P
  let : Module.FinitePresentation R N := Module.finitePresentation_of_projective R N
  let : Module.Free (Localization.AtPrime x.asIdeal)
      (LocalizedModule x.asIdeal.primeCompl N) := Module.free_of_flat_of_isLocalRing
  let b := (Module.finBasis (Localization.AtPrime x.asIdeal)
    (LocalizedModule x.asIdeal.primeCompl N)).reindex Equiv.ulift.symm
  obtain ⟨r, hrx, b', _⟩ := Module.FinitePresentation.exists_basis_localizedModule_powers
    x.asIdeal.primeCompl (LocalizedModule.mkLinearMap x.asIdeal.primeCompl N)
    (Localization.AtPrime x.asIdeal) b
  let e := LocalizedModule.equivTensorProduct (Submonoid.powers r) N
  exact ⟨_, PrimeSpectrum.basicOpen r, hrx,
    ⟨freeChartOfLocalizedBasis P r _ (b'.map e)⟩⟩

end DerivedSections

variable {X : Scheme.{u}}

/-- Finite projective sections on affine opens give finite free neighborhoods
of a quasi-coherent module sheaf on an arbitrary scheme. -/
theorem exists_freeNeighborhood_of_finite_projective_affineSections
    (M : X.Modules) [M.IsQuasicoherent]
    (hfinite : ∀ U : X.affineOpens, Module.Finite Γ(X, U) Γ(M, U))
    (hprojective : ∀ U : X.affineOpens, Module.Projective Γ(X, U) Γ(M, U))
    (x : X) :
    ∃ (n : ℕ) (U : X.Opens), x ∈ U ∧ Nonempty
      (M.restrict U.ι ≅ SheafOfModules.free
        (R := U.toScheme.ringCatSheaf) (ULift.{u} (Fin n))) := by
  obtain ⟨U, hU, hxU, _⟩ := exists_isAffineOpen_mem_and_subset
    (show x ∈ (⊤ : X.Opens) from trivial)
  let P := M.restrict hU.fromSpec
  let e : moduleSpecΓFunctor.obj P ≃ₗ[Γ(X, U)] Γ(M, U) :=
    (FieldGlobalFunctions.affineChartSectionsIso M hU).toLinearEquiv
  have : Module.Finite Γ(X, U) Γ(M, U) := hfinite ⟨U, hU⟩
  have : Module.Projective Γ(X, U) Γ(M, U) := hprojective ⟨U, hU⟩
  have : Module.Finite Γ(X, U) (moduleSpecΓFunctor.obj P) :=
    Module.Finite.equiv e.symm
  have : Module.Projective Γ(X, U) (moduleSpecΓFunctor.obj P) :=
    Module.Projective.of_equiv e.symm
  let t : Spec Γ(X, U) := hU.isoSpec.hom ⟨x, hxU⟩
  have ht : hU.fromSpec t = x := by
    change (hU.isoSpec.hom ≫ hU.isoSpec.inv ≫ U.ι) ⟨x, hxU⟩ = x
    simp
  obtain ⟨n, W, htW, ⟨eW⟩⟩ :=
    DerivedSections.exists_freeNeighborhood_of_finite_projective P t
  let j := W.ι ≫ hU.fromSpec
  let E : M.restrict j ≅ SheafOfModules.free
      (R := W.toScheme.ringCatSheaf) (ULift.{u} (Fin n)) :=
    (Scheme.Modules.restrictFunctorComp W.ι hU.fromSpec).app M ≪≫ eW
  exact ⟨n, j.opensRange, ⟨⟨t, htW⟩, ht⟩,
    ⟨DerivedSections.freeChartOnOpensRange M j _ E⟩⟩

/-- A quasi-coherent sheaf with finite projective affine sections has a
cover by actual finite bases, without a constant-rank hypothesis. -/
theorem hasFiniteLocalBasis_of_finite_projective_affineSections
    (M : X.Modules) [M.IsQuasicoherent]
    (hfinite : ∀ U : X.affineOpens, Module.Finite Γ(X, U) Γ(M, U))
    (hprojective : ∀ U : X.affineOpens, Module.Projective Γ(X, U) Γ(M, U)) :
    Langlands.Scheme.Modules.HasFiniteLocalBasis M := by
  classical
  choose n U hx e using
    exists_freeNeighborhood_of_finite_projective_affineSections M hfinite hprojective
  refine ⟨Langlands.Scheme.Modules.freeNeighborhoodGenerators M U hx
      (fun x => ULift.{u} (Fin (n x))) (fun x => (e x).some),
    Langlands.Scheme.Modules.freeNeighborhoodGenerators_isLocallyFreeData M U hx
      (fun x => ULift.{u} (Fin (n x))) (fun x => (e x).some), ?_⟩
  constructor
  intro x
  change ((SheafOfModules.free.generatingSections
    (ULift.{u} (Fin (n x)))).ofEpi _).IsFiniteType
  exact ⟨inferInstanceAs (Finite (ULift.{u} (Fin (n x))))⟩

end Langlands.AlgebraicGeometry.Modules
