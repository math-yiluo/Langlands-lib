import Langlands.AlgebraicGeometry.Modules.TildePullback
import Langlands.AlgebraicGeometry.Modules.AffineQuasicoherentHigherDirectImageVanishingProof

/-! # Quasi-coherent pullback along a morphism of spectra -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.Scheme.Modules

variable {R S : CommRingCat.{u}} (φ : R ⟶ S)

/-- The actual pullback of a quasi-coherent sheaf on a spectrum is the associated
sheaf of the scalar extension of its global sections. -/
def affinePullbackTildeIso (M : (Spec R).Modules) [M.IsQuasicoherent] :
    (AlgebraicGeometry.Scheme.Modules.pullback (Spec.map φ)).obj M ≅
      tilde ((ModuleCat.extendScalars φ.hom).obj
        ((moduleSpecΓFunctor (R := R)).obj M)) :=
  ((AlgebraicGeometry.Scheme.Modules.pullback (Spec.map φ)).mapIso
    (asIso M.fromTildeΓ)).symm ≪≫
      tildePullbackIso φ ((moduleSpecΓFunctor (R := R)).obj M)

/-- This identification agrees with the existing tilde pullback comparison
after pulling back the tilde–global-sections counit. -/
@[reassoc]
lemma affinePullbackTildeIso_counit (M : (Spec R).Modules) [M.IsQuasicoherent] :
    (AlgebraicGeometry.Scheme.Modules.pullback (Spec.map φ)).map M.fromTildeΓ ≫
        (affinePullbackTildeIso φ M).hom =
      (tildePullbackIso φ ((moduleSpecΓFunctor (R := R)).obj M)).hom := by
  simp [affinePullbackTildeIso]

/-- Pullback between spectra preserves quasi-coherence. -/
instance isQuasicoherent_affinePullback (M : (Spec R).Modules) [M.IsQuasicoherent] :
    ((AlgebraicGeometry.Scheme.Modules.pullback (Spec.map φ)).obj M).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent (Spec S).ringCatSheaf).prop_of_iso
    (affinePullbackTildeIso φ M).symm inferInstance

/-- The identification is natural in a quasi-coherent coefficient sheaf. -/
@[reassoc]
lemma affinePullbackTildeIso_naturality {M N : (Spec R).Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (a : M ⟶ N) :
    (AlgebraicGeometry.Scheme.Modules.pullback (Spec.map φ)).map a ≫
        (affinePullbackTildeIso φ N).hom =
      (affinePullbackTildeIso φ M).hom ≫
        tilde.map ((ModuleCat.extendScalars φ.hom).map
          ((moduleSpecΓFunctor (R := R)).map a)) := by
  apply (cancel_epi
    ((AlgebraicGeometry.Scheme.Modules.pullback (Spec.map φ)).map M.fromTildeΓ)).1
  have h := (tilde.adjunction (R := R)).counit.naturality a
  dsimp only [Functor.comp_map, Functor.id_map] at h
  change tilde.map ((moduleSpecΓFunctor (R := R)).map a) ≫ N.fromTildeΓ =
    M.fromTildeΓ ≫ a at h
  have h' := congrArg
    (AlgebraicGeometry.Scheme.Modules.pullback (Spec.map φ)).map h
  simp only [Functor.map_comp] at h'
  rw [← Category.assoc, ← h', Category.assoc,
    affinePullbackTildeIso_counit, ← Category.assoc,
    affinePullbackTildeIso_counit]
  exact tildePullbackIso_hom_naturality φ ((moduleSpecΓFunctor (R := R)).map a)

end Langlands.Scheme.Modules

namespace Langlands.AlgebraicGeometry.Modules.DerivedSections

variable {R S : CommRingCat.{u}} (φ : R ⟶ S)

/-- The actual pullback of a quasi-coherent module between spectra is acyclic
for pushforward along that same morphism. -/
lemma isZero_higherDirectImage_affinePullback (M : (Spec R).Modules)
    [M.IsQuasicoherent] (q : ℕ) :
    IsZero ((higherDirectImage (Spec.map φ) (q + 1)).obj
      ((AlgebraicGeometry.Scheme.Modules.pullback (Spec.map φ)).obj M)) :=
  affineQuasicoherentHigherDirectImageVanishing (Spec S) (Spec R) (Spec.map φ)
    inferInstance _ inferInstance q

end Langlands.AlgebraicGeometry.Modules.DerivedSections
