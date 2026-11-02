import Langlands.AlgebraicGeometry.Modules.DirectImageBaseChangeSheaf
import Langlands.AlgebraicGeometry.Modules.FixedRankLocalBases
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree

/-! # Fixed-rank direct images from affine sections data -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct ChangeOfRings

namespace Langlands.AlgebraicGeometry.Modules.DerivedSections

variable {R : CommRingCat.{u}} {X : Scheme.{u}}

/-- The principal-open localization presentation is Cartesian. -/
lemma isPullback_principalOpenBaseChange (f : X ⟶ Spec R) (r : R) :
    IsPullback (f ⁻¹ᵁ PrimeSpectrum.basicOpen r).ι
      ((f ∣_ PrimeSpectrum.basicOpen r) ≫ (basicOpenIsoSpecAway r).hom)
      f (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r)))) := by
  apply (isPullback_morphismRestrict f (PrimeSpectrum.basicOpen r)).flip.of_iso
    (Iso.refl _) (Iso.refl _) (basicOpenIsoSpecAway r) (Iso.refl _)
  · simp
  · simp
  · simp
  · simpa using (basicOpenIsoSpecAway_hom_SpecMap r).symm

/-- Cartesian affine scalar base change implies quasi-coherence of the direct image. -/
lemma isQuasicoherent_pushforward_of_affineScalarBaseChange
    (f : X ⟶ Spec R) (M : X.Modules)
    (h : ∀ (T : CommRingCat.{u}) (φ : R ⟶ T) (XT : Scheme.{u})
      (p : XT ⟶ X) (fT : XT ⟶ Spec T) (hp : IsPullback p fT f (Spec.map φ)),
      IsIso (scalarSectionsBaseChangeMap φ f fT p hp.w M)) :
    ((Scheme.Modules.pushforward f).obj M).IsQuasicoherent := by
  apply isQuasicoherent_pushforward_of_isIso_principalOpenScalarSectionsBaseChangeMap
  intro r
  exact h _ _ _ _ _ (isPullback_principalOpenBaseChange f r)

/-- A basis after principal-open scalar extension gives an actual free sheaf chart. -/
def freeChartOfLocalizedBasis (P : (Spec R).Modules) [P.IsQuasicoherent]
    (r : R) (I : Type u)
    (b : Module.Basis I (Localization.Away r)
      (Localization.Away r ⊗[R] ((moduleSpecΓFunctor (R := R)).obj P))) :
    P.restrict (Scheme.Opens.ι (X := Spec R) (PrimeSpectrum.basicOpen r)) ≅
      SheafOfModules.free (R := (Scheme.Opens.toScheme (X := Spec R) (PrimeSpectrum.basicOpen r)).ringCatSheaf) I := by
  let Ar := Localization.Away r
  let N := (moduleSpecΓFunctor (R := R)).obj P
  let φ : R ⟶ CommRingCat.of Ar := CommRingCat.ofHom (algebraMap R Ar)
  let E : P.restrict (Spec.map φ) ≅
      SheafOfModules.free (R := (Spec (CommRingCat.of Ar)).ringCatSheaf) I :=
    (Scheme.Modules.restrictFunctorIsoPullback (Spec.map φ)).app P ≪≫
      Langlands.Scheme.Modules.affinePullbackTildeIso φ P ≪≫
      (tilde.functor (CommRingCat.of Ar)).mapIso
        (Langlands.Scheme.Modules.extendScalarsAlgebraIso R (CommRingCat.of Ar) N) ≪≫
      (tilde.functor (CommRingCat.of Ar)).mapIso b.repr.toModuleIso ≪≫
      tildeFinsupp I
  exact (Scheme.Modules.restrictFunctorCongr
      (basicOpenIsoSpecAway_hom_SpecMap r).symm).app P ≪≫
    (Scheme.Modules.restrictFunctorComp (basicOpenIsoSpecAway r).hom (Spec.map φ)).app P ≪≫
    (Scheme.Modules.restrictFunctor (basicOpenIsoSpecAway r).hom).mapIso E ≪≫
    (Scheme.Modules.restrictFunctorIsoPullback (basicOpenIsoSpecAway r).hom).app _ ≪≫
    SheafOfModules.pullbackObjFreeIso (basicOpenIsoSpecAway r).hom.toRingCatSheafHom I

/-- A quasi-coherent sheaf with finite projective sections of constant stalk rank
has free neighborhoods with the prescribed number of generators. -/
theorem exists_freeNeighborhood_of_finite_projective_rankAtStalk
    (P : (Spec R).Modules) [P.IsQuasicoherent]
    [Module.Finite R ((moduleSpecΓFunctor (R := R)).obj P)]
    [Module.Projective R ((moduleSpecΓFunctor (R := R)).obj P)]
    (n : ℕ) (hr : ∀ q : PrimeSpectrum R,
      Module.rankAtStalk ((moduleSpecΓFunctor (R := R)).obj P) q = n)
    (x : Spec R) :
    ∃ U : (Spec R).Opens, x ∈ U ∧ Nonempty (P.restrict U.ι ≅
      SheafOfModules.free (R := U.toScheme.ringCatSheaf) (ULift.{u} (Fin n))) := by
  let N := (moduleSpecΓFunctor (R := R)).obj P
  let : Module.FinitePresentation R N := Module.finitePresentation_of_projective R N
  let : Module.Free (Localization.AtPrime x.asIdeal)
      (LocalizedModule x.asIdeal.primeCompl N) := Module.free_of_flat_of_isLocalRing
  let b : Module.Basis (ULift.{u} (Fin n)) (Localization.AtPrime x.asIdeal)
      (LocalizedModule x.asIdeal.primeCompl N) :=
    (Module.finBasisOfFinrankEq _ _ (hr x)).reindex Equiv.ulift.symm
  obtain ⟨r, hrx, b', _⟩ := Module.FinitePresentation.exists_basis_localizedModule_powers
    x.asIdeal.primeCompl (LocalizedModule.mkLinearMap x.asIdeal.primeCompl N)
    (Localization.AtPrime x.asIdeal) b
  let e := LocalizedModule.equivTensorProduct (Submonoid.powers r) N
  exact ⟨PrimeSpectrum.basicOpen r, hrx,
    ⟨freeChartOfLocalizedBasis P r (ULift.{u} (Fin n)) (b'.map e)⟩⟩

/-- Constant stalk rank of finite projective affine sections gives actual fixed rank. -/
theorem isLocallyFreeOfRank_of_finite_projective_rankAtStalk
    (P : (Spec R).Modules) [P.IsQuasicoherent]
    [Module.Finite R ((moduleSpecΓFunctor (R := R)).obj P)]
    [Module.Projective R ((moduleSpecΓFunctor (R := R)).obj P)]
    (n : ℕ) (hr : ∀ q : PrimeSpectrum R,
      Module.rankAtStalk ((moduleSpecΓFunctor (R := R)).obj P) q = n) :
    Langlands.Scheme.Modules.IsLocallyFreeOfRank P n :=
  Langlands.Scheme.Modules.isLocallyFreeOfRank_of_freeNeighborhoods P n
    (exists_freeNeighborhood_of_finite_projective_rankAtStalk P n hr)

end Langlands.AlgebraicGeometry.Modules.DerivedSections
