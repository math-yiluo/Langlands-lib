import Langlands.Cohomology.ModuleComplex.GeometricFibreDegreeZero
import Langlands.AlgebraicGeometry.Modules.PerfectModelHomology
import Langlands.AlgebraicGeometry.Modules.PerfectFibreVanishing
import Langlands.AlgebraicGeometry.Modules.RestrictionPerfectModelsProof

/-!
# Cohomology and base change for line bundles with fibre cohomology in degree zero
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.Cohomology Langlands.AlgebraicGeometry.Picard

namespace Langlands.AlgebraicGeometry.Modules.DerivedSections

attribute [local instance] HasDerivedCategory.standard

/-- The cohomology of a line bundle `L` on `X` over `Spec R` along the geometric fibres is
concentrated in degree zero, of dimension `r`: for every algebraically closed field `k`, every
ring map `R ⟶ k` and every pullback square of `f` along `Spec k ⟶ Spec R`, the pulled-back line
bundle has vanishing cohomology in positive degrees and an `r`-dimensional space of sections. -/
def GeometricFibreCohomologyDegreeZero {R : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec R)
    (L : LineBundle X) (r : ℕ) : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (φ : R ⟶ CommRingCat.of k) (X' : Scheme.{u})
    (p : X' ⟶ X) (f' : X' ⟶ Spec (CommRingCat.of k)) (_ : IsPullback p f' f (Spec.map φ)),
    (∀ i : ℕ, 0 < i →
      IsZero ((relativeCohomology f' i).obj ((Scheme.Modules.pullback p).obj L.obj))) ∧
      Module.finrank k ((relativeCohomology f' 0).obj ((Scheme.Modules.pullback p).obj L.obj)) =
        r

/-- A universal perfect model of the derived sections of a line bundle whose geometric fibres
have cohomology only in degree zero, of dimension `r`, has the same property. -/
lemma geometricFibresDegreeZero_of_universalPerfectModel {R : CommRingCat.{u}} {X : Scheme.{u}}
    {f : X ⟶ Spec R} {L : LineBundle X} {r : ℕ} (h : GeometricFibreCohomologyDegreeZero f L r)
    {K : CochainComplex (ModuleCat.{u} R) ℤ} (hK : ModuleComplex.IsStrictlyPerfect K)
    (a : DerivedCategory.Q.obj K ⟶
      (DerivedPlus.derivedComplex (relativeGlobalSections f) ⋙ DerivedCategory.Plus.ι).obj
        L.obj)
    (hbc : ∀ (T : CommRingCat.{u}) (φ : R ⟶ T) (X' : Scheme.{u}) (p : X' ⟶ X)
      (f' : X' ⟶ Spec T) (hp : IsPullback p f' f (Spec.map φ)),
      IsIso (perfectModelBaseChange hp L hK a)) :
    ModuleComplex.GeometricFibresDegreeZero K r := by
  intro k _ _ φ
  let φ' : R ⟶ CommRingCat.of k := CommRingCat.ofHom φ
  let hp := IsPullback.of_hasPullback f (Spec.map φ')
  have := hbc _ φ' _ _ _ hp
  let e := asIso (perfectModelBaseChange hp L hK a)
  obtain ⟨hz, hr⟩ := h k φ' _ _ _ hp
  refine ⟨fun i hi ↦ ?_, ?_⟩
  · obtain hn | hn := lt_or_gt_of_ne hi
    · refine IsZero.of_iso ?_ ((DerivedCategory.homologyFunctorFactors _ i).app _).symm
      exact IsZero.of_iso (DerivedPlus.isZero_homology_of_neg _ _ hn)
        ((DerivedCategory.homologyFunctor _ i).mapIso e)
    · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn.le
      exact IsZero.of_iso (hz m (by omega))
        (DerivedPlus.homologyIsoOfIsoDerivedComplex _ e m)
  · rw [← hr]
    exact (DerivedPlus.homologyIsoOfIsoDerivedComplex _ e 0).toLinearEquiv.finrank_eq

/-- Cohomology and base change for a line bundle `L` on a smooth proper `f : X ⟶ Spec R` whose
geometric fibres have cohomology only in degree zero, of dimension `r`: the `R`-module of sections
`Γ(X, L)` is finite projective of constant rank `r`, and the base-change map
`T ⊗_R Γ(X, L) ⟶ Γ(X', p^* L)` is an isomorphism for every pullback square of `f` along a map of
affine schemes. -/
theorem sections_of_geometricFibreCohomologyDegreeZero {R : CommRingCat.{u}} {X : Scheme.{u}}
    (f : X ⟶ Spec R) [Smooth f] [IsProper f] (L : LineBundle X) {r : ℕ}
    (h : GeometricFibreCohomologyDegreeZero f L r) :
    Module.Finite R ((relativeGlobalSections f).obj L.obj) ∧
      Module.Projective R ((relativeGlobalSections f).obj L.obj) ∧
      (∀ p : PrimeSpectrum R, Module.rankAtStalk ((relativeGlobalSections f).obj L.obj) p = r) ∧
      ∀ (T : CommRingCat.{u}) (φ : R ⟶ T) (X' : Scheme.{u}) (p : X' ⟶ X) (f' : X' ⟶ Spec T)
        (hp : IsPullback p f' f (Spec.map φ)),
        IsIso (scalarSectionsBaseChangeMap φ f f' p hp.w L.obj) := by
  obtain ⟨K, hK, a, ha, hbc⟩ := universalPerfectModel f L
  have hgeo := geometricFibresDegreeZero_of_universalPerfectModel h hK a hbc
  obtain ⟨hfin, hproj, hrank, hiso⟩ :=
    ModuleComplex.homology_zero_of_geometricFibresDegreeZero hK hgeo
  let E : K.homology 0 ≅ (relativeGlobalSections f).obj L.obj :=
    DerivedPlus.homologyIsoOfIsoDerivedComplex _ (asIso a) 0 ≪≫
      (relativeCohomologyZeroIso f).app L.obj
  refine ⟨Module.Finite.equiv E.toLinearEquiv, Module.Projective.of_equiv E.toLinearEquiv,
    fun p ↦ ?_, fun T φ X' p f' hp ↦ ?_⟩
  · rw [← Module.rankAtStalk_eq_of_equiv E.toLinearEquiv]
    exact hrank p
  · have := hbc T φ X' p f' hp
    rw [isIso_scalarSectionsBaseChangeMap_iff_of_perfectModel hp L hK a ha this]
    exact hiso T φ.hom

end Langlands.AlgebraicGeometry.Modules.DerivedSections
