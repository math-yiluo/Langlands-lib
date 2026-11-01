import Langlands.AlgebraicGeometry.Picard.AffineGenerationLocusIntersectionProof
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness

/-! # Finite tests for monomorphisms from line bundles -/

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Langlands.SchemeModule

variable {X : Scheme.{u}}

lemma stalk_injective_of_mono {M N : X.Modules} (f : M ⟶ N) [Mono f] (x : X) :
    Function.Injective
      ((TopCat.Presheaf.stalkFunctor Ab.{u} x).map f.mapPresheaf) := by
  have : Mono f.mapPresheaf := (Scheme.Modules.toPresheaf X).map_mono f
  apply TopCat.Presheaf.stalkFunctor_map_injective_of_app_injective
  intro U
  exact ConcreteCategory.injective_of_mono_of_preservesPullback _

lemma mono_of_stalk_injective {M N : X.Modules} (f : M ⟶ N)
    (hf : ∀ x : X, Function.Injective
      ((TopCat.Presheaf.stalkFunctor Ab.{u} x).map f.mapPresheaf)) : Mono f := by
  have happ : ∀ U : X.Opens, Function.Injective (f.app U) := fun U =>
    TopCat.Presheaf.app_injective_of_stalkFunctor_map_injective
      (F := ⟨M.presheaf, M.isSheaf⟩) f.mapPresheaf U (fun x _ => hf x)
  refine Preadditive.mono_of_cancel_zero _ fun {K} g hg => ?_
  apply Scheme.Modules.hom_ext
  intro U
  ext a
  exact happ U (show (g ≫ f).app U a = ((0 : K ⟶ M) ≫ f).app U a by
    rw [hg, zero_comp])

lemma stalk_injective_of_mono_restrict {M N : X.Modules} (f : M ⟶ N)
    (U : X.Opens) [Mono ((Scheme.Modules.restrictFunctor U.ι).map f)] (y : U.toScheme) :
    Function.Injective
      ((TopCat.Presheaf.stalkFunctor Ab.{u} (U.ι y)).map f.mapPresheaf) := by
  let G := Scheme.Modules.restrictFunctor U.ι ⋙ Scheme.Modules.toPresheaf U.toScheme ⋙
    TopCat.Presheaf.stalkFunctor Ab.{u} y
  let F := Scheme.Modules.toPresheaf X ⋙
    TopCat.Presheaf.stalkFunctor Ab.{u} (U.ι y)
  let e : G ≅ F := Scheme.Modules.restrictStalkNatIso U.ι y
  have : Mono (G.map f) :=
    ConcreteCategory.mono_of_injective _
      (stalk_injective_of_mono ((Scheme.Modules.restrictFunctor U.ι).map f) y)
  have heq : F.map f = e.inv.app M ≫ G.map f ≫ e.hom.app N := by
    rw [e.hom.naturality, ← Category.assoc, e.inv_hom_id_app]
    simp
  have : Mono (F.map f) := by
    rw [heq]
    infer_instance
  exact ConcreteCategory.injective_of_mono_of_preservesPullback (F.map f)

lemma unitEnd_mono_of_regular [IsAffine X]
    (f : structureModule X ⟶ structureModule X)
    (hf : unitEndCoefficient f ⊤ ∈ nonZeroDivisors Γ(X, ⊤)) : Mono f := by
  apply mono_of_stalk_injective
  apply TopCat.Presheaf.stalkFunctor_map_injective_of_isBasis (isBasis_basicOpen X)
  rintro U ⟨r, rfl⟩
  have hr : X.presheaf.map (homOfLE le_top : X.basicOpen r ⟶ ⊤).op
      (unitEndCoefficient f ⊤) ∈ nonZeroDivisors Γ(X, X.basicOpen r) :=
    IsLocalization.nonZeroDivisors_le_comap (Submonoid.powers r) _ hf
  change Function.Injective (f.app (X.basicOpen r))
  intro a b hab
  rw [unitEndCoefficient_app, unitEndCoefficient_app, unitEndCoefficient_res] at hab
  exact (isRegular_iff_mem_nonZeroDivisors.mpr hr).right hab

lemma exists_finite_unitEnd_mono_detector [IsAffine X] [IsLocallyNoetherian X] :
    ∃ E : Set X, E.Finite ∧
      ∀ f : structureModule X ⟶ structureModule X,
        (∀ x ∈ E, IsIso ((TopCat.Presheaf.stalkFunctor Ab.{u} x).map f.mapPresheaf)) →
        Mono f := by
  classical
  let A := Γ(X, ⊤)
  let : IsNoetherianRing A :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top X⟩
  let := (associatedPrimes.finite A A).fintype
  let point : associatedPrimes A A → X :=
    fun p => X.isoSpec.inv ⟨p.1, p.2.isPrime⟩
  refine ⟨Set.range point, Set.finite_range point, ?_⟩
  intro f hf
  apply unitEnd_mono_of_regular f
  by_contra h
  have hmem : unitEndCoefficient f ⊤ ∈
      ⋃ p ∈ associatedPrimes A A, (p : Set A) := by
    rw [biUnion_associatedPrimes_eq_compl_nonZeroDivisors]
    exact h
  obtain ⟨p, hp, hfp⟩ := Set.mem_iUnion₂.mp hmem
  have hpoint := (unitEnd_stalkIso_iff_mem_basicOpen f (point ⟨p, hp⟩)).mp
    (hf _ ⟨⟨p, hp⟩, rfl⟩)
  rw [← X.map_PrimeSpectrum_basicOpen_of_affine] at hpoint
  have heq : X.isoSpec.hom (point ⟨p, hp⟩) = ⟨p, hp.isPrime⟩ := by
    change X.isoSpec.hom (X.isoSpec.inv _) = _
    rw [← Scheme.Hom.comp_apply, X.isoSpec.inv_hom_id]
    rfl
  change X.isoSpec.hom (point ⟨p, hp⟩) ∈ PrimeSpectrum.basicOpen _ at hpoint
  rw [heq] at hpoint
  exact hpoint hfp

end Langlands.SchemeModule

namespace Langlands.AlgebraicGeometry.Picard

variable {X : Scheme.{u}}

def restrictTrivializationOfLE {M : X.Modules} {U V : X.Opens} (hVU : V ≤ U)
    (e : M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) :
    M.restrict V.ι ≅ SheafOfModules.unit V.toScheme.ringCatSheaf :=
  ((Scheme.Modules.restrictFunctorCongr (X.homOfLE_ι hVU).symm).app M) ≪≫
    ((Scheme.Modules.restrictFunctorComp (X.homOfLE hVU) U.ι).app M) ≪≫
      (Scheme.Modules.restrictFunctor (X.homOfLE hVU)).mapIso e ≪≫
        Scheme.Modules.restrictUnitIso (X.homOfLE hVU)

lemma IsLocallyFreeRankOne.exists_affine_trivialization {M : X.Modules}
    (hM : IsLocallyFreeRankOne M) (x : X) :
    ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧
      Nonempty (M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) := by
  obtain ⟨V, hxV, ⟨e⟩⟩ := hM x
  obtain ⟨U, hU, hxU, hUV⟩ :=
    (Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens) hxV
  exact ⟨U, hU, hxU, ⟨restrictTrivializationOfLE hUV e⟩⟩

/-- Stalk isomorphisms on `E` suffice for a morphism into the structure module
to be a monomorphism. -/
def IsMonoDetector (M : X.Modules) (E : Set X) : Prop :=
  ∀ f : M ⟶ SheafOfModules.unit X.ringCatSheaf,
    (∀ x ∈ E, IsIso ((TopCat.Presheaf.stalkFunctor Ab.{u} x).map f.mapPresheaf)) →
    Mono f

lemma IsLocallyFreeRankOne.exists_finite_mono_detector
    [CompactSpace X] [IsLocallyNoetherian X] {M : X.Modules}
    (hM : IsLocallyFreeRankOne M) :
    ∃ E : Set X, E.Finite ∧ IsMonoDetector M E := by
  classical
  choose U hU hx he using hM.exists_affine_trivialization
  let e (x : X) := (he x).some
  have (x : X) : IsAffine (U x).toScheme := hU x
  choose E hE hdet using fun x : X =>
    Langlands.SchemeModule.exists_finite_unitEnd_mono_detector (X := (U x).toScheme)
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun x : X => (U x : Set X))
    (fun x => (U x).isOpen) (fun x _ => Set.mem_iUnion.mpr ⟨x, hx x⟩)
  refine ⟨⋃ x ∈ (s : Set X), (U x).ι '' E x,
    s.finite_toSet.biUnion (fun x _ => (hE x).image _), ?_⟩
  intro f hf
  have hlocal (x : X) (hxs : x ∈ s) :
      Mono ((Scheme.Modules.restrictFunctor (U x).ι).map f) := by
    let fU := (e x).inv ≫ (Scheme.Modules.restrictFunctor (U x).ι).map f ≫
      (Scheme.Modules.restrictUnitIso (U x).ι).hom
    have : Mono fU := hdet x fU (by
      intro y hy
      have : IsIso ((TopCat.Presheaf.stalkFunctor Ab.{u} y).map
          (((Scheme.Modules.restrictFunctor (U x).ι).map f).mapPresheaf)) :=
        (Langlands.SchemeModule.isIso_stalk_restrict_iff f (U x) y).mpr
          (hf _ (Set.mem_iUnion₂.mpr ⟨x, hxs, ⟨y, hy, rfl⟩⟩))
      have : IsIso ((Scheme.Modules.toPresheaf (U x).toScheme ⋙
          TopCat.Presheaf.stalkFunctor Ab.{u} y).map
            ((Scheme.Modules.restrictFunctor (U x).ι).map f)) := this
      change IsIso ((Scheme.Modules.toPresheaf (U x).toScheme ⋙
        TopCat.Presheaf.stalkFunctor Ab.{u} y).map fU)
      dsimp only [fU]
      rw [Functor.map_comp, Functor.map_comp]
      infer_instance)
    have heq : (Scheme.Modules.restrictFunctor (U x).ι).map f =
        (e x).hom ≫ fU ≫ (Scheme.Modules.restrictUnitIso (U x).ι).inv := by
      simp [fU]
    rw [heq]
    infer_instance
  apply Langlands.SchemeModule.mono_of_stalk_injective
  intro z
  obtain ⟨x, hxs, hz⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ z))
  have := hlocal x hxs
  exact Langlands.SchemeModule.stalk_injective_of_mono_restrict f (U x) ⟨z, hz⟩

end Langlands.AlgebraicGeometry.Picard
