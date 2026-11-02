import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.RingTheory.Etale.Locus

/-! # The etale locus of a scheme morphism -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

variable {X Y : Scheme.{u}} {f : X ⟶ Y}

/-- Formal etaleness is invariant under isomorphisms of arrows. -/
lemma formallyEtale_respectsIso : RingHom.RespectsIso.{u} @RingHom.FormallyEtale := by
  have h := RingHom.FormallyUnramified.respectsIso.and
    RingHom.FormallySmooth.respectsIso
  have heq : @RingHom.FormallyEtale =
      (fun {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) ↦
        f.FormallyUnramified ∧ f.FormallySmooth) := by
    funext R S _ _ f
    let := f.toAlgebra
    exact propext Algebra.FormallyEtale.iff_formallyUnramified_and_formallySmooth
  rwa [heq]

/-- Stalkwise formal etaleness can be computed on any affine chart. -/
lemma formallyEtale_stalkMap_iff {x : X} (U : Y.Opens)
    (hU : IsAffineOpen U) (V : X.Opens) (hV : IsAffineOpen V)
    (hVU : V ≤ f ⁻¹ᵁ U) (hx : x ∈ V) :
    letI := (f.appLE U V hVU).hom.toAlgebra
    (f.stalkMap x).hom.FormallyEtale ↔
      hV.primeIdealOf ⟨x, hx⟩ ∈ Algebra.etaleLocus Γ(Y, U) Γ(X, V) := by
  let := (f.appLE U V hVU).hom.toAlgebra
  let p := (hU.primeIdealOf ⟨f x, hVU hx⟩).asIdeal
  let q := (hV.primeIdealOf ⟨x, hx⟩).asIdeal
  have : q.LiesOver p :=
    ⟨congr($(IsAffineOpen.comap_primeIdealOf_appLE U hU V hV hVU hx).1).symm⟩
  let := Localization.AtPrime.algebraOfLiesOver p q
  trans Algebra.FormallyEtale (Localization.AtPrime p) (Localization.AtPrime q)
  · rw [← RingHom.formallyEtale_algebraMap]
    exact formallyEtale_respectsIso.arrow_mk_iso_iff
      (IsAffineOpen.arrowStalkMapIso f U hU V hV hVU hx)
  · exact Algebra.FormallyEtale.iff_restrictScalars.symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A formally etale stalk of a locally finitely presented morphism has
an affine neighborhood on which the ring map is etale. -/
lemma exists_etale_of_formallyEtale_stalk
    (f : X ⟶ Y) [LocallyOfFinitePresentation f]
    (x : X) (H : (f.stalkMap x).hom.FormallyEtale) :
    ∃ (U : Y.Opens) (_ : IsAffineOpen U) (V : X.Opens) (_ : IsAffineOpen V)
      (hVU : V ≤ f ⁻¹ᵁ U), x ∈ V ∧ (f.appLE U V hVU).hom.Etale := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxU (U.2.preimage f.continuous)
  have := f.finitePresentation_appLE hU hV hVU
  algebraize [(f.appLE U V hVU).hom]
  have : Algebra.IsEtaleAt _ _ := (formallyEtale_stalkMap_iff U hU V hV hVU hxV).mp H
  obtain ⟨r, hrx, hr⟩ := Algebra.exists_etale_of_isEtaleAt (R := Γ(Y, U))
    (hV.primeIdealOf ⟨x, hxV⟩).asIdeal
  refine ⟨_, hU, _, hV.basicOpen r, (X.basicOpen_le r).trans hVU, ?_, ?_⟩
  · rwa [← PrimeSpectrum.mem_basicOpen, IsAffineOpen.primeIdealOf,
      ← hV.fromSpec_preimage_basicOpen, Scheme.Hom.mem_preimage, ← Scheme.Hom.comp_apply,
      IsAffineOpen.isoSpec_hom, IsAffineOpen.toSpecΓ_fromSpec] at hrx
  · have := hV.isLocalization_basicOpen r
    rw [← RingHom.etale_algebraMap] at hr
    convert!
      RingHom.Etale.propertyIsLocal.respectsIso.1 _
        (IsLocalization.algEquiv (.powers r) _ Γ(X, X.basicOpen r)).toRingEquiv hr
    ext
    dsimp
    simp only [IsScalarTower.algebraMap_apply Γ(Y, U) Γ(X, V) (Localization _),
      IsLocalization.map_eq]
    simp only [RingHom.algebraMap_toAlgebra, RingHomCompTriple.comp_apply, ← ConcreteCategory.comp_apply,
      Scheme.Hom.appLE_map]

/-- The formally etale stalks form an open subset for a locally finitely
presented morphism. -/
lemma isOpen_schemeEtaleLocus [LocallyOfFinitePresentation f] :
    IsOpen {x | (f.stalkMap x).hom.FormallyEtale} := by
  refine isOpen_iff_forall_mem_open.mpr fun x hx ↦ ?_
  obtain ⟨U, hU, V, hV, hVU, hxV, H⟩ := exists_etale_of_formallyEtale_stalk f x hx
  algebraize [(f.appLE U V hVU).hom]
  exact ⟨V, fun y hy ↦ (formallyEtale_stalkMap_iff U hU V hV hVU hy).mpr
    (inferInstanceAs (Algebra.IsEtaleAt _ _)), V.2, hxV⟩

/-- The etale locus of a locally finitely presented scheme morphism. -/
def schemeEtaleLocus (f : X ⟶ Y) [LocallyOfFinitePresentation f] : X.Opens :=
  ⟨{x | (f.stalkMap x).hom.FormallyEtale}, isOpen_schemeEtaleLocus⟩

lemma mem_schemeEtaleLocus [LocallyOfFinitePresentation f] {x : X} :
    x ∈ schemeEtaleLocus f ↔ (f.stalkMap x).hom.FormallyEtale := .rfl

lemma schemeEtaleLocus_eq_top (f : X ⟶ Y) [Etale f] :
    schemeEtaleLocus f = ⊤ := by
  rw [← top_le_iff]
  rintro x -
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxU (U.2.preimage f.continuous)
  have := f.etale_appLE hU hV hVU
  algebraize [(f.appLE U V hVU).hom]
  rw [mem_schemeEtaleLocus, formallyEtale_stalkMap_iff U hU V hV hVU hxV]
  exact inferInstanceAs (Algebra.IsEtaleAt _ _)

set_option backward.isDefEq.respectTransparency.types false in
lemma schemeEtaleLocus_eq_top_iff [LocallyOfFinitePresentation f] :
    schemeEtaleLocus f = ⊤ ↔ Etale f := by
  refine ⟨fun H ↦ ?_, fun _ ↦ schemeEtaleLocus_eq_top f⟩
  let : MorphismProperty.RespectsRight (@Etale) (@IsOpenImmersion) :=
    ⟨fun i hi g hg ↦ by
      let := hi
      let := hg
      infer_instance⟩
  refine (IsZariskiLocalAtSource.iff_exists_resLE (P := @Etale)).mpr fun x ↦ ?_
  obtain ⟨U, hU, V, hV, hVU, hxV, H⟩ :=
    exists_etale_of_formallyEtale_stalk f _ (H.ge (Set.mem_univ x))
  refine ⟨U, V, hxV, hVU, ?_⟩
  have : IsAffine _ := hU
  have : IsAffine _ := hV
  rw [HasRingHomProperty.iff_of_isAffine (P := @Etale)]
  exact (RingHom.Etale.propertyIsLocal.respectsIso.arrow_mk_iso_iff
    (arrowResLEAppIso f U V hVU)).mpr H

lemma preimage_schemeEtaleLocus_eq {U : Scheme.{u}}
    (f : U ⟶ X) (g : X ⟶ Y) [IsOpenImmersion f] [LocallyOfFinitePresentation g] :
    f ⁻¹ᵁ schemeEtaleLocus g = schemeEtaleLocus (f ≫ g) := by
  ext x
  refine (formallyEtale_respectsIso.cancel_right_isIso _ (f.stalkMap x)).symm.trans ?_
  rw [← CommRingCat.hom_comp, ← Scheme.Hom.stalkMap_comp]
  rfl

/-- The restriction of a locally finitely presented morphism to its etale
locus is etale. -/
lemma etale_schemeEtaleLocus (f : X ⟶ Y) [LocallyOfFinitePresentation f] :
    Etale ((schemeEtaleLocus f).ι ≫ f) := by
  apply schemeEtaleLocus_eq_top_iff.mp
  rw [← preimage_schemeEtaleLocus_eq]
  ext x
  simp

/-- A formally etale stalk has an open neighborhood etale over the target. -/
lemma exists_open_etale_of_formallyEtale_stalk
    (f : X ⟶ Y) [LocallyOfFinitePresentation f] (x : X)
    (hx : (f.stalkMap x).hom.FormallyEtale) :
    ∃ V : X.Opens, x ∈ V ∧ Etale (V.ι ≫ f) :=
  ⟨schemeEtaleLocus f, hx, etale_schemeEtaleLocus f⟩

end Langlands.AlgebraicGeometry
