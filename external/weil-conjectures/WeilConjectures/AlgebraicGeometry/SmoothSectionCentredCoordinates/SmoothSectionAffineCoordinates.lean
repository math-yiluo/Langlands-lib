/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.Regular.RegularSequence
import WeilConjectures.AlgebraicGeometry.DeformationToNormalCone
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Affine
import WeilConjectures.Mathlib.RingTheory.Regular.RegularSequence
import WeilConjectures.Mathlib.RingTheory.MvPolynomial.Ideal
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace
import Mathlib.RingTheory.RingHom.Etale
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-!
# Affine regular coordinates centred on a smooth section

The geometric construction of centred étale charts, with its affine ideal equations.
Source: Stacks Tags 054L, 024T and 00LF.
(blueprint: lem-sc-smooth-section-affine-coordinates).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.unusedSimpArgs false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.SmoothSectionCentredCoordinates

/-- The geometric and regular-equation data of an affine centred section chart.
Source: Stacks Tags 054L, 024T and 00LF.
(blueprint: lem-sc-smooth-section-affine-coordinates). -/
structure AffineChart {V S : Scheme.{u}} (d : ℕ) (g : V ⟶ S)
    (s : S ⟶ V) [IsClosedImmersion s] where
  T : S.affineOpens
  U : V.affineOpens
  mapsInto : U.1 ≤ g ⁻¹ᵁ T.1
  openInBaseChange : IsOpenImmersion
    (pullback.lift U.1.ι (g.resLE T.1 U.1 mapsInto) (g.resLE_comp_ι mapsInto).symm)
  sectionInto : T.1 ≤ s ⁻¹ᵁ U.1
  sectionPreimage : s ⁻¹ᵁ U.1 = T.1
  e : U.1.toScheme ⟶ AffineSpace (ULift.{u} (Fin d)) T.1.toScheme
  over : e ≫ (AffineSpace (ULift.{u} (Fin d)) T.1.toScheme ↘ T.1.toScheme) =
    g.resLE T.1 U.1 mapsInto
  etale : Etale e
  separated : IsSeparated e
  zeroFiber : IsPullback (s.resLE U.1 T.1 sectionInto) (𝟙 T.1.toScheme) e
    (AffineSpace.homOfVector (𝟙 T.1.toScheme) (fun _ ↦ 0))
  x : Fin d → Γ(V, U.1)
  coordinates : ∀ j : Fin d,
    x j = U.1.topIso.hom (e.appTop (AffineSpace.coord T.1.toScheme (ULift.up j)))
  algebraEtale : (MvPolynomial.eval₂Hom (g.appLE T.1 U.1 mapsInto).hom x).Etale
  algebraFlat : (MvPolynomial.eval₂Hom (g.appLE T.1 U.1 mapsInto).hom x).Flat
  sectionIdeal : Ideal.map (MvPolynomial.eval₂Hom (g.appLE T.1 U.1 mapsInto).hom x)
    (Ideal.span (Set.range (MvPolynomial.X : Fin d → MvPolynomial (Fin d) Γ(S, T.1)))) =
      s.ker.ideal U
  quotient : Γ(V, U.1) ⧸ s.ker.ideal U ≃+* Γ(S, T.1)
  augmentation : ∀ b : Γ(V, U.1),
    quotient (Ideal.Quotient.mk (s.ker.ideal U) b) = s.appLE U.1 T.1 sectionInto b
  regular : RingTheory.Sequence.IsRegular Γ(V, U.1) (List.ofFn x)

set_option backward.isDefEq.respectTransparency false in
/-- Every point of the base has a centred affine étale chart whose coordinate ideal
is the section kernel and whose coordinates form a regular sequence.
Source: Stacks Tags 054L, 024T, 01IT, 01I4 and 00LF.
(blueprint: lem-sc-smooth-section-affine-coordinates).

Proof: Apply the proved adopted-source theorem
`Scheme.Hom.exists_etale_coordinates_of_mem_range` at t. It supplies affine
opens with exactly the section preimage and an etale polynomial map generating
the section kernel. Define e by `homOfVector` with these actual coordinates,
transported through the affine opens' top-section isomorphisms. The polynomial
presentation of affine space identifies its section map with the supplied map,
up to ring isomorphisms, proving etaleness. The zero section kernel is generated
by the polynomial variables; after pulling back this is the section kernel.
The section composes with e to zero on the base and every coordinate. The
closed-immersion kernel criterion therefore makes that square Cartesian.
The quotient equivalence is induced by the surjective section augmentation.
Flatness preserves the weak regularity of the polynomial variables; the
quotient is the base chart ring, which is nontrivial because t belongs to it.
This gives full regularity, including the empty list when d = 0. The affine
source makes e separated. The map into the base change is open because its
composite with the open first projection is the open inclusion of U. -/
theorem exists_affineChart {V S : Scheme.{u}} (d : ℕ) (g : V ⟶ S)
    [SmoothOfRelativeDimension d g] (s : S ⟶ V) [IsClosedImmersion s]
    (hs : s ≫ g = 𝟙 S) (t : S) :
    ∃ c : AffineChart d g s, t ∈ c.T.1 := by
  obtain ⟨T, hT, U, hUT, ht, hsU, ψ, hψ, hψC, hψI⟩ :=
    g.exists_etale_coordinates_of_mem_range s d hs t
  let UA : V.affineOpens := ⟨U.1, U.2⟩
  let TA : S.affineOpens := ⟨T, hT⟩
  have hst : T ≤ s ⁻¹ᵁ U.1 := hsU.ge
  let f := g.resLE T U.1 hUT
  let σ := s.appLE U.1 T hst
  have hσ : σ = s.app U.1 ≫ S.presheaf.map (eqToHom hsU.symm).op := rfl
  have hsurj : Function.Surjective σ.hom := by
    rw [hσ, CommRingCat.hom_comp]
    exact (ConcreteCategory.bijective_of_isIso
      (S.presheaf.map (eqToHom hsU.symm).op)).2.comp (s.app_surjective U.1 U.2)
  have hker : RingHom.ker σ.hom = s.ker.ideal UA := by
    rw [hσ, CommRingCat.hom_comp,
      RingHom.ker_comp_of_injective _ (ConcreteCategory.bijective_of_isIso _).1,
      Scheme.Hom.ker_apply]
  let q := (Ideal.quotEquivOfEq hker.symm).trans
    (RingHom.quotientKerEquivOfSurjective hsurj)
  let x : Fin d → Γ(V, U.1) := fun j ↦ ψ (MvPolynomial.X j)
  have heval : MvPolynomial.eval₂Hom (g.appLE T U.1 hUT).hom x = ψ := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simpa only [MvPolynomial.eval₂Hom_C, RingHom.comp_apply] using congrArg (fun k ↦ k a) hψC.symm
    · intro j
      simp [x]
  have hflat : ψ.Flat := (RingHom.Etale.iff_flat_and_formallyUnramified.mp hψ).1
  have hI : Ideal.span (Set.range x) = s.ker.ideal UA := by
    have h := hψI.symm
    rw [Ideal.mvPolynomialOrigin, Ideal.map_span, ← Set.range_comp] at h
    exact h
  have hmem (j : Fin d) : x j ∈ s.ker.ideal UA := hI ▸ Ideal.subset_span ⟨j, rfl⟩
  have hreg : RingTheory.Sequence.IsRegular Γ(V, U.1) (List.ofFn x) := by
    have hw := (MvPolynomial.isWeaklyRegular_ofFn_X_sub_C
      (fun _ : Fin d ↦ (0 : Γ(S, T)))).map_of_flat hflat
    have hw' : RingTheory.Sequence.IsWeaklyRegular Γ(V, U.1) (List.ofFn x) := by
      simpa [List.map_ofFn, x, Function.comp_def] using hw
    refine ⟨hw', ?_⟩
    rw [Ideal.smul_eq_mul, Ideal.mul_top]
    have hlist : Ideal.ofList (List.ofFn x) = s.ker.ideal UA := by
      have hset : {r | r ∈ List.ofFn x} = Set.range x := by
        ext r
        simp
      simpa only [Ideal.ofList, hset] using hI
    rw [hlist, ← hker]
    intro htop
    have hone : σ.hom 1 = 0 := RingHom.mem_ker.mp (htop ▸ trivial)
    have : Nontrivial Γ(S, T) := (S.presheaf.germ T t ht).hom.domain_nontrivial
    simp at hone
  let e := AffineSpace.homOfVector f
    (fun j : ULift.{u} (Fin d) ↦ U.1.topIso.inv (x j.down))
  have hcoords (j : Fin d) :
      x j = U.1.topIso.hom (e.appTop (AffineSpace.coord T.toScheme (ULift.up j))) := by
    change x j = U.1.topIso.hom
      ((AffineSpace.homOfVector f _).appTop (AffineSpace.coord T.toScheme (ULift.up j)))
    rw [AffineSpace.homOfVector_appTop_coord]
    exact (Iso.inv_hom_id_apply U.1.topIso (x j)).symm
  have : IsAffine U.1.toScheme := U.2
  have : IsAffine T.toScheme := hT
  let π := AffineSpace (ULift.{u} (Fin d)) T.toScheme ↘ T.toScheme
  let θ : MvPolynomial (ULift.{u} (Fin d)) Γ(T.toScheme, ⊤) →+*
      Γ(AffineSpace (ULift.{u} (Fin d)) T.toScheme, ⊤) :=
    MvPolynomial.eval₂Hom π.appTop.hom (AffineSpace.coord T.toScheme)
  have : IsIso (CommRingCat.ofHom θ) := by
    have : IsIso ((Scheme.ΓSpecIso _).hom ≫ CommRingCat.ofHom θ) := by
      rw [show (Scheme.ΓSpecIso _).hom ≫ CommRingCat.ofHom θ =
        (AffineSpace.isoOfIsAffine (ULift.{u} (Fin d)) T.toScheme).hom.appTop from
          (AffineSpace.isoOfIsAffine_hom_appTop T.toScheme).symm]
      infer_instance
    exact IsIso.of_isIso_comp_left (Scheme.ΓSpecIso _).hom (CommRingCat.ofHom θ)
  have hθ : Function.Bijective θ := ConcreteCategory.bijective_of_isIso (CommRingCat.ofHom θ)
  let er := (MvPolynomial.renameEquiv Γ(T.toScheme, ⊤) Equiv.ulift).toRingEquiv.trans
    (MvPolynomial.mapEquiv (Fin d) T.topIso.commRingCatIsoToRingEquiv)
  have heθ : e.appTop.hom.comp θ =
      U.1.topIso.inv.hom.comp (ψ.comp er.toRingHom) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply, θ, MvPolynomial.eval₂Hom_C]
      change (e ≫ π).appTop a = _
      change (AffineSpace.homOfVector f _ ≫ π).appTop a = _
      rw [AffineSpace.homOfVector_over]
      have ha := congrArg (fun k ↦ k (T.topIso.hom a)) hψC
      change (g.resLE T U.1 hUT).app ⊤ a = _
      rw [g.resLE_app_top]
      change U.1.topIso.inv (g.appLE T U.1 hUT (T.topIso.hom a)) = _
      have har : er (MvPolynomial.C a) = MvPolynomial.C (T.topIso.hom a) := by
        simp [er, MvPolynomial.renameEquiv_apply]
      change U.1.topIso.inv (g.appLE T U.1 hUT (T.topIso.hom a)) =
        U.1.topIso.inv (ψ (er (MvPolynomial.C a)))
      rw [har]
      exact congrArg U.1.topIso.inv ha.symm
    · intro j
      simp [θ, e, er, x, MvPolynomial.renameEquiv_apply]
  have het : Etale e := by
    rw [HasRingHomProperty.iff_of_isAffine (P := @Etale)]
    apply (RingHom.Etale.respectsIso.cancel_left_isIso
      (CommRingCat.ofHom θ) e.appTop).mp
    change (e.appTop.hom.comp θ).Etale
    rw [heθ]
    exact RingHom.Etale.respectsIso.1 _ U.1.topIso.symm.commRingCatIsoToRingEquiv
      (RingHom.Etale.respectsIso.2 ψ er hψ)
  have hz : IsPullback (s.resLE U.1 T hst) (𝟙 T.toScheme) e
      (AffineSpace.homOfVector (𝟙 T.toScheme) (fun _ ↦ 0)) := by
    let z := AffineSpace.homOfVector (𝟙 T.toScheme)
      (fun _ : ULift.{u} (Fin d) ↦ (0 : Γ(T.toScheme, ⊤)))
    let h := s.resLE U.1 T hst
    have hp : IsPullback h T.ι U.1.ι s :=
      IsOpenImmersion.isPullback _ _ _ _ (s.resLE_comp_ι hst).symm (by simp [hsU])
    have : IsClosedImmersion h := MorphismProperty.of_isPullback hp.flip inferInstance
    have hsf : h ≫ f = 𝟙 T.toScheme := by
      apply (cancel_mono T.ι).mp
      change (s.resLE U.1 T hst ≫ g.resLE T U.1 hUT) ≫ T.ι = (𝟙 T.toScheme) ≫ T.ι
      rw [Category.assoc, g.resLE_comp_ι, ← Category.assoc, s.resLE_comp_ι,
        Category.assoc, hs, Category.comp_id, Category.id_comp]
    have hxzero (j : Fin d) : σ (x j) = 0 := by
      apply RingHom.mem_ker.mp
      rw [hker]
      exact hmem j
    have hh : h.appTop = U.1.topIso.hom ≫ σ ≫ T.topIso.inv := by
      exact s.resLE_app_top hst
    have : IsClosedImmersion z :=
      inferInstanceAs (IsClosedImmersion
        (AffineSpace.zeroSection (ULift.{u} (Fin d)) T.toScheme))
    have hcomm : h ≫ e = (𝟙 T.toScheme) ≫ z := by
      apply AffineSpace.hom_ext
      · change (h ≫ e) ≫ π = (𝟙 T.toScheme ≫ z) ≫ π
        rw [Category.assoc, show e ≫ π = f from AffineSpace.homOfVector_over _ _, hsf,
          Category.id_comp]
        exact (AffineSpace.homOfVector_over _ _).symm
      · intro j
        simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
          e, AffineSpace.homOfVector_appTop_coord, z, Category.id_comp]
        change h.appTop (U.1.topIso.inv (x j.down)) = 0
        rw [hh]
        simpa only [CommRingCat.comp_apply, Iso.inv_hom_id_apply, map_zero]
          using congrArg T.topIso.inv (hxzero j.down)
    have hzero : z.appTop.hom.comp θ = MvPolynomial.eval (fun _ ↦ 0) := by
      apply MvPolynomial.ringHom_ext
      · intro a
        simp only [RingHom.comp_apply, θ, MvPolynomial.eval₂Hom_C]
        change (z ≫ π).appTop a = _
        rw [MvPolynomial.eval_C]
        change (AffineSpace.homOfVector (𝟙 T.toScheme) _ ≫ π).appTop a = a
        rw [AffineSpace.homOfVector_over]
        rw [Scheme.Hom.id_appTop]
        rfl
      · intro j
        simp [θ, z]
    have hzeroideal : RingHom.ker z.appTop.hom =
        (Ideal.span (Set.range
          (MvPolynomial.X : ULift.{u} (Fin d) →
            MvPolynomial (ULift.{u} (Fin d)) Γ(T.toScheme, ⊤)))).map θ := by
      have hk : (RingHom.ker z.appTop.hom).comap θ =
          Ideal.span (Set.range (MvPolynomial.X : ULift.{u} (Fin d) →
            MvPolynomial (ULift.{u} (Fin d)) Γ(T.toScheme, ⊤))) := by
        rw [RingHom.comap_ker, hzero, MvPolynomial.ker_eval]
        simp
      rw [← hk, Ideal.map_comap_of_surjective θ hθ.2]
    apply isPullback_of_isClosedImmersion h z (𝟙 T.toScheme) e hcomm
    rw [Scheme.ker_of_isAffine, Scheme.IdealSheafData.comap_ofIdealTop, Scheme.ker_of_isAffine]
    congr 1
    rw [hzeroideal, Ideal.map_map, Ideal.map_span]
    have hrange : (e.appTop.hom.comp θ) '' Set.range MvPolynomial.X =
        U.1.topIso.inv.hom '' Set.range x := by
      ext a
      simp only [Set.mem_image, Set.mem_range, exists_exists_eq_and,
        RingHom.comp_apply, θ, MvPolynomial.eval₂Hom_X', e,
        AffineSpace.homOfVector_appTop_coord]
      exact ⟨fun ⟨j, hj⟩ ↦ ⟨j.down, hj⟩, fun ⟨j, hj⟩ ↦ ⟨ULift.up j, hj⟩⟩
    rw [hrange, ← Ideal.map_span, hI, ← hker]
    have hmap : (RingHom.ker σ.hom).map U.1.topIso.inv.hom =
        (RingHom.ker σ.hom).comap U.1.topIso.hom.hom := by
      exact Ideal.map_symm U.1.topIso.commRingCatIsoToRingEquiv
    rw [hmap, RingHom.comap_ker]
    rw [hh, CommRingCat.hom_comp, CommRingCat.hom_comp]
    exact (RingHom.ker_comp_of_injective (σ.hom.comp U.1.topIso.hom.hom)
      (ConcreteCategory.bijective_of_isIso T.topIso.inv).1).symm
  refine ⟨{
    T := TA
    U := UA
    mapsInto := hUT
    sectionInto := hst
    sectionPreimage := hsU
    e := e
    over := AffineSpace.homOfVector_over _ _
    etale := het
    separated := inferInstance
    zeroFiber := hz
    x := x
    coordinates := hcoords
    algebraEtale := by rwa [heval]
    algebraFlat := by rwa [heval]
    sectionIdeal := by
      rw [heval]
      exact hψI.symm
    quotient := q
    augmentation := by
      intro b
      change (RingHom.quotientKerEquivOfSurjective hsurj)
        ((Ideal.quotEquivOfEq hker.symm) (Ideal.Quotient.mk _ b)) = σ b
      rw [Ideal.quotEquivOfEq_mk, RingHom.quotientKerEquivOfSurjective_apply_mk]
    regular := hreg
    openInBaseChange := by
      let i := pullback.lift UA.1.ι (g.resLE TA.1 UA.1 hUT)
        (g.resLE_comp_ι hUT).symm
      have : IsOpenImmersion (i ≫ pullback.fst g T.ι) := by
        dsimp only [i]
        rw [pullback.lift_fst]
        infer_instance
      exact IsOpenImmersion.of_comp i (pullback.fst g T.ι) }, ht⟩

end AlgebraicGeometry.SmoothSectionCentredCoordinates
