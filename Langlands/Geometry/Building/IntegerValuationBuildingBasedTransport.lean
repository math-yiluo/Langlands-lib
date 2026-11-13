import Langlands.Geometry.Building.IntegerValuationBuildingIsoTransport
import Langlands.Geometry.Building.FullValidity.DatumTransport.Base

/-! # Integer-valued building data under based group isomorphisms

For `f : G ≅ H`, `σ : S ≅ S'` and `j : S' → H` with `B.i ≫ f = σ ≫ j`, the building data
`B : IntegerValuationBuildingData v G` give building data of `H` with torus exactly `j`: the
apartment class is the image of the source class, the centralizer is transported along both
isomorphisms, and V 6 is transported here. The reduced buildings are compared by the quotient
map of `(g, x) ↦ (f(g), x ∘ (σ⁻¹, f⁻¹))`, which carries fixers, one-group stabilizers and
special points to the same objects of the target.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace

namespace Langlands.Geometry.Building

open DatumTransport

/-! ### V 6 under based isomorphisms -/

namespace IntegerValuation

section Based

variable {k : Type u} [Field k] (v : Valuation k (WithZero (Multiplicative ℤ)))
  {S S' : CommGroupScheme (Spec (CommRingCat.of k))}
  {G H : GroupScheme (Spec (CommRingCat.of k))}
  {i : S.toGrp ⟶ G} {j : S'.toGrp ⟶ H}
  (C : CentralizerDatum i) (E : CentralizerDatum j)
  (e : S ≅ S') (f : G ≅ H)
  (h : i ≫ f.hom = CommGroupScheme.groupHom e.hom ≫ j)

/-- The comparison of the centralizer representatives through `(e, f)`. -/
private def basedComparison : C.Z ≅ E.Z :=
  (C.isRepresentedBy.torusCentralizer_of_iso_square (torusGrpIso e) f h).isoOfIsRepresentedBy
    E.isRepresentedBy

private theorem basedComparison_hom_comp :
    (basedComparison C E e f h).hom ≫ E.j = C.j ≫ f.hom :=
  SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy_hom_comp _ E.isRepresentedBy

private theorem basedComparison_torus :
    C.s ≫ (basedComparison C E e f h).hom = CommGroupScheme.groupHom e.hom ≫ E.s := by
  apply E.isRepresentedBy.hom_ext
  rw [Category.assoc, basedComparison_hom_comp, ← Category.assoc, C.comp_eq,
    Category.assoc, E.comp_eq, h]

private theorem basedComparison_characterRestriction (chi : rationalCharacters E.Z) :
    characterLattice.congr e
      (BruhatTits.Cartan.characterRestriction C.s
        (characterRestrict (basedComparison C E e f h).hom chi)) =
      BruhatTits.Cartan.characterRestriction E.s chi := by
  change CommGroupScheme.groupHom e.inv ≫
      (C.s ≫ (basedComparison C E e f h).hom) ≫ chi.toMul = E.s ≫ chi.toMul
  rw [basedComparison_torus]
  change CommGroupScheme.groupHom (e.inv ≫ e.hom) ≫ E.s ≫ chi.toMul = _
  rw [Iso.inv_hom_id]
  rfl

private theorem basedComparison_translation (z : rationalPoints C.Z) :
    cocharacterRealCongr e (centralizerTranslation v C.s C.bijective z).toAdd =
      (centralizerTranslation v E.s E.bijective
        (rationalPoints.map (basedComparison C E e f h).hom z)).toAdd := by
  apply E.bijective.injective
  apply AddMonoidHom.ext
  intro chi
  change eval S' (BruhatTits.Cartan.characterRestriction E.s chi)
      (cocharacterRealCongr e (centralizerTranslation v C.s C.bijective z).toAdd) =
    eval S' (BruhatTits.Cartan.characterRestriction E.s chi)
      (centralizerTranslation v E.s E.bijective
        (rationalPoints.map (basedComparison C E e f h).hom z)).toAdd
  conv_lhs =>
    rw [← basedComparison_characterRestriction C E e f h chi, eval_cocharacterRealCongr]
  rw [eval_centralizerTranslation, eval_centralizerTranslation]
  congr 2

private theorem basedComparison_map_comp (z : rationalPoints C.Z) :
    rationalPoints.map E.j (rationalPoints.map (basedComparison C E e f h).hom z) =
      rationalPoints.map f.hom (rationalPoints.map C.j z) := by
  simpa only [rationalPoints.map_apply, Grp.comp_hom_hom, Category.assoc] using
    congrArg (fun a : C.Z ⟶ H => z ≫ a.hom.hom) (basedComparison_hom_comp C E e f h)

variable [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]

include h in
/-- Full integer-valued V 6 is preserved through a simultaneous isomorphism of the torus and
the ambient group, for any target centralizer representative. -/
theorem IsCentralizerCompatible.transport_basedIso {phi : RootFunctionFamily S G}
    (hphi : IsCentralizerCompatible v i C.j C.s C.bijective phi) :
    IsCentralizerCompatible v j E.j E.s E.bijective
      (RootFunctionFamily.transportEquiv e f phi) := by
  intro a ha z w hw
  obtain ⟨a, rfl⟩ := (characterLattice.congr e).surjective a
  have ha' := (roots_mem_of_transport_iff e f h a).mp ha
  obtain ⟨z, rfl⟩ := (isoPointsEquiv (basedComparison C E e f h)
    (Over.mk (𝟙 _))).surjective z
  obtain ⟨w, rfl⟩ := (isoPointsEquiv f (Over.mk (𝟙 _))).surjective w
  have hw' : w ∈ rootGroupPoints i a := (rootGroupPoints_transport_iff e f h a w).mp hw
  change RootFunctionFamily.transportEquiv e f phi (characterLattice.congr e a)
      ((rationalPoints.map E.j
        (rationalPoints.map (basedComparison C E e f h).hom z))⁻¹ *
        rationalPoints.map f.hom w *
        rationalPoints.map E.j (rationalPoints.map (basedComparison C E e f h).hom z)) =
    RootFunctionFamily.transportEquiv e f phi (characterLattice.congr e a)
      (rationalPoints.map f.hom w) +
    ((eval S' (characterLattice.congr e a)
      (centralizerTranslation v E.s E.bijective
        (rationalPoints.map (basedComparison C E e f h).hom z)).toAdd : ℝ) : WithTop ℝ)
  rw [basedComparison_map_comp C E e f h z, ← map_inv, ← map_mul, ← map_mul,
    RootFunctionFamily.transportEquiv_apply_map, RootFunctionFamily.transportEquiv_apply_map,
    ← basedComparison_translation v C E e f h z, eval_cocharacterRealCongr]
  exact hphi a ha' z w hw'

variable [Mono i.hom.hom.left] [Mono j.hom.hom.left]

include h in
/-- The transported apartment class satisfies integer-valued V 6 with any target centralizer. -/
theorem IsOmegaCompatible.transport_basedIso {D : KPApartmentData i (order v)}
    (hD : IsOmegaCompatible v D C) : IsOmegaCompatible v (D.transport e f h) E := by
  rintro _ ⟨phi, hphi, rfl⟩
  exact (hD phi hphi).transport_basedIso v C E e f h

end Based

end IntegerValuation

/-! ### The transported building data -/

namespace IntegerValuationBuildingData

variable {k : Type u} [Field k] {v : Valuation k (WithZero (Multiplicative ℤ))}
  {G H : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
  (B : IntegerValuationBuildingData v G) {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {j : S.toGrp ⟶ H} (σ : B.S ≅ S) (f : G ≅ H)
  (h : B.i ≫ f.hom = CommGroupScheme.groupHom σ.hom ≫ j)

omit [IsAffineHom H.X.hom] in
include h in
/-- The prescribed target torus is a maximal split torus of `H`. -/
theorem isMaximalSplitTorus_of_basedIso : IsMaximalSplitTorus j := by
  rw [target_eq σ f h]
  exact isMaximalSplitTorus_torusIso_comp (B.isMaximalSplitTorus.comp_iso f) σ.symm

/-- The building data of `H` with torus `j`: the image of the apartment class of `B`, the
transported centralizer and the transported V 6. -/
def basedTransport : IntegerValuationBuildingData v H where
  isConnectedReductive := B.isConnectedReductive.of_iso f.symm
  S := S
  i := j
  isMaximalSplitTorus := B.isMaximalSplitTorus_of_basedIso σ f h
  apartment :=
    have := mono_of_isMaximalSplitTorus (B.isMaximalSplitTorus_of_basedIso σ f h)
    B.apartment.transport σ f h
  centralizer := B.centralizer.basedTransport σ f h
  isOmegaCompatible :=
    have := mono_of_isMaximalSplitTorus (B.isMaximalSplitTorus_of_basedIso σ f h)
    B.isOmegaCompatible.transport_basedIso v B.centralizer _ σ f h

@[simp] theorem basedTransport_S : (B.basedTransport σ f h).S = S := rfl

@[simp] theorem basedTransport_i : (B.basedTransport σ f h).i = j := rfl

/-- The affine comparison `A(S) ≃ A(S')` of the apartments. -/
def basedApartmentEquiv : B.Apartment ≃ᵃ[ℝ] (B.basedTransport σ f h).Apartment :=
  have := mono_of_isMaximalSplitTorus (B.isMaximalSplitTorus_of_basedIso σ f h)
  B.apartment.apartmentTransportAffineEquiv σ f h

/-- The comparison `B(G) ≃ B(H)` of the reduced buildings. -/
def basedBuildingEquiv : B.ReducedBuilding ≃ (B.basedTransport σ f h).ReducedBuilding :=
  have := mono_of_isMaximalSplitTorus (B.isMaximalSplitTorus_of_basedIso σ f h)
  B.apartment.reducedBuildingTransportEquiv σ f h

theorem basedBuildingEquiv_smul (g : rationalPoints G) (y : B.ReducedBuilding) :
    B.basedBuildingEquiv σ f h (g • y) =
      rationalPoints.map f.hom g • B.basedBuildingEquiv σ f h y :=
  have := mono_of_isMaximalSplitTorus (B.isMaximalSplitTorus_of_basedIso σ f h)
  B.apartment.reducedBuildingTransportEquiv_smul σ f h g y

theorem basedBuildingEquiv_apartmentMap (x : B.Apartment) :
    B.basedBuildingEquiv σ f h (B.apartmentMap x) =
      (B.basedTransport σ f h).apartmentMap (B.basedApartmentEquiv σ f h x) :=
  have := mono_of_isMaximalSplitTorus (B.isMaximalSplitTorus_of_basedIso σ f h)
  B.apartment.reducedBuildingTransportEquiv_apartmentMap σ f h x

/-- Full point fixers are carried to full point fixers. -/
theorem map_fixer_basedTransport (y : B.ReducedBuilding) :
    (B.fixer y).map (rationalPoints.map f.hom) =
      (B.basedTransport σ f h).fixer (B.basedBuildingEquiv σ f h y) :=
  have := mono_of_isMaximalSplitTorus (B.isMaximalSplitTorus_of_basedIso σ f h)
  B.apartment.map_reducedFixer_transport σ f h y

/-- One-group stabilizers are carried to one-group stabilizers. -/
theorem map_oneStabilizer_basedTransport (y : B.ReducedBuilding) :
    (B.oneStabilizer y).map (rationalPoints.map f.hom) =
      (B.basedTransport σ f h).oneStabilizer (B.basedBuildingEquiv σ f h y) := by
  ext z
  obtain ⟨g, rfl⟩ := (pointsEquiv f).surjective z
  rw [pointsEquiv_apply, mem_map_iff, B.mem_oneStabilizer,
    (B.basedTransport σ f h).mem_oneStabilizer, mem_characterValuationKernel_mapIso_iff,
    ← basedBuildingEquiv_smul]
  exact and_congr_right fun _ => (B.basedBuildingEquiv σ f h).injective.eq_iff.symm

/-- The affine roots of the target are the transported affine roots. -/
theorem transportedRoots_basedApartmentEquiv :
    AffineRootSystem.transportedRoots (B.basedApartmentEquiv σ f h) B.affineRoots =
      (B.basedTransport σ f h).affineRoots := by
  have := mono_of_isMaximalSplitTorus (B.isMaximalSplitTorus_of_basedIso σ f h)
  have hfunc (ψ : B.Apartment →ᵃ[ℝ] ℝ) :
      AffineRootSystem.affineFunctionalTransport (B.basedApartmentEquiv σ f h) ψ =
        B.apartment.affineFunctionalTransportEquiv σ f h ψ := by
    ext x
    rfl
  ext ψ'
  obtain ⟨ψ, rfl⟩ :=
    (AffineRootSystem.affineFunctionalTransport (B.basedApartmentEquiv σ f h)).surjective ψ'
  constructor
  · rintro ⟨ζ, hζ, hζψ⟩
    have hζeq :=
      (AffineRootSystem.affineFunctionalTransport (B.basedApartmentEquiv σ f h)).injective hζψ
    subst ζ
    rw [hfunc]
    exact (B.apartment.mem_affineRoots_transport_iff σ f h ψ).mpr hζ
  · intro hψ
    rw [hfunc] at hψ
    exact ⟨ψ, (B.apartment.mem_affineRoots_transport_iff σ f h ψ).mp hψ, rfl⟩

/-- Special points of the reduced building are preserved and reflected. -/
theorem isSpecialPoint_basedTransport_iff (y : B.ReducedBuilding) :
    (B.basedTransport σ f h).IsSpecialPoint (B.basedBuildingEquiv σ f h y) ↔
      B.IsSpecialPoint y := by
  have hspecial (a : B.Apartment) :
      AffineRootSystem.IsSpecialPoint (B.basedTransport σ f h).affineRoots
          (B.basedApartmentEquiv σ f h a) ↔
        AffineRootSystem.IsSpecialPoint B.affineRoots a := by
    rw [← B.transportedRoots_basedApartmentEquiv σ f h]
    exact AffineRootSystem.isSpecialPoint_transportedRoots_iff _ _ _
  constructor
  · rintro ⟨g, a, heq, ha⟩
    obtain ⟨g, rfl⟩ := (pointsEquiv f).surjective g
    obtain ⟨a, rfl⟩ := (B.basedApartmentEquiv σ f h).surjective a
    refine ⟨g, a, (B.basedBuildingEquiv σ f h).injective ?_, (hspecial a).mp ha⟩
    rw [B.basedBuildingEquiv_smul, B.basedBuildingEquiv_apartmentMap]
    exact heq
  · rintro ⟨g, a, rfl, ha⟩
    exact ⟨rationalPoints.map f.hom g, B.basedApartmentEquiv σ f h a,
      by rw [B.basedBuildingEquiv_smul, B.basedBuildingEquiv_apartmentMap],
      (hspecial a).mpr ha⟩

end IntegerValuationBuildingData

end Langlands.Geometry.Building
