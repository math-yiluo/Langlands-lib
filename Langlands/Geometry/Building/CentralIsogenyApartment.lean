import Langlands.Geometry.Building.CentralIsogenyFullValuation

/-! # Apartment pullback through an actual central isogeny -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace

namespace Langlands.Geometry.Building

variable {k : Type u} [Field k]
  {S T : CommGroupScheme (Spec (CommRingCat.of k))}
  {C G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom C.X.hom] [IsAffineHom G.X.hom]
  [LocallyOfFiniteType C.X.hom] [LocallyOfFiniteType G.X.hom]
  {i : S.toGrp ⟶ C} {j : T.toGrp ⟶ G}
  (q : C ⟶ G) (hq : IsCentralIsogeny q)
  (hS : IsSplitTorus S.toGrp) (hT : IsSplitTorus T.toGrp)
  (t : S ⟶ T) (h : i ≫ q = CommGroupScheme.groupHom t ≫ j)
  (ht : IsIsogeny (CommGroupScheme.groupHom t))

open RootFunctionFamily

omit [IsAffineHom C.X.hom] [LocallyOfFiniteType C.X.hom] in
private theorem torusPoint_mem_centralizer (s : rationalPoints S.toGrp) :
    rationalPoints.map i s ∈ centralizerPoints i := by
  rw [← torusCentralizer_carrier_base]
  intro U b x
  change ((b ≫ s) ≫ i.hom.hom) * (x ≫ i.hom.hom) =
    (x ≫ i.hom.hom) * ((b ≫ s) ≫ i.hom.hom)
  rw [← MonObj.mul_comp, ← MonObj.mul_comp, mul_comm]

omit [IsAffineHom C.X.hom] [LocallyOfFiniteType C.X.hom] in
private theorem torus_conj_mem_rootGroupPoints (a : characterLattice S)
    (s : rationalPoints S.toGrp) (g : rationalPoints C)
    (hg : g ∈ rootGroupPoints i a) :
    (rationalPoints.map i s)⁻¹ * g * rationalPoints.map i s ∈ rootGroupPoints i a := by
  have hs := (centralizerPoints i).inv_mem (torusPoint_mem_centralizer s)
  have hc := RelativeRoot.comp_mem_subgroup i a
    (C.innerIso ((rationalPoints.map i s)⁻¹)).hom hg
  rw [(mem_centralizerPoints i).mp hs] at hc
  simpa only [rootGroupPoints, comp_innerIso_hom, GroupScheme.constantPoint_self,
    inv_inv] using hc

/-- The split-torus part of V6 pulls back with the same scalar valuation. -/
theorem IsSplitTorusCompatible.centralIsogenyPullback
    {ω : kˣ → ℝ} {φ : RootFunctionFamily T G}
    (hφ : IsSplitTorusCompatible j ω φ) :
    IsSplitTorusCompatible i ω
      (RootFunctionFamily.centralIsogenyPullback q hq hS hT t h ht φ) := by
  intro a ha s g hg
  obtain ⟨a', he⟩ :=
    (centralIsogenyRootPullbackEquiv q hq hS hT t h ht).surjective ⟨a, ha⟩
  have he' : t ≫ a'.val = a := congrArg Subtype.val he
  subst a
  have hcg := torus_conj_mem_rootGroupPoints (t ≫ a'.val) s g hg
  have hs : rationalPoints.map q (rationalPoints.map i s) =
      rationalPoints.map j (rationalPoints.map (CommGroupScheme.groupHom t) s) := by
    simpa only [rationalPoints.map_apply, Category.assoc, Grp.comp_hom_hom] using
      congrArg (fun m : S.toGrp ⟶ G => s ≫ m.hom.hom) h
  have hχ : characterRestrict (CommGroupScheme.groupHom t)
      ((rationalCharacters.equivCharacterLattice T).symm a'.val) =
      (rationalCharacters.equivCharacterLattice S).symm (t ≫ a'.val) := by
    apply (rationalCharacters.equivCharacterLattice S).injective
    rfl
  have heval :
      rationalCharacterEval ((rationalCharacters.equivCharacterLattice T).symm a'.val)
          (rationalPoints.map (CommGroupScheme.groupHom t) s) =
        rationalCharacterEval
          ((rationalCharacters.equivCharacterLattice S).symm (t ≫ a'.val)) s := by
    rw [← rationalCharacterEval_characterRestrict, hχ]
  rw [RootFunctionFamily.centralIsogenyPullback_apply_root q hq hS hT t h ht φ a' _ hcg,
    RootFunctionFamily.centralIsogenyPullback_apply_root q hq hS hT t h ht φ a' g hg,
    map_mul, map_mul, map_inv, hs, ← heval]
  exact hφ a'.val a'.property _ _
    (centralIsogenyRootGroupPointsEquiv q hq hS t h ht a' ⟨g, hg⟩).property

namespace KPApartmentData

variable [Mono i.hom.hom.left] [Mono j.hom.hom.left]
  {ω : kˣ → ℝ}

/-- The image of the entire target apartment class under normalized pullback. -/
def centralIsogenyPullback (D : KPApartmentData j ω) : KPApartmentData i ω where
  carrier := RootFunctionFamily.centralIsogenyPullback q hq hS hT t h ht '' D.carrier
  exists_eq_orbit := by
    obtain ⟨φ, hφ, hω, hc⟩ := D.exists_eq_orbit
    refine ⟨RootFunctionFamily.centralIsogenyPullback q hq hS hT t h ht φ,
      hφ.centralIsogenyPullback_isRootDatumValuation q hq hS hT t h ht,
      hω.centralIsogenyPullback q hq hS hT t h ht, ?_⟩
    rw [hc]
    ext ψ
    constructor
    · rintro ⟨ψ, ⟨w, rfl⟩, rfl⟩
      obtain ⟨v, rfl⟩ :=
        (splitTorusIsogenyCocharacter k S T t hS hT ht).2.2.2.surjective w
      exact ⟨v, (RootFunctionFamily.centralIsogenyPullback_vadd
        q hq hS hT t h ht φ v).symm⟩
    · rintro ⟨v, rfl⟩
      exact ⟨cocharacterMapReal t v +ᵥ φ, ⟨cocharacterMapReal t v, rfl⟩,
        RootFunctionFamily.centralIsogenyPullback_vadd q hq hS hT t h ht φ v⟩
  smul_mem n ψ hψ := by
    obtain ⟨φ, hφ, rfl⟩ := hψ
    exact ⟨splitTorusIsogenyNormalizerMap q hS hT t h ht n • φ,
      D.smul_mem _ _ hφ,
      RootFunctionFamily.centralIsogenyPullback_smul q hS hT t h ht hq n φ⟩

variable (D : KPApartmentData j ω)

/-- Point pullback is injective because each target family is normalized. -/
private theorem apartmentPullback_injective :
    Function.Injective (fun x : D.Apartment =>
      (⟨RootFunctionFamily.centralIsogenyPullback q hq hS hT t h ht x.val,
        ⟨x.val, x.mem, rfl⟩⟩ : (D.centralIsogenyPullback q hq hS hT t h ht).Apartment)) := by
  intro x y he
  apply Apartment.ext
  exact RootFunctionFamily.centralIsogenyPullback_injective q hq hS hT t h ht
    x.isValuation.isNormalized y.isValuation.isNormalized (congrArg Apartment.val he)

/-- Reindex the actual valuation points of the whole apartment class. -/
def centralIsogenyApartmentEquiv :
    D.Apartment ≃ (D.centralIsogenyPullback q hq hS hT t h ht).Apartment :=
  Equiv.ofBijective
    (fun x => ⟨RootFunctionFamily.centralIsogenyPullback q hq hS hT t h ht x.val,
      ⟨x.val, x.mem, rfl⟩⟩)
    ⟨D.apartmentPullback_injective q hq hS hT t h ht, by
      rintro ⟨ψ, φ, hφ, rfl⟩
      exact ⟨⟨φ, hφ⟩, rfl⟩⟩

@[simp] theorem centralIsogenyApartmentEquiv_val (x : D.Apartment) :
    (D.centralIsogenyApartmentEquiv q hq hS hT t h ht x).val =
      RootFunctionFamily.centralIsogenyPullback q hq hS hT t h ht x.val := rfl

/-- Point pullback intertwines the actual quotient translation actions. -/
theorem centralIsogenyApartmentEquiv_vadd (v : TranslationSpace i) (x : D.Apartment) :
    D.centralIsogenyApartmentEquiv q hq hS hT t h ht
        (centralIsogenyTranslationEquiv q hq hS hT t h ht v +ᵥ x) =
      v +ᵥ D.centralIsogenyApartmentEquiv q hq hS hT t h ht x := by
  refine Submodule.Quotient.induction_on _ v fun w => ?_
  apply Apartment.ext
  exact RootFunctionFamily.centralIsogenyPullback_vadd q hq hS hT t h ht x.val w

/-- The original actual normalizer actions commute with point pullback. -/
theorem centralIsogenyApartmentEquiv_smul (n : normalizerPoints i) (x : D.Apartment) :
    D.centralIsogenyApartmentEquiv q hq hS hT t h ht
        (splitTorusIsogenyNormalizerMap q hS hT t h ht n • x) =
      n • D.centralIsogenyApartmentEquiv q hq hS hT t h ht x := by
  apply Apartment.ext
  exact RootFunctionFamily.centralIsogenyPullback_smul q hS hT t h ht hq n x.val

/-- The actual point bijection is affine, with the inverse torus quotient derivative. -/
def centralIsogenyApartmentAffineEquiv :
    D.Apartment ≃ᵃ[ℝ] (D.centralIsogenyPullback q hq hS hT t h ht).Apartment where
  toEquiv := D.centralIsogenyApartmentEquiv q hq hS hT t h ht
  linear := (centralIsogenyTranslationEquiv q hq hS hT t h ht).symm
  map_vadd' x v := by
    obtain ⟨v, rfl⟩ := (centralIsogenyTranslationEquiv q hq hS hT t h ht).surjective v
    simpa only [LinearEquiv.symm_apply_apply] using
      D.centralIsogenyApartmentEquiv_vadd q hq hS hT t h ht v x

/-- The affine constructor preserves the actual family pullback. -/
@[simp] theorem centralIsogenyApartmentAffineEquiv_val (x : D.Apartment) :
    (D.centralIsogenyApartmentAffineEquiv q hq hS hT t h ht x).val =
      RootFunctionFamily.centralIsogenyPullback q hq hS hT t h ht x.val := rfl

/-- The affine maps intertwine the original actual normalizer automorphisms. -/
theorem centralIsogenyApartmentAffineEquiv_normalizer (n : normalizerPoints i) :
    (D.normalizerAffineEquiv (splitTorusIsogenyNormalizerMap q hS hT t h ht n)).trans
        (D.centralIsogenyApartmentAffineEquiv q hq hS hT t h ht) =
      (D.centralIsogenyApartmentAffineEquiv q hq hS hT t h ht).trans
        ((D.centralIsogenyPullback q hq hS hT t h ht).normalizerAffineEquiv n) := by
  apply AffineEquiv.ext
  exact D.centralIsogenyApartmentEquiv_smul q hq hS hT t h ht n

end KPApartmentData

end Langlands.Geometry.Building
