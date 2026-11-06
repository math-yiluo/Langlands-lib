import Langlands.Geometry.Building.RootValuationFieldDescent

/-! # Actual apartment descent by literal field restriction -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
open Langlands.GroupScheme.GaloisPointComparison

namespace Langlands.Geometry.Building.KPApartmentData

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [Smooth G.X.hom]
  (i : S.toGrp ⟶ G) [Mono i.hom.hom.left]

local notation "b" => algebraBaseMap k K
local notation "S_K" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange b) S
local notation "G_K" => baseChanged k K G
local notation "i_K" => CategoryTheory.Functor.map (GroupScheme.baseChange b) i

private instance extendedAffine : IsAffineHom (G_K).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom b)
  infer_instance

private instance extendedMono : Mono (i_K).hom.hom.left := by
  let : Mono i.hom.hom := Over.mono_of_mono_left _
  change Mono ((Over.pullback b).map i.hom.hom).left
  infer_instance

variable (hS : IsSplitTorus S.toGrp) (hE : RelativeRoot.HasOppositeFactorPairs i)
  (ω : Kˣ →* Multiplicative ℝ)
  (hω : ∃ t : kˣ, (ω (Units.map (algebraMap k K).toMonoidHom t)).toAdd ≠ 0)

/-- Restrict the actual normalizer-stable equipollence class. Its carrier is
the literal image of the upstairs class under actual family restriction. -/
def fieldRestrict
    (hS : IsSplitTorus S.toGrp) (hE : RelativeRoot.HasOppositeFactorPairs i)
    (ω : Kˣ →* Multiplicative ℝ)
    (hω : ∃ t : kˣ, (ω (Units.map (algebraMap k K).toMonoidHom t)).toAdd ≠ 0)
    (D : KPApartmentData (S := S_K) (G := G_K) (i_K) (fun t => (ω t).toAdd)) : KPApartmentData i
    (fun t => (ω (Units.map (algebraMap k K).toMonoidHom t)).toAdd) where
  carrier := RootFunctionFamily.fieldRestrict (k := k) '' D.carrier
  exists_eq_orbit := by
    obtain ⟨ψ, hψ, hcompat, hcarrier⟩ := D.exists_eq_orbit
    refine ⟨RootFunctionFamily.fieldRestrict (k := k) ψ,
      (hψ.fieldRestrictValuation i hS hE ω hcompat hω).property,
      RootFunctionFamily.fieldRestrict_isSplitTorusCompatible hS hcompat, ?_⟩
    rw [hcarrier]
    ext φ
    constructor
    · rintro ⟨_, ⟨v, rfl⟩, rfl⟩
      refine ⟨(splitCocharacterBaseChange (K := K) S hS).symm v, ?_⟩
      simpa only [LinearEquiv.apply_symm_apply] using
        (RootFunctionFamily.fieldRestrict_vadd hS ψ
          ((splitCocharacterBaseChange (K := K) S hS).symm v)).symm
    · rintro ⟨v, rfl⟩
      refine ⟨splitCocharacterBaseChange (K := K) S hS v +ᵥ ψ, ⟨_, rfl⟩, ?_⟩
      exact RootFunctionFamily.fieldRestrict_vadd hS ψ v
  smul_mem := by
    rintro n _ ⟨ψ, hψ, rfl⟩
    refine ⟨normalizerPointsFieldExtend (K := K) i n • ψ,
      D.smul_mem _ _ hψ, ?_⟩
    exact RootFunctionFamily.fieldRestrict_normalizer i n ψ

/-- The actual restriction on apartment points. -/
def fieldRestrictPoint
    (D : KPApartmentData (S := S_K) (G := G_K) (i_K) (fun t => (ω t).toAdd))
    (x : D.Apartment) : (fieldRestrict i hS hE ω hω D).Apartment :=
  ⟨RootFunctionFamily.fieldRestrict (k := k) x.val, ⟨x.val, x.mem, rfl⟩⟩

@[simp] theorem fieldRestrictPoint_val
    (D : KPApartmentData (S := S_K) (G := G_K) (i_K) (fun t => (ω t).toAdd))
    (x : D.Apartment) :
    (fieldRestrictPoint i hS hE ω hω D x).val =
      RootFunctionFamily.fieldRestrict (k := k) x.val := rfl

/-- Actual reduced translation pullback is the linear part of restriction. -/
theorem fieldRestrictPoint_vadd
    (D : KPApartmentData (S := S_K) (G := G_K) (i_K) (fun t => (ω t).toAdd))
    (v : TranslationSpace i) (x : D.Apartment) :
    fieldRestrictPoint i hS hE ω hω D
        (splitTranslationBaseChange (K := K) hS i v +ᵥ x) =
      v +ᵥ fieldRestrictPoint i hS hE ω hω D x := by
  refine Submodule.Quotient.induction_on _ v fun w => ?_
  apply Apartment.ext
  exact RootFunctionFamily.fieldRestrict_vadd hS x.val w

/-- Original normalizer points act through their actual scalar extensions. -/
theorem fieldRestrictPoint_normalizer
    (D : KPApartmentData (S := S_K) (G := G_K) (i_K) (fun t => (ω t).toAdd))
    (n : normalizerPoints i) (x : D.Apartment) :
    fieldRestrictPoint i hS hE ω hω D
        (normalizerPointsFieldExtend (K := K) i n • x) =
      n • fieldRestrictPoint i hS hE ω hω D x := by
  apply Apartment.ext
  exact RootFunctionFamily.fieldRestrict_normalizer i n x.val

/-- No distinct points in the supplied equipollence class become identified
by actual field restriction. -/
theorem fieldRestrictPoint_injective
    (D : KPApartmentData (S := S_K) (G := G_K) (i_K) (fun t => (ω t).toAdd)) :
    Function.Injective (fieldRestrictPoint i hS hE ω hω D) := by
  intro x y hxy
  obtain ⟨v, hv⟩ := D.equipollent_of_mem x.mem y.mem
  obtain ⟨w, rfl⟩ := (splitCocharacterBaseChange (K := K) S hS).surjective v
  have heq := congrArg Apartment.val hxy
  change RootFunctionFamily.fieldRestrict (k := k) x.val =
    RootFunctionFamily.fieldRestrict (k := k) y.val at heq
  have hw : w ∈ rootAnnihilator i := by
    apply (fieldRestrictPoint i hS hE ω hω D x).isValuation.vadd_eq_self_iff.mp
    change w +ᵥ RootFunctionFamily.fieldRestrict (k := k) x.val =
      RootFunctionFamily.fieldRestrict (k := k) x.val
    rw [← RootFunctionFamily.fieldRestrict_vadd hS x.val w, ← hv]
    exact heq.symm
  have hwK := (splitCocharacterBaseChange_mem_rootAnnihilator_iff
    (K := K) hS i w).mpr hw
  apply Apartment.ext
  rw [hv, x.isValuation.vadd_eq_self_iff.mpr hwK]

theorem fieldRestrictPoint_surjective
    (D : KPApartmentData (S := S_K) (G := G_K) (i_K) (fun t => (ω t).toAdd)) :
    Function.Surjective (fieldRestrictPoint i hS hE ω hω D) := by
  intro y
  obtain ⟨ψ, hψ, hψy⟩ := y.mem
  exact ⟨⟨ψ, hψ⟩, Apartment.ext hψy⟩

/-- The actual upstairs apartment is affinely identified with the literal
restricted apartment, through inverse reduced translation base change. -/
def fieldRestrictAffineEquiv
    (D : KPApartmentData (S := S_K) (G := G_K) (i_K) (fun t => (ω t).toAdd)) :
    D.Apartment ≃ᵃ[ℝ] (fieldRestrict i hS hE ω hω D).Apartment where
  toEquiv := Equiv.ofBijective (fieldRestrictPoint i hS hE ω hω D)
    ⟨fieldRestrictPoint_injective i hS hE ω hω D,
      fieldRestrictPoint_surjective i hS hE ω hω D⟩
  linear := (splitTranslationBaseChange (K := K) hS i).symm
  map_vadd' x v := by
    change fieldRestrictPoint i hS hE ω hω D (v +ᵥ x) =
      (splitTranslationBaseChange (K := K) hS i).symm v +ᵥ
        fieldRestrictPoint i hS hE ω hω D x
    obtain ⟨w, rfl⟩ := (splitTranslationBaseChange (K := K) hS i).surjective v
    simpa only [LinearEquiv.symm_apply_apply] using
      fieldRestrictPoint_vadd i hS hE ω hω D w x

@[simp] theorem fieldRestrictAffineEquiv_apply
    (D : KPApartmentData (S := S_K) (G := G_K) (i_K) (fun t => (ω t).toAdd))
    (x : D.Apartment) :
    fieldRestrictAffineEquiv i hS hE ω hω D x =
      fieldRestrictPoint i hS hE ω hω D x := rfl

/-- All nonzero-character filtrations are literal pointwise preimages, with
exactly the original real bound. -/
theorem filtration_fieldRestrictPoint
    (D : KPApartmentData (S := S_K) (G := G_K) (i_K) (fun t => (ω t).toAdd))
    (x : D.Apartment) (a : characterLattice S)
    (ha : a ≠ 0) (r : ℝ) :
    (fieldRestrict i hS hE ω hω D).filtration (fieldRestrictPoint i hS hE ω hω D x) a r =
      (D.filtration x (characterLattice.baseChange b S a) r).comap (rationalExtend k K G) := by
  apply SetLike.ext'
  exact rootFiltration_fieldRestrict i hS x.val a ha r

end Langlands.Geometry.Building.KPApartmentData
