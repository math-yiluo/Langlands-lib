import Langlands.Representation.Plancherel.RationalRestrictionSurjectivity
import Langlands.Topology.ComplexCharacterExtension
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-! # The actual character quotient by ambient unramified restriction -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.Plancherel

universe u

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G H : GroupScheme (Spec (CommRingCat.of F))} (f : H ⟶ G)

/-- Evaluation of a kernel valuation on a chosen actual algebraic character. -/
def rationalValuationKernelCoordinate (chi : rationalCharacters H) :
    (rationalValuationImageMap f).ker →* Multiplicative ℤ where
  toFun a := Multiplicative.ofAdd (a.val.val.toAdd chi)
  map_one' := rfl
  map_mul' _ _ := rfl

include f in
/-- One rational character direction modulo ambient restrictions detects
the entire kernel of the actual valuation-image map. -/
theorem rationalValuationKernelCoordinate_injective
    (chi0 : rationalCharacters H)
    (hspan : ∀ chi : rationalCharacters H,
      ∃ n : ℕ, 0 < n ∧ ∃ (c : ℤ) (psi : rationalCharacters G),
        n • chi = c • chi0 + characterRestrict f psi) :
    Function.Injective (rationalValuationKernelCoordinate f chi0) := by
  intro a b hab
  have h0 : a.val.val.toAdd chi0 = b.val.val.toAdd chi0 :=
    congrArg Multiplicative.toAdd hab
  have hf : rationalValuationImageMap f a.val = rationalValuationImageMap f b.val :=
    a.property.trans b.property.symm
  let d := a.val.val.toAdd - b.val.val.toAdd
  have hd0 : d chi0 = 0 := sub_eq_zero.mpr h0
  have hdf (psi : rationalCharacters G) : d (characterRestrict f psi) = 0 := by
    have hc := congrArg (fun x : rationalDiscreteValuationImage G => x.val.toAdd psi) hf
    change a.val.val.toAdd (characterRestrict f psi) -
      b.val.val.toAdd (characterRestrict f psi) = 0
    exact sub_eq_zero.mpr (by simpa only [rationalValuationImageMap_apply] using hc)
  apply Subtype.ext
  apply Subtype.ext
  apply Multiplicative.toAdd.injective
  apply AddMonoidHom.ext
  intro chi
  obtain ⟨n, hn, c, psi, hchi⟩ := hspan chi
  have hd : d (n • chi) = 0 := by
    rw [hchi, map_add, map_zsmul, hd0, hdf, smul_zero, zero_add]
  have he : n • a.val.val.toAdd chi = n • b.val.val.toAdd chi := by
    change a.val.val.toAdd (n • chi) - b.val.val.toAdd (n • chi) = 0 at hd
    simpa only [map_nsmul, sub_eq_zero] using hd
  exact nsmul_right_injective (M := ℤ) hn.ne' he

/-- The actual valuation kernel is cyclic when there is only one rational
character direction modulo ambient restrictions. -/
theorem rationalValuationKernel_isCyclic_of_one_direction
    (chi0 : rationalCharacters H)
    (hspan : ∀ chi : rationalCharacters H,
      ∃ n : ℕ, 0 < n ∧ ∃ (c : ℤ) (psi : rationalCharacters G),
        n • chi = c • chi0 + characterRestrict f psi) :
    IsCyclic (rationalValuationImageMap f).ker :=
  isCyclic_of_injective (rationalValuationKernelCoordinate f chi0)
    (rationalValuationKernelCoordinate_injective f chi0 hspan)

section CanonicalTopology

variable [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  [IsAffine H.X.left] [LocallyOfFiniteType H.X.hom]

local instance sourcePointTopology : TopologicalSpace (rationalPoints H) :=
  rationalPointTopology F H.X
local instance targetPointTopology : TopologicalSpace (rationalPoints G) :=
  rationalPointTopology F G.X

/-- Restrict the existing descended image character to the actual kernel
of the ambient valuation map. -/
def rationalUnramifiedValuationKernelRestrict :
    unramifiedCharacters (fun chi => (rationalNormCharacters H chi).toMul) →*
      ((rationalValuationImageMap f).ker →* ℂˣ) where
  toFun chi := (rationalImageUnramifiedDescend H chi).toMonoidHom.comp
    (rationalValuationImageMap f).ker.subtype
  map_one' := by
    apply MonoidHom.ext
    intro a
    change rationalImageUnramifiedDescend H 1 a.val = 1
    obtain ⟨h, hh⟩ := rationalValuationImageProjection_surjective H a.val
    rw [← hh, rationalImageUnramifiedDescend_projection]
    rfl
  map_mul' chi psi := by
    apply MonoidHom.ext
    intro a
    change rationalImageUnramifiedDescend H (chi * psi) a.val =
      rationalImageUnramifiedDescend H chi a.val * rationalImageUnramifiedDescend H psi a.val
    obtain ⟨h, hh⟩ := rationalValuationImageProjection_surjective H a.val
    rw [← hh, rationalImageUnramifiedDescend_projection,
      rationalImageUnramifiedDescend_projection, rationalImageUnramifiedDescend_projection]
    rfl

omit [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] [LocallyOfFiniteType H.X.hom] in
@[simp]
theorem rationalUnramifiedValuationKernelRestrict_apply
    (chi : unramifiedCharacters (fun psi => (rationalNormCharacters H psi).toMul))
    (a : (rationalValuationImageMap f).ker) :
    rationalUnramifiedValuationKernelRestrict f chi a =
      rationalImageUnramifiedDescend H chi a.val := rfl

omit [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] in
/-- Every complex character of the actual kernel extends to an actual
unramified character of the source group. -/
theorem rationalUnramifiedValuationKernelRestrict_surjective :
    Function.Surjective (rationalUnramifiedValuationKernelRestrict f) := by
  intro chi
  obtain ⟨theta, htheta⟩ := Langlands.Topology.exists_complex_character_extension
    (rationalValuationImageMap f).ker.subtype Subtype.val_injective chi
  let theta' : rationalImageCharacters H := ⟨theta, continuous_of_discreteTopology⟩
  refine ⟨rationalCanonicalImageUnramifiedContinuousEquiv H theta', ?_⟩
  apply MonoidHom.ext
  intro a
  have he := (rationalCanonicalImageUnramifiedContinuousEquiv H).symm_apply_apply theta'
  have ha := congrArg (fun c : rationalImageCharacters H => c a.val) he
  exact ha.trans (DFunLike.congr_fun htheta a)

omit [LocallyOfFiniteType H.X.hom] in
/-- Killing the actual valuation kernel is exactly being the restriction
of an ambient unramified character. -/
theorem rationalUnramifiedValuationKernelRestrict_eq_one_iff
    (chi : unramifiedCharacters (fun psi => (rationalNormCharacters H psi).toMul)) :
    rationalUnramifiedValuationKernelRestrict f chi = 1 ↔
      ∃ eta : unramifiedCharacters (fun psi => (rationalNormCharacters G psi).toMul),
        rationalUnramifiedCharacterRestrict f eta = chi := by
  constructor
  · intro hchi
    let vmap : rationalDiscreteValuationImage H →ₜ* rationalDiscreteValuationImage G :=
      ⟨rationalValuationImageMap f, continuous_of_discreteTopology⟩
    have hker : vmap.toMonoidHom.ker ≤
        (rationalImageUnramifiedDescend H chi).toMonoidHom.ker := by
      intro a ha
      exact DFunLike.congr_fun hchi ⟨a, ha⟩
    obtain ⟨theta, htheta⟩ :=
      Langlands.Topology.exists_continuous_complex_character_of_open_map vmap
        (fun _ _ => isOpen_discrete _) (rationalImageUnramifiedDescend H chi) hker
    refine ⟨rationalCanonicalImageUnramifiedContinuousEquiv G theta, ?_⟩
    apply Subtype.ext
    apply ContinuousMonoidHom.ext
    intro h
    change (rationalCanonicalImageUnramifiedContinuousEquiv G theta).val
        (rationalPoints.map f h) = chi.val h
    rw [rationalCanonicalImageUnramifiedContinuousEquiv_apply,
      ← rationalValuationImageMap_projection f h]
    exact (DFunLike.congr_fun htheta (rationalValuationImageProjection H h)).trans
      (rationalImageUnramifiedDescend_projection H chi h)
  · rintro ⟨eta, rfl⟩
    apply MonoidHom.ext
    intro a
    obtain ⟨h, hh⟩ := rationalValuationImageProjection_surjective H a.val
    change rationalImageUnramifiedDescend H (rationalUnramifiedCharacterRestrict f eta) a.val = 1
    rw [← hh, rationalImageUnramifiedDescend_projection,
      rationalUnramifiedCharacterRestrict_apply]
    have hmap : rationalValuationImageProjection G (rationalPoints.map f h) = 1 := by
      rw [← rationalValuationImageMap_projection f h, hh]
      exact a.property
    have he := rationalImageUnramifiedDescend_projection G eta (rationalPoints.map f h)
    rw [hmap, map_one] at he
    exact he.symm

omit [LocallyOfFiniteType H.X.hom] in
/-- The fibers of kernel restriction are precisely the multiplicative
orbits of ambient unramified restrictions. -/
theorem rationalUnramifiedValuationKernelRestrict_eq_iff
    (chi psi : unramifiedCharacters (fun theta => (rationalNormCharacters H theta).toMul)) :
    rationalUnramifiedValuationKernelRestrict f chi =
        rationalUnramifiedValuationKernelRestrict f psi ↔
      ∃ eta : unramifiedCharacters (fun theta => (rationalNormCharacters G theta).toMul),
        chi = rationalUnramifiedCharacterRestrict f eta * psi := by
  have hd : rationalUnramifiedValuationKernelRestrict f (chi / psi) =
      rationalUnramifiedValuationKernelRestrict f chi /
        rationalUnramifiedValuationKernelRestrict f psi :=
    map_div (rationalUnramifiedValuationKernelRestrict f) chi psi
  rw [← div_eq_one, ← hd,
    rationalUnramifiedValuationKernelRestrict_eq_one_iff]
  constructor
  · rintro ⟨eta, he⟩
    exact ⟨eta, div_eq_iff_eq_mul.mp he.symm⟩
  · rintro ⟨eta, he⟩
    exact ⟨eta, (div_eq_iff_eq_mul.mpr he).symm⟩

end CanonicalTopology

end Langlands.Plancherel
