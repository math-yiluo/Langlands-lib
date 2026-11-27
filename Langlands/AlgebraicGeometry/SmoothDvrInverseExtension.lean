import Langlands.AlgebraicGeometry.RationalMapAffineTrace
import Langlands.AlgebraicGeometry.SmoothDvrCodimensionOneOpen
import Langlands.AlgebraicGeometry.FibreDenseOpenDescent

/-! # Open immersions from extension of a rational inverse -/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Topology

namespace Langlands.AlgebraicGeometry

open SmoothDvrCodimensionOneOpen FactorialAffineExtension

set_option backward.isDefEq.respectTransparency false

/-- A partial inverse to a morphism of smooth DVR schemes extends around every point of
its image if it has the prescribed inverse values at the generic and principal prime
points of the source stalks. A common dense chart then identifies the morphism with the
inclusion of the extended domain. -/
theorem isOpenImmersion_of_inverse_at_stalk_primes
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X Y C : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) (g : Y ⟶ Spec (CommRingCat.of R))
    [Smooth f] [Smooth g] [IsSeparated f] [IsSeparated g]
    (τ : X ⟶ Y) (r : Y.PartialMap X) (hr : r.hom ≫ f = r.domain.ι ≫ g)
    (i : C ⟶ X) (j : C ⟶ r.domain.toScheme) [IsDominant i] [IsDominant j]
    (hτi : i ≫ τ = j ≫ r.domain.ι) (hri : j ≫ r.hom = i)
    (hsmall : ∀ (x : X) (p : PrimeSpectrum (X.presheaf.stalk x)), IsGenericOrPrimeElement p →
      ∃ hp : τ (X.fromSpecStalk x p) ∈ r.domain,
        r.hom ⟨τ (X.fromSpecStalk x p), hp⟩ = X.fromSpecStalk x p) :
    IsOpenImmersion τ := by
  have : X.IsSeparated := separatedScheme_of_separated_over f
  have : Y.IsSeparated := separatedScheme_of_separated_over g
  have : IsReduced X := SmoothReducedBase.isReduced_of_smooth_of_isReduced f
  have : IsReduced Y := SmoothReducedBase.isReduced_of_smooth_of_isReduced g
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian g
  let D := r.toRationalMap.domain
  have hD (x : X) : τ x ∈ D := by
    obtain ⟨H, hH, hxH, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := x) (by trivial)
    let : IsDomain (X.presheaf.stalk x) := isDomain_stalk R f x
    let : IsDomain (Y.presheaf.stalk (τ x)) := isDomain_stalk R g (τ x)
    let : UniqueFactorizationMonoid (X.presheaf.stalk x) := factorial_stalk R f x
    let : UniqueFactorizationMonoid (Y.presheaf.stalk (τ x)) := factorial_stalk R g (τ x)
    apply rationalMap_mem_domain_of_affineTrace g f r hr τ x H hH
    intro p hp
    obtain ⟨h, he⟩ := hsmall x p hp
    have hy : X.fromSpecStalk x p ∈ Set.range (X.fromSpecStalk x) := Set.mem_range_self p
    rw [Scheme.range_fromSpecStalk] at hy
    refine ⟨h, ?_⟩
    rw [he]
    exact hy.mem_open H.isOpen hxH
  let e : X ⟶ D.toScheme := IsOpenImmersion.lift D.ι τ (by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    exact hD x)
  have he : e ≫ D.ι = τ := IsOpenImmersion.lift_fac _ _ _
  let h := r.toRationalMap.toPartialMap.hom
  let k := Y.homOfLE r.le_domain_toRationalMap
  have hk : k ≫ h = r.hom := r.toPartialMap_toRationalMap_restrict
  have hik : i ≫ e = j ≫ k := by
    apply (cancel_mono D.ι).mp
    rw [Category.assoc, he, hτi, Category.assoc, Scheme.homOfLE_ι]
  have heh : e ≫ h = 𝟙 X := by
    apply AlgebraicGeometry.ext_of_isDominant i
    rw [← Category.assoc, hik, Category.assoc, hk, hri, Category.comp_id]
  have : IsDominant k := Opens.isDominant_homOfLE r.dense_domain _
  have : D.toScheme.IsSeparated := separatedScheme_of_separated_over D.ι
  have hhe : h ≫ e = 𝟙 D.toScheme := by
    apply AlgebraicGeometry.ext_of_isDominant (j ≫ k)
    rw [Category.assoc, ← Category.assoc k, hk, ← Category.assoc j, hri, hik,
      Category.comp_id]
  have : IsIso e := ⟨⟨h, heh, hhe⟩⟩
  rw [← he]
  infer_instance

end Langlands.AlgebraicGeometry
