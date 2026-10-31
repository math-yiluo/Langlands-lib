import Langlands.AlgebraicGeometry.FiniteSingletonFiberLocalAlgebra
import Langlands.AlgebraicGeometry.FiniteSingletonFiberLocalClosedImmersionStatement

/-! # Affine fibers and actual stalk maps -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- A singleton scheme fiber gives one prime over the corresponding prime on
any affine target neighborhood with affine whole inverse image. -/
theorem primesOver_eq_singleton_of_singletonFiber
    {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X)
    (hF : f ⁻¹' {f x} = {x}) (U : Y.Opens) (hU : IsAffineOpen U)
    (hV : IsAffineOpen (f ⁻¹ᵁ U)) (hx : f x ∈ U) :
    let := (f.app U).hom.toAlgebra
    (hU.primeIdealOf ⟨f x, hx⟩).asIdeal.primesOver Γ(X, f ⁻¹ᵁ U) =
      {(hV.primeIdealOf ⟨x, hx⟩).asIdeal} := by
  let := (f.app U).hom.toAlgebra
  ext Q
  constructor
  · intro hQ
    let z : PrimeSpectrum Γ(X, f ⁻¹ᵁ U) := ⟨Q, hQ.1⟩
    have hzP : z.comap (f.app U).hom = hU.primeIdealOf ⟨f x, hx⟩ := by
      apply PrimeSpectrum.ext
      exact hQ.2.over.symm
    have hz : f (hV.fromSpec z) = f x := by
      calc
        f (hV.fromSpec z) = hU.fromSpec (z.comap (f.app U).hom) := by
          simpa only [Scheme.Hom.appLE_eq_app, Scheme.Hom.comp_apply, Spec.map_apply] using
            (congrArg (fun g : Spec Γ(X, f ⁻¹ᵁ U) ⟶ Y ↦ g z)
            (IsAffineOpen.SpecMap_appLE_fromSpec f hU hV le_rfl)).symm
        _ = f x := by rw [hzP, hU.fromSpec_primeIdealOf]
    have hzmem : hV.fromSpec z ∈ f ⁻¹' {f x} := hz
    rw [hF, Set.mem_singleton_iff] at hzmem
    have hzQ : z = hV.primeIdealOf ⟨x, hx⟩ :=
      hV.fromSpec.isOpenEmbedding.injective
        (hzmem.trans (hV.fromSpec_primeIdealOf ⟨x, hx⟩).symm)
    exact congrArg PrimeSpectrum.asIdeal hzQ
  · intro hQ
    rw [Set.mem_singleton_iff] at hQ
    subst Q
    refine ⟨inferInstance, ⟨?_⟩⟩
    change (hU.primeIdealOf ⟨f x, hx⟩).asIdeal =
      (hV.primeIdealOf ⟨x, hx⟩).asIdeal.comap (f.app U).hom
    simpa only [Scheme.Hom.appLE_eq_app, PrimeSpectrum.comap_asIdeal] using
      congrArg PrimeSpectrum.asIdeal
        (IsAffineOpen.comap_primeIdealOf_appLE U hU (f ⁻¹ᵁ U) hV le_rfl hx).symm

set_option backward.isDefEq.respectTransparency false in
/-- The actual stalk map of a finite scheme morphism is finite at a singleton
fiber. -/
theorem finite_stalkMap_of_singletonFiber
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] (x : X)
    (hF : f ⁻¹' {f x} = {x}) : (f.stalkMap x).hom.Finite := by
  obtain ⟨U, hU, hx, -⟩ := exists_isAffineOpen_mem_and_subset
    (X := Y) (x := f x) (U := ⊤) (by trivial)
  have hV := hU.preimage f
  let R := Γ(Y, U)
  let S := Γ(X, f ⁻¹ᵁ U)
  let := (f.app U).hom.toAlgebra
  let p : Ideal R := (hU.primeIdealOf ⟨f x, hx⟩).asIdeal
  let q : Ideal S := (hV.primeIdealOf ⟨x, hx⟩).asIdeal
  have : p.IsPrime := (hU.primeIdealOf ⟨f x, hx⟩).isPrime
  have : q.IsPrime := (hV.primeIdealOf ⟨x, hx⟩).isPrime
  have hq : p.primesOver S = {q} :=
    primesOver_eq_singleton_of_singletonFiber f x hF U hU hV hx
  have : q.LiesOver p := (hq.ge rfl).2
  have : Module.Finite R S := f.finite_app U hU
  let := Localization.AtPrime.algebraOfLiesOver p q
  have : Module.Finite (Localization.AtPrime p) (Localization.AtPrime q) :=
    Localization.finite_of_primesOver_eq_singleton hq
  apply (RingHom.finite_respectsIso.arrow_mk_iso_iff
    (IsAffineOpen.arrowStalkMapIso f U hU (f ⁻¹ᵁ U) hV le_rfl hx)).mpr
  simp only [Scheme.Hom.appLE_eq_app]
  change (Localization.localRingHom p q (algebraMap R S) (q.over_def p)).Finite
  rw [← Localization.AtPrime.algebraMap_eq p q, RingHom.finite_algebraMap]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- Stalk surjectivity of a finite map spreads over an entire target neighborhood
when the fiber is a singleton. -/
theorem exists_isClosedImmersion_restrict_of_singletonFiber
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] (x : X)
    (hF : f ⁻¹' {f x} = {x}) (H : Function.Surjective (f.stalkMap x).hom) :
    ∃ W : Y.Opens, f x ∈ W ∧ IsClosedImmersion (f ∣_ W) := by
  obtain ⟨U, hU, hx, -⟩ := exists_isAffineOpen_mem_and_subset
    (X := Y) (x := f x) (U := ⊤) (by trivial)
  have hV := hU.preimage f
  let R := Γ(Y, U)
  let S := Γ(X, f ⁻¹ᵁ U)
  let := (f.app U).hom.toAlgebra
  let p : Ideal R := (hU.primeIdealOf ⟨f x, hx⟩).asIdeal
  let q : Ideal S := (hV.primeIdealOf ⟨x, hx⟩).asIdeal
  have : p.IsPrime := (hU.primeIdealOf ⟨f x, hx⟩).isPrime
  have : q.IsPrime := (hV.primeIdealOf ⟨x, hx⟩).isPrime
  have hq : p.primesOver S = {q} :=
    primesOver_eq_singleton_of_singletonFiber f x hF U hU hV hx
  have : q.LiesOver p := (hq.ge rfl).2
  have : Module.Finite R S := f.finite_app U hU
  have Hloc : Function.Surjective
      (Localization.localRingHom p q (algebraMap R S) (q.over_def p)) := by
    have H' := (RingHom.surjective_respectsIso.arrow_mk_iso_iff
      (IsAffineOpen.arrowStalkMapIso f U hU (f ⁻¹ᵁ U) hV le_rfl hx)).mp H
    simp only [Scheme.Hom.appLE_eq_app] at H'
    change Function.Surjective
      (Localization.localRingHom p q (algebraMap R S) (q.over_def p)) at H'
    exact H'
  obtain ⟨r, hr, hsurj⟩ :=
    Langlands.CommutativeAlgebra.exists_awayMap_surjective_of_singleton hq Hloc
  have hrx : f x ∈ Y.basicOpen r := by
    have heq : hU.fromSpec (hU.primeIdealOf ⟨f x, hx⟩) = f x :=
      hU.fromSpec_primeIdealOf ⟨f x, hx⟩
    rw [← heq]
    change hU.primeIdealOf ⟨f x, hx⟩ ∈ hU.fromSpec ⁻¹ᵁ Y.basicOpen r
    rw [hU.fromSpec_preimage_basicOpen]
    exact hr
  have hsurj' : Function.Surjective (f.app (Y.basicOpen r)).hom := by
    have := hU.isLocalization_basicOpen r
    have := hV.isLocalization_basicOpen (f.app U r)
    apply (RingHom.surjective_respectsIso.arrow_mk_iso_iff
      (IsAffineOpen.appBasicOpenIsoAwayMap f hU hV r)).mpr
    change Function.Surjective
      (IsLocalization.Away.map Γ(Y, Y.basicOpen r)
        Γ(X, X.basicOpen (f.app U r)) (f.app U).hom r)
    rw [IsLocalization.Away.map_surjective_iff]
    exact Localization.awayMap_surjective_iff.mp (hsurj r (dvd_refl r))
  refine ⟨Y.basicOpen r, hrx, ?_⟩
  have : IsAffine (Y.basicOpen r) := hU.basicOpen r
  have : IsAffine (f ⁻¹ᵁ Y.basicOpen r) := (hU.basicOpen r).preimage f
  apply IsClosedImmersion.of_surjective_of_isAffine
  have Hrestrict := (RingHom.surjective_respectsIso.arrow_mk_iso_iff
    (arrowResLEAppIso f (Y.basicOpen r) (f ⁻¹ᵁ Y.basicOpen r) le_rfl)).mpr
    (by simpa only [Scheme.Hom.appLE_eq_app] using hsurj')
  simpa only [Scheme.Hom.resLE_eq_morphismRestrict] using Hrestrict

/-- A finite scheme morphism has finite stalks and a closed-immersion neighborhood
at any singleton fiber with a surjective stalk map. -/
theorem finiteSingletonFiber_localClosedImmersion :
    FiniteSingletonFiberLocalClosedImmersionStatement.{u} := by
  intro X Y f _ x hF
  exact ⟨finite_stalkMap_of_singletonFiber f x hF,
    exists_isClosedImmersion_restrict_of_singletonFiber f x hF⟩

end Langlands.AlgebraicGeometry
