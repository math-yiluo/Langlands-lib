import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.RingTheory.Ideal.GoingDown
import Mathlib.RingTheory.Ideal.Height

/-! # Local dimension under flat locally quasi-finite morphisms -/

universe u v

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

/-- Flatness supplies going down, and quasi-finiteness supplies incomparability. -/
private lemma height_eq_under_of_flat_quasiFinite
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    [Module.Flat R S] [Algebra.QuasiFinite R S] (P : Ideal S) [P.IsPrime] :
    P.height = (P.under R).height := by
  have hstrict : StrictMono (PrimeSpectrum.comap (algebraMap R S)) := by
    intro p q hpq
    change p.asIdeal.under R < q.asIdeal.under R
    refine lt_of_le_of_ne (Ideal.comap_mono hpq.le) ?_
    intro heq
    exact hpq.ne (PrimeSpectrum.ext
      (Algebra.QuasiFinite.eq_of_le_of_under_eq p.asIdeal q.asIdeal hpq.le heq))
  have hlift : ∀ (p : PrimeSpectrum S) (q : PrimeSpectrum R),
      q < PrimeSpectrum.comap (algebraMap R S) p →
        ∃ p' < p, PrimeSpectrum.comap (algebraMap R S) p' = q := by
    intro p q hq
    obtain ⟨P', hP', hprime, hlo⟩ :=
      Ideal.exists_ideal_lt_liesOver_of_lt p.asIdeal (p := q.asIdeal) hq
    exact ⟨⟨P', hprime⟩, hP', PrimeSpectrum.ext hlo.over.symm⟩
  simpa only [← PrimeSpectrum.height_eq_orderHeight, PrimeSpectrum.comap_asIdeal] using
    Order.height_eq_of_strictMono (PrimeSpectrum.comap (algebraMap R S))
      hstrict hlift ⟨P, inferInstance⟩

/-- A flat quasi-finite local algebra has the same Krull dimension as its base. -/
theorem ringKrullDim_eq_of_flat_quasiFinite_local
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
    [Module.Flat R S] [Algebra.QuasiFinite R S] : ringKrullDim S = ringKrullDim R := by
  have h := height_eq_under_of_flat_quasiFinite R S (IsLocalRing.maximalIdeal S)
  have h' := congrArg (fun n : ℕ∞ => (n : WithBot ℕ∞)) h
  simpa only [Ideal.under, IsLocalRing.maximalIdeal_comap,
    IsLocalRing.maximalIdeal_height_eq_ringKrullDim] using h'

/-- A flat locally quasi-finite scheme morphism preserves every stalk's Krull dimension. -/
theorem stalk_ringKrullDim_eq_of_flat_locallyQuasiFinite
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] [LocallyQuasiFinite f] (x : X) :
    ringKrullDim (X.presheaf.stalk x) = ringKrullDim (Y.presheaf.stalk (f x)) := by
  let := (f.stalkMap x).hom.toAlgebra
  have : IsLocalHom
      (algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)) :=
    f.toLRSHom.prop x
  have : Module.Flat (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    (Flat.stalkMap f x)
  have : Algebra.QuasiFinite (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    f.quasiFiniteAt x
  exact ringKrullDim_eq_of_flat_quasiFinite_local _ _

end Langlands.AlgebraicGeometry
