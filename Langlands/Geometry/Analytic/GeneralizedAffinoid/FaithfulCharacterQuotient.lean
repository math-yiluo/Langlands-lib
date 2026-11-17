import Langlands.Geometry.Analytic.GeneralizedAffinoid.ClosedQuotient
import Mathlib.Logic.Small.Basic

/-! # Presented quotients with faithful bounded characters -/

noncomputable section

universe u v uL

namespace Langlands.Analytic.PresentedAffinoidAlgebra.FaithfulCharacterQuotient

variable {K : Type u} [NormedField K] [IsUltrametricDist K]
  {R : PresentedAffinoidAlgebra K}
  {L : Type uL} [NormedCommRing L] [NormedAlgebra K L]
  (χ : BoundedAlgHom K R L)

/-- The actual algebraic kernel of the bounded character. -/
def kernel : Ideal R := RingHom.ker χ.toAlgHom.toRingHom

instance kernel_closed : IsClosed (kernel χ : Set R) :=
  isClosed_eq χ.continuous continuous_const

/-- The presented closed quotient of the source by the character kernel. -/
def algebra : PresentedAffinoidAlgebra K :=
  ClosedQuotient.algebra R (kernel χ)

/-- The actual bounded quotient map. -/
def map : BoundedAlgHom K R (algebra χ) :=
  ClosedQuotient.map R (kernel χ)

theorem map_surjective : Function.Surjective (map χ) :=
  ClosedQuotient.map_surjective R (kernel χ)

@[simp]
theorem map_eq_zero_iff (r : R) : map χ r = 0 ↔ χ r = 0 :=
  ClosedQuotient.map_eq_zero_iff R (kernel χ) r

/-- The character descends boundedly to the presented quotient. -/
def character : BoundedAlgHom K (algebra χ) L :=
  ClosedQuotient.lift R (kernel χ) χ (fun _ hr => hr)

@[simp]
theorem character_map (r : R) : character χ (map χ r) = χ r :=
  ClosedQuotient.lift_map R (kernel χ) χ (fun _ hr => hr) r

theorem character_comp_map : (character χ).comp (map χ) = χ :=
  ClosedQuotient.lift_comp_map R (kernel χ) χ (fun _ hr => hr)

/-- Removing exactly the character kernel makes the descended character faithful. -/
theorem character_injective : Function.Injective (character χ) := by
  intro b c hbc
  obtain ⟨r, rfl⟩ := map_surjective χ b
  obtain ⟨s, rfl⟩ := map_surjective χ c
  apply sub_eq_zero.mp
  rw [← map_sub]
  apply (map_eq_zero_iff χ (r - s)).mpr
  rw [map_sub, sub_eq_zero]
  simpa only [character_map] using hbc

/-- Surjectivity of the quotient map separates all quotient seminorms. -/
theorem comap_injective :
    Function.Injective (BanachSpectrum.comap (map χ).toBoundedRingHom) := by
  intro x y hxy
  apply BanachSpectrum.ext
  intro b
  obtain ⟨r, rfl⟩ := map_surjective χ b
  exact congrArg (fun z : BanachSpectrum R => z r) hxy

/-- The quotient spectrum fits every universe that already contains the source spectrum. -/
theorem small_spectrum [Small.{v} (BanachSpectrum R)] :
    Small.{v} (BanachSpectrum (algebra χ)) :=
  small_of_injective (comap_injective χ)

/-- A faithful character detects equality of bounded maps into the quotient algebra. -/
theorem hom_ext {S : PresentedAffinoidAlgebra K}
    (f g : BoundedAlgHom K S (algebra χ))
    (h : (character χ).comp f = (character χ).comp g) : f = g :=
  BoundedAlgHom.ext fun s =>
    character_injective χ (congrArg (fun ψ : BoundedAlgHom K S L => ψ s) h)

end Langlands.Analytic.PresentedAffinoidAlgebra.FaithfulCharacterQuotient
