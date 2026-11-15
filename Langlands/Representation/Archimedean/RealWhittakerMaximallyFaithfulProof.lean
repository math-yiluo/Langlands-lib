import Langlands.Representation.Archimedean.Kostant.Main
import Langlands.Representation.Archimedean.Kostant.NilpotentCone
import Langlands.Representation.Archimedean.Kostant.OrbitVanishing

/-!
# Kostant's theorem for `𝔤𝔩_n`: Whittaker modules with an infinitesimal character are maximally
faithful

* `glProductWhittakerMaximallyFaithful`: the Library statement
  `GLProductWhittakerMaximallyFaithfulStatement`, for finite products of `𝔤𝔩_{n i}(ℂ)`.
* `realWhittakerMaximallyFaithful`: the Library statement `RealWhittakerMaximallyFaithfulStatement`,
  for `ℂ ⊗[ℝ] 𝔤𝔩_n(ℝ)`.

Both follow from the conditional forms in `Kostant.Main` once the two geometric inputs are
supplied: `nilpotentConeIdeal` (the ideal of the nilpotent cone) and `orbitVanishing` (a
coadjoint-stable space of polynomials vanishing at the Whittaker point vanishes on the
nilpotent cone).
-/

noncomputable section

set_option autoImplicit false

namespace Langlands.Archimedean.Kostant

universe uV

/-- **Kostant's theorem** for finite products of `𝔤𝔩_{n i}(ℂ)` (Kostant 1978, Theorem 3.9;
Matumoto 1987, Corollary 5). -/
theorem glProductWhittakerMaximallyFaithful :
    GLProductWhittakerMaximallyFaithfulStatement.{uV} :=
  glProductWhittaker_of (fun _ _ n => nilpotentConeIdeal n) (fun _ _ _ n => orbitVanishing n)

/-- **Kostant's theorem** for `ℂ ⊗[ℝ] 𝔤𝔩_n(ℝ) ≅ 𝔤𝔩_n(ℂ)`: a module with an infinitesimal
character whose algebraic dual has a nonzero Whittaker vector for a nondegenerate character is
maximally faithful. -/
theorem realWhittakerMaximallyFaithful : RealWhittakerMaximallyFaithfulStatement.{uV} :=
  realWhittaker_of (fun n => nilpotentConeIdeal (fun _ : Unit => n))
    (fun n => orbitVanishing (fun _ : Unit => n))

end Langlands.Archimedean.Kostant
