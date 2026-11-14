import Langlands.Automorphic.PrincipalSeriesGammaMatchStatement
import Langlands.Representation.Unramified.SphericalSpectrumExistenceProof
import Langlands.Representation.Induction.NormalizedProductCharacterTwist
import Langlands.Representation.Induction.BlockEquivalence
import Langlands.Representation.RankinSelberg.HighlyRamifiedGammaAssembly
import Langlands.Representation.Whittaker.Transport

/-!
# Principal-series constituents and their character twists

Subquotients transport along equivalences of the ambient representation and along common
character twists. The determinant twist of a normalized principal series
`i(μ_1, …, μ_(r+1))` by `η` is equivalent to `i(μ_1 η, …, μ_(r+1) η)`. Hence the twist of a
generic constituent of `i(μ)` by `η` is a generic constituent of `i(μ η)`.
-/

noncomputable section

set_option autoImplicit false

universe u uU uU' uW

namespace Langlands.Correspondence

section Subquotient

variable {G : Type*} [Group G] {U : Type uU} {U' : Type uU'} {W : Type uW}
  [AddCommGroup U] [Module ℂ U] [AddCommGroup U'] [Module ℂ U'] [AddCommGroup W] [Module ℂ W]

/-- A subquotient of `ρ` is a subquotient of every representation equivalent to `ρ`. -/
theorem isSubquotientOf_of_equiv_left {ρ : Representation ℂ G U}
    {ρ' : Representation ℂ G U'} {π : Representation ℂ G W} (e : ρ.Equiv ρ')
    (h : IsSubquotientOf ρ π) : IsSubquotientOf ρ' π := by
  obtain ⟨S, f, hf⟩ := h
  have key : ∀ (g : G) (y : U'), e.symm (ρ' g y) = ρ g (e.symm y) := fun g y =>
    Representation.IntertwiningMap.isIntertwining _ _ e.symm.toIntertwiningMap g y
  let S' : Subrepresentation ρ' :=
    ⟨S.toSubmodule.comap e.symm.toLinearMap, fun g y hy => by
      rw [Submodule.mem_comap] at hy ⊢
      change e.symm (ρ' g y) ∈ S.toSubmodule
      rw [key]
      exact S.apply_mem_toSubmodule g hy⟩
  let r : S'.toSubmodule →ₗ[ℂ] S.toSubmodule :=
    e.symm.toLinearMap.restrict (fun y hy => hy)
  have hr : ∀ (g : G) (y : S'.toSubmodule),
      r (S'.toRepresentation g y) = S.toRepresentation g (r y) := by
    intro g y
    apply Subtype.ext
    exact key g y
  refine ⟨S', ⟨f.toLinearMap ∘ₗ r, fun g => LinearMap.ext fun y => ?_⟩, ?_⟩
  · change f.toLinearMap (r (S'.toRepresentation g y)) = π g (f.toLinearMap (r y))
    rw [hr]
    exact Representation.IntertwiningMap.isIntertwining _ _ f g (r y)
  · intro w
    obtain ⟨x, rfl⟩ := hf w
    have hx : e.symm.toLinearMap (e x) ∈ S.toSubmodule := by
      change e.symm (e x) ∈ S.toSubmodule
      rw [Representation.Equiv.symm_apply_apply]
      exact x.2
    refine ⟨⟨e x, hx⟩, ?_⟩
    change f.toLinearMap (r ⟨e x, hx⟩) = f.toLinearMap x
    congr 1
    apply Subtype.ext
    exact e.symm_apply_apply (x : U)

/-- A common character twist preserves the subquotient relation. -/
theorem isSubquotientOf_twist {ρ : Representation ℂ G U} {π : Representation ℂ G W}
    (χ : G →* ℂˣ) (h : IsSubquotientOf ρ π) :
    IsSubquotientOf (Langlands.twist χ ρ) (Langlands.twist χ π) := by
  obtain ⟨S, f, hf⟩ := h
  let S' : Subrepresentation (Langlands.twist χ ρ) :=
    ⟨S.toSubmodule, fun g v hv => by
      change ((χ g : ℂˣ) : ℂ) • ρ g v ∈ S.toSubmodule
      exact S.toSubmodule.smul_mem _ (S.apply_mem_toSubmodule g hv)⟩
  refine ⟨S', ⟨f.toLinearMap, fun g => LinearMap.ext fun y => ?_⟩, hf⟩
  have h1 : S'.toRepresentation g y = ((χ g : ℂˣ) : ℂ) • S.toRepresentation g y := rfl
  change f.toLinearMap (S'.toRepresentation g y) = ((χ g : ℂˣ) : ℂ) • π g (f.toLinearMap y)
  rw [h1, map_smul]
  congr 1
  exact Representation.IntertwiningMap.isIntertwining _ _ f g y

end Subquotient

section PrincipalSeries

variable {p : ℕ} [Fact p.Prime] (K : PadicField.{u} p)

/-- A quasi-character as a smooth character of `K^×`. -/
def quasiSmoothCharacter (η : QuasiCharacter K) :
    letI := K.canonicalTopologicalData.topology
    Induction.SmoothCharacter ℂ K.Carrierˣ :=
  letI := K.canonicalTopologicalData.topology
  ⟨η.toMonoidHom, RankinSelberg.quasicharacter_isOpen_ker K.canonicalTopologicalData η⟩

/-- The twist of the rank-one block `μ ∘ det` by `η ∘ det` is `(μ η) ∘ det`. -/
def characterBlockTwistEquiv (μ η : QuasiCharacter K) :
    (Langlands.twist (determinantQuasiCharacter K 1 η)
      (characterRepresentation (determinantQuasiCharacter K 1 μ))).Equiv
      (characterRepresentation (determinantQuasiCharacter K 1 (μ * η))) :=
  Representation.Equiv.mk (LinearEquiv.refl ℂ ℂ) fun g => by
    apply LinearMap.ext
    intro v
    change ((η (GeneralLinear.determinant g) : ℂˣ) : ℂ) •
        (((μ (GeneralLinear.determinant g) : ℂˣ) : ℂ) • v) =
      ((μ (GeneralLinear.determinant g) * η (GeneralLinear.determinant g) : ℂˣ) : ℂ) • v
    rw [smul_smul, Units.val_mul, mul_comm]

/-- The determinant twist of a normalized principal series by `η` is the principal series of
the twisted characters. -/
def principalSeriesTwistEquiv {r : ℕ} (μ : Fin (r + 1) → QuasiCharacter K)
    (η : QuasiCharacter K) :
    (Langlands.twist (determinantQuasiCharacter K r.succPNat η)
      (principalSeries K r μ)).Equiv (principalSeries K r (fun i => μ i * η)) :=
  (K.canonicalTopologicalData.normalizedProductDeterminantTwistEquiv (borelShape r)
    (quasiSmoothCharacter K η) _).trans
    (K.canonicalTopologicalData.normalizedProductInducedEquiv (borelShape r)
      (fun i => characterBlockTwistEquiv K (μ i) η))

/-- **Twisted generic constituent.** If `π` has a generic representative that is a subquotient of
`i(μ)`, then every twist of `π` by `η` has a generic representative that is a subquotient of
`i(μ η)`. -/
theorem exists_generic_subquotient_twist {r : ℕ} (ψ : NontrivialAdditiveCharacter K)
    (μ : Fin (r + 1) → QuasiCharacter K) (η : QuasiCharacter K)
    {π πη : AutomorphicClass.{u, u} K r.succPNat}
    (hπ : ∃ A : AutomorphicObject.{u, u} K r.succPNat,
      automorphicClassOf K A = π ∧
        (letI := K.canonicalTopologicalData.topology
         letI := K.canonicalGeneralLinearTopology (r + 1)
         Whittaker.IsGeneric ψ r A.obj.representation ∧
           IsSubquotientOf (principalSeries K r μ) A.obj.representation))
    (htw : IsCharacterTwist K η π πη) :
    ∃ B : AutomorphicObject.{u, u} K r.succPNat,
      automorphicClassOf K B = πη ∧
        (letI := K.canonicalTopologicalData.topology
         letI := K.canonicalGeneralLinearTopology (r + 1)
         Whittaker.IsGeneric ψ r B.obj.representation ∧
           IsSubquotientOf (principalSeries K r (fun i => μ i * η)) B.obj.representation) := by
  let := K.canonicalTopologicalData.topology
  let := K.canonicalGeneralLinearTopology (r + 1)
  obtain ⟨A, rfl, hgen, hsub⟩ := hπ
  obtain ⟨A', B, hA', rfl, ⟨e⟩⟩ := htw
  obtain ⟨e'⟩ := (automorphicClassOf_eq_iff K A' A).mp hA'
  let f : (Langlands.twist (determinantQuasiCharacter K r.succPNat η)
      A.obj.representation).Equiv B.obj.representation :=
    (Langlands.twistEquiv _ e'.symm).trans e
  refine ⟨B, rfl, ?_, ?_⟩
  · exact (Whittaker.isGeneric_iff_of_equiv ψ r f).mp
      (RankinSelberg.isGeneric_quasicharacter_twist K.canonicalTopologicalData ψ η hgen)
  · exact (Unramified.isSubquotientOf_iff_of_equiv f).mp
      (isSubquotientOf_of_equiv_left (principalSeriesTwistEquiv K μ η)
        (isSubquotientOf_twist _ hsub))

end PrincipalSeries

end Langlands.Correspondence

namespace Langlands.Unramified

open Correspondence

attribute [local instance] heckeFieldTopology heckeGeneralLinearTopology

/-- A spherical Hecke spectrum of an irreducible admissible object is realized by an
unramified principal series having the object as a spherical subquotient. -/
theorem hasSphericalSpectrum_of_hasSphericalHeckeSpectrum {p : ℕ} [Fact p.Prime]
    (F : PadicField.{u} p) {r : ℕ} (A : AutomorphicObject.{u, uW} F r.succPNat)
    (s : Eigenvalues (r + 1)) (hs : HasSphericalHeckeSpectrum F A s) :
    HasSphericalSpectrum F A s := by
  obtain ⟨z, hz⟩ := Eigenvalues.ofTuple_surjective (r + 1) s
  obtain ⟨B, hB⟩ := SphericalExistence.sphericalConstituentExistence p F r z
  have hBs : HasSphericalHeckeSpectrum F B s := by
    rw [← hz]
    exact sphericalConstituentHeckeScalar p F r z B hB
  obtain ⟨e⟩ := sphericalHeckeSpectrumDetermination p F r A B s hs hBs
  exact ⟨z, hz, (isSphericalConstituent_iff_of_equiv F z e).mpr hB⟩

end Langlands.Unramified
