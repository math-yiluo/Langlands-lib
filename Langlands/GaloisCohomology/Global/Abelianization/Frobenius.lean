import Langlands.GaloisCohomology.Global.Abelianization
import Langlands.GaloisCohomology.Global.Abelianization.Presentation
import Langlands.Galois.FiniteHeckeAvatarLiftProof

/-!
# Characters of `G_S` at the places outside `S`: inertia and Frobenius

For a number field `K`, a separable closure `Ω`, a finite set `S` of finite places and `n ≠ 0`,
this file describes a continuous character `χ : G_S → ℤ/n` at a finite place `v ∉ S` in the
Library's local vocabulary (`Langlands.GaloisRepresentation`: the absolute Galois group
`LocalGroup v` of `K_v`, its inertia group `localInertia v`, geometric Frobenius lifts
`IsGeometricFrobeniusLift v`, and `localToGlobalGalois v`, Mathlib's
`Field.absoluteGaloisGroup.map` for the completion):

* `χ` is trivial on the image of `localInertia v`
  (`apply_quotientMap_autCongr_localToGlobalGalois_of_mem_localInertia`);
* at a uniformizer `π` of `K_v`, the character `continuousCharEquivNarrowSIdeleClass Ω hS n χ` of
  the narrow `S`-idèle class group takes the value of `χ` at the image of any geometric Frobenius
  lift (`continuousCharEquivNarrowSIdeleClass_finiteIdeleInclusion_of_isGeometricFrobeniusLift`),
  and likewise `continuousCharEquivSIdeleClass`, in particular on the generator of the divisors
  prime to `S` at `v` in the presentation `sPresentation`
  (`continuousCharEquivSIdeleClass_sPresentation_one_single`).

Elements of `Gal(AlgebraicClosure K / K)` are carried to `Gal(Ω / K)` by an arbitrary isomorphism
`f : AlgebraicClosure K ≃ₐ[K] Ω`; the values of `χ` do not depend on `f`
(`apply_quotientMap_autCongr_eq`).

**Proof.** The character of the idèle classes attached to `χ` (`ideleClassCharacter`) is trivial
on the local units outside `S`, so by `exists_matchesGeometricArtinOutside` (from the Library's
`finiteAbelianClassFieldExistence`, `finiteArtinUnramifiedCriterion` and
`finiteUnramifiedGaloisRestriction`) it has a lift to the absolute Galois group that is trivial on
inertia and takes geometric Frobenius lifts to the values at uniformizers outside `S`. By
`MatchesGeometricArtinOutside.apply_eq_of_geometricArtinMap` that lift takes at every `σ` the
value at `x` of the idèle-class character whenever `σ` lifts `geometricArtinMap K x`, which is also
the value of `χ` at `σ|_{K_S}`; since the Artin map is surjective, the lift is `χ` read on the
absolute Galois group (`matchesGeometricArtinOutside_absoluteCharacter`).

## References

Neukirch, *Algebraic Number Theory*, Chapter VI, Proposition (5.6), p. 391 (compatibility of
local and global reciprocity); Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*,
Chapter VIII, §3, p. 460 (images of the local groups and of the units under the reciprocity map).
-/

noncomputable section

universe u v

namespace Langlands.GaloisCohomology

open Langlands.Global Langlands.Galois Langlands.ClassFieldTheory.Global.Artin
  Langlands.GaloisRepresentation IsDedekindDomain
open scoped NumberField

variable {K : Type u} [Field K] [NumberField K] {Ω : Type v} [Field Ω] [Algebra K Ω]
  {S : Set (HeightOneSpectrum (𝓞 K))} {n : ℕ}

/-- The value of a character of `G_S` on the restriction of an automorphism of
`AlgebraicClosure K` carried to `Ω` by an isomorphism does not depend on the isomorphism. -/
theorem apply_quotientMap_autCongr_eq [IsGalois K Ω]
    (χ : GaloisGroupUnramifiedOutside K Ω S →ₜ* Multiplicative (ZMod n))
    (f f' : AlgebraicClosure K ≃ₐ[K] Ω) (τ : Gal(AlgebraicClosure K/K)) :
    χ (GaloisGroupUnramifiedOutside.quotientMap K Ω S (f.autCongr τ)) =
      χ (GaloisGroupUnramifiedOutside.quotientMap K Ω S (f'.autCongr τ)) := by
  have h : f.autCongr τ = (f'.symm.trans f) * f'.autCongr τ * (f'.symm.trans f)⁻¹ := by
    ext x
    simp [AlgEquiv.autCongr_apply, AlgEquiv.mul_apply]
  rw [h, map_mul, map_mul, map_inv, map_mul, map_mul, map_inv, mul_inv_cancel_comm]

variable [NeZero n]

/-- The idèle-class character attached to a continuous character of `G_S(AlgebraicClosure K)`,
as a continuous homomorphism. -/
def ideleClassCharacter
    (χ : GaloisGroupUnramifiedOutside K (AlgebraicClosure K) S →ₜ* Multiplicative (ZMod n)) :
    IdeleClasses K →ₜ* Multiplicative (ZMod n) :=
  (LocalClassField.abelianizationLift
    (show Field.absoluteGaloisGroup K →ₜ* Multiplicative (ZMod n) from
      absoluteCharacter χ)).comp (geometricArtinMap K)

/-- On the class of an idèle, `ideleClassCharacter χ` is `narrowSIdeleClassCharacter χ`. -/
theorem ideleClassCharacter_ideleClassMap
    (χ : GaloisGroupUnramifiedOutside K (AlgebraicClosure K) S →ₜ* Multiplicative (ZMod n))
    (x : Ideles K) :
    ideleClassCharacter χ (ideleClassMap K x) = narrowSIdeleClassCharacter χ
      (NarrowSIdeleClassGroup.mk S x) :=
  rfl

/-- A continuous character of `G_S(AlgebraicClosure K)`, read on the absolute Galois group,
matches its idèle-class character outside `S` in the sense of `MatchesGeometricArtinOutside`:
it is trivial on local inertia at every finite place outside `S`, and its value at a geometric
Frobenius lift is the value of the idèle-class character at a uniformizer. By uniqueness of
the lift (`exists_matchesGeometricArtinOutside`, `MatchesGeometricArtinOutside.unique`,
`MatchesGeometricArtinOutside.apply_eq_of_geometricArtinMap`). -/
theorem matchesGeometricArtinOutside_absoluteCharacter (hS : S.Finite)
    (χ : GaloisGroupUnramifiedOutside K (AlgebraicClosure K) S →ₜ* Multiplicative (ZMod n)) :
    MatchesGeometricArtinOutside hS.toFinset (ideleClassCharacter χ)
      (show Field.absoluteGaloisGroup K →ₜ* Multiplicative (ZMod n) from absoluteCharacter χ) := by
  have hT : ∀ v ∉ hS.toFinset, IsTrivialOnLocalUnits (ideleClassCharacter χ) v := by
    intro v hv a ha
    exact ideleCharacter_finiteIdeleInclusion χ (fun h => hv (hS.mem_toFinset.2 h)) ha
  obtain ⟨ψ, hψ⟩ := exists_matchesGeometricArtinOutside finiteAbelianClassFieldExistence
    finiteArtinUnramifiedCriterion finiteUnramifiedGaloisRestriction (ideleClassCharacter χ)
    hS.toFinset hT
  have heq : ψ = (show Field.absoluteGaloisGroup K →ₜ* Multiplicative (ZMod n) from
      absoluteCharacter χ) := by
    ext σ
    obtain ⟨c, hc⟩ := geometricArtinMap_surjective K
      (LocalClassField.absoluteAbelianizationProjection K σ)
    rw [hψ.apply_eq_of_geometricArtinMap c σ hc.symm]
    change LocalClassField.abelianizationLift
      (show Field.absoluteGaloisGroup K →ₜ* Multiplicative (ZMod n) from absoluteCharacter χ)
        (geometricArtinMap K c) = _
    rw [hc]
    rfl
  rw [← heq]
  exact hψ

section SeparableClosure

variable [IsSepClosure K Ω]

omit [NeZero n] in
/-- A continuous character of `G_S(Ω)`, transported to `G_S(AlgebraicClosure K)` as in
`continuousCharEquivNarrowSIdeleClass`, read on `Gal(AlgebraicClosure K / K)`: it is the
character on `Gal(Ω / K)` carried by any isomorphism `f : AlgebraicClosure K ≃ₐ[K] Ω`. -/
theorem absoluteCharacter_continuousCharCongr
    (χ : ContinuousMonoidHom (GaloisGroupUnramifiedOutside K Ω S) (Multiplicative (ZMod n)))
    (f : AlgebraicClosure K ≃ₐ[K] Ω) (τ : Gal(AlgebraicClosure K/K)) :
    absoluteCharacter (continuousCharCongr
        (galoisGroupUnramifiedOutsideCongr S (IsSepClosure.equiv K (AlgebraicClosure K) Ω)) n χ) τ =
      χ (GaloisGroupUnramifiedOutside.quotientMap K Ω S (f.autCongr τ)) := by
  rw [absoluteCharacter_apply, continuousCharCongr_apply,
    galoisGroupUnramifiedOutsideCongr_quotientMap]
  exact apply_quotientMap_autCongr_eq χ _ f τ

/-- **Inertia.** For finite `S`, a continuous character of `G_S` with values in `ℤ/n` is trivial on
the image of the local inertia group at every finite place outside `S` (the local Galois group
of `K_v` mapped to `Gal(AlgebraicClosure K / K)` by Mathlib's `Field.absoluteGaloisGroup.map`,
then to `Gal(Ω / K)` by any isomorphism `f`). -/
theorem apply_quotientMap_autCongr_localToGlobalGalois_of_mem_localInertia (hS : S.Finite)
    (χ : ContinuousMonoidHom (GaloisGroupUnramifiedOutside K Ω S) (Multiplicative (ZMod n)))
    (f : AlgebraicClosure K ≃ₐ[K] Ω) {v : FinitePlace K} (hv : v ∉ S) (i : localInertia v) :
    χ (GaloisGroupUnramifiedOutside.quotientMap K Ω S
      (f.autCongr (localToGlobalGalois v i.val))) = 1 := by
  refine (absoluteCharacter_continuousCharCongr χ f (localToGlobalGalois v i.val)).symm.trans ?_
  exact ((matchesGeometricArtinOutside_absoluteCharacter hS _) v
    (fun h => hv (hS.mem_toFinset.1 h))).1 i

/-- **Frobenius.** For finite `S`, a finite place `v ∉ S`, a uniformizer `π` of `K_v` and a
geometric Frobenius lift `g` at `v`, the character of the narrow `S`-idèle class group attached
to a continuous character `χ` of `G_S` takes at the class of `π` the value of `χ` at the image of
`g`. -/
theorem continuousCharEquivNarrowSIdeleClass_finiteIdeleInclusion_of_isGeometricFrobeniusLift
    (hS : S.Finite)
    (χ : ContinuousMonoidHom (GaloisGroupUnramifiedOutside K Ω S) (Multiplicative (ZMod n)))
    (f : AlgebraicClosure K ≃ₐ[K] Ω) {v : FinitePlace K} (hv : v ∉ S)
    (π : (FiniteCompletion K v)ˣ) (hπ : Valued.v (π : FiniteCompletion K v) = WithZero.exp (-1 : ℤ))
    (g : LocalGroup v) (hg : IsGeometricFrobeniusLift v g) :
    continuousCharEquivNarrowSIdeleClass Ω hS n χ
        (NarrowSIdeleClassGroup.mk S (finiteIdeleInclusion K v π)) =
      χ (GaloisGroupUnramifiedOutside.quotientMap K Ω S
        (f.autCongr (localToGlobalGalois v g))) := by
  refine Eq.trans ?_ (absoluteCharacter_continuousCharCongr χ f (localToGlobalGalois v g))
  change ideleClassCharacter _ (finiteClassInclusion K v π) = _
  exact (((matchesGeometricArtinOutside_absoluteCharacter hS _) v
    (fun h => hv (hS.mem_toFinset.1 h))).2 π hπ g hg).symm

/-- **Frobenius**, for `continuousCharEquivSIdeleClass`. -/
theorem continuousCharEquivSIdeleClass_finiteIdeleInclusion_of_isGeometricFrobeniusLift
    (hS : S.Finite) (h : Odd n ∨ NumberField.IsTotallyComplex K)
    (χ : ContinuousMonoidHom (GaloisGroupUnramifiedOutside K Ω S) (Multiplicative (ZMod n)))
    (f : AlgebraicClosure K ≃ₐ[K] Ω) {v : FinitePlace K} (hv : v ∉ S)
    (π : (FiniteCompletion K v)ˣ) (hπ : Valued.v (π : FiniteCompletion K v) = WithZero.exp (-1 : ℤ))
    (g : LocalGroup v) (hg : IsGeometricFrobeniusLift v g) :
    continuousCharEquivSIdeleClass Ω hS h χ (SIdeleClassGroup.mk S (finiteIdeleInclusion K v π)) =
      χ (GaloisGroupUnramifiedOutside.quotientMap K Ω S
        (f.autCongr (localToGlobalGalois v g))) := by
  rw [← NarrowSIdeleClassGroup.precompToSIdeleClassGroup_apply_mk,
    precompToSIdeleClassGroup_continuousCharEquivSIdeleClass,
    continuousCharEquivNarrowSIdeleClass_finiteIdeleInclusion_of_isGeometricFrobeniusLift hS χ f
      hv π hπ g hg]

/-- **Frobenius**, on the presentation of the `S`-idèle class group: the generator of the
divisors prime to `S` at `v ∉ S` corresponds to a geometric Frobenius at `v`. -/
theorem continuousCharEquivSIdeleClass_sPresentation_one_single [Finite S]
    (h : Odd n ∨ NumberField.IsTotallyComplex K)
    (χ : ContinuousMonoidHom (GaloisGroupUnramifiedOutside K Ω S) (Multiplicative (ZMod n)))
    (f : AlgebraicClosure K ≃ₐ[K] Ω) {v : FinitePlace K} (hv : v ∉ S)
    (g : LocalGroup v) (hg : IsGeometricFrobeniusLift v g) :
    continuousCharEquivSIdeleClass Ω (Set.toFinite S) h χ
        (sPresentation S (1, Multiplicative.ofAdd (Finsupp.single ⟨v, hv⟩ 1))) =
      χ (GaloisGroupUnramifiedOutside.quotientMap K Ω S
        (f.autCongr (localToGlobalGalois v g))) := by
  rw [sPresentation_one_single, zpow_one]
  exact continuousCharEquivSIdeleClass_finiteIdeleInclusion_of_isGeometricFrobeniusLift
    (Set.toFinite S) h χ f hv (localUniformizer v) (valued_localUniformizer v) g hg

end SeparableClosure

end Langlands.GaloisCohomology
