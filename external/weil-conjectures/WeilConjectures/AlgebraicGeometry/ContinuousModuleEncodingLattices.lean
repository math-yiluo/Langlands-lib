/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientModuleEncoding
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.LocallyFree
import WeilConjectures.AlgebraicGeometry.ContinuousModuleEncodingLocalFreeness
import WeilConjectures.AlgebraicGeometry.ContinuousModuleEncodingScalarExtension
import WeilConjectures.AlgebraicGeometry.ContinuousModuleEncodingRestriction

/-! # Lattice compatibility of the continuous module encoding

Source: Stacks Project, Modules on Sites, and Bhatt--Scholze, Section 6.8.
(auxiliary; not a blueprint node)
-/

@[expose] public section

universe u
open CategoryTheory
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The explicit continuous module encodings preserve local finite freeness and
translate any specified etale lattice and its rationalization back to internal modules.

Source: Stacks Project, Modules on Sites, Tags 03DM (local finite freeness),
03DO (pullback), 03D7 (adjunction), 03EK and 03EL (tensor and pullback);
Bhatt--Scholze, Definition 6.8.3 and Proposition 6.8.4(6).
(auxiliary; not a blueprint node)

Proof in words. A finite free internal module is a finite biproduct of the regular
module. The proved continuousFieldFreeIso and continuousIntegerFreeIso give the
corresponding sectionwise free modules, including the coefficient identifications.
The existing finiteLocallyFree_restrict transports local freeness along those
coefficient-ring isomorphisms.
On the slice over a pro-etale chart, the sectionwise encoding of inverse image
is restriction of the encoded sheaf. This follows from the inverse-image adjunction
and the unchanged underlying sheaf in sectionModuleEquivalence.
The proved continuousChart_pullback identifies its coefficient comparison with
condensedPullbackHom, using the adjoint form of
continuousChart_scheme_naturality and the pullback projection on sections.
The supplied free cover therefore gives finite locally free generators for the
encoded rational module.
Conversely, a sectionwise finite free trivialization on a covering slice transports
back through the inverse integral equivalence, and the comparison with inverse
image gives a pro-etale free cover of that internal module. Covers of the terminal
object can be replaced by the pro-etale precoverage since it generates the topology.
For rationalization, extension of scalars in both encodings is left adjoint to
restriction of scalars. The coefficient square commutes by chartComparison_naturality,
with lisseScalar_square for the integral and spectral coefficient identifications.
The proved continuousRing_comap_compatibility compares restriction of scalars
for the full continuous encodings, using sectionModuleComapIso at the reconstructed-ring
stage. Transport it further through the spectral and integral coefficient identifications.
Uniqueness of left adjoints supplies the scalar-extension comparison. Restriction
along an etale arrow is inverse image on the small pro-etale sites. Its analogous
adjunction comparison identifies the right side of the specified lattice isomorphism
with the encoding of the canonical internal pullback. Transport that isomorphism
back through the fully faithful rational encoding and use the counit of the integral
equivalence. This asserts compatibility for an already supplied lattice; it does
not assert that any lattice or etale neighborhood exists. Empty and zero-rank
trivializations remain empty and zero-rank under these equivalences. -/
theorem continuousModuleEncoding_lattice_compatibility
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E]
    [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]
    (X : Scheme.{u})
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) X))
    (hP : IsLocallyFree (condensedRingObj (Profinite.continuousMapRingObj E) X) P) :
    ((continuousFieldModuleEquivalence ℓ E X).functor.obj P).IsFiniteLocallyFree ∧
    ∀ (Y : Scheme.{u}) (f : Y ⟶ X) [Etale f]
      (M : ringedSiteModules.{u + 1} ((sheafCompose (Scheme.ProEt.topology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (lisseIntegerSheaf ℓ E Y))),
      M.IsFiniteLocallyFree →
      Nonempty ((SheafOfModules.changeOfRings (lisseIntegerToField ℓ E Y) M).val ≅
        (PresheafOfModules.pushforward (lisseEtaleCoefficientIdentification ℓ E f)).obj
          ((continuousFieldModuleEquivalence ℓ E X).functor.obj P).val) →
      IsLocallyFree (condensedRingObj (integralCoeff ℓ E) Y)
        ((continuousIntegerModuleEquivalence ℓ E Y).inverse.obj M) ∧
      Nonempty ((Mod.extendScalars (coefficientMap (integralScalarMap ℓ E) Y)).obj
          ((continuousIntegerModuleEquivalence ℓ E Y).inverse.obj M) ≅
        (upperStar (Profinite.continuousMapRingObj E) f).obj P) := by
  refine ⟨continuousField_locallyFree ℓ E X P hP, ?_⟩
  intro Y f _ M hM hα
  let : M.IsFiniteLocallyFree := hM
  refine ⟨continuousInteger_inverse_locallyFree ℓ E Y M, ?_⟩
  obtain ⟨eS⟩ := continuousModuleEncoding_scalar_extension ℓ E Y M
  obtain ⟨eR⟩ := continuousField_module_restriction ℓ E X Y f P
  obtain ⟨eα⟩ := hα
  let F := continuousFieldModuleEquivalence ℓ E Y
  refine ⟨F.fullyFaithfulFunctor.preimageIso ?_⟩
  exact eS ≪≫ (SheafOfModules.fullyFaithfulForget _).preimageIso (eα ≪≫ eR.symm)

end AlgebraicGeometry.ProEtale.CondensedRing
