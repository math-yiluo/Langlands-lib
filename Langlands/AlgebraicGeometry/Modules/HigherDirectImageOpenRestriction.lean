import Langlands.AlgebraicGeometry.Modules.DerivedRestrictionVanishing
import Langlands.AlgebraicGeometry.Modules.OpenCohomologyVanishing
import Langlands.AlgebraicGeometry.Modules.PushforwardComparison
import Langlands.Cohomology.LeftExactHomology

/-!
# Higher direct images and restriction to an open of the base

For a morphism of schemes `f : X ⟶ Y` and an open `V` of `Y`, the higher direct images of the
restriction of `M` to `f⁻¹ V` along `f ∣_ V` are the restrictions to `V` of the higher direct
images of `M` along `f`:
`Rⁿ (f ∣_ V)_* (M|_{f⁻¹ V}) ≅ (Rⁿ f_* M)|_V`.

The proof uses the composite comparison `compComparison` for the factorization
`(f ∣_ V)_* ∘ ρ_{f⁻¹ V} ≅ ρ_V ∘ f_*`. Restriction to `f⁻¹ V` is exact and sends injective
modules to flasque modules, which are `(f ∣_ V)_*`-acyclic. Restriction to `V` is exact, so it
commutes with the right derived functors of `f_*`.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.Cohomology Langlands.Cohomology.AcyclicResolution

namespace Langlands.AlgebraicGeometry.Modules.DerivedSections

section Exact

variable {A : Type*} [Category* A] [Abelian A] [HasInjectiveResolutions A]
  {B : Type*} [Category* B] [Abelian B]

/-- The positive right derived functors of a homology-preserving functor vanish. -/
lemma isZero_rightDerived_succ_of_preservesHomology (F : A ⥤ B) [F.Additive]
    [F.PreservesHomology] (N : A) (q : ℕ) : IsZero ((F.rightDerived (q + 1)).obj N) := by
  let I := injectiveResolution N
  refine IsZero.of_iso ?_ (I.isoRightDerivedObj F (q + 1))
  apply HomologicalComplex.ExactAt.isZero_homology
  have h := I.cocomplex_exactAt_succ q
  rw [HomologicalComplex.exactAt_iff] at h ⊢
  exact h.map F

end Exact

section OpenRestriction

variable {X Y : Scheme.{u}}

/-- Restriction along an open immersion is additive, since it is isomorphic to pullback. -/
instance additive_restrictFunctor {U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (Scheme.Modules.restrictFunctor j).Additive :=
  Functor.additive_of_iso (Scheme.Modules.restrictFunctorIsoPullback j).symm

/-- Restriction along an open immersion preserves homology. -/
lemma preservesHomology_restrictFunctor {U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (Scheme.Modules.restrictFunctor j).PreservesHomology := by
  have : PreservesFiniteLimits (Scheme.Modules.restrictFunctor j) :=
    OpenCohomologyVanishing.preservesFiniteLimits_pushforward _
  exact Functor.preservesHomology_of_preservesEpis_and_kernels _

variable (f : X ⟶ Y) (V : Y.Opens)

/-- The opens `f⁻¹ (V.ι '' W)` and `(f⁻¹ V).ι '' ((f ∣_ V)⁻¹ W)` of `X` agree, for every open
`W` of `V`. -/
def restrictPushforwardOpensIso :
    V.ι.opensFunctor ⋙ TopologicalSpace.Opens.map f.base ≅
      TopologicalSpace.Opens.map (f ∣_ V).base ⋙ (f ⁻¹ᵁ V).ι.opensFunctor :=
  NatIso.ofComponents (fun W => eqToIso (image_morphismRestrict_preimage f V W).symm)

set_option backward.isDefEq.respectTransparency false in
/-- Restriction to `f⁻¹ V` followed by pushforward along `f ∣_ V` is pushforward along `f`
followed by restriction to `V`. Both sides are pushforwards along composite functors of opens; the
isomorphism compares them along `restrictPushforwardOpensIso`. -/
def restrictPushforwardIso :
    Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι ⋙ Scheme.Modules.pushforward (f ∣_ V) ≅
      Scheme.Modules.pushforward f ⋙ Scheme.Modules.restrictFunctor V.ι := by
  refine SheafOfModules.pushforwardComp _ _ ≪≫ ?_ ≪≫ (SheafOfModules.pushforwardComp _ _).symm
  refine SheafOfModules.pushforwardCongr₂ _ (restrictPushforwardOpensIso f V) ?_
  ext : 3
  rename_i W
  obtain ⟨W⟩ := W
  simp only [Scheme.Hom.toRingCatSheafHom, restrictPushforwardOpensIso, Scheme.Opens.ι_appIso]
  simp
  ext x
  change (f.appLE (V.ι ''ᵁ W) _ _ ≫ X.presheaf.map _) x = f.app (V.ι ''ᵁ W) x
  rw [Scheme.Hom.appLE_map, Scheme.Hom.appLE_eq_app]

/-- Restriction to `f⁻¹ V` has vanishing positive right derived functors. -/
lemma isZero_rightDerived_restrictFunctor (M : X.Modules) (q : ℕ) :
    IsZero (((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).rightDerived (q + 1)).obj M) :=
  haveI := preservesHomology_restrictFunctor (f ⁻¹ᵁ V).ι
  isZero_rightDerived_succ_of_preservesHomology _ M q

/-- The restriction to `f⁻¹ V` of an injective module has vanishing positive higher direct
images along `f ∣_ V`: it is flasque. -/
lemma isZero_higherDirectImage_restrict_of_injective (J : X.Modules) [Injective J] (q : ℕ) :
    IsZero ((higherDirectImage (f ∣_ V) (q + 1)).obj
      ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj J)) :=
  haveI := PushforwardInjectiveAcyclic.isFlasque_of_injective J
  haveI := OpenCohomologyVanishing.isFlasque_restrict (f ⁻¹ᵁ V) J
  isZero_higherDirectImage_of_isFlasque (f ∣_ V) q _

/-- **Open restriction of higher direct images.** For every `𝒪_X`-module `M` and every `n`,
`Rⁿ (f ∣_ V)_* (M|_{f⁻¹ V}) ≅ (Rⁿ f_* M)|_V`. It is the inverse of the composite comparison
`compComparison` for `restrictPushforwardIso`, followed by the comparison
`LeftExactHomology.derivedNatTrans` of the exact functor `ρ_V` with `Rⁿ f_*`. -/
def higherDirectImageRestrictIso (M : X.Modules) (n : ℕ) :
    (higherDirectImage (f ∣_ V) n).obj ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj M) ≅
      (Scheme.Modules.restrictFunctor V.ι).obj ((higherDirectImage f n).obj M) :=
  haveI := isIso_compComparison (Scheme.Modules.pushforward (f ∣_ V)) (restrictPushforwardIso f V)
    M (isZero_rightDerived_restrictFunctor f V M)
    (fun J _ q => isZero_higherDirectImage_restrict_of_injective f V J q) n
  haveI := preservesHomology_restrictFunctor V.ι
  haveI := LeftExactHomology.isIso_derivedNatTrans (Scheme.Modules.restrictFunctor V.ι)
    (Scheme.Modules.pushforward f) n
  (asIso (compComparison (Scheme.Modules.pushforward (f ∣_ V)) (restrictPushforwardIso f V) M
      (isZero_rightDerived_restrictFunctor f V M) n)).symm ≪≫
    (asIso (LeftExactHomology.derivedNatTrans (Scheme.Modules.restrictFunctor V.ι)
      (Scheme.Modules.pushforward f) n)).app M

/-- If the restriction of `Rⁿ f_* M` to `V` vanishes, then `Rⁿ (f ∣_ V)_* (M|_{f⁻¹ V})`
vanishes. -/
theorem isZero_higherDirectImage_restrict_of_isZero_restrict (M : X.Modules) (n : ℕ)
    (hM : IsZero ((Scheme.Modules.restrictFunctor V.ι).obj ((higherDirectImage f n).obj M))) :
    IsZero ((higherDirectImage (f ∣_ V) n).obj
      ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj M)) :=
  hM.of_iso (higherDirectImageRestrictIso f V M n)

/-- If `Rⁿ f_* M` vanishes, then `Rⁿ (f ∣_ V)_* (M|_{f⁻¹ V})` vanishes. -/
theorem isZero_higherDirectImage_restrict (M : X.Modules) (n : ℕ)
    (hM : IsZero ((higherDirectImage f n).obj M)) :
    IsZero ((higherDirectImage (f ∣_ V) n).obj
      ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj M)) :=
  isZero_higherDirectImage_restrict_of_isZero_restrict f V M n
    ((Scheme.Modules.restrictFunctor V.ι).map_isZero hM)

/-- The same vanishing for the pullback of `M` along `(f⁻¹ V).ι`, which is isomorphic to the
restriction. -/
theorem isZero_higherDirectImage_pullback (M : X.Modules) (n : ℕ)
    (hM : IsZero ((higherDirectImage f n).obj M)) :
    IsZero ((higherDirectImage (f ∣_ V) n).obj
      ((Scheme.Modules.pullback (f ⁻¹ᵁ V).ι).obj M)) :=
  (isZero_higherDirectImage_restrict f V M n hM).of_iso
    ((higherDirectImage (f ∣_ V) n).mapIso
      ((Scheme.Modules.restrictFunctorIsoPullback (f ⁻¹ᵁ V).ι).app M)).symm

end OpenRestriction

end Langlands.AlgebraicGeometry.Modules.DerivedSections
