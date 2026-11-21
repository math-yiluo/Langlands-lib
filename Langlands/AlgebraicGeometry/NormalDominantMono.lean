import Langlands.AlgebraicGeometry.Picard.ValuationBaseNormality
import Langlands.AlgebraicGeometry.ProperOfFibres.MonoNormalization

/-! # Dominant monomorphisms into normal integral schemes -/

set_option autoImplicit false

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory

namespace Langlands.AlgebraicGeometry

private theorem isIntegrallyClosed_affineSections_of_hasNormalStalks
    {Y : Scheme.{u}} [IsIntegral Y] (hY : HasNormalStalks Y)
    {U : Y.Opens} (hU : IsAffineOpen U) [Nonempty U] :
    IsIntegrallyClosed Γ(Y, U) := by
  apply IsIntegrallyClosed.of_localization_maximal
  intro p _ hp
  let y : PrimeSpectrum Γ(Y, U) := ⟨p, hp.isPrime⟩
  have hy : hU.fromSpec y ∈ U := hU.range_fromSpec.le ⟨y, rfl⟩
  let : Algebra Γ(Y, U) (Y.presheaf.stalk (hU.fromSpec y)) :=
    TopCat.Presheaf.algebra_section_stalk Y.presheaf ⟨hU.fromSpec y, hy⟩
  have : IsLocalization.AtPrime (Y.presheaf.stalk (hU.fromSpec y)) p :=
    hU.isLocalization_stalk' y hy
  let e := IsLocalization.algEquiv p.primeCompl
    (Y.presheaf.stalk (hU.fromSpec y)) (Localization.AtPrime p)
  exact (hY (hU.fromSpec y)).2.of_equiv e.toRingEquiv

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y)
  [Mono f] [LocallyOfFiniteType f] [QuasiCompact f] [IsDominant f]

set_option backward.isDefEq.respectTransparency false in
private theorem isIso_fromNormalization_of_hasNormalStalks (hY : HasNormalStalks Y) :
    IsIso f.fromNormalization := by
  have hη : f (genericPoint X) = genericPoint Y := by
    apply IsGenericPoint.eq _ (genericPoint_spec Y)
    simpa only [Set.image_univ, f.denseRange.closure_range] using
      (genericPoint_spec X).image f.continuous
  refine (IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := .isomorphisms _) _
    (iSup_affineOpens_eq_top Y)).mpr fun U => ?_
  change IsIso (f.fromNormalization ∣_ U.1)
  by_cases hU : Nonempty U.1
  · rw [isIso_morphismRestrict_iff_isIso_app _ U.2, f.fromNormalization_app U.2]
    let A := Γ(Y, U.1)
    let V := f ⁻¹ᵁ U.1
    let B := Γ(X, V)
    let K := X.functionField
    have hUY : genericPoint Y ∈ U.1 :=
      ((genericPoint_spec Y).mem_open_set_iff U.1.isOpen).mpr (by simpa using hU)
    have hUX : genericPoint X ∈ V := by
      change f (genericPoint X) ∈ U.1
      exact hη.symm ▸ hUY
    let : Nonempty V := ⟨⟨_, hUX⟩⟩
    let : Algebra A B := (f.app U.1).hom.toAlgebra
    let : Algebra A K :=
      ((X.germToFunctionField V).hom.comp (f.app U.1).hom).toAlgebra
    have : IsScalarTower A B K := IsScalarTower.of_algebraMap_eq fun _ => rfl
    let g := (Y.presheaf.stalkCongr (.of_eq hη.symm)).hom
    let e : Y.functionField →ₐ[A] K :=
      { (g ≫ f.stalkMap (genericPoint X)).hom with
        commutes' := fun a => by
          change ((Y.germToFunctionField U.1 ≫ g ≫ f.stalkMap (genericPoint X)) a) =
            ((f.app U.1 ≫ X.germToFunctionField V) a)
          have hg : Y.germToFunctionField U.1 ≫ g =
              Y.presheaf.germ U.1 (f (genericPoint X)) hUX :=
            Y.presheaf.germ_stalkSpecializes hUY (.of_eq hη)
          rw [← Category.assoc, hg, f.germ_stalkMap] }
    have : IsFractionRing A Y.functionField :=
      functionField_isFractionRing_of_isAffineOpen Y U.1 U.2
    have he : Function.Bijective e :=
      ⟨e.toRingHom.injective, (ProperOfFibres.surjective_stalkMap_genericPoint f).comp
        (ConcreteCategory.bijective_of_isIso g).2⟩
    have : IsFractionRing A K := IsFractionRing.of_algEquiv (AlgEquiv.ofBijective e he)
    have hA : IsIntegrallyClosed A :=
      isIntegrallyClosed_affineSections_of_hasNormalStalks hY U.2
    have hj : Function.Injective (algebraMap B K) := X.germToFunctionField_injective V
    have h : IsIso (CommRingCat.ofHom (algebraMap A (integralClosure A B))) := by
      refine (ConcreteCategory.isIso_iff_bijective _).mpr ⟨?_, ?_⟩
      · intro a b hab
        apply IsFractionRing.injective A K
        exact congrArg (fun z : integralClosure A B => algebraMap B K z) hab
      · rintro ⟨b, hb⟩
        obtain ⟨a, ha⟩ := (isIntegrallyClosed_iff K).mp hA
          (hb.map (IsScalarTower.toAlgHom A B K))
        exact ⟨a, Subtype.ext (hj ha)⟩
    infer_instance
  · have : IsEmpty U.1 := not_nonempty_iff.mp hU
    infer_instance

/-- The relative normalization of a normal integral scheme in a quasi-compact dominant
monomorphism locally of finite type from an integral scheme identifies with the target. -/
@[simps! hom]
def normalizationIsoOfDominantMonoOfHasNormalStalks (hY : HasNormalStalks Y) :
    f.normalization ≅ Y :=
  let := isIso_fromNormalization_of_hasNormalStalks f hY
  asIso f.fromNormalization

/-- A quasi-compact dominant monomorphism locally of finite type between integral schemes
is an open immersion when the target has normal stalks. -/
theorem isOpenImmersion_of_dominant_mono_of_hasNormalStalks (hY : HasNormalStalks Y) :
    IsOpenImmersion f := by
  rw [← f.toNormalization_fromNormalization,
    ← normalizationIsoOfDominantMonoOfHasNormalStalks_hom f hY]
  infer_instance

end Langlands.AlgebraicGeometry
