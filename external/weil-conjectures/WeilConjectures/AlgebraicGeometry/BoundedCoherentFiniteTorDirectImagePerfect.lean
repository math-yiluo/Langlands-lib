/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FiniteTorDimensionOver
public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBase
public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.DirectImageBoundedCoherent
import WeilConjectures.AlgebraicGeometry.NoetherianBoundedCoherentPseudoCoherent
import WeilConjectures.AlgebraicGeometry.PerfectOfPseudoCoherentFiniteTorDimension
import WeilConjectures.AlgebraicGeometry.ProperDirectImageFiniteTor

/-! # Perfect direct image of a bounded coherent finite-Tor complex

Source: Stacks Project, Derived Categories of Schemes, Lemma 36.27.1 (Tag 08EV)
(blueprint: lem-pc-bounded-coherent-finite-tor-proper-pushforward-perfect).
-/

@[expose] public section

universe u wX wS

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

-- Uniqueness of localization transports isomorphisms of the same two complexes.
private theorem iso_Q_transport
    {C : Type (u + 1)} [Category.{u} C] [Abelian C]
    (h₁ : HasDerivedCategory.{wX} C) (h₂ : HasDerivedCategory.{wS} C)
    (K L : CochainComplex C ℤ)
    (e : Nonempty ((@DerivedCategory.Q C _ _ h₁).obj K ≅
      (@DerivedCategory.Q C _ _ h₁).obj L)) :
    Nonempty ((@DerivedCategory.Q C _ _ h₂).obj K ≅
      (@DerivedCategory.Q C _ _ h₂).obj L) := by
  let Q₁ := @DerivedCategory.Q C _ _ h₁
  let Q₂ := @DerivedCategory.Q C _ _ h₂
  let W := HomologicalComplex.quasiIso C (ComplexShape.up ℤ)
  let F := (Localization.uniq Q₁ Q₂ W).functor
  let c := Localization.compUniqFunctor Q₁ Q₂ W
  obtain ⟨e⟩ := e
  exact ⟨(c.app K).symm ≪≫ F.mapIso e ≪≫ c.app L⟩

-- Finite generation is unchanged by an isomorphism, including on an open site.
private theorem finiteType_of_iso
    {C : Type wX} [Category.{wS} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}}
    [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{u}]
    [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
    {F G : SheafOfModules.{u} R} (e : F ≅ G) (hF : F.IsFiniteType) :
    G.IsFiniteType := by
  have := hF
  obtain ⟨q, hq⟩ := SheafOfModules.IsFiniteType.exists_localGeneratorsData F
  let q' : G.LocalGeneratorsData :=
    { I := q.I
      X := q.X
      coversTop := q.coversTop
      generators j := (q.generators j).ofEpi
        ((SheafOfModules.overFunctor R (q.X j)).map e.hom) }
  refine ⟨q', ?_⟩
  constructor
  intro j
  have := hq.isFiniteType j
  exact inferInstanceAs ((q.generators j).ofEpi
    ((SheafOfModules.overFunctor R (q.X j)).map e.hom)).IsFiniteType

private theorem coherent_of_iso {X : Scheme.{u}}
    {F G : SheafOfModules.{u} (moduleRings X.toRingedSpace)}
    (e : F ≅ G) (hF : RingedSpace.IsCoherent X.toRingedSpace F) :
    RingedSpace.IsCoherent X.toRingedSpace G := by
  refine ⟨finiteType_of_iso.{u, u, u} e hF.1, ?_⟩
  intro U n f
  let eU := (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U).mapIso e
  let g := f ≫ eU.inv
  have hk := hF.2 U n g
  exact finiteType_of_iso.{u, u, u}
    (kernelCompMono f eU.inv) hk

private theorem supportProper_of_iso {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f]
    {F G : SheafOfModules.{u} (moduleRings X.toRingedSpace)} (e : F ≅ G)
    (hF : Modules.HasSupportProperOver f F) : Modules.HasSupportProperOver f G := by
  obtain ⟨Z, hZ, hp⟩ := hF
  refine ⟨Z, hZ.trans ?_, hp⟩
  ext x
  let e' := ((Scheme.Modules.toPresheaf X) ⋙
    TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).mapIso e
  exact not_congr (Equiv.subsingleton_congr (Equiv.ofBijective e'.hom
    (ConcreteCategory.bijective_of_isIso e'.hom)))

private theorem finiteTor_Q_transport (S : Scheme.{u})
    (h₁ : HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings S.toRingedSpace)))
    (h₂ : HasDerivedCategory.{wS} (SheafOfModules.{u} (moduleRings S.toRingedSpace)))
    (K : CochainComplex (SheafOfModules.{u} (moduleRings S.toRingedSpace)) ℤ)
    (h : @HasFiniteTorDimension S h₁ ((@DerivedCategory.Q _ _ _ h₁).obj K)) :
    @HasFiniteTorDimension S h₂ ((@DerivedCategory.Q _ _ _ h₂).obj K) := by
  obtain ⟨a, b, hab, h⟩ := h
  refine ⟨a, b, hab, ?_⟩
  intro F i hi
  obtain ⟨P, hP, eP, hz⟩ := h F i hi
  exact ⟨P, hP, iso_Q_transport h₁ h₂ P K eP, hz⟩

private theorem finiteTor_of_iso (S : Scheme.{u})
    [HasDerivedCategory.{wS} (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
    {E F : schemeDerivedCategory S} (e : E ≅ F) (h : HasFiniteTorDimension S E) :
    HasFiniteTorDimension S F := by
  obtain ⟨a, b, hab, h⟩ := h
  refine ⟨a, b, hab, ?_⟩
  intro G i hi
  obtain ⟨P, hP, ⟨eP⟩, hz⟩ := h G i hi
  exact ⟨P, hP, ⟨eP ≪≫ e⟩, hz⟩

/-- A bounded coherent complex with proper cohomological support and finite Tor dimension
 over the inverse-image structure sheaf has perfect derived direct image.
Source: Stacks Project, Derived Categories of Schemes, Lemma 36.27.1 (Tag 08EV)
(blueprint: lem-pc-bounded-coherent-finite-tor-proper-pushforward-perfect).

Proof:
1. Apply lem-pc-direct-image-bounded-coherent: the Noetherian base, locally finite-type
   morphism, bounded coherent cohomology, and proper supports give bounded coherent
   cohomology of Rf_*E.
2. Apply lem-pc-noetherian-bounded-coherent-pseudo-coherent on S to obtain pseudo-coherence.
3. Represent E by a complex K and transport its hypotheses to the standard source
   localization using homology comparison and uniqueness of localization. Enlarge the
   bounded interval to [min a b, b]. Apply lem-pc-proper-direct-image-finite-tor in the
   standard source and target localizations, which share a morphism universe. In both
   target localizations the K-injective computation represents the direct image by the
   same complex f_*I(K). Uniqueness of localization transports the K-flat representatives
   witnessing finite Tor dimension back to the given target localization.
4. Apply lem-pc-pseudo-coherent-finite-tor-perfect to the conclusions of steps 2 and 3.
-/
theorem isPerfect_schemeDerivedDirectImage_of_bounded_coherent_finiteTor
    {X S : Scheme.{u}} [IsNoetherian S] (f : X ⟶ S) [LocallyOfFiniteType f]
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wS} (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
    [∀ U : S.Opens,
      HasDerivedCategory.{wS} (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U))]
    (E : schemeDerivedCategory X)
    (hbounded : ∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i →
      IsZero ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) i).obj E))
    (hcoherent : ∀ i : ℤ,
      RingedSpace.IsCoherent X.toRingedSpace
        ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) i).obj E))
    (hsupport : ∀ i : ℤ,
      Scheme.Modules.HasSupportProperOver f
        ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) i).obj E))
    (hTor : HasFiniteTorDimensionOver f E) :
    IsPerfect S ((schemeDerivedDirectImage f).obj E) := by
  classical
  obtain ⟨hbounded', hcoherent'⟩ :=
    directImage_isBounded_coherent f E hbounded hcoherent hsupport
  have hpseudo := isPseudoCoherent_of_bounded_coherent S
    ((schemeDerivedDirectImage f).obj E) hbounded' hcoherent'
  let CX := SheafOfModules.{u} (moduleRings X.toRingedSpace)
  let CS := SheafOfModules.{u} (moduleRings S.toRingedSpace)
  let hX : HasDerivedCategory.{wX} CX := inferInstance
  let hS : HasDerivedCategory.{wS} CS := inferInstance
  let QX : CochainComplex CX ℤ ⥤ DerivedCategory CX := DerivedCategory.Q
  let QS : CochainComplex CS ℤ ⥤ DerivedCategory CS := DerivedCategory.Q
  let D := schemeDerivedDirectImage f
  let K := QX.objPreimage E
  let eK : QX.obj K ≅ E := QX.objObjPreimageIso E
  let J : CochainComplex CS ℤ :=
    ((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj ((CochainComplex.kInjectiveResolutionFunctor.{u} CX).obj K)
  let eD : D.obj E ≅ QS.obj J := D.mapIso eK.symm ≪≫
    (Classical.choice (RingedSpace.derivedModuleDirectImageFactorization
      f.toLRSHom.toShHom)).app K
  have hTor' : HasFiniteTorDimension S (D.obj E) := by
    let hXs := HasDerivedCategory.standard CX
    let hSs := HasDerivedCategory.standard CS
    let QXs : CochainComplex CX ℤ ⥤ DerivedCategory CX := DerivedCategory.Q
    let QSs : CochainComplex CS ℤ ⥤ DerivedCategory CS := DerivedCategory.Q
    let Ds := schemeDerivedDirectImage f
    let eH (i : ℤ) : (DerivedCategory.homologyFunctor CX i).obj (QXs.obj K) ≅
        (@DerivedCategory.homologyFunctor CX _ _ hX i).obj E :=
      (DerivedCategory.homologyFunctorFactors CX i).app K ≪≫
        ((@DerivedCategory.homologyFunctorFactors CX _ _ hX i).app K).symm ≪≫
        (@DerivedCategory.homologyFunctor CX _ _ hX i).mapIso eK
    have hb : ∃ a b : ℤ, a ≤ b ∧ ∀ i : ℤ, i < a ∨ b < i →
        IsZero ((DerivedCategory.homologyFunctor CX i).obj (QXs.obj K)) := by
      obtain ⟨a, b, hab⟩ := hbounded
      refine ⟨min a b, b, min_le_right _ _, ?_⟩
      intro i hi
      apply (eH i).isZero_iff.mpr
      apply hab i
      rcases hi with hi | hi
      · exact Or.inl (lt_of_lt_of_le hi (min_le_left _ _))
      · exact Or.inr hi
    have hc : ∀ i : ℤ, RingedSpace.IsCoherent X.toRingedSpace
        ((DerivedCategory.homologyFunctor CX i).obj (QXs.obj K)) :=
      fun i ↦ coherent_of_iso (eH i).symm (hcoherent i)
    have hs : ∀ i : ℤ, Modules.HasSupportProperOver f
        ((DerivedCategory.homologyFunctor CX i).obj (QXs.obj K)) :=
      fun i ↦ supportProper_of_iso f (eH i).symm (hsupport i)
    have ht : HasFiniteTorDimensionOver f (QXs.obj K) := by
      obtain ⟨L, ⟨eL⟩, P, hP, q, hq, a, b, hab, hvan⟩ := hTor
      exact ⟨L, iso_Q_transport hX hXs L K ⟨eL ≪≫ eK.symm⟩,
        P, hP, q, hq, a, b, hab, hvan⟩
    have htd := hasFiniteTorDimension_schemeDerivedDirectImage_of_bounded_coherent_support
      S X f (QXs.obj K) hb hc hs ht
    let eDs : Ds.obj (QXs.obj K) ≅ QSs.obj J :=
      (Classical.choice (RingedSpace.derivedModuleDirectImageFactorization
        f.toLRSHom.toShHom)).app K
    have hJ := finiteTor_of_iso S eDs htd
    exact @finiteTor_of_iso S hS _ _ eD.symm
      (finiteTor_Q_transport S hSs hS J hJ)
  exact isPerfect_of_isPseudoCoherent_of_hasFiniteTorDimension S
    ((schemeDerivedDirectImage f).obj E) hpseudo hTor'

end AlgebraicGeometry.Scheme
