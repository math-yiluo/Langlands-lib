import Langlands.Cohomology.AcyclicResolution.DerivedComparisonComposite
import Langlands.AlgebraicGeometry.Modules.DerivedBaseChange
import Langlands.AlgebraicGeometry.Modules.ClosedImmersionHigherDirectImageVanishingProof

/-!
# Derived restriction along closed immersions and derived base change

For a closed immersion `i : Z ⟶ X` and `f : X ⟶ Spec R`, `derivedRestrictionMap i f M` is the
map `RΓ_R(X, M) ⟶ RΓ_R(Z, i^* M)` of derived `R`-module global sections induced by the unit
`M ⟶ i_* i^* M`, with cohomology the map induced by the unit on cohomology
(`derivedRestrictionMap_homology`).

For a commutative square `gZ ≫ i = i' ≫ g` of schemes with closed immersions `i`, `i'`, the file
proves the unit identity relating the units of `i`, `gZ`, `g` and `i'`
(`unit_comp_pushforwardSquareIso_eq`, sheaf form `pullback_map_unit_comp_pushforwardBaseChange`),
and, for a commutative square of bases `g ≫ f = f' ≫ Spec.map φ`, that derived restriction commutes
with the derived base change map `derivedBaseChangeMap`
(`derivedRestrictionMap_comp_derivedBaseChangeMap`), with its degreewise form
(`restrictionCohomologyMap_comp_baseChangeMap`). These two results assume explicitly the vanishing
of the higher direct images along `g` of `g^* M`, along `gZ` of `gZ^* i^* M`, and along `g` of
`i'_* i'^* g^* M`.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.Cohomology Langlands.Cohomology.AcyclicResolution

namespace Langlands.AlgebraicGeometry.Modules.DerivedSections

attribute [local instance] HasDerivedCategory.standard

section Unit

variable {X X' Z Z' : Scheme.{u}} (g : X' ⟶ X) (i : Z ⟶ X) (i' : Z' ⟶ X') (gZ : Z' ⟶ Z)
  (sq : gZ ≫ i = i' ≫ g)

/-- The comparison `gZ^* i^* ≅ i'^* g^*` of pullbacks around the commutative square
`gZ ≫ i = i' ≫ g`. -/
def pullbackSquareIso :
    Scheme.Modules.pullback i ⋙ Scheme.Modules.pullback gZ ≅
      Scheme.Modules.pullback g ⋙ Scheme.Modules.pullback i' :=
  Scheme.Modules.pullbackComp gZ i ≪≫ Scheme.Modules.pullbackCongr sq ≪≫
    (Scheme.Modules.pullbackComp i' g).symm

/-- The comparison `i_* gZ_* ≅ g_* i'_*` of pushforwards around the commutative square
`gZ ≫ i = i' ≫ g`. -/
def pushforwardSquareIso :
    Scheme.Modules.pushforward gZ ⋙ Scheme.Modules.pushforward i ≅
      Scheme.Modules.pushforward i' ⋙ Scheme.Modules.pushforward g :=
  Scheme.Modules.pushforwardComp gZ i ≪≫ Scheme.Modules.pushforwardCongr sq ≪≫
    (Scheme.Modules.pushforwardComp i' g).symm

/-- For equal morphisms, the pullback and pushforward comparison isomorphisms are conjugate. -/
lemma conjugateEquiv_pullbackCongr_inv {a b : Z' ⟶ X} (h : a = b) :
    conjugateEquiv (Scheme.Modules.pullbackPushforwardAdjunction a)
        (Scheme.Modules.pullbackPushforwardAdjunction b) (Scheme.Modules.pullbackCongr h).inv =
      (Scheme.Modules.pushforwardCongr h).hom := by
  subst h
  have h₁ : (Scheme.Modules.pullbackCongr (rfl : a = a)).inv = 𝟙 _ := rfl
  rw [h₁, conjugateEquiv_id]
  refine NatTrans.ext (funext fun M => Scheme.Modules.hom_ext _ _ fun U => ?_)
  simp

/-- The pullback and pushforward comparisons of a commutative square are conjugate. -/
lemma conjugateEquiv_pullbackSquareIso_inv :
    conjugateEquiv
        ((Scheme.Modules.pullbackPushforwardAdjunction i).comp
          (Scheme.Modules.pullbackPushforwardAdjunction gZ))
        ((Scheme.Modules.pullbackPushforwardAdjunction g).comp
          (Scheme.Modules.pullbackPushforwardAdjunction i'))
        (pullbackSquareIso g i i' gZ sq).inv =
      (pushforwardSquareIso g i i' gZ sq).hom := by
  have h₁ := Scheme.Modules.conjugateEquiv_pullbackComp_inv gZ i
  have h₂ := conjugateEquiv_pullbackCongr_inv sq
  have h₃ : conjugateEquiv (Scheme.Modules.pullbackPushforwardAdjunction (i' ≫ g))
      ((Scheme.Modules.pullbackPushforwardAdjunction g).comp
        (Scheme.Modules.pullbackPushforwardAdjunction i'))
      (Scheme.Modules.pullbackComp i' g).hom = (Scheme.Modules.pushforwardComp i' g).inv := by
    refine (Iso.hom_comp_eq_id _).mp ?_
    rw [← Scheme.Modules.conjugateEquiv_pullbackComp_inv i' g]
    exact conjugateEquiv_comm _ _ (Iso.hom_inv_id _)
  simp only [pullbackSquareIso, pushforwardSquareIso, Iso.trans_inv, Iso.trans_hom, Iso.symm_inv,
    Iso.symm_hom]
  rw [← conjugateEquiv_comp _ (Scheme.Modules.pullbackPushforwardAdjunction (gZ ≫ i)) _,
    ← conjugateEquiv_comp _ (Scheme.Modules.pullbackPushforwardAdjunction (i' ≫ g)) _, h₁, h₂,
    h₃]

set_option backward.isDefEq.respectTransparency false in
/-- The composite unit for `i` and `gZ`, followed by the pushforward comparison, is the
composite unit for `g` and `i'`, followed by the inverse pullback comparison. -/
lemma unit_comp_pushforwardSquareIso_hom_app (M : X.Modules) :
    (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app M ≫
        (Scheme.Modules.pushforward i).map
          ((Scheme.Modules.pullbackPushforwardAdjunction gZ).unit.app
            ((Scheme.Modules.pullback i).obj M)) ≫
        (pushforwardSquareIso g i i' gZ sq).hom.app
          ((Scheme.Modules.pullback gZ).obj ((Scheme.Modules.pullback i).obj M)) =
      (Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M ≫
        (Scheme.Modules.pushforward g).map
          ((Scheme.Modules.pullbackPushforwardAdjunction i').unit.app
            ((Scheme.Modules.pullback g).obj M)) ≫
        (Scheme.Modules.pushforward g).map ((Scheme.Modules.pushforward i').map
          ((pullbackSquareIso g i i' gZ sq).inv.app M)) := by
  have h := unit_conjugateEquiv ((Scheme.Modules.pullbackPushforwardAdjunction i).comp
      (Scheme.Modules.pullbackPushforwardAdjunction gZ))
    ((Scheme.Modules.pullbackPushforwardAdjunction g).comp
      (Scheme.Modules.pullbackPushforwardAdjunction i'))
    (pullbackSquareIso g i i' gZ sq).inv M
  rw [conjugateEquiv_pullbackSquareIso_inv, Adjunction.comp_unit_app,
    Adjunction.comp_unit_app] at h
  simp only [Category.assoc, Functor.comp_map] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
/-- Unit identity for a commutative square: the unit of `i`, the pushforward of the unit of
`gZ` and of the pullback comparison, and the pushforward comparison give the unit of `g`
followed by the pushforward of the unit of `i'`. -/
theorem unit_comp_pushforwardSquareIso_eq (M : X.Modules) :
    (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app M ≫
        (Scheme.Modules.pushforward i).map
          ((Scheme.Modules.pullbackPushforwardAdjunction gZ).unit.app
            ((Scheme.Modules.pullback i).obj M)) ≫
        (Scheme.Modules.pushforward i).map ((Scheme.Modules.pushforward gZ).map
          ((pullbackSquareIso g i i' gZ sq).hom.app M)) ≫
        (pushforwardSquareIso g i i' gZ sq).hom.app
          ((Scheme.Modules.pullback i').obj ((Scheme.Modules.pullback g).obj M)) =
      (Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M ≫
        (Scheme.Modules.pushforward g).map
          ((Scheme.Modules.pullbackPushforwardAdjunction i').unit.app
            ((Scheme.Modules.pullback g).obj M)) := by
  have hc := (pushforwardSquareIso g i i' gZ sq).hom.naturality
    ((pullbackSquareIso g i i' gZ sq).hom.app M)
  simp only [Functor.comp_map, Functor.comp_obj] at hc
  rw [hc, reassoc_of% (unit_comp_pushforwardSquareIso_hom_app g i i' gZ sq M),
    ← Functor.map_comp (Scheme.Modules.pushforward g),
    ← Functor.map_comp (Scheme.Modules.pushforward i'), Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]

/-- The base change morphism `g^* i_* P ⟶ i'_* gZ^* P` of the commutative square: the adjunct
of the pushforward along `i` of the unit of `gZ`, followed by the pushforward comparison. -/
def pushforwardBaseChange (P : Z.Modules) :
    (Scheme.Modules.pullback g).obj ((Scheme.Modules.pushforward i).obj P) ⟶
      (Scheme.Modules.pushforward i').obj ((Scheme.Modules.pullback gZ).obj P) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _).symm
    ((Scheme.Modules.pushforward i).map
        ((Scheme.Modules.pullbackPushforwardAdjunction gZ).unit.app P) ≫
      (pushforwardSquareIso g i i' gZ sq).hom.app ((Scheme.Modules.pullback gZ).obj P))

set_option backward.isDefEq.respectTransparency false in
/-- Sheaf form of the unit identity: the pullback along `g` of the unit of `i`, followed by
the base change morphism and the pushforward of the pullback comparison, is the unit of `i'`
at `g^* M`. -/
theorem pullback_map_unit_comp_pushforwardBaseChange (M : X.Modules) :
    (Scheme.Modules.pullback g).map ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app M) ≫
        pushforwardBaseChange g i i' gZ sq ((Scheme.Modules.pullback i).obj M) ≫
        (Scheme.Modules.pushforward i').map ((pullbackSquareIso g i i' gZ sq).hom.app M) =
      (Scheme.Modules.pullbackPushforwardAdjunction i').unit.app
        ((Scheme.Modules.pullback g).obj M) := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _).injective
  have hc := (pushforwardSquareIso g i i' gZ sq).hom.naturality
    ((pullbackSquareIso g i i' gZ sq).hom.app M)
  simp only [Functor.comp_map, Functor.comp_obj] at hc
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
    pushforwardBaseChange]
  erw [Equiv.apply_symm_apply]
  rw [Adjunction.homEquiv_unit, Category.assoc, ← hc]
  exact unit_comp_pushforwardSquareIso_eq g i i' gZ sq M

end Unit

section Comparison

variable {X Y : Scheme.{u}} (h : X ⟶ Y) {R : CommRingCat.{u}} (g : Y ⟶ Spec R)

/-- The inverse of the derived pushforward comparison is natural in the coefficient module. -/
@[reassoc]
lemma derivedPushforwardComparisonIso_inv_naturality {M N : X.Modules} (u : M ⟶ N)
    (hM : ∀ q : ℕ, IsZero ((higherDirectImage h (q + 1)).obj M))
    (hN : ∀ q : ℕ, IsZero ((higherDirectImage h (q + 1)).obj N)) :
    (DerivedPlus.derivedComplex (relativeGlobalSections g) ⋙ DerivedCategory.Plus.ι).map
        ((Scheme.Modules.pushforward h).map u) ≫ (derivedPushforwardComparisonIso h g N hN).inv =
      (derivedPushforwardComparisonIso h g M hM).inv ≫
        (DerivedPlus.derivedComplex (relativeGlobalSections (h ≫ g)) ⋙
          DerivedCategory.Plus.ι).map u := by
  rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp]
  exact (derivedPushforwardComparison_naturality h g u hM hN).symm

end Comparison

section Restriction

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] {R : CommRingCat.{u}}
  (f : X ⟶ Spec R)

/-- Positive higher direct images along a closed immersion vanish. -/
lemma isZero_higherDirectImage_of_isClosedImmersion (P : Z.Modules) (q : ℕ) :
    IsZero ((higherDirectImage i (q + 1)).obj P) :=
  closedImmersionHigherDirectImageVanishing Z X i inferInstance P q

/-- Pushforward along a closed immersion preserves homology. -/
lemma preservesHomology_pushforward_of_isClosedImmersion :
    (Scheme.Modules.pushforward i).PreservesHomology := by
  have := ClosedImmersionHigherDirectImageVanishing.pushforward_preservesEpimorphisms i
  exact Functor.preservesHomology_of_preservesEpis_and_kernels _

/-- The derived restriction map `RΓ_R(X, M) ⟶ RΓ_R(Z, i^* M)` along a closed immersion
`i : Z ⟶ X`: the map induced by the unit `M ⟶ i_* i^* M`, followed by the inverse of the
derived pushforward comparison for `i^* M`. -/
def derivedRestrictionMap (M : X.Modules) :
    (DerivedPlus.derivedComplex (relativeGlobalSections f) ⋙ DerivedCategory.Plus.ι).obj M ⟶
      (DerivedPlus.derivedComplex (relativeGlobalSections (i ≫ f)) ⋙
        DerivedCategory.Plus.ι).obj ((Scheme.Modules.pullback i).obj M) :=
  (DerivedPlus.derivedComplex (relativeGlobalSections f) ⋙ DerivedCategory.Plus.ι).map
      ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app M) ≫
    (derivedPushforwardComparisonIso i f _
      (isZero_higherDirectImage_of_isClosedImmersion i _)).inv

/-- The derived restriction map is natural in the module. -/
@[reassoc]
theorem derivedRestrictionMap_naturality {M N : X.Modules} (u : M ⟶ N) :
    (DerivedPlus.derivedComplex (relativeGlobalSections f) ⋙ DerivedCategory.Plus.ι).map u ≫
        derivedRestrictionMap i f N =
      derivedRestrictionMap i f M ≫
        (DerivedPlus.derivedComplex (relativeGlobalSections (i ≫ f)) ⋙
          DerivedCategory.Plus.ι).map ((Scheme.Modules.pullback i).map u) := by
  have hu := (Scheme.Modules.pullbackPushforwardAdjunction i).unit.naturality u
  simp only [Functor.id_map, Functor.comp_map] at hu
  simp only [derivedRestrictionMap, Category.assoc]
  rw [← Functor.map_comp_assoc, hu, Functor.map_comp_assoc,
    derivedPushforwardComparisonIso_inv_naturality]

set_option backward.isDefEq.respectTransparency false in
/-- Nonnegative cohomology of the derived restriction map, followed by the degreewise
pushforward comparison, is the map induced on cohomology by the unit `M ⟶ i_* i^* M`. -/
theorem derivedRestrictionMap_homology (M : X.Modules) (n : ℕ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} R) (n : ℤ)).map
        (derivedRestrictionMap i f M) ≫
      (DerivedPlus.homologyIso (relativeGlobalSections (i ≫ f))
        (injectiveResolution ((Scheme.Modules.pullback i).obj M)) n).hom ≫
      pushforwardComparison i f ((Scheme.Modules.pullback i).obj M)
        (isZero_higherDirectImage_of_isClosedImmersion i _) n =
    (DerivedPlus.homologyIso (relativeGlobalSections f) (injectiveResolution M) n).hom ≫
      (relativeCohomology f n).map
        ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app M) := by
  have h₁ : (DerivedCategory.homologyFunctor (ModuleCat.{u} R) (n : ℤ)).map
        ((DerivedPlus.derivedComplex (relativeGlobalSections f) ⋙ DerivedCategory.Plus.ι).map
          ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app M)) ≫
        (DerivedPlus.homologyIso (relativeGlobalSections f)
          (injectiveResolution ((Scheme.Modules.pushforward i).obj
            ((Scheme.Modules.pullback i).obj M))) n).hom =
      (DerivedPlus.homologyIso (relativeGlobalSections f) (injectiveResolution M) n).hom ≫
        (relativeCohomology f n).map
          ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app M) :=
    DerivedPlus.homologyIso_hom_naturality _ _ _ _ n
  have h₂ : (DerivedCategory.homologyFunctor (ModuleCat.{u} R) (n : ℤ)).map
        (derivedPushforwardComparisonIso i f _
          (isZero_higherDirectImage_of_isClosedImmersion i _)).inv ≫
        (DerivedPlus.homologyIso (relativeGlobalSections (i ≫ f))
          (injectiveResolution ((Scheme.Modules.pullback i).obj M)) n).hom ≫
        pushforwardComparison i f ((Scheme.Modules.pullback i).obj M)
          (isZero_higherDirectImage_of_isClosedImmersion i _) n =
      (DerivedPlus.homologyIso (relativeGlobalSections f)
        (injectiveResolution ((Scheme.Modules.pushforward i).obj
          ((Scheme.Modules.pullback i).obj M))) n).hom := by
    rw [← derivedPushforwardComparison_homology, ← Functor.map_comp_assoc,
      ← derivedPushforwardComparisonIso_hom, Iso.inv_hom_id, CategoryTheory.Functor.map_id,
      Category.id_comp]
  simp only [derivedRestrictionMap, Functor.map_comp, Category.assoc]
  rw [h₂]
  exact h₁

/-- The degreewise restriction map `Hⁿ_R(X, M) ⟶ Hⁿ_R(Z, i^* M)` along a closed immersion: the
map induced on cohomology by the unit `M ⟶ i_* i^* M`, followed by the inverse of the
pushforward comparison for `i^* M`. -/
def restrictionCohomologyMap (M : X.Modules) (n : ℕ) :
    (relativeCohomology f n).obj M ⟶
      (relativeCohomology (i ≫ f) n).obj ((Scheme.Modules.pullback i).obj M) :=
  haveI := isIso_pushforwardComparison i f ((Scheme.Modules.pullback i).obj M)
    (isZero_higherDirectImage_of_isClosedImmersion i _)
    (fun J hJ q => (pushforwardInjectiveAcyclic Z X i J hJ q).2 R f) n
  (relativeCohomology f n).map ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app M) ≫
    inv (pushforwardComparison i f _ (isZero_higherDirectImage_of_isClosedImmersion i _) n)

set_option backward.isDefEq.respectTransparency false in
/-- Nonnegative cohomology of the derived restriction map is the degreewise restriction map,
through the specified homology isomorphisms. -/
theorem derivedRestrictionMap_homology_eq (M : X.Modules) (n : ℕ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} R) (n : ℤ)).map
        (derivedRestrictionMap i f M) ≫
      (DerivedPlus.homologyIso (relativeGlobalSections (i ≫ f))
        (injectiveResolution ((Scheme.Modules.pullback i).obj M)) n).hom =
    (DerivedPlus.homologyIso (relativeGlobalSections f) (injectiveResolution M) n).hom ≫
      restrictionCohomologyMap i f M n := by
  have := isIso_pushforwardComparison i f ((Scheme.Modules.pullback i).obj M)
    (isZero_higherDirectImage_of_isClosedImmersion i _)
    (fun J hJ q => (pushforwardInjectiveAcyclic Z X i J hJ q).2 R f) n
  rw [restrictionCohomologyMap, ← Category.assoc, IsIso.eq_comp_inv, Category.assoc]
  exact derivedRestrictionMap_homology i f M n

end Restriction

section Square

variable {X X' Z Z' : Scheme.{u}} {R R' : CommRingCat.{u}} (φ : R ⟶ R') (f : X ⟶ Spec R)
  (f' : X' ⟶ Spec R') (g : X' ⟶ X) (w : g ≫ f = f' ≫ Spec.map φ)
  (i : Z ⟶ X) (i' : Z' ⟶ X') (gZ : Z' ⟶ Z) (sq : gZ ≫ i = i' ≫ g)

/-- Global sections over `Spec R` of a morphism act on elements as the morphism on top sections. -/
lemma moduleSpecΓFunctor_map_hom_apply {M N : (Spec R).Modules} (ψ : M ⟶ N)
    (x : moduleSpecΓFunctor.obj M) :
    (moduleSpecΓFunctor.map ψ).hom x = (ψ.app ⊤).hom x :=
  rfl

/-- Global sections over `Spec R` of the comparison between pushforwards along equal morphisms
act on elements as the identity. -/
lemma relativeGlobalSections_map_pushforwardCongr_apply {Y : Scheme.{u}} {a b : Y ⟶ X}
    (h : a = b) (Q : Y.Modules)
    (x : (relativeGlobalSections f).obj ((Scheme.Modules.pushforward a).obj Q)) :
    ((relativeGlobalSections f).map ((Scheme.Modules.pushforwardCongr h).hom.app Q)).hom x = x := by
  subst h
  have h₁ : (Scheme.Modules.pushforwardCongr (rfl : a = a)).hom.app Q = 𝟙 _ :=
    Scheme.Modules.hom_ext _ _ fun U => by simp
  rw [h₁, CategoryTheory.Functor.map_id]
  rfl

include w sq in
/-- The square over the bases for the closed subschemes. -/
lemma square_restrict_comm : gZ ≫ i ≫ f = (i' ≫ f') ≫ Spec.map φ := by
  rw [← Category.assoc, sq, Category.assoc, w, Category.assoc]

include w in
/-- The square over the bases for `i' ≫ g`. -/
lemma square_restrict_comm' : i' ≫ g ≫ f = (i' ≫ f') ≫ Spec.map φ := by
  rw [w, Category.assoc]

/-- The termwise comparisons of the two factorizations of the square agree on sections. -/
lemma relativeGlobalSectionsCompIso_square (Q : Z'.Modules) :
    (relativeGlobalSectionsCompIso gZ (i ≫ f)).inv.app Q ≫
        (relativeGlobalSectionsCompIso i f).inv.app ((Scheme.Modules.pushforward gZ).obj Q) ≫
        (relativeGlobalSections f).map ((pushforwardSquareIso g i i' gZ sq).hom.app Q) =
      ((relativeGlobalSectionsBaseRingIso φ (gZ ≫ i ≫ f) (i' ≫ f')
          (square_restrict_comm φ f f' g w i i' gZ sq)).symm ≪≫
        relativeGlobalSectionsBaseRingIso φ (i' ≫ g ≫ f) (i' ≫ f')
          (square_restrict_comm' φ f f' g w i')).hom.app Q ≫
        (relativeGlobalSectionsCompIso i' (g ≫ f)).inv.app Q ≫
        (relativeGlobalSectionsCompIso g f).inv.app ((Scheme.Modules.pushforward i').obj Q) := by
  ext x
  exact relativeGlobalSections_map_pushforwardCongr_apply f sq Q x

set_option backward.isDefEq.respectTransparency false in
/-- Comparison of the two factorizations `gZ ≫ i = i' ≫ g` of the square: the inverse derived
pushforward comparisons along `i` and `gZ` agree with those along `g` and `i'`, after the
pushforward comparison of the square and the identifications of `R`-module sections along
`gZ ≫ i ≫ f` and `i' ≫ g ≫ f` with scalar restriction of `R'`-module sections along `i' ≫ f'`. -/
theorem derivedPushforwardComparisonIso_inv_square [IsClosedImmersion i] [IsClosedImmersion i']
    (N : Z'.Modules) (hN : ∀ q : ℕ, IsZero ((higherDirectImage gZ (q + 1)).obj N))
    (hN' : ∀ q : ℕ,
      IsZero ((higherDirectImage g (q + 1)).obj ((Scheme.Modules.pushforward i').obj N))) :
    (derivedPushforwardComparisonIso i f _
        (isZero_higherDirectImage_of_isClosedImmersion i _)).inv ≫
        (derivedPushforwardComparisonIso gZ (i ≫ f) N hN).inv ≫
        (DerivedPlus.derivedCompIso (relativeGlobalSections (i' ≫ f'))
          (ModuleCat.restrictScalars φ.hom)
          (relativeGlobalSectionsBaseRingIso φ (gZ ≫ i ≫ f) (i' ≫ f')
            (square_restrict_comm φ f f' g w i i' gZ sq))).inv.app N =
      (DerivedPlus.derivedComplex (relativeGlobalSections f) ⋙ DerivedCategory.Plus.ι).map
          ((pushforwardSquareIso g i i' gZ sq).hom.app N) ≫
        (derivedPushforwardComparisonIso g f _ hN').inv ≫
        (derivedPushforwardComparisonIso i' (g ≫ f) N
          (isZero_higherDirectImage_of_isClosedImmersion i' N)).inv ≫
        (DerivedPlus.derivedCompIso (relativeGlobalSections (i' ≫ f'))
          (ModuleCat.restrictScalars φ.hom)
          (relativeGlobalSectionsBaseRingIso φ (i' ≫ g ≫ f) (i' ≫ f')
            (square_restrict_comm' φ f f' g w i'))).inv.app N := by
  have := preservesHomology_pushforward_of_isClosedImmersion i
  have hNi : ∀ q : ℕ, IsZero (((Scheme.Modules.pushforward gZ ⋙
      Scheme.Modules.pushforward i).rightDerived (q + 1)).obj N) :=
    fun q => isZero_rightDerived_comp_of_preservesHomology _ _ N (q + 1) (hN q)
  have hT := derivedCompComparison_comp_factorization (relativeGlobalSections f)
    (relativeGlobalSectionsCompIso i f) (relativeGlobalSectionsCompIso gZ (i ≫ f))
    (relativeGlobalSectionsCompIso g f) (relativeGlobalSectionsCompIso i' (g ≫ f))
    ((relativeGlobalSectionsBaseRingIso φ (gZ ≫ i ≫ f) (i' ≫ f')
        (square_restrict_comm φ f f' g w i i' gZ sq)).symm ≪≫
      relativeGlobalSectionsBaseRingIso φ (i' ≫ g ≫ f) (i' ≫ f')
        (square_restrict_comm' φ f f' g w i'))
    (pushforwardSquareIso g i i' gZ sq) N hN
    (isZero_higherDirectImage_of_isClosedImmersion i _)
    (isZero_higherDirectImage_of_isClosedImmersion i' N) hN' hNi
    (relativeGlobalSectionsCompIso_square φ f f' g w i i' gZ sq)
  rw [← derivedCompIso_inv_app_comp_hom_app] at hT
  have hT' : (derivedPushforwardComparisonIso gZ (i ≫ f) N hN).hom ≫
      (derivedPushforwardComparisonIso i f _
        (isZero_higherDirectImage_of_isClosedImmersion i _)).hom ≫
      (DerivedPlus.derivedComplex (relativeGlobalSections f) ⋙ DerivedCategory.Plus.ι).map
        ((pushforwardSquareIso g i i' gZ sq).hom.app N) =
    (DerivedPlus.derivedCompIso (relativeGlobalSections (i' ≫ f'))
        (ModuleCat.restrictScalars φ.hom)
        (relativeGlobalSectionsBaseRingIso φ (gZ ≫ i ≫ f) (i' ≫ f')
          (square_restrict_comm φ f f' g w i i' gZ sq))).inv.app N ≫
      (DerivedPlus.derivedCompIso (relativeGlobalSections (i' ≫ f'))
        (ModuleCat.restrictScalars φ.hom)
        (relativeGlobalSectionsBaseRingIso φ (i' ≫ g ≫ f) (i' ≫ f')
          (square_restrict_comm' φ f f' g w i'))).hom.app N ≫
      (derivedPushforwardComparisonIso i' (g ≫ f) N
        (isZero_higherDirectImage_of_isClosedImmersion i' N)).hom ≫
      (derivedPushforwardComparisonIso g f _ hN').hom := by
    rw [Category.assoc] at hT
    exact hT
  rw [Iso.inv_comp_eq, Iso.inv_comp_eq]
  slice_rhs 1 3 => rw [hT']
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id_app, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
/-- The derived pushforward comparison along `i'` commutes with restriction of scalars along
`φ`, under the identifications of `R`-module sections along `g ≫ f` and `i' ≫ g ≫ f` with
scalar restriction of `R'`-module sections along `f'` and `i' ≫ f'`. -/
theorem derivedPushforwardComparisonIso_inv_restrictScalars [IsClosedImmersion i']
    (N : Z'.Modules) :
    (DerivedPlus.derivedCompIso (relativeGlobalSections f') (ModuleCat.restrictScalars φ.hom)
        (relativeGlobalSectionsBaseRingIso φ (g ≫ f) f' w)).inv.app
          ((Scheme.Modules.pushforward i').obj N) ≫
      (ModuleCat.restrictScalars φ.hom).mapDerivedCategory.map
        (derivedPushforwardComparisonIso i' f' N
          (isZero_higherDirectImage_of_isClosedImmersion i' N)).inv =
    (derivedPushforwardComparisonIso i' (g ≫ f) N
        (isZero_higherDirectImage_of_isClosedImmersion i' N)).inv ≫
      (DerivedPlus.derivedCompIso (relativeGlobalSections (i' ≫ f'))
        (ModuleCat.restrictScalars φ.hom)
        (relativeGlobalSectionsBaseRingIso φ (i' ≫ g ≫ f) (i' ≫ f')
          (square_restrict_comm' φ f f' g w i'))).inv.app N := by
  have hc : ∀ Q : Z'.Modules,
      (relativeGlobalSectionsBaseRingIso φ (i' ≫ g ≫ f) (i' ≫ f')
          (square_restrict_comm' φ f f' g w i')).hom.app Q ≫
        (relativeGlobalSectionsCompIso i' (g ≫ f)).inv.app Q =
      (ModuleCat.restrictScalars φ.hom).map ((relativeGlobalSectionsCompIso i' f').inv.app Q) ≫
        (relativeGlobalSectionsBaseRingIso φ (g ≫ f) f' w).hom.app
          ((Scheme.Modules.pushforward i').obj Q) := by
    intro Q
    ext x
    rfl
  have h := derivedCompComparison_postcomp (relativeGlobalSections f')
    (relativeGlobalSectionsCompIso i' f') (ModuleCat.restrictScalars φ.hom)
    (relativeGlobalSectionsBaseRingIso φ (g ≫ f) f' w)
    (relativeGlobalSectionsBaseRingIso φ (i' ≫ g ≫ f) (i' ≫ f')
      (square_restrict_comm' φ f f' g w i'))
    (relativeGlobalSectionsCompIso i' (g ≫ f)) N
    (isZero_higherDirectImage_of_isClosedImmersion i' N) hc
  have key : (ModuleCat.restrictScalars φ.hom).mapDerivedCategory.mapIso
        (derivedPushforwardComparisonIso i' f' N
          (isZero_higherDirectImage_of_isClosedImmersion i' N)) ≪≫
      (DerivedPlus.derivedCompIso (relativeGlobalSections f') (ModuleCat.restrictScalars φ.hom)
        (relativeGlobalSectionsBaseRingIso φ (g ≫ f) f' w)).app
          ((Scheme.Modules.pushforward i').obj N) =
    (DerivedPlus.derivedCompIso (relativeGlobalSections (i' ≫ f'))
        (ModuleCat.restrictScalars φ.hom)
        (relativeGlobalSectionsBaseRingIso φ (i' ≫ g ≫ f) (i' ≫ f')
          (square_restrict_comm' φ f f' g w i'))).app N ≪≫
      derivedPushforwardComparisonIso i' (g ≫ f) N
        (isZero_higherDirectImage_of_isClosedImmersion i' N) :=
    Iso.ext h.symm
  have key' := congrArg Iso.inv key
  simp only [Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv] at key'
  exact key'

set_option backward.isDefEq.respectTransparency false in
/-- Derived restriction along closed immersions commutes with derived base change. For a
commutative square `gZ ≫ i = i' ≫ g` with closed immersions `i : Z ⟶ X` and `i' : Z' ⟶ X'`,
and a commutative square of bases `g ≫ f = f' ≫ Spec.map φ`, restricting along `i` and then
applying derived base change on `Z` (followed by the pullback comparison `gZ^* i^* ≅ i'^* g^*`)
agrees with applying derived base change on `X` and then restricting along `i'`. The three
vanishing hypotheses are the higher direct image conditions along `g` for `g^* M`, along `gZ`
for `gZ^* i^* M`, and along `g` for `i'_* i'^* g^* M`. -/
theorem derivedRestrictionMap_comp_derivedBaseChangeMap [IsClosedImmersion i]
    [IsClosedImmersion i'] (M : X.Modules)
    (hM : ∀ q : ℕ,
      IsZero ((higherDirectImage g (q + 1)).obj ((Scheme.Modules.pullback g).obj M)))
    (hMZ : ∀ q : ℕ, IsZero ((higherDirectImage gZ (q + 1)).obj
      ((Scheme.Modules.pullback gZ).obj ((Scheme.Modules.pullback i).obj M))))
    (hM' : ∀ q : ℕ, IsZero ((higherDirectImage g (q + 1)).obj
      ((Scheme.Modules.pushforward i').obj
        ((Scheme.Modules.pullback i').obj ((Scheme.Modules.pullback g).obj M))))) :
    derivedRestrictionMap i f M ≫
        derivedBaseChangeMap φ (i ≫ f) (i' ≫ f') gZ (square_restrict_comm φ f f' g w i i' gZ sq)
          ((Scheme.Modules.pullback i).obj M) hMZ ≫
        (ModuleCat.restrictScalars φ.hom).mapDerivedCategory.map
          ((DerivedPlus.derivedComplex (relativeGlobalSections (i' ≫ f')) ⋙
            DerivedCategory.Plus.ι).map ((pullbackSquareIso g i i' gZ sq).hom.app M)) =
      derivedBaseChangeMap φ f f' g w M hM ≫
        (ModuleCat.restrictScalars φ.hom).mapDerivedCategory.map
          (derivedRestrictionMap i' f' ((Scheme.Modules.pullback g).obj M)) := by
  have hN : ∀ q : ℕ, IsZero ((higherDirectImage gZ (q + 1)).obj
      ((Scheme.Modules.pullback i').obj ((Scheme.Modules.pullback g).obj M))) := fun q =>
    (hMZ q).of_iso ((higherDirectImage gZ (q + 1)).mapIso
      ((pullbackSquareIso g i i' gZ sq).app M)).symm
  have h₁ : (DerivedPlus.derivedCompIso (relativeGlobalSections (i' ≫ f'))
        (ModuleCat.restrictScalars φ.hom)
        (relativeGlobalSectionsBaseRingIso φ (gZ ≫ i ≫ f) (i' ≫ f')
          (square_restrict_comm φ f f' g w i i' gZ sq))).inv.app
          ((Scheme.Modules.pullback gZ).obj ((Scheme.Modules.pullback i).obj M)) ≫
        (ModuleCat.restrictScalars φ.hom).mapDerivedCategory.map
          ((DerivedPlus.derivedComplex (relativeGlobalSections (i' ≫ f')) ⋙
            DerivedCategory.Plus.ι).map ((pullbackSquareIso g i i' gZ sq).hom.app M)) =
      (DerivedPlus.derivedComplex (relativeGlobalSections (gZ ≫ i ≫ f)) ⋙
          DerivedCategory.Plus.ι).map ((pullbackSquareIso g i i' gZ sq).hom.app M) ≫
        (DerivedPlus.derivedCompIso (relativeGlobalSections (i' ≫ f'))
          (ModuleCat.restrictScalars φ.hom)
          (relativeGlobalSectionsBaseRingIso φ (gZ ≫ i ≫ f) (i' ≫ f')
            (square_restrict_comm φ f f' g w i i' gZ sq))).inv.app
          ((Scheme.Modules.pullback i').obj ((Scheme.Modules.pullback g).obj M)) :=
    ((DerivedPlus.derivedCompIso (relativeGlobalSections (i' ≫ f'))
        (ModuleCat.restrictScalars φ.hom)
        (relativeGlobalSectionsBaseRingIso φ (gZ ≫ i ≫ f) (i' ≫ f')
          (square_restrict_comm φ f f' g w i i' gZ sq))).inv.naturality
      ((pullbackSquareIso g i i' gZ sq).hom.app M)).symm
  have h₂ := derivedPushforwardComparisonIso_inv_naturality
    (M := (Scheme.Modules.pullback gZ).obj ((Scheme.Modules.pullback i).obj M))
    (N := (Scheme.Modules.pullback i').obj ((Scheme.Modules.pullback g).obj M)) gZ (i ≫ f)
    ((pullbackSquareIso g i i' gZ sq).hom.app M) hMZ hN
  have h₃ := derivedPushforwardComparisonIso_inv_naturality
    (M := (Scheme.Modules.pullback i).obj M)
    (N := (Scheme.Modules.pushforward gZ).obj
      ((Scheme.Modules.pullback i').obj ((Scheme.Modules.pullback g).obj M))) i f
    ((Scheme.Modules.pullbackPushforwardAdjunction gZ).unit.app ((Scheme.Modules.pullback i).obj M) ≫
      (Scheme.Modules.pushforward gZ).map ((pullbackSquareIso g i i' gZ sq).hom.app M))
    (isZero_higherDirectImage_of_isClosedImmersion i _)
    (isZero_higherDirectImage_of_isClosedImmersion i _)
  have h₄ : (DerivedPlus.derivedCompIso (relativeGlobalSections f')
        (ModuleCat.restrictScalars φ.hom) (relativeGlobalSectionsBaseRingIso φ (g ≫ f) f' w)).inv.app
          ((Scheme.Modules.pullback g).obj M) ≫
        (ModuleCat.restrictScalars φ.hom).mapDerivedCategory.map
          ((DerivedPlus.derivedComplex (relativeGlobalSections f') ⋙ DerivedCategory.Plus.ι).map
            ((Scheme.Modules.pullbackPushforwardAdjunction i').unit.app
              ((Scheme.Modules.pullback g).obj M))) =
      (DerivedPlus.derivedComplex (relativeGlobalSections (g ≫ f)) ⋙ DerivedCategory.Plus.ι).map
          ((Scheme.Modules.pullbackPushforwardAdjunction i').unit.app
            ((Scheme.Modules.pullback g).obj M)) ≫
        (DerivedPlus.derivedCompIso (relativeGlobalSections f')
          (ModuleCat.restrictScalars φ.hom)
          (relativeGlobalSectionsBaseRingIso φ (g ≫ f) f' w)).inv.app
          ((Scheme.Modules.pushforward i').obj
            ((Scheme.Modules.pullback i').obj ((Scheme.Modules.pullback g).obj M))) :=
    ((DerivedPlus.derivedCompIso (relativeGlobalSections f') (ModuleCat.restrictScalars φ.hom)
        (relativeGlobalSectionsBaseRingIso φ (g ≫ f) f' w)).inv.naturality
      ((Scheme.Modules.pullbackPushforwardAdjunction i').unit.app
        ((Scheme.Modules.pullback g).obj M))).symm
  have h₅ := derivedPushforwardComparisonIso_inv_naturality
    (M := (Scheme.Modules.pullback g).obj M)
    (N := (Scheme.Modules.pushforward i').obj
      ((Scheme.Modules.pullback i').obj ((Scheme.Modules.pullback g).obj M))) g f
    ((Scheme.Modules.pullbackPushforwardAdjunction i').unit.app ((Scheme.Modules.pullback g).obj M))
    hM hM'
  have h₆ := derivedPushforwardComparisonIso_inv_restrictScalars φ f f' g w i'
    ((Scheme.Modules.pullback i').obj ((Scheme.Modules.pullback g).obj M))
  have h₇ := derivedPushforwardComparisonIso_inv_square φ f f' g w i i' gZ sq
    ((Scheme.Modules.pullback i').obj ((Scheme.Modules.pullback g).obj M)) hN hM'
  have hU := congrArg
    (DerivedPlus.derivedComplex (relativeGlobalSections f) ⋙ DerivedCategory.Plus.ι).map
    (unit_comp_pushforwardSquareIso_eq g i i' gZ sq M)
  simp only [Functor.map_comp] at hU
  simp only [derivedRestrictionMap, derivedBaseChangeMap, Functor.map_comp, Category.assoc]
  slice_lhs 5 6 => rw [h₁]
  slice_lhs 4 5 => rw [← h₂]
  slice_lhs 3 4 => rw [← Functor.map_comp]
  slice_lhs 2 3 => rw [← h₃]
  simp only [Category.assoc]
  rw [h₇, Functor.map_comp (Scheme.Modules.pushforward i), Functor.map_comp]
  have hU' := fun {W : DerivedCategory (ModuleCat.{u} R)}
      (k : (DerivedPlus.derivedComplex (relativeGlobalSections f) ⋙ DerivedCategory.Plus.ι).obj
        ((Scheme.Modules.pushforward g).obj ((Scheme.Modules.pushforward i').obj
          ((Scheme.Modules.pullback i').obj ((Scheme.Modules.pullback g).obj M)))) ⟶ W) =>
    hU =≫ k
  have h₄' := fun {W : DerivedCategory (ModuleCat.{u} R)}
      (k : (ModuleCat.restrictScalars φ.hom).mapDerivedCategory.obj
        ((DerivedPlus.derivedComplex (relativeGlobalSections f') ⋙ DerivedCategory.Plus.ι).obj
          ((Scheme.Modules.pushforward i').obj
            ((Scheme.Modules.pullback i').obj ((Scheme.Modules.pullback g).obj M)))) ⟶ W) =>
    h₄ =≫ k
  have h₅' := fun {W : DerivedCategory (ModuleCat.{u} R)}
      (k : (DerivedPlus.derivedComplex (relativeGlobalSections (g ≫ f)) ⋙
        DerivedCategory.Plus.ι).obj ((Scheme.Modules.pushforward i').obj
          ((Scheme.Modules.pullback i').obj ((Scheme.Modules.pullback g).obj M))) ⟶ W) =>
    h₅ =≫ k
  simp only [Category.assoc] at hU' h₄' h₅' ⊢
  rw [hU', h₄', ← h₅', h₆]

set_option backward.isDefEq.respectTransparency false in
/-- Degreewise form of `derivedRestrictionMap_comp_derivedBaseChangeMap`: restricting along `i`
and then applying the base change map on `Z` (followed by the pullback comparison) agrees with
applying the base change map on `X` and then restricting along `i'`. -/
theorem restrictionCohomologyMap_comp_baseChangeMap [IsClosedImmersion i]
    [IsClosedImmersion i'] (M : X.Modules)
    (hM : ∀ q : ℕ,
      IsZero ((higherDirectImage g (q + 1)).obj ((Scheme.Modules.pullback g).obj M)))
    (hMZ : ∀ q : ℕ, IsZero ((higherDirectImage gZ (q + 1)).obj
      ((Scheme.Modules.pullback gZ).obj ((Scheme.Modules.pullback i).obj M))))
    (hM' : ∀ q : ℕ, IsZero ((higherDirectImage g (q + 1)).obj
      ((Scheme.Modules.pushforward i').obj
        ((Scheme.Modules.pullback i').obj ((Scheme.Modules.pullback g).obj M)))))
    (n : ℕ) :
    restrictionCohomologyMap i f M n ≫
        baseChangeMap φ (i ≫ f) (i' ≫ f') gZ (square_restrict_comm φ f f' g w i i' gZ sq)
          ((Scheme.Modules.pullback i).obj M) hMZ
          (fun J hJ q => (pushforwardInjectiveAcyclic Z' Z gZ J hJ q).2 R (i ≫ f)) n ≫
        (ModuleCat.restrictScalars φ.hom).map ((relativeCohomology (i' ≫ f') n).map
          ((pullbackSquareIso g i i' gZ sq).hom.app M)) =
      baseChangeMap φ f f' g w M hM
          (fun J hJ q => (pushforwardInjectiveAcyclic X' X g J hJ q).2 R f) n ≫
        (ModuleCat.restrictScalars φ.hom).map
          (restrictionCohomologyMap i' f' ((Scheme.Modules.pullback g).obj M) n) := by
  have e₁ := derivedRestrictionMap_homology_eq i f M n
  have e₂ := derivedBaseChangeMap_homology φ (i ≫ f) (i' ≫ f') gZ
    (square_restrict_comm φ f f' g w i i' gZ sq) ((Scheme.Modules.pullback i).obj M) hMZ n
  have e₃ := derivedBaseChangeMap_homology φ f f' g w M hM n
  have e₄ := derivedRestrictionMap_homology_eq i' f' ((Scheme.Modules.pullback g).obj M) n
  have e₅ : (DerivedCategory.homologyFunctor (ModuleCat.{u} R') (n : ℤ)).map
        ((DerivedPlus.derivedComplex (relativeGlobalSections (i' ≫ f')) ⋙
          DerivedCategory.Plus.ι).map ((pullbackSquareIso g i i' gZ sq).hom.app M)) ≫
        (DerivedPlus.homologyIso (relativeGlobalSections (i' ≫ f'))
          (injectiveResolution ((Scheme.Modules.pullback i').obj
            ((Scheme.Modules.pullback g).obj M))) n).hom =
      (DerivedPlus.homologyIso (relativeGlobalSections (i' ≫ f'))
          (injectiveResolution ((Scheme.Modules.pullback gZ).obj
            ((Scheme.Modules.pullback i).obj M))) n).hom ≫
        (relativeCohomology (i' ≫ f') n).map ((pullbackSquareIso g i i' gZ sq).hom.app M) :=
    DerivedPlus.homologyIso_hom_naturality _ _ _ _ n
  have e₆ := DerivedPlus.mapDerivedCategoryHomologyIso_hom_naturality
    (ModuleCat.restrictScalars φ.hom) (n : ℤ)
    ((DerivedPlus.derivedComplex (relativeGlobalSections (i' ≫ f')) ⋙
      DerivedCategory.Plus.ι).map ((pullbackSquareIso g i i' gZ sq).hom.app M))
  have e₇ := DerivedPlus.mapDerivedCategoryHomologyIso_hom_naturality
    (ModuleCat.restrictScalars φ.hom) (n : ℤ)
    (derivedRestrictionMap i' f' ((Scheme.Modules.pullback g).obj M))
  have main := congrArg (DerivedCategory.homologyFunctor (ModuleCat.{u} R) (n : ℤ)).map
    (derivedRestrictionMap_comp_derivedBaseChangeMap φ f f' g w i i' gZ sq M hM hMZ hM')
  have main' := main =≫
    ((DerivedPlus.mapDerivedCategoryHomologyIso (ModuleCat.restrictScalars φ.hom) (n : ℤ)).hom.app
        ((DerivedPlus.derivedComplex (relativeGlobalSections (i' ≫ f')) ⋙
          DerivedCategory.Plus.ι).obj
          ((Scheme.Modules.pullback i').obj ((Scheme.Modules.pullback g).obj M))) ≫
      (ModuleCat.restrictScalars φ.hom).map
        (DerivedPlus.homologyIso (relativeGlobalSections (i' ≫ f'))
          (injectiveResolution ((Scheme.Modules.pullback i').obj
            ((Scheme.Modules.pullback g).obj M))) n).hom)
  simp only [Functor.map_comp, Category.assoc, Functor.comp_map, Functor.comp_obj] at main' e₄ e₅
  rw [reassoc_of% e₆, ← Functor.map_comp (ModuleCat.restrictScalars φ.hom), e₅,
    Functor.map_comp (ModuleCat.restrictScalars φ.hom), reassoc_of% e₂, reassoc_of% e₁,
    reassoc_of% e₇, ← Functor.map_comp (ModuleCat.restrictScalars φ.hom), e₄,
    Functor.map_comp (ModuleCat.restrictScalars φ.hom), reassoc_of% e₃] at main'
  exact (cancel_epi _).1 main'

end Square

end Langlands.AlgebraicGeometry.Modules.DerivedSections
