import Langlands.AlgebraicGeometry.Picard.PoincareDirectImageSupport
import Langlands.AlgebraicGeometry.Modules.HigherDirectImageVanishingAffineBaseChangeProof
import Langlands.AlgebraicGeometry.Modules.HigherDirectImageOpenRestriction
import Langlands.Cohomology.PerfectModuleComplex
import Langlands.Cohomology.DerivedPlus

/-! # Cohomology of the Poincaré bundle over affine schemes avoiding the origin -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.AlgebraicGeometry.Modules
open Langlands.AlgebraicGeometry.Modules.DerivedSections

section AffineVanishing

variable (K : Type u) [Field K] [IsAlgClosed K] (A : AbelianScheme (Spec (CommRingCat.of K)))
  (hA : HasDualScheme A)

/-- Over an affine scheme mapping to the dual away from its origin, every cohomology group of
the Poincaré bundle pulled back to a fibre product with the Poincaré projection vanishes. -/
theorem poincare_isZero_relativeCohomology_of_isPullback
    [LocallyOfFiniteType (dualScheme A hA).hom] {T : CommRingCat.{u}}
    (y : Spec T ⟶ (dualScheme A hA).left)
    (hy : ∀ t, y t ≠ (dualOrigin A hA).left (IsLocalRing.closedPoint K))
    {Z : Scheme.{u}} {a : Z ⟶ ((baseChange (dualScheme A hA).hom).obj A).X.left}
    {b : Z ⟶ Spec T} (h : IsPullback a b ((baseChange (dualScheme A hA).hom).obj A).X.hom y)
    {R : CommRingCat.{u}} (s : Z ⟶ Spec R) (n : ℕ) :
    IsZero ((relativeCohomology s n).obj
      ((Scheme.Modules.pullback a).obj (poincareLineBundle A hA).obj)) := by
  let D := dualScheme A hA
  let p := ((baseChange D.hom).obj A).X.hom
  let P := (poincareLineBundle A hA).obj
  let U := rationalPointComplement D.hom {dualOrigin A hA} (Set.finite_singleton _)
  have hU : ∀ z : D.left, z ∈ U ↔ z ≠ (dualOrigin A hA).left (IsLocalRing.closedPoint K) := by
    intro z
    simp [U, rationalPointComplement]
  have hyU : Set.range y ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨t, rfl⟩
    exact (hU _).2 (hy t)
  let x : Spec T ⟶ U.toScheme := IsOpenImmersion.lift U.ι y hyU
  have hx : x ≫ U.ι = y := IsOpenImmersion.lift_fac _ _ _
  let Q : LineBundle (p ⁻¹ᵁ U).toScheme :=
    (LineBundle.pullback (p ⁻¹ᵁ U).ι).obj (poincareLineBundle A hA)
  have hvan : ∀ q : ℕ, IsZero ((higherDirectImage (p ∣_ U) q).obj Q.obj) := by
    intro q
    refine IsZero.of_iso ?_ ((higherDirectImage (p ∣_ U) q).mapIso
      ((Scheme.Modules.restrictFunctorIsoPullback (p ⁻¹ᵁ U).ι).app P).symm)
    refine IsZero.of_iso ?_ (higherDirectImageRestrictIso p U P q)
    exact (poincareDirectImage_isZero_away_from_origin K A hA q).of_iso
      ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app _)
  have hsm : Smooth (p ∣_ U) :=
    MorphismProperty.of_isPullback (P := @Smooth) (isPullback_morphismRestrict p U).flip
      inferInstance
  have hpr : IsProper (p ∣_ U) :=
    MorphismProperty.of_isPullback (P := @IsProper) (isPullback_morphismRestrict p U).flip
      inferInstance
  have h₀ := higherDirectImageVanishingAffineBaseChange _ _ (p ∣_ U) hsm hpr Q hvan T x n
  have h₁ : IsZero ((relativeCohomology (pullback.snd (p ∣_ U) x) n).obj
      ((Scheme.Modules.pullback (pullback.fst (p ∣_ U) x ≫ (p ⁻¹ᵁ U).ι)).obj P)) :=
    h₀.of_iso ((relativeCohomology (pullback.snd (p ∣_ U) x) n).mapIso
      ((Scheme.Modules.pullbackComp (pullback.fst (p ∣_ U) x) (p ⁻¹ᵁ U).ι).app P).symm)
  have hsq : IsPullback (pullback.fst (p ∣_ U) x ≫ (p ⁻¹ᵁ U).ι) (pullback.snd (p ∣_ U) x) p
      (x ≫ U.ι) :=
    (IsPullback.of_hasPullback (p ∣_ U) x).paste_horiz (isPullback_morphismRestrict p U).flip
  exact isZero_relativeCohomology_of_isPullback p hsq h (Iso.refl _) (by simpa using hx)
    (pullback.snd (p ∣_ U) x) s P n h₁

attribute [local instance] HasDerivedCategory.standard in
/-- Let `V` be an affine open of the dual and `φ : Γ(D, V) ⟶ T` a ring map such that
`Spec T ⟶ Spec Γ(D, V) ⟶ D` avoids the origin. Every complex of `Γ(D, V)`-modules whose base
change along `φ` represents the derived sections of the Poincaré bundle on the fibre product
of the Poincaré projection with `Spec T` is acyclic after base change along `φ`. -/
theorem poincare_isZero_homology_baseChange_of_avoids_origin
    [LocallyOfFiniteType (dualScheme A hA).hom] {V : (dualScheme A hA).left.Opens}
    (hV : IsAffineOpen V) {T : CommRingCat.{u}} (φ : Γ((dualScheme A hA).left, V) ⟶ T)
    (hφ : ∀ t, (Spec.map φ ≫ hV.fromSpec) t ≠ (dualOrigin A hA).left (IsLocalRing.closedPoint K))
    (Kc : CochainComplex (ModuleCat.{u} Γ((dualScheme A hA).left, V)) ℤ)
    (e : DerivedCategory.Q.obj ((Cohomology.ModuleComplex.baseChange φ.hom).obj Kc) ≅
      DerivedCategory.Plus.ι.obj
        ((Cohomology.DerivedPlus.derivedComplex (relativeGlobalSections
          (pullback.snd (pullback.snd ((baseChange (dualScheme A hA).hom).obj A).X.hom
            hV.fromSpec) (Spec.map φ)))).obj
          ((Scheme.Modules.pullback (pullback.fst (pullback.snd
            ((baseChange (dualScheme A hA).hom).obj A).X.hom hV.fromSpec) (Spec.map φ))).obj
            ((LineBundle.pullback (pullback.fst ((baseChange (dualScheme A hA).hom).obj A).X.hom
              hV.fromSpec)).obj (poincareLineBundle A hA)).obj)))
    (n : ℤ) :
    IsZero (((Cohomology.ModuleComplex.baseChange φ.hom).obj Kc).homology n) := by
  rcases lt_or_ge n 0 with hn | hn
  · refine IsZero.of_iso ?_ ((DerivedCategory.homologyFunctorFactors _ n).app _).symm
    exact IsZero.of_iso (Cohomology.DerivedPlus.isZero_homology_of_neg _ _ hn)
      ((DerivedCategory.homologyFunctor _ n).mapIso e)
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m := ⟨n.toNat, by omega⟩
    let p := ((baseChange (dualScheme A hA).hom).obj A).X.hom
    let a₁ := pullback.fst p hV.fromSpec
    let a₂ := pullback.fst (pullback.snd p hV.fromSpec) (Spec.map φ)
    have hsq : IsPullback (a₂ ≫ a₁) (pullback.snd (pullback.snd p hV.fromSpec) (Spec.map φ)) p
        (Spec.map φ ≫ hV.fromSpec) :=
      (IsPullback.of_hasPullback (pullback.snd p hV.fromSpec) (Spec.map φ)).paste_horiz
        (IsPullback.of_hasPullback p hV.fromSpec)
    have h := poincare_isZero_relativeCohomology_of_isPullback K A hA _ hφ hsq
      (pullback.snd (pullback.snd p hV.fromSpec) (Spec.map φ)) m
    refine IsZero.of_iso ?_ (Cohomology.DerivedPlus.homologyIsoOfIsoDerivedComplex _ e m)
    exact h.of_iso ((relativeCohomology _ m).mapIso
      ((Scheme.Modules.pullbackComp a₂ a₁).app (poincareLineBundle A hA).obj))

end AffineVanishing

section BasicOpen

variable {Y : Scheme.{u}} {V : Y.Opens} (hV : IsAffineOpen V)

/-- For `f` in the prime ideal of a point `y` of an affine open `V`, the map
`Spec Γ(Y, V)_f ⟶ Y` misses `y`. -/
theorem fromSpec_away_ne_of_mem_primeIdealOf {y : Y} (hy : y ∈ V) {f : Γ(Y, V)}
    (hf : f ∈ (hV.primeIdealOf ⟨y, hy⟩).asIdeal)
    (t : Spec (CommRingCat.of (Localization.Away f))) :
    (Spec.map (CommRingCat.ofHom (algebraMap Γ(Y, V) (Localization.Away f))) ≫ hV.fromSpec) t ≠
      y := by
  intro ht
  have h1 : Spec.map (CommRingCat.ofHom (algebraMap Γ(Y, V) (Localization.Away f))) t =
      hV.primeIdealOf ⟨y, hy⟩ := by
    apply hV.fromSpec.isOpenEmbedding.injective
    rw [hV.fromSpec_primeIdealOf]
    exact ht
  have h2 : algebraMap Γ(Y, V) (Localization.Away f) f ∈ t.asIdeal := by
    have : f ∈ (Spec.map (CommRingCat.ofHom
        (algebraMap Γ(Y, V) (Localization.Away f))) t).asIdeal := by
      rw [h1]
      exact hf
    exact this
  exact t.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h2
    (IsLocalization.Away.algebraMap_isUnit f))

end BasicOpen

section Localization

variable (K : Type u) [Field K] [IsAlgClosed K] (A : AbelianScheme (Spec (CommRingCat.of K)))
  (hA : HasDualScheme A)

attribute [local instance] HasDerivedCategory.standard in
/-- Let `V` be an affine open of the dual containing its origin and `Kc` a complex of
`Γ(D, V)`-modules whose base change along every ring map `φ` represents the derived sections of
the Poincaré bundle on the fibre product of the Poincaré projection with `Spec φ`. Then `Kc`
becomes acyclic after inverting any function vanishing at the origin. -/
theorem poincare_isZero_homology_localization_of_mem_originIdeal
    [LocallyOfFiniteType (dualScheme A hA).hom] {V : (dualScheme A hA).left.Opens}
    (hV : IsAffineOpen V) (hx : (dualOrigin A hA).left (IsLocalRing.closedPoint K) ∈ V)
    (Kc : CochainComplex (ModuleCat.{u} Γ((dualScheme A hA).left, V)) ℤ)
    (hbc : ∀ (T : CommRingCat.{u}) (φ : Γ((dualScheme A hA).left, V) ⟶ T),
      Nonempty (DerivedCategory.Q.obj ((Cohomology.ModuleComplex.baseChange φ.hom).obj Kc) ≅
        DerivedCategory.Plus.ι.obj
          ((Cohomology.DerivedPlus.derivedComplex (relativeGlobalSections
            (pullback.snd (pullback.snd ((baseChange (dualScheme A hA).hom).obj A).X.hom
              hV.fromSpec) (Spec.map φ)))).obj
            ((Scheme.Modules.pullback (pullback.fst (pullback.snd
              ((baseChange (dualScheme A hA).hom).obj A).X.hom hV.fromSpec) (Spec.map φ))).obj
              ((LineBundle.pullback (pullback.fst ((baseChange (dualScheme A hA).hom).obj A).X.hom
                hV.fromSpec)).obj (poincareLineBundle A hA)).obj))))
    (f : Γ((dualScheme A hA).left, V)) (hf : f ∈ (hV.primeIdealOf ⟨_, hx⟩).asIdeal) (n : ℤ) :
    IsZero (((Cohomology.ModuleComplex.baseChange
      (algebraMap Γ((dualScheme A hA).left, V) (Localization.Away f))).obj Kc).homology n) :=
  poincare_isZero_homology_baseChange_of_avoids_origin K A hA hV
    (CommRingCat.ofHom (algebraMap Γ((dualScheme A hA).left, V) (Localization.Away f)))
    (fromSpec_away_ne_of_mem_primeIdealOf hV hx hf) Kc (hbc _ _).some n

end Localization

end Langlands.AbelianScheme
