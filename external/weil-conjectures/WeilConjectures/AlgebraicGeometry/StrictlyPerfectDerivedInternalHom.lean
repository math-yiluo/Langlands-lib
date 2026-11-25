/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import Mathlib.AlgebraicGeometry.AffineScheme
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FiniteFreeInternalHomExact
import WeilConjectures.Algebra.Homology.BoundedExactTermHomQuasiIso
import Mathlib.CategoryTheory.MorphismProperty.Retract

/-! # Internal Hom from a strictly perfect complex

Source: Stacks Project, Cohomology of Sheaves, Lemma 20.46.9, Tag 08DM
(blueprint: lem-pc-rhom-strict-perfect-hom).

The affine scheme is presented as an affine open `U` of a scheme `X`; its module
category is the recorded localized-site carrier of `Scheme.IsStrictlyPerfect`.
The comparison is computed with any functorial K-injective replacement, as in
`derivedInternalHom_comparison`. No boundedness is imposed on the second complex.
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme

private theorem shortExact_of_retract
    {A : Type*} [Category A] [Abelian A] {S T : ShortComplex A}
    (i : S ⟶ T) (r : T ⟶ S) (hir : i ≫ r = 𝟙 S) (hT : T.ShortExact) :
    S.ShortExact := by
  have h₁ : i.τ₁ ≫ r.τ₁ = 𝟙 S.X₁ := congrArg (fun f => f.τ₁) hir
  have h₂ : i.τ₂ ≫ r.τ₂ = 𝟙 S.X₂ := congrArg (fun f => f.τ₂) hir
  have h₃ : i.τ₃ ≫ r.τ₃ = 𝟙 S.X₃ := congrArg (fun f => f.τ₃) hir
  have : Mono T.f := hT.mono_f
  have : Epi T.g := hT.epi_g
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · rw [S.exact_iff_isZero_homology, IsZero.iff_id_eq_zero]
    rw [← ShortComplex.homologyMap_id, ← hir, ShortComplex.homologyMap_comp]
    have hz := T.exact_iff_isZero_homology.mp hT.exact
    rw [hz.eq_of_src (ShortComplex.homologyMap r) 0, comp_zero]
  · exact (MorphismProperty.monomorphisms A).of_retract
      { i := Arrow.homMk i.τ₁ i.τ₂ i.comm₁₂
        r := Arrow.homMk r.τ₁ r.τ₂ r.comm₁₂
        retract := by ext <;> assumption } inferInstance
  · exact (MorphismProperty.epimorphisms A).of_retract
      { i := Arrow.homMk i.τ₂ i.τ₃ i.comm₂₃
        r := Arrow.homMk r.τ₂ r.τ₃ r.comm₂₃
        retract := by ext <;> assumption } inferInstance

set_option backward.isDefEq.respectTransparency false in
private theorem internalHom_shortExact_of_finiteFree_retract
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (R : Sheaf J CommRingCat.{u})
    (E : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (m : ℕ)
    (ι : E ⟶ SheafOfModules.free
      (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (ULift.{u} (Fin m)))
    (π : SheafOfModules.free
      (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (ULift.{u} (Fin m)) ⟶ E)
    (hιπ : ι ≫ π = 𝟙 E)
    (S : ShortComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)))
    (hS : S.ShortExact) :
    ∃ hz : SheafOfModules.homObjMap (R := R) (𝟙 E) S.f ≫
        SheafOfModules.homObjMap (R := R) (𝟙 E) S.g = 0,
      (ShortComplex.mk (SheafOfModules.homObjMap (R := R) (𝟙 E) S.f)
        (SheafOfModules.homObjMap (R := R) (𝟙 E) S.g) hz).ShortExact := by
  have hz : SheafOfModules.homObjMap (R := R) (𝟙 E) S.f ≫
      SheafOfModules.homObjMap (R := R) (𝟙 E) S.g = 0 := by
    rw [SheafOfModules.homObjMap_comp_homObjMap (R := R), Category.id_comp, S.zero]
    apply SheafOfModules.hom_ext
    ext X φ : 3
    rfl
  refine ⟨hz, ?_⟩
  let F := SheafOfModules.free
    (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (ULift.{u} (Fin m))
  obtain ⟨hzF, hF, _⟩ := SheafOfModules.finiteFreeInternalHomExact
    (R := R) m F (Iso.refl F) S hS
  let T := ShortComplex.mk (SheafOfModules.homObjMap (R := R) (𝟙 F) S.f)
    (SheafOfModules.homObjMap (R := R) (𝟙 F) S.g) hzF
  let V := ShortComplex.mk (SheafOfModules.homObjMap (R := R) (𝟙 E) S.f)
    (SheafOfModules.homObjMap (R := R) (𝟙 E) S.g) hz
  let i : V ⟶ T :=
    { τ₁ := SheafOfModules.homObjMap (R := R) π (𝟙 S.X₁)
      τ₂ := SheafOfModules.homObjMap (R := R) π (𝟙 S.X₂)
      τ₃ := SheafOfModules.homObjMap (R := R) π (𝟙 S.X₃)
      comm₁₂ := by
        dsimp [V, T]
        simp only [SheafOfModules.homObjMap_comp_homObjMap (R := R),
          Category.id_comp, Category.comp_id]
      comm₂₃ := by
        dsimp [V, T]
        simp only [SheafOfModules.homObjMap_comp_homObjMap (R := R),
          Category.id_comp, Category.comp_id] }
  let r : T ⟶ V :=
    { τ₁ := SheafOfModules.homObjMap (R := R) ι (𝟙 S.X₁)
      τ₂ := SheafOfModules.homObjMap (R := R) ι (𝟙 S.X₂)
      τ₃ := SheafOfModules.homObjMap (R := R) ι (𝟙 S.X₃)
      comm₁₂ := by
        dsimp [V, T]
        simp only [SheafOfModules.homObjMap_comp_homObjMap (R := R),
          Category.id_comp, Category.comp_id]
      comm₂₃ := by
        dsimp [V, T]
        simp only [SheafOfModules.homObjMap_comp_homObjMap (R := R),
          Category.id_comp, Category.comp_id] }
  exact shortExact_of_retract i r (by
    apply ShortComplex.hom_ext <;>
      simp only [ShortComplex.comp_τ₁, ShortComplex.comp_τ₂, ShortComplex.comp_τ₃,
        ShortComplex.id_τ₁, ShortComplex.id_τ₂, ShortComplex.id_τ₃, i, r,
        SheafOfModules.homObjMap_comp_homObjMap (R := R), hιπ, Category.id_comp,
        SheafOfModules.homObjMap_id]) hF

/-- On an affine open, the ordinary Hom complex from a strictly perfect complex represents
its derived internal Hom. For every functorial K-injective replacement `η : 𝟭 ⟶ I`, the
canonical map `𝓗om^•(P, M) ⟶ 𝓗om^•(P, I(M))` becomes an isomorphism in the derived
category. Since `Q (𝓗om^•(P, I(M)))` computes derived internal Hom
(`derivedInternalHom_comparison`), this map is the ordinary-to-derived comparison.

Source: Stacks Project, Cohomology of Sheaves, Lemma 20.46.9, Tag 08DM
(blueprint: lem-pc-rhom-strict-perfect-hom).

Proof:
1. Replace `M` by a functorial K-injective resolution `η.app M : M ⟶ I.obj M`.
   By `def-pur-derived-internal-hom`, the Hom complex from `P` into this resolution
   represents derived internal Hom.
2. Each term of `P` is a direct summand of a finite free module. Its internal Hom
   functor is therefore a direct summand of an exact finite-free internal Hom functor
   (`lem-sc-finite-free-internal-hom-exact`), hence exact. It preserves the
   quasi-isomorphism to the resolution in each fixed degree of `P`.
3. The bounded stupid-truncation filtration of `P` has finitely many graded pieces
   `P^k[-k]`. Applying the Hom-complex functor gives termwise split short exact
   sequences, since only finitely many factors are nonzero. Induction, the long exact
   cohomology sequence (Stacks Tag 0117), and the five lemma show that the induced
   Hom-complex map is a quasi-isomorphism.
4. Localization inverts that map. Compose with the computation isomorphism of
   `def-pur-derived-internal-hom` to obtain the representation and the canonical
   comparison isomorphism. Functoriality makes this independent of the replacement. -/
theorem isIso_homComplex_resolution_of_isStrictlyPerfect
    (X : Scheme.{u}) (U : X.Opens) [IsAffine U.toScheme]
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      ((sheafCompose ((Opens.grothendieckTopology X).over U)
        (forget₂ CommRingCat RingCat)).obj (X.sheaf.over U)))]
    (P M : CochainComplex (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ)
    (hP : IsStrictlyPerfect X U P) :
    Nonempty (DerivedCategory.Q.obj (homComplex (R := X.sheaf.over U) P M) ≅
      (derivedInternalHom ((Opens.grothendieckTopology X).over U) (X.sheaf.over U)).obj
        (op (DerivedCategory.Q.obj P), DerivedCategory.Q.obj M)) ∧
    ∀ (I : CochainComplex (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ ⥤
        CochainComplex (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ)
      (η : 𝟭 (CochainComplex
        (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ) ⟶ I),
      (∀ N : CochainComplex (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ,
        QuasiIso (η.app N) ∧ (I.obj N).IsKInjective) →
        IsIso (DerivedCategory.Q.map
          (((homComplexFunctor (R := X.sheaf.over U)).obj (op P)).map (η.app M))) := by
  -- Use the same presentation as internal Hom so instance search reuses the structure.
  let A := SheafOfModules.{u}
    ((sheafCompose ((Opens.grothendieckTopology X).over U)
      (forget₂ CommRingCat RingCat)).obj (X.sheaf.over U))
  let : Abelian A := inferInstance
  have hexact (n : ℤ) (S : ShortComplex A) (hS : S.ShortExact) :
      ∃ hz : SheafOfModules.homObjMap (R := X.sheaf.over U) (𝟙 (P.X n)) S.f ≫
          SheafOfModules.homObjMap (R := X.sheaf.over U) (𝟙 (P.X n)) S.g = 0,
        (ShortComplex.mk
          (SheafOfModules.homObjMap (R := X.sheaf.over U) (𝟙 (P.X n)) S.f)
          (SheafOfModules.homObjMap (R := X.sheaf.over U) (𝟙 (P.X n)) S.g) hz).ShortExact := by
    obtain ⟨m, ι, π, hιπ⟩ := hP.2 n
    exact internalHom_shortExact_of_finiteFree_retract
      ((Opens.grothendieckTopology X).over U) (X.sheaf.over U) (P.X n) m ι π hιπ S hS
  have hq {N N' : CochainComplex A ℤ} (f : N ⟶ N') [QuasiIso f] :
      QuasiIso (((homComplexFunctor (R := X.sheaf.over U)).obj (op P)).map f) :=
    quasiIso_homComplex_map_of_bounded_exact_terms
      ((Opens.grothendieckTopology X).over U) (X.sheaf.over U) P hP.1 hexact f
  have hcomp (I : CochainComplex A ℤ ⥤ CochainComplex A ℤ)
      (η : 𝟭 (CochainComplex A ℤ) ⟶ I)
      (hI : ∀ N, QuasiIso (η.app N) ∧ (I.obj N).IsKInjective) :
      IsIso (DerivedCategory.Q.map
        (((homComplexFunctor (R := X.sheaf.over U)).obj (op P)).map (η.app M))) := by
    have : QuasiIso (η.app M) := (hI M).1
    have := hq (η.app M)
    infer_instance
  refine ⟨?_, hcomp⟩
  let : IsGrothendieckAbelian.{u} A := SheafOfModules.isGrothendieckAbelian _
  let I := CochainComplex.kInjectiveResolutionFunctor.{u} A
  let η := CochainComplex.toKInjectiveResolution.{u} A
  have hI (N : CochainComplex A ℤ) : QuasiIso (η.app N) ∧ (I.obj N).IsKInjective :=
    ⟨(CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u} A N).2,
      CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{u} A N⟩
  obtain ⟨e⟩ := derivedInternalHom_comparison
    ((Opens.grothendieckTopology X).over U) (X.sheaf.over U) I η hI
  have := hcomp I η hI
  exact ⟨asIso (DerivedCategory.Q.map
      (((homComplexFunctor (R := X.sheaf.over U)).obj (op P)).map (η.app M))) ≪≫
    (e.app (op P, M)).symm⟩

end AlgebraicGeometry.Scheme
