/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.FunctionField
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Algebra
/-! # A dominant field point of the reduced generic pullback

Source: Stacks Project, Tags 0559 and 030R. -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Topology
namespace AlgebraicGeometry
/-- The generic fibre is reduced because its affine ring is a localization of the
reduced source ring. The residue field at the generic point identifies with the actual
function field of the integral base. Source: Stacks Project, Tag 0559, second proof.
(blueprint: lem-sbc-reduced-generic-fibre-field-embedding-core-map) -/
private theorem reduced_generic_fibre
    {Z S : Scheme.{u}} [IsAffine Z] [IsReduced Z] [IsAffine S] [IsIntegral S]
    (g : Z ⟶ S) (η : S) (hη : IsGenericPoint η Set.univ) :
    IsReduced (g.fiber η) := by
  classical
  have heq : η = genericPoint S := hη.eq (genericPoint_spec S)
  subst η
  have : Nonempty (⊤ : S.Opens) := ⟨⟨genericPoint S, trivial⟩⟩
  have hr : IsIso (S.residue (genericPoint S)) := by
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    exact ⟨(show S.functionField →+* S.residueField (genericPoint S) from
      (S.residue (genericPoint S)).hom).injective, S.residue_surjective _⟩
  let A := Γ(S, ⊤)
  let B := Γ(Z, ⊤)
  let C := Γ(Spec (S.residueField (genericPoint S)), ⊤)
  let D := Γ(g.fiber (genericPoint S), ⊤)
  let t := S.fromSpecResidueField (genericPoint S)
  let : Algebra A B := g.appTop.hom.toAlgebra
  let : Algebra A C := t.appTop.hom.toAlgebra
  let : Algebra B D := (g.fiberι (genericPoint S)).appTop.hom.toAlgebra
  let : Algebra C D := (g.fiberToSpecResidueField (genericPoint S)).appTop.hom.toAlgebra
  let : Algebra A D := ((g.fiberι (genericPoint S)).appTop.hom.comp g.appTop.hom).toAlgebra
  have : IsScalarTower A B D := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower A C D := by
    apply IsScalarTower.of_algebraMap_eq'
    have he := congrArg Scheme.Hom.appTop (g.fiber_fac (genericPoint S))
    simp only [Scheme.Hom.comp_appTop] at he
    exact congrArg CommRingCat.Hom.hom he
  let e : C ≅ S.functionField :=
    Scheme.ΓSpecIso (S.residueField (genericPoint S)) ≪≫ (asIso (S.residue _)).symm
  let : Algebra A S.functionField := (S.germToFunctionField ⊤).hom.toAlgebra
  let eA : C ≃ₐ[A] S.functionField :=
    { e.commRingCatIsoToRingEquiv with
      commutes' := by
        intro x
        have he : t.appTop ≫ e.hom = S.germToFunctionField ⊤ := by
          change (Spec.map (S.residue _) ≫ S.fromSpecStalk _).appTop ≫
            ((Scheme.ΓSpecIso _).hom ≫ inv (S.residue _)) = _
          rw [Scheme.Hom.comp_appTop, Category.assoc,
            Scheme.ΓSpecIso_naturality_assoc, Scheme.fromSpecStalk_appTop]
          simp [Scheme.germToFunctionField, Category.assoc]
        exact congr($(he) x) }
  have : IsFractionRing A S.functionField :=
    functionField_isFractionRing_of_isAffineOpen S ⊤ (isAffineOpen_top S)
  have : IsFractionRing A C := IsFractionRing.of_algEquiv eA.symm
  have H := isPushout_appTop_of_isPullback (IsPullback.of_hasPullback g t)
  have : Algebra.IsPushout A C B D :=
    CommRingCat.isPushout_iff_isPushout.mp H.flip
  have : Algebra.IsPushout A B C D := Algebra.IsPushout.symm inferInstance
  have : IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors A)) D :=
    (Algebra.isLocalization_iff_isPushout (nonZeroDivisors A) C).mpr inferInstance
  have : _root_.IsReduced D :=
    isReduced_localizationPreserves (Algebra.algebraMapSubmonoid B (nonZeroDivisors A))
      D inferInstance
  exact isReduced_of_isAffine_isReduced _

set_option backward.isDefEq.respectTransparency false in
/-- A lift already constructed from the original dominant field point is dominant.
Source: Stacks Project, Tag 0559, second proof, and Tag 030R.
Proof: after transporting the residue field along e, its spectrum map is a
universal homeomorphism because k'/k is purely inseparable. The fibre comparison
is its base change. The reduction immersion is closed and surjective; base changing
it to the generic fibre is again a universal homeomorphism. Compose these two
comparisons to get d. The two identities on h show h ≫ d is the original dominant
field point precomposed with Spec E → Spec L, which is surjective. Since d is a
homeomorphism, h has dense range. The generic fibre of the reduced pullback is
reduced by localization at the integral base's generic point, as proved above.
Mathlib then turns dominance into scheme-theoretic dominance. The identity
extension and arbitrary characteristic are included; no lift is constructed here.
(blueprint: lem-sbc-reduced-generic-fibre-field-embedding-core-map) -/
private theorem reduced_generic_fibre_lift_dominant
    {Z S S' : Scheme.{u}} [IsAffine Z] [IsAffine S] [IsAffine S'] [IsIntegral S']
    (g : Z ⟶ S) (q : S' ⟶ S) (η : S) (η' : S') (hq : q η' = η)
    (hη' : IsGenericPoint η' Set.univ)
    (L k' E : Type u) [Field L] [Field k'] [Field E]
    [Algebra (S.residueField η) L] [Algebra (S.residueField η) k']
    [Algebra L E] [Algebra k' E]
    [Module.Finite (S.residueField η) k'] [IsPurelyInseparable (S.residueField η) k']
    (j : Spec (.of L) ⟶ g.fiber η) (hj : IsSchemeTheoreticallyDominant j)
    (hjbase : j ≫ g.fiberToSpecResidueField η =
      Spec.map (CommRingCat.ofHom (algebraMap (S.residueField η) L)))
    (e : S'.residueField η' ≃+* k')
    (he : e.toRingHom.comp
      (((S.residueFieldCongr hq).inv ≫ q.residueFieldMap η').hom) =
        algebraMap (S.residueField η) k')
    (hsquare : (algebraMap k' E).comp (algebraMap (S.residueField η) k') =
      (algebraMap L E).comp (algebraMap (S.residueField η) L))
    (aE : Algebra (S'.residueField η') E)
    (haE : @algebraMap (S'.residueField η') E _ _ aE = (algebraMap k' E).comp e.toRingHom) :
    letI := aE
    ∀ h : Spec (.of E) ⟶
        ((pullback g q).nilradical.subschemeι ≫ pullback.snd g q).fiber η',
      h ≫ ((pullback g q).nilradical.subschemeι ≫
        pullback.snd g q).fiberToSpecResidueField η' =
          Spec.map (CommRingCat.ofHom (algebraMap (S'.residueField η') E)) →
      h ≫ ((pullback g q).nilradical.subschemeι ≫ pullback.snd g q).fiberι η' ≫
        (pullback g q).nilradical.subschemeι ≫ pullback.fst g q =
          Spec.map (CommRingCat.ofHom (algebraMap L E)) ≫ j ≫ g.fiberι η →
      IsSchemeTheoreticallyDominant h := by
  let := aE
  intro h hb hc
  subst η
  let r : S.residueField (q η') ⟶ S'.residueField η' := q.residueFieldMap η'
  have hr : IsUniversalHomeomorphism (Spec.map r) := by
    let er : S'.residueField η' ⟶ CommRingCat.of k' := CommRingCat.ofHom e.toRingHom
    have : IsIso er := (ConcreteCategory.isIso_iff_bijective er).mpr e.bijective
    have hre : r ≫ er = CommRingCat.ofHom (algebraMap (S.residueField (q η')) k') := by
      apply CommRingCat.hom_ext
      simpa [r, er] using he
    have heq : Spec.map r = Spec.map (inv er) ≫
        Spec.map (CommRingCat.ofHom (algebraMap (S.residueField (q η')) k')) := by
      rw [← hre, Spec.map_comp]
      simp
    rw [heq]
    infer_instance
  let P := pullback g q
  let i := P.nilradical.subschemeι
  let p := pullback.snd g q
  let f := i ≫ p
  let v : f.fiber η' ⟶ p.fiber η' :=
    pullback.map _ _ _ _ i (𝟙 _) (𝟙 _) (by simp [f]) (by simp)
  have hvb : v ≫ p.fiberToSpecResidueField η' = f.fiberToSpecResidueField η' := by
    simp [v, Scheme.Hom.fiberToSpecResidueField, pullback.map]
  have hv : IsPullback (f.fiberι η') v i (p.fiberι η') := by
    apply IsPullback.flip
    apply IsPullback.of_right (h₁₂ := p.fiberToSpecResidueField η') (h₂₂ := p)
    · rw [hvb]
      exact (IsPullback.of_hasPullback f (S'.fromSpecResidueField η')).flip
    · simp [v, Scheme.Hom.fiberι, pullback.map]
    · exact (IsPullback.of_hasPullback p (S'.fromSpecResidueField η')).flip
  have : Surjective i := by
    constructor
    rw [← Set.range_eq_univ, Scheme.IdealSheafData.range_subschemeι,
      Scheme.support_nilradical]
    rfl
  have : IsUniversalHomeomorphism i := inferInstance
  have : IsUniversalHomeomorphism v :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hv inferInstance
  let c : p.fiber η' ⟶ g.fiber (q η') :=
    pullback.map _ _ _ _ (pullback.fst g q) (Spec.map r) q
      (pullback.condition.symm) (by simp [r])
  have hcPB : IsPullback c (p.fiberToSpecResidueField η')
      (g.fiberToSpecResidueField (q η')) (Spec.map r) :=
    isPullback_fiberToSpecResidueField_of_isPullback
      (IsPullback.of_hasPullback g q) η'
  have : IsUniversalHomeomorphism c :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hcPB.flip inferInstance
  let d := v ≫ c
  have hd : IsUniversalHomeomorphism d := inferInstance
  have hdcomp : h ≫ d = Spec.map (CommRingCat.ofHom (algebraMap L E)) ≫ j := by
    apply pullback.hom_ext
    · simpa [d, c, v, Scheme.Hom.fiberι, Category.assoc] using hc
    · simp only [d, c, Category.assoc, pullback.map, pullback.lift_snd]
      change h ≫ (v ≫ p.fiberToSpecResidueField η') ≫ Spec.map r =
        Spec.map (CommRingCat.ofHom (algebraMap L E)) ≫
          (j ≫ g.fiberToSpecResidueField (q η'))
      rw [hvb, ← Category.assoc, hb, hjbase, ← Spec.map_comp, ← Spec.map_comp]
      congr 1
      apply CommRingCat.hom_ext
      change (algebraMap (S'.residueField η') E).comp r.hom = _
      rw [haE, RingHom.comp_assoc]
      have he' : e.toRingHom.comp r.hom = algebraMap (S.residueField (q η')) k' := by
        simpa [r] using he
      rw [he', hsquare]
      rfl
  have : IsSchemeTheoreticallyDominant j := hj
  have : IsDominant j := inferInstance
  have hl : Surjective (Spec.map (CommRingCat.ofHom (algebraMap L E))) :=
    ⟨fun x ↦ ⟨IsLocalRing.closedPoint E, Subsingleton.elim _ _⟩⟩
  have : IsDominant (h ≫ d) := by
    rw [hdcomp]
    infer_instance
  have hdom : IsDominant h := by
    constructor
    have hh := (h ≫ d).denseRange
    change DenseRange (d ∘ h) at hh
    rw [DenseRange, d.isHomeomorph.isInducing.dense_iff]
    intro x
    rw [← Set.range_comp]
    exact hh (d x)
  have : IsReduced P.nilradical.subscheme := inferInstance
  have : IsAffine P := inferInstance
  have : IsAffine P.nilradical.subscheme := isAffine_of_isAffineHom i
  have : IsReduced (f.fiber η') := reduced_generic_fibre f η' hη'
  exact IsSchemeTheoreticallyDominant.of_isDominant h

/-- The affine reduction and generic-fibre construction supplies the dominant map;
its compatibility with the chosen residue-field embedding is handled separately.
Proof: the compatibility of aE with e gives the scalar square. Lift the original
field point through the pullback, then through its reduction (the field source kills
nilpotents), and finally to the fibre. Its two projection identities are the pullback
identities. The induced residue-field map is a purely inseparable extension, so the
comparison from the pullback fibre to the original fibre is a universal homeomorphism.
Base change of the surjective reduction immersion is also a universal homeomorphism.
Their composite transfers dominance of the original field point to h. The reduced
pullback's generic fibre is reduced: its affine ring is a localization of the reduced
source ring, since the base residue field is its fraction field. Dominance into this
reduced fibre gives scheme-theoretic dominance. Source: Stacks Project, Tags 0559 and 030R.
(blueprint: lem-sbc-reduced-generic-fibre-field-embedding-core-map) -/
theorem exists_reduced_generic_fibre_map_core
    {Z S S' : Scheme.{u}} [IsAffine Z] [IsAffine S] [IsAffine S'] [IsIntegral S']
    (g : Z ⟶ S) (q : S' ⟶ S) (η : S) (η' : S') (hq : q η' = η)
    (hη' : IsGenericPoint η' Set.univ)
    (L k' E : Type u) [Field L] [Field k'] [Field E]
    [Algebra (S.residueField η) L] [Algebra (S.residueField η) k']
    [Algebra L E] [Algebra k' E]
    [Module.Finite (S.residueField η) k'] [IsPurelyInseparable (S.residueField η) k']
    (j : Spec (.of L) ⟶ g.fiber η) (hj : IsSchemeTheoreticallyDominant j)
    (hjbase : j ≫ g.fiberToSpecResidueField η =
      Spec.map (CommRingCat.ofHom (algebraMap (S.residueField η) L)))
    (e : S'.residueField η' ≃+* k')
    (he : e.toRingHom.comp
      (((S.residueFieldCongr hq).inv ≫ q.residueFieldMap η').hom) =
        algebraMap (S.residueField η) k')
    (hsquare : (algebraMap k' E).comp (algebraMap (S.residueField η) k') =
      (algebraMap L E).comp (algebraMap (S.residueField η) L))
    (aE : Algebra (S'.residueField η') E)
    (haE : aE = ((algebraMap k' E).comp e.toRingHom).toAlgebra) :
    letI := aE
    ∃ h : Spec (.of E) ⟶
          ((pullback g q).nilradical.subschemeι ≫ pullback.snd g q).fiber η',
        IsSchemeTheoreticallyDominant h ∧
        h ≫ ((pullback g q).nilradical.subschemeι ≫
          pullback.snd g q).fiberToSpecResidueField η' =
            Spec.map (CommRingCat.ofHom (algebraMap (S'.residueField η') E)) := by
  let := aE
  have haEr : algebraMap (S'.residueField η') E =
      (algebraMap k' E).comp e.toRingHom := by
    change (@algebraMap (S'.residueField η') E _ _ aE) = _
    rw [haE]
    rfl
  let l : Spec (.of E) ⟶ Spec (.of L) :=
    Spec.map (CommRingCat.ofHom (algebraMap L E))
  let b : Spec (.of E) ⟶ Spec (S'.residueField η') :=
    Spec.map (CommRingCat.ofHom (algebraMap (S'.residueField η') E))
  let r : S.residueField η ⟶ S'.residueField η' :=
    (S.residueFieldCongr hq).inv ≫ q.residueFieldMap η'
  have hr : Spec.map r ≫ S.fromSpecResidueField η =
      S'.fromSpecResidueField η' ≫ q := by
    dsimp [r]
    simp only [Spec.map_comp, Category.assoc]
    simp
  have hscalar : b ≫ Spec.map r =
      l ≫ Spec.map (CommRingCat.ofHom (algebraMap (S.residueField η) L)) := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    change (@algebraMap (S'.residueField η') E _ _ aE).comp r.hom = _
    rw [haEr, RingHom.comp_assoc, he, hsquare]
    rfl
  have hw : (l ≫ j ≫ g.fiberι η) ≫ g =
      (b ≫ S'.fromSpecResidueField η') ≫ q := by
    rw [Category.assoc, Category.assoc, g.fiber_fac, ← Category.assoc j,
      hjbase, ← Category.assoc l, ← hscalar, Category.assoc b, hr]
    simp only [Category.assoc]
  let t := pullback.lift (l ≫ j ≫ g.fiberι η)
    (b ≫ S'.fromSpecResidueField η') hw
  have hk : (pullback g q).nilradical.subschemeι.ker ≤ t.ker := by
    rw [Scheme.IdealSheafData.ker_subschemeι]
    intro U x hx
    rw [Scheme.Hom.ker_apply]
    exact (show IsNilpotent x from hx).map (t.app U).hom |>.eq_zero
  let tr := IsClosedImmersion.lift (pullback g q).nilradical.subschemeι t hk
  have htr : tr ≫ (pullback g q).nilradical.subschemeι = t :=
    IsClosedImmersion.lift_fac _ _ _
  let f := (pullback g q).nilradical.subschemeι ≫ pullback.snd g q
  have htrbase : tr ≫ f = b ≫ S'.fromSpecResidueField η' := by
    dsimp [f]
    rw [← Category.assoc, htr]
    exact pullback.lift_snd _ _ _
  let h : Spec (.of E) ⟶ f.fiber η' := pullback.lift tr b htrbase
  have hb : h ≫ f.fiberToSpecResidueField η' = b := pullback.lift_snd _ _ _
  have hc : h ≫ f.fiberι η' ≫ (pullback g q).nilradical.subschemeι ≫
      pullback.fst g q = l ≫ j ≫ g.fiberι η := by
    rw [← Category.assoc h, show h ≫ f.fiberι η' = tr from pullback.lift_fst _ _ _,
      ← Category.assoc tr, htr]
    exact pullback.lift_fst _ _ _
  exact ⟨h, reduced_generic_fibre_lift_dominant g q η η' hq hη' L k' E
    j hj hjbase e he hsquare aE haEr h hb hc, hb⟩
end AlgebraicGeometry
