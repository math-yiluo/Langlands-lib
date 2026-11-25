/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Algebra.Category.ModuleCat.AB
import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleShriekSpecializationZero
import all WeilConjectures.AlgebraicGeometry.ProEtale.Ringed.ProEtaleRingedLocalizationSequence
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
import Mathlib.CategoryTheory.Sites.Adjunction
import Mathlib.Algebra.Category.ModuleCat.Adjunctions
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Mono

/-!
# Proper direct image preserves quasi-compact open support

## References

* Stacks Project, Tags 096V, 09AG and 09AH
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

variable (A : Type u) [CommRing A]

private theorem fixed_shriek_specialization_zero
    {X Z : Scheme.{u}} (U : X.ProEt) [Mono U.hom] (i : Z ⟶ X) [IsClosedImmersion i]
    (hd : IsEmpty ↥(pullback U.hom i)) (Q : X.ProEt) [IsAffine Q.left]
    (hs : ∀ q : Q.left, ∃ z : ↥(pullback Q.hom i),
      Specializes q ((pullback.fst Q.hom i) z))
    (G : Sheaf (ProEt.topology U.left) (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) :
    Subsingleton
      (((ProEtale.localizationLowerShriek
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) U.hom U.prop).obj G).obj.obj (op Q)) := by
  let L := (MorphismProperty.Over.map ⊤ U.prop).op
  let H := forget₂ (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) AddCommGrpCat.{u + 1}
  let P := L.leftKanExtension G.obj
  have : (ModuleCat.restrictScalars.{u + 1}
      (algebraMap ℤ (ULift.{u + 1, u} A))).IsLeftAdjoint :=
    (ModuleCat.restrictCoextendScalarsAdj.{0, 0, u + 1}
      (algebraMap ℤ (ULift.{u + 1, u} A))).isLeftAdjoint
  have : H.IsLeftAdjoint := Functor.isLeftAdjoint_of_iso
    (F := ModuleCat.restrictScalars.{u + 1} (algebraMap ℤ (ULift.{u + 1, u} A)) ⋙
      forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1})
    (NatIso.ofComponents (fun _ ↦ Iso.refl _) fun _ ↦ rfl)
  have : (ProEt.topology X).PreservesSheafification H :=
    Sheaf.preservesSheafification_of_adjunction _ (Adjunction.ofIsLeftAdjoint H)
  let e₁ := sheafifyComposeIso (ProEt.topology X) H P
  let e₂ := H.leftKanExtensionCompIsoOfPreserves G.obj L
  let e := e₁.symm ≪≫
    (sheafToPresheaf (ProEt.topology X) AddCommGrpCat.{u + 1}).mapIso
      ((presheafToSheaf (ProEt.topology X) AddCommGrpCat.{u + 1}).mapIso e₂)
  have hz := ProEt.shriek_sections_subsingleton_of_specializes_closed U i hd Q hs
    ((sheafCompose (ProEt.topology U.left) H).obj G)
  refine ⟨fun x y ↦ ?_⟩
  apply (ConcreteCategory.bijective_of_isIso (e.app (op Q)).hom).injective
  exact @Subsingleton.elim _ hz _ _

private theorem fixed_shriek_specialization_zero_general
    {X Z : Scheme.{u}} (U : X.ProEt) [Mono U.hom] (i : Z ⟶ X) [IsClosedImmersion i]
    (hd : IsEmpty ↥(pullback U.hom i)) (Q : X.ProEt)
    [CompactSpace Q.left] [QuasiSeparatedSpace Q.left]
    (hs : ∀ q : Q.left, ∃ z : ↥(pullback Q.hom i),
      Specializes q ((pullback.fst Q.hom i) z))
    (G : Sheaf (ProEt.topology U.left) (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) :
    Subsingleton
      (((ProEtale.localizationLowerShriek
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) U.hom U.prop).obj G).obj.obj (op Q)) := by
  classical
  let E := Q.left.affineCover.finiteSubcover
  let B (j : E.I₀) := E.X j
  let C (j : E.I₀) : Set (B j) := (E.f j ≫ Q.hom) ⁻¹' Set.range i
  have hC (j : E.I₀) : IsClosed (C j) :=
    i.isClosedEmbedding.isClosed_range.preimage (E.f j ≫ Q.hom).continuous
  choose W w hW hw hreach hspec using
    fun j ↦ ProEt.exists_closed_specialization_localization (B j) (C j) (hC j)
  let T (j : E.I₀) : X.ProEt :=
    have := hw j
    ProEt.mk (w j ≫ E.f j ≫ Q.hom)
  let f (j : E.I₀) : T j ⟶ Q := MorphismProperty.Over.homMk (w j ≫ E.f j)
  have hsurj : ∀ q : Q.left, ∃ j, q ∈ Set.range (f j).left := by
    intro q
    obtain ⟨z, hqz⟩ := hs q
    obtain ⟨j, t, ht⟩ := E.exists_eq (pullback.fst Q.hom i z)
    have htC : t ∈ C j := by
      refine ⟨pullback.snd Q.hom i z, ?_⟩
      change i _ = Q.hom (E.f j t)
      rw [ht]
      exact (congrArg (fun a : pullback Q.hom i ⟶ X ↦ a z)
        (pullback.condition (f := Q.hom) (g := i))).symm
    obtain ⟨q', hq't, hq'q⟩ := Flat.generalizingMap (E.f j) (ht ▸ hqz)
    obtain ⟨b, hb⟩ := hreach j q' ⟨t, htC, hq't⟩
    exact ⟨j, b, by change E.f j (w j b) = q; rw [hb, hq'q]⟩
  have hcover : Presieve.ofArrows T f ∈ ProEt.precoverage X Q := by
    rw [ProEt.mem_precoverage_iff, Presieve.map_ofArrows]
    refine ⟨?_, ?_⟩
    · let E' : PreZeroHypercover Q.left :=
        ⟨E.I₀, fun j ↦ (T j).left, fun j ↦ (f j).left⟩
      change E'.presieve₀ ∈ Scheme.qcPrecoverage Q.left
      rw [Scheme.presieve₀_mem_qcPrecoverage_iff]
      refine ⟨fun {H} hH ↦ ?_⟩
      have (j : E.I₀) : IsAffine (T j).left := hW j
      exact IsCompactOpenCovered.of_finite_of_isSpectralMap
        (fun j ↦ (f j).left.isSpectralMap) (fun q _ ↦ hsurj q) H.2 hH.isCompact
    · apply (Scheme.ofArrows_mem_precoverage_iff _).mpr
      refine ⟨hsurj, fun j ↦ ?_⟩
      have := hw j
      change WeaklyEtale (w j ≫ E.f j)
      infer_instance
  let F := (ProEtale.localizationLowerShriek
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) U.hom U.prop).obj G
  have hF := (isSheaf_iff_isSheaf_of_type _ _).mp
    ((Presheaf.isSheaf_iff_isSheaf_forget _ _
      (CategoryTheory.forget (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))).mp F.property)
  refine ⟨fun s t ↦ ?_⟩
  apply (hF.isSheafFor_of_mem_precoverage hcover).isSeparatedFor.ext
  rintro R g ⟨j⟩
  have hT : IsAffine (T j).left := hW j
  have hsT : ∀ t : (T j).left, ∃ z : ↥(pullback (T j).hom i),
      Specializes t ((pullback.fst (T j).hom i) z) := by
    intro t
    obtain ⟨t', htt', z, hz⟩ := hspec j t
    obtain ⟨z', hz', _⟩ := Scheme.Pullback.exists_preimage_pullback
      (f := (T j).hom) (g := i) t' z hz.symm
    exact ⟨z', hz'.symm ▸ htt'⟩
  exact @Subsingleton.elim _ (fixed_shriek_specialization_zero A U i hd (T j) hsT G) _ _

private theorem proper_shriek_specialization_zero
    {V T Z W : Scheme.{u}} (p : V ⟶ T) [IsProper p]
    (j : W ⟶ T) [IsOpenImmersion j] (i : Z ⟶ T) [IsClosedImmersion i]
    (hdis : Disjoint (Set.range j) (Set.range i))
    (Q : T.ProEt) [IsAffine Q.left]
    (hs : ∀ q : Q.left, ∃ z : ↥(pullback Q.hom i),
      Specializes q ((pullback.fst Q.hom i) z))
    (M : Sheaf (ProEt.topology (pullback p j))
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) :
    Subsingleton (((ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) p).obj
      ((ProEtale.openImmersionLowerShriek
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) (pullback.fst p j)).obj M)).obj.obj
          (op Q)) := by
  let R := (MorphismProperty.Over.pullback @WeaklyEtale ⊤ p).obj Q
  let iV := pullback.fst p i
  let U : V.ProEt := ProEt.mk (pullback.fst p j)
  have : Mono U.hom := inferInstanceAs (Mono (pullback.fst p j))
  have hd : IsEmpty ↥(pullback U.hom iV) := by
    refine ⟨fun x ↦ ?_⟩
    let a := pullback.fst U.hom iV x
    let b := pullback.snd U.hom iV x
    have hab : U.hom a = iV b :=
      congrArg (fun f : pullback U.hom iV ⟶ V ↦ f x) pullback.condition
    have h₁ : p (U.hom a) ∈ Set.range j := by
      refine ⟨pullback.snd p j a, ?_⟩
      exact (congrArg (fun f : pullback p j ⟶ T ↦ f a)
        (pullback.condition (f := p) (g := j))).symm
    have h₂ : p (U.hom a) ∈ Set.range i := by
      rw [hab]
      refine ⟨pullback.snd p i b, ?_⟩
      exact (congrArg (fun f : pullback p i ⟶ T ↦ f b)
        (pullback.condition (f := p) (g := i))).symm
    exact Set.disjoint_left.mp hdis h₁ h₂
  have : IsAffine ((𝟭 Scheme).obj Q.left) := inferInstanceAs (IsAffine Q.left)
  have hR : CompactSpace R.left :=
    inferInstanceAs (CompactSpace ↥(pullback Q.hom p))
  have hsep : R.left.IsSeparated := by
    rw [Scheme.isSeparated_iff]
    change IsSeparated (terminal.from (pullback Q.hom p))
    rw [← terminal.comp_from (pullback.fst Q.hom p)]
    infer_instance
  have hsR : ∀ q : R.left, ∃ z : ↥(pullback R.hom iV),
      Specializes q ((pullback.fst R.hom iV) z) := by
    intro q
    obtain ⟨z, hqz⟩ := hs ((pullback.fst Q.hom p) q)
    obtain ⟨q', hqq', hq'⟩ :=
      (pullback.fst Q.hom p).isClosedMap.specializingMap hqz
    have he : p (R.hom q') = i ((pullback.snd Q.hom i) z) := by
      change p ((pullback.snd Q.hom p) q') = _
      rw [← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply, hq']
      exact congrArg (fun f : pullback Q.hom i ⟶ T ↦ f z) pullback.condition
    obtain ⟨v, hv, _⟩ := Scheme.Pullback.exists_preimage_pullback
      (f := p) (g := i) (R.hom q') ((pullback.snd Q.hom i) z) he
    obtain ⟨b, hb, _⟩ := Scheme.Pullback.exists_preimage_pullback
      (f := R.hom) (g := iV) q' v hv.symm
    exact ⟨b, hb.symm ▸ hqq'⟩
  exact fixed_shriek_specialization_zero_general A U iV hd R hsR M

/-- Proper direct image preserves support in a quasi-compact open, with fixed scalar
coefficients. -/
theorem sfFixedProperQcOpenCounit_isIso
    {V T W : Scheme.{u}} (p : V ⟶ T) [IsProper p]
    (j : W ⟶ T) [IsOpenImmersion j] [QuasiCompact j]
    (M : Sheaf (ProEt.topology (pullback p j))
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) :
    IsIso ((ProEtale.openImmersionLowerShriekAdjunction
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).counit.app
        ((ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) p).obj
          ((ProEtale.openImmersionLowerShriek
            (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) (pullback.fst p j)).obj M))) := by
  let Λ := ModuleCat.{u + 1} (ULift.{u + 1, u} A)
  let F := (ProEtale.lowerStar Λ p).obj
    ((ProEtale.openImmersionLowerShriek Λ (pullback.fst p j)).obj M)
  let adj := ProEtale.openImmersionLowerShriekAdjunction Λ j
  let c := adj.counit.app F
  have hm : Mono c := by
    apply ProEtale.mono_of_mono_openImmersionLowerShriekAdjunction_unit_app_comp
      Λ j c
    rw [adj.right_triangle_components]
    exact inferInstanceAs (Mono (𝟙 ((ProEtale.openImmersionRestriction Λ j).obj F)))
  have hl : Presheaf.IsLocallySurjective (ProEt.topology T) c.hom := by
    constructor
    intro Q s
    let U : T.ProEt := ProEt.mk j
    have : IsOpenImmersion U.hom := inferInstanceAs (IsOpenImmersion j)
    have : QuasiCompact U.hom := inferInstanceAs (QuasiCompact j)
    let i := j.closedComplement
    have hi : Set.range j = (Set.range i)ᶜ := by
      rw [Scheme.Hom.range_closedComplement, compl_compl]
    obtain ⟨I, B, b, hb, hB⟩ := localization_cover i U hi Q
    apply (ProEt.topology T).superset_covering _
      (Precoverage.generate_mem_toGrothendieck hb)
    rw [Sieve.generate_le_iff]
    rintro R a ⟨k⟩
    rcases hB k with hOpen | ⟨hAff, _, hs⟩
    · obtain ⟨φ⟩ := hOpen
      have hφ : φ.left ≫ U.hom = (B k).hom := MorphismProperty.Over.w φ
      have : WeaklyEtale (φ.left ≫ U.hom) := hφ.symm ▸ (B k).prop
      have : WeaklyEtale φ.left := WeaklyEtale.of_comp φ.left U.hom
      let D : U.left.ProEt := ProEt.mk φ.left
      let L := MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale U.hom)
      let e : L.obj D ≅ B k := MorphismProperty.Over.isoMk (Iso.refl _) (by
        change (B k).hom = φ.left ≫ U.hom
        exact hφ.symm)
      have hcD : IsIso (c.hom.app (op (L.obj D))) :=
        inferInstanceAs (IsIso (((ProEtale.openImmersionRestriction Λ j).map c).hom.app
          (op D)))
      have : IsIso (c.hom.app (op (B k))) :=
        (NatTrans.isIso_app_iff_of_iso c.hom e.op).mpr hcD
      exact (ConcreteCategory.bijective_of_isIso (c.hom.app (op (B k)))).surjective
        (F.obj.map (b k).op s)
    · have : IsAffine (B k).left := hAff
      have hz := proper_shriek_specialization_zero A p j i
        (by rw [Scheme.Hom.range_closedComplement]; exact disjoint_compl_right) (B k) hs M
      exact ⟨0, @Subsingleton.elim _ hz _ _⟩
  have he : Epi c := Sheaf.epi_of_isLocallySurjective c
  exact isIso_of_mono_of_epi c

end AlgebraicGeometry.Scheme
