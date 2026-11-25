/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
import WeilConjectures.AlgebraicGeometry.Perfect.PerfectClosureFiniteNormalModel
import WeilConjectures.AlgebraicGeometry.Reduced.ReducedNormalizationOverNormalReduction
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Finite
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import WeilConjectures.AlgebraicGeometry.Morphisms.FiniteNormalDenseOpenIso
import WeilConjectures.AlgebraicGeometry.ProperBaseChange.NormalityPerfectClosureTest

/-!
# Geometrically normal normalization after purely inseparable extension

## References

* Stacks Project, Varieties, Tag 0BXT
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

private theorem reduced_closedImmersion_iso
    {A B : Scheme.{u}} (f : A ⟶ B) [IsClosedImmersion f] [Surjective f]
    [IsReduced A] :
    ∃ e : A ≅ B.nilradical.subscheme, e.hom ≫ B.nilradical.subschemeι = f := by
  let g := f.liftNilradical
  have hg : g ≫ B.nilradical.subschemeι = f := by simp [g]
  have : IsClosedImmersion (g ≫ B.nilradical.subschemeι) := by rw [hg]; infer_instance
  have : IsClosedImmersion g :=
    IsClosedImmersion.of_comp_isClosedImmersion g B.nilradical.subschemeι
  have : Surjective g := ⟨fun y => by
    obtain ⟨x, hx⟩ := f.surjective (B.nilradical.subschemeι y)
    refine ⟨x, B.nilradical.subschemeι.isClosedEmbedding.injective ?_⟩
    change (g ≫ B.nilradical.subschemeι) x = _
    rwa [hg]⟩
  have : IsIso g := isIso_of_isClosedImmersion_of_surjective g
  exact ⟨asIso g, hg⟩

private theorem normal_stalks_of_iso {A B : Scheme.{u}} (e : A ≅ B)
    (hA : ∀ z : A, IsDomain (A.presheaf.stalk z) ∧
      IsIntegrallyClosed (A.presheaf.stalk z)) :
    ∀ z : B, IsDomain (B.presheaf.stalk z) ∧
      IsIntegrallyClosed (B.presheaf.stalk z) := by
  intro z
  obtain ⟨hd, hi⟩ := hA (e.inv z)
  have : IsDomain (A.presheaf.stalk (e.inv z)) := hd
  have : IsIntegrallyClosed (A.presheaf.stalk (e.inv z)) := hi
  let es := (asIso (e.inv.stalkMap z)).commRingCatIsoToRingEquiv
  exact ⟨es.symm.toMulEquiv.isDomain, IsIntegrallyClosed.of_equiv es⟩

private theorem normal_stalks_of_openImmersion {A B : Scheme.{u}} (f : A ⟶ B)
    [IsOpenImmersion f]
    (hB : ∀ z : B, IsDomain (B.presheaf.stalk z) ∧
      IsIntegrallyClosed (B.presheaf.stalk z)) :
    ∀ z : A, IsDomain (A.presheaf.stalk z) ∧
      IsIntegrallyClosed (A.presheaf.stalk z) := by
  intro z
  obtain ⟨hd, hi⟩ := hB (f z)
  have : IsDomain (B.presheaf.stalk (f z)) := hd
  have : IsIntegrallyClosed (B.presheaf.stalk (f z)) := hi
  let es := (asIso (f.stalkMap z)).commRingCatIsoToRingEquiv
  exact ⟨es.symm.toMulEquiv.isDomain, IsIntegrallyClosed.of_equiv es⟩

private theorem normal_stalks_of_self_baseChange
    {k : Type u} [Field k] (Y : Scheme.{u}) (q : Y ⟶ Spec (.of k))
    (h : ∀ z : (pullback q (Spec.map
        (CommRingCat.ofHom (algebraMap k k))) : Scheme.{u}),
      IsDomain ((pullback q (Spec.map
        (CommRingCat.ofHom (algebraMap k k)))).presheaf.stalk z) ∧
      IsIntegrallyClosed ((pullback q (Spec.map
        (CommRingCat.ofHom (algebraMap k k)))).presheaf.stalk z)) :
    ∀ z : Y, IsDomain (Y.presheaf.stalk z) ∧
      IsIntegrallyClosed (Y.presheaf.stalk z) := by
  let b := Spec.map (CommRingCat.ofHom (algebraMap k k))
  have hb : b = 𝟙 (Spec (.of k)) := by simp [b]
  have : IsIso b := by rw [hb]; infer_instance
  let g := inv (pullback.fst q b)
  intro z
  obtain ⟨hd, hi⟩ := h (g z)
  have : IsDomain ((pullback q b).presheaf.stalk (g z)) := hd
  have : IsIntegrallyClosed ((pullback q b).presheaf.stalk (g z)) := hi
  let e := (asIso (g.stalkMap z)).commRingCatIsoToRingEquiv
  exact ⟨e.symm.toMulEquiv.isDomain, IsIntegrallyClosed.of_equiv e⟩

private theorem component_normalization_normal (T : Scheme.{u})
    (Z : irreducibleComponents T)
    (z : (T.reducedNormalizationComponent Z).normalization) :
    IsDomain ((T.reducedNormalizationComponent Z).normalization.presheaf.stalk z) ∧
      IsIntegrallyClosed ((T.reducedNormalizationComponent Z).normalization.presheaf.stalk z) := by
  constructor
  · infer_instance
  · apply Scheme.Hom.isIntegrallyClosed_stalk_normalization
    intro x
    let F := (T.reducedNormalizationComponent Z).functionField
    let e := (Spec.stalkIso F x).commRingCatIsoToRingEquiv
    let eF : F ≃+* Localization.AtPrime x.asIdeal := RingEquiv.ofBijective _
      (Field.localization_map_bijective (M := x.asIdeal.primeCompl) (by simp))
    have hfield : IsField ((Spec F).presheaf.stalk x) :=
      e.isField (eF.symm.isField (Field.toIsField F))
    let := hfield.toField
    infer_instance

private theorem reducedNormalization_normal (T : Scheme.{u}) :
    ∀ z : T.reducedNormalization,
      IsDomain (T.reducedNormalization.presheaf.stalk z) ∧
        IsIntegrallyClosed (T.reducedNormalization.presheaf.stalk z) := by
  intro z
  obtain ⟨i, x, hx⟩ := (sigmaOpenCover
    (fun Z : irreducibleComponents T =>
      (T.reducedNormalizationComponent Z).normalization)).exists_eq z
  obtain ⟨hd, hi⟩ := component_normalization_normal T i x
  have : IsDomain ((T.reducedNormalizationComponent i).normalization.presheaf.stalk x) := hd
  have : IsIntegrallyClosed
      ((T.reducedNormalizationComponent i).normalization.presheaf.stalk x) := hi
  subst z
  let e := (asIso ((Sigma.ι
    (fun Z : irreducibleComponents T =>
      (T.reducedNormalizationComponent Z).normalization) i).stalkMap x)).commRingCatIsoToRingEquiv
  exact ⟨e.toMulEquiv.isDomain, IsIntegrallyClosed.of_equiv e.symm⟩

private theorem reducedNormalization_finite
    {k : Type u} [Field k] (T : Scheme.{u}) (q : T ⟶ Spec (.of k))
    [LocallyOfFiniteType q] [QuasiCompact q] : IsFinite T.fromReducedNormalization := by
  classical
  have : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian q
  have : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace q
  have : IsNoetherian T := ⟨⟩
  have : Finite (irreducibleComponents T) :=
    (finite_irreducibleComponents_of_isNoetherian (X := T)).to_subtype
  have (Z : irreducibleComponents T) :
      IsFinite ((T.reducedNormalizationComponent Z).fromNormalization ≫
        (Scheme.IdealSheafData.vanishingIdeal
          ⟨Z.1, isClosed_of_mem_irreducibleComponents _ Z.2⟩).subschemeι) := by
    let a := (Scheme.IdealSheafData.vanishingIdeal
      ⟨Z.1, isClosed_of_mem_irreducibleComponents _ Z.2⟩).subschemeι
    have : LocallyOfFiniteType (a ≫ q) := inferInstance
    have := (T.reducedNormalizationComponent Z).isFinite_fromNormalization_of_locallyOfFiniteType
      (a ≫ q)
    exact inferInstance
  exact IsFinite.sigmaDesc _

private theorem reducedNormalization_dense_preimage (T : Scheme.{u}) [IsNoetherian T]
    (U : T.Opens) (hU : Dense (U : Set T)) :
    Dense (T.fromReducedNormalization ⁻¹ᵁ U : Set T.reducedNormalization) := by
  classical
  let C (Z : irreducibleComponents T) := T.reducedNormalizationComponent Z
  let a (Z : irreducibleComponents T) : C Z ⟶ T :=
    (Scheme.IdealSheafData.vanishingIdeal
      ⟨Z.1, isClosed_of_mem_irreducibleComponents _ Z.2⟩).subschemeι
  have ha (Z : irreducibleComponents T) : Set.range (a Z) = Z.1 := by
    change Set.range (Scheme.IdealSheafData.vanishingIdeal
      ⟨Z.1, isClosed_of_mem_irreducibleComponents _ Z.2⟩).subschemeι = _
    rw [Scheme.IdealSheafData.range_subschemeι]
    rfl
  have hfinite : (irreducibleComponents T).Finite :=
    finite_irreducibleComponents_of_isNoetherian (X := T)
  have hnonempty (Z : irreducibleComponents T) :
      (((C Z).fromNormalization ≫ a Z) ⁻¹ᵁ U : Set (C Z).normalization).Nonempty := by
    let W : T.Opens := ⟨(⋃₀ (irreducibleComponents T \ {Z.1}))ᶜ, by
      rw [Set.sUnion_eq_biUnion, isOpen_compl_iff]
      exact hfinite.sdiff.isClosed_biUnion
        (fun V hV => isClosed_of_mem_irreducibleComponents V hV.1)⟩
    have hW : closure (W : Set T) = Z.1 :=
      closure_sUnion_irreducibleComponents_sdiff_singleton hfinite Z.1 Z.2
    have hWne : (W : Set T).Nonempty := by
      by_contra! he
      exact Z.2.1.nonempty.ne_empty (by rw [← hW, he, closure_empty])
    obtain ⟨x, hxW, hxU⟩ := hU.inter_open_nonempty W W.isOpen hWne
    have hxZ : x ∈ Z.1 := by rw [← hW]; exact subset_closure hxW
    obtain ⟨c, hc⟩ := (ha Z).symm ▸ hxZ
    obtain ⟨z, hz⟩ := (C Z).fromNormalization.surjective c
    refine ⟨z, ?_⟩
    change a Z ((C Z).fromNormalization z) ∈ U
    rwa [hz, hc]
  intro z
  obtain ⟨i, x, rfl⟩ := (sigmaOpenCover (fun Z => (C Z).normalization)).exists_eq z
  let V := ((C i).fromNormalization ≫ a i) ⁻¹ᵁ U
  have hx : x ∈ closure (V : Set (C i).normalization) := V.isOpen.dense (hnonempty i) x
  have himg := mem_closure_image
    (Sigma.ι (fun Z => (C Z).normalization) i).continuous.continuousAt hx
  apply closure_mono _ himg
  rintro _ ⟨y, hy, rfl⟩
  change T.fromReducedNormalization ((Sigma.ι (fun Z => (C Z).normalization) i) y) ∈ U
  change ((Sigma.ι (fun Z => (C Z).normalization) i) ≫ T.fromReducedNormalization) y ∈ U
  simpa [Scheme.fromReducedNormalization, C, a, V] using hy

private theorem finite_component_normalization_presentation (T : Scheme.{u})
    [IsNoetherian T] :
    ∃ (n : ℕ) (C : Fin n → Scheme.{u}) (hC : ∀ i, IsIntegral (C i))
      (a : ∀ i, C i ⟶ T),
      (∀ i, IsClosedImmersion (a i)) ∧
      Function.Injective (fun i => Set.range (a i)) ∧
      (∀ Z : Set T, Z ∈ irreducibleComponents T ↔ ∃ i, Set.range (a i) = Z) ∧
      ∃ e : (∐ fun i => @Scheme.normalization (C i) (hC i)) ≅ T.reducedNormalization,
        e.hom ≫ T.fromReducedNormalization =
          Sigma.desc (fun i => @Scheme.fromNormalization (C i) (hC i) ≫ a i) := by
  classical
  let : Fintype (irreducibleComponents T) :=
    (finite_irreducibleComponents_of_isNoetherian (X := T)).fintype
  let n := Fintype.card (irreducibleComponents T)
  let e : Fin n ≃ irreducibleComponents T := (Fintype.equivFin _).symm
  let C (i : Fin n) := T.reducedNormalizationComponent (e i)
  let a (i : Fin n) : C i ⟶ T :=
    (Scheme.IdealSheafData.vanishingIdeal
      ⟨(e i).1, isClosed_of_mem_irreducibleComponents _ (e i).2⟩).subschemeι
  have ha (i : Fin n) : Set.range (a i) = (e i).1 := by
    change Set.range (Scheme.IdealSheafData.vanishingIdeal
      ⟨(e i).1, isClosed_of_mem_irreducibleComponents _ (e i).2⟩).subschemeι = _
    rw [Scheme.IdealSheafData.range_subschemeι]
    rfl
  refine ⟨n, C, fun i => inferInstance, a, fun i => inferInstance, ?_, ?_, ?_⟩
  · intro i j hij
    apply e.injective
    apply Subtype.ext
    simpa only [ha] using hij
  · intro Z
    constructor
    · intro hZ
      obtain ⟨i, hi⟩ := e.surjective ⟨Z, hZ⟩
      exact ⟨i, (ha i).trans (congrArg Subtype.val hi)⟩
    · rintro ⟨i, rfl⟩
      rw [ha]
      exact (e i).2
  · let r : (∐ fun i : Fin n => (C i).normalization) ≅ T.reducedNormalization :=
      Sigma.whiskerEquiv
        (f := fun i : Fin n => (C i).normalization)
        (g := fun Z : irreducibleComponents T =>
          (T.reducedNormalizationComponent Z).normalization)
        e (fun _ => Iso.refl _)
    refine ⟨r, ?_⟩
    apply Sigma.hom_ext
    intro i
    dsimp only [r]
    simp only [Iso.refl_inv, Sigma.whiskerEquiv_hom]
    simp [Scheme.fromReducedNormalization, C, a]

/-- The componentwise normalization becomes geometrically normal after a finite purely
inseparable extension `k'/k`: here the integral closed subschemes `C i` enumerate the reduced
irreducible components of `X_{k'}` without repetitions. -/
theorem exists_finite_purelyInseparable_geometricallyNormal_normalization
    (k : Type u) [Field k] (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k))] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k))] :
    ∃ (k' : Type u) (_ : Field k') (_ : Algebra k k'),
      Module.Finite k k' ∧ IsPurelyInseparable k k' ∧
      ∃ (n : ℕ) (C : Fin n → Scheme.{u}) (hC : ∀ i, IsIntegral (C i))
        (ι : ∀ i, C i ⟶ pullback (X ↘ Spec (CommRingCat.of k))
          (Spec.map (CommRingCat.ofHom (algebraMap k k')))),
        (∀ i, IsClosedImmersion (ι i)) ∧
        Function.Injective (fun i => Set.range (ι i)) ∧
        (∀ Z : Set ↥(pullback (X ↘ Spec (CommRingCat.of k))
            (Spec.map (CommRingCat.ofHom (algebraMap k k')))),
          Z ∈ irreducibleComponents ↥(pullback (X ↘ Spec (CommRingCat.of k))
            (Spec.map (CommRingCat.ofHom (algebraMap k k')))) ↔
            ∃ i, Set.range (ι i) = Z) ∧
        ∀ (L : Type u) [Field L] [Algebra k' L],
          ∀ z : ↥(pullback
            (Sigma.desc (fun i => @Scheme.fromNormalization (C i) (hC i) ≫ ι i) ≫
              pullback.snd (X ↘ Spec (CommRingCat.of k))
                (Spec.map (CommRingCat.ofHom (algebraMap k k'))))
            (Spec.map (CommRingCat.ofHom (algebraMap k' L)))),
            IsDomain ((pullback
              (Sigma.desc (fun i => @Scheme.fromNormalization (C i) (hC i) ≫ ι i) ≫
                pullback.snd (X ↘ Spec (CommRingCat.of k))
                  (Spec.map (CommRingCat.ofHom (algebraMap k k'))))
              (Spec.map (CommRingCat.ofHom (algebraMap k' L)))).presheaf.stalk z) ∧
            IsIntegrallyClosed ((pullback
              (Sigma.desc (fun i => @Scheme.fromNormalization (C i) (hC i) ≫ ι i) ≫
                pullback.snd (X ↘ Spec (CommRingCat.of k))
                  (Spec.map (CommRingCat.ofHom (algebraMap k k'))))
              (Spec.map (CommRingCat.ofHom (algebraMap k' L)))).presheaf.stalk z) := by
  classical
  let K := perfectClosure k (AlgebraicClosure k)
  let q := X ↘ Spec (CommRingCat.of k)
  obtain ⟨E, hE, Y, f, U, hf, hs, hU, hYdense, hclosed, hK⟩ :=
    exists_perfectClosure_finite_normal_model k K X q
  have : Module.Finite k E := hE
  have : IsFinite f := hf
  have : Surjective f := hs
  have : IsClosedImmersion (f ∣_ U) := hclosed
  let T := pullback q (Spec.map (CommRingCat.ofHom (algebraMap k E)))
  let p : T ⟶ Spec (.of E) := pullback.snd _ _
  have : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian p
  have : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace p
  have : IsNoetherian T := ⟨⟩
  have hpower : ∀ a : K, ∃ n : ℕ, ∃ b : E,
      algebraMap E K b = a ^ (ringExpChar E ^ n) := by
    intro a
    exact IsPurelyInseparable.pow_mem E (ringExpChar E) a
  have hgeom := (normal_stalks_perfectClosure_iff E K hpower Y (f ≫ p)).mp hK
  have hYn := normal_stalks_of_self_baseChange Y (f ≫ p) (hgeom E)
  have hfiniteN := reducedNormalization_finite T p
  have hN := reducedNormalization_normal T
  have hNdense := reducedNormalization_dense_preimage T U
    (by simpa [Scheme.Opens.range_ι] using hU)
  have (z : Y) : IsDomain (Y.presheaf.stalk z) := (hYn z).1
  have : IsReduced Y := isReduced_of_isReduced_stalk Y
  have : Surjective (f ∣_ U) := IsZariskiLocalAtTarget.restrict hs U
  obtain ⟨eY, heY⟩ := reduced_closedImmersion_iso (f ∣_ U)
  have hred := normal_stalks_of_iso eY
    (normal_stalks_of_openImmersion (f ⁻¹ᵁ U).ι hYn)
  obtain ⟨eR, heR⟩ := Scheme.reducedNormalization_over_normal_reduction T p U
    (by simpa [Scheme.Opens.range_ι] using hU) hred
  let eU := eR ≪≫ eY.symm
  have heU : eU.hom ≫ (f ∣_ U) = T.fromReducedNormalization ∣_ U := by
    rw [← heY]
    simp only [eU, Iso.trans_hom, Iso.symm_hom, Category.assoc,
      Iso.inv_hom_id_assoc, heR]
  have : IsFinite T.fromReducedNormalization := hfiniteN
  obtain ⟨eNY, heNY⟩ := Scheme.finite_normal_iso_of_dense_open
    T.fromReducedNormalization f hN hYn U hNdense hYdense eU heU
  obtain ⟨n, C, hC, a, ha, hinj, hcomp, eN, heN⟩ :=
    finite_component_normalization_presentation T
  refine ⟨E, inferInstance, inferInstance, hE, inferInstance, n, C, hC, a,
    ha, hinj, hcomp, ?_⟩
  intro L _ _ z
  let e := eN ≪≫ eNY
  have he : e.hom ≫ f =
      Sigma.desc (fun i => @Scheme.fromNormalization (C i) (hC i) ≫ a i) := by
    simp only [e, Iso.trans_hom, Category.assoc, heNY, heN]
  let b := Spec.map (CommRingCat.ofHom (algebraMap E L))
  let r := Sigma.desc (fun i => @Scheme.fromNormalization (C i) (hC i) ≫ a i)
  let m : pullback (r ≫ p) b ⟶ pullback (f ≫ p) b :=
    pullback.map _ _ _ _ e.hom (𝟙 _) (𝟙 _)
      (by simp only [Category.comp_id, ← Category.assoc, he, r]) (by simp)
  have : IsIso m := by dsimp only [m]; infer_instance
  obtain ⟨hd, hi⟩ := hgeom L (m z)
  have : IsDomain ((pullback (f ≫ p) b).presheaf.stalk (m z)) := hd
  have : IsIntegrallyClosed ((pullback (f ≫ p) b).presheaf.stalk (m z)) := hi
  let es := (asIso (m.stalkMap z)).commRingCatIsoToRingEquiv
  exact ⟨es.symm.toMulEquiv.isDomain, IsIntegrallyClosed.of_equiv es⟩

end AlgebraicGeometry
