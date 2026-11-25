/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Reduced.ReducedNormalization
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import WeilConjectures.FieldTheory.SeparableExtension
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.FieldTheory.SeparablyGenerated
import WeilConjectures.RingTheory.ProperBaseChange.NormalAlgebraSeparableScalarExtension
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.IsIso
import WeilConjectures.Mathlib.Topology.Sober
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import WeilConjectures.AlgebraicGeometry.Morphisms.FiniteNormalDenseOpenIso
import Mathlib.AlgebraicGeometry.SpreadingOut
import WeilConjectures.AlgebraicGeometry.Morphisms.NormalizationDominantLift

/-!
# Geometry and separable field change of reduced algebraic normalization

## References

* Stacks Project, Varieties, Tags 0BXR and 0C3N
* Stacks Project, Morphisms, Tags 035Q, 035K, 035S and 0CDV

## Implementation details

The isomorphism locus of the normalization is identified with the normal locus by spreading
out a section of the normalization over an integral neighborhood of a normal point.
Compatibility with restriction and with field change is obtained by comparing finite normal
schemes on a dense open, via `Scheme.finite_normal_iso_of_dense_open`; separable scalar
extension preserves normality of the stalks, and flat base change preserves schematic
dominance, so reducedness descends.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Componentwise normalization of a finite-type scheme over a field is finite. -/
theorem finite_normalization {k : Type u} [Field k]
    (X : Scheme.{u}) (q : X ⟶ Spec (.of k))
    [LocallyOfFiniteType q] [QuasiCompact q] :
    IsFinite X.fromReducedNormalization := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian q
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace q
  have : IsNoetherian X := ⟨⟩
  let : Finite (irreducibleComponents X) :=
    (finite_irreducibleComponents_of_isNoetherian (X := X)).to_subtype
  have (Z : irreducibleComponents X) :
      IsFinite ((X.reducedNormalizationComponent Z).fromNormalization ≫
        (Scheme.IdealSheafData.vanishingIdeal
          ⟨Z.1, isClosed_of_mem_irreducibleComponents _ Z.2⟩).subschemeι) := by
    let i := (Scheme.IdealSheafData.vanishingIdeal
      ⟨Z.1, isClosed_of_mem_irreducibleComponents _ Z.2⟩).subschemeι
    have : LocallyOfFiniteType (i ≫ q) := inferInstance
    have := (X.reducedNormalizationComponent Z).isFinite_fromNormalization_of_locallyOfFiniteType
      (i ≫ q)
    infer_instance
  exact IsFinite.sigmaDesc _

private theorem surjective_normalization (X : Scheme.{u}) :
    Surjective X.fromReducedNormalization := by
  refine ⟨fun x ↦ ?_⟩
  let Z : irreducibleComponents X :=
    ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩
  let I := Scheme.IdealSheafData.vanishingIdeal
    ⟨Z.1, isClosed_of_mem_irreducibleComponents _ Z.2⟩
  have hx : x ∈ Set.range I.subschemeι := by
    rw [I.range_subschemeι]
    change x ∈ Z.1
    exact mem_irreducibleComponent
  obtain ⟨y, hy⟩ := hx
  obtain ⟨z, hz⟩ := (X.reducedNormalizationComponent Z).fromNormalization.surjective y
  refine ⟨(Sigma.ι (fun Z : irreducibleComponents X ↦
    (X.reducedNormalizationComponent Z).normalization) Z) z, ?_⟩
  change (Sigma.desc _ : X.reducedNormalization ⟶ X) ((Sigma.ι (fun Z : irreducibleComponents X ↦
    (X.reducedNormalizationComponent Z).normalization) Z) z) = x
  rw [← Scheme.Hom.comp_apply, Sigma.ι_comp_desc, Scheme.Hom.comp_apply]
  exact (congrArg I.subschemeι hz).trans hy
/-- The stalks of the componentwise normalization are integrally closed domains. -/
theorem normal_normalization (X : Scheme.{u}) (z : X.reducedNormalization) :
    IsDomain (X.reducedNormalization.presheaf.stalk z) ∧
      IsIntegrallyClosed (X.reducedNormalization.presheaf.stalk z) := by
  let C (Z : irreducibleComponents X) := (X.reducedNormalizationComponent Z).normalization
  obtain ⟨Z, y, rfl⟩ := (sigmaOpenCover C).exists_eq z
  let T := X.reducedNormalizationComponent Z
  have hK (y : Spec T.functionField) :
      IsIntegrallyClosed ((Spec T.functionField).presheaf.stalk y) := by
    have := (Spec.stalkIso T.functionField y).commRingCatIsoToRingEquiv
    exact IsIntegrallyClosed.of_equiv this.symm
  have : IsIntegrallyClosed (T.normalization.presheaf.stalk y) :=
    T.fromSpecFunctionField.isIntegrallyClosed_stalk_normalization hK y
  let e := (asIso ((Sigma.ι C Z).stalkMap y)).commRingCatIsoToRingEquiv
  exact ⟨e.toMulEquiv.isDomain_iff.mpr inferInstance, IsIntegrallyClosed.of_equiv e.symm⟩

private theorem finite_normal_unique_iso
    {L N E : Scheme.{u}} [IsLocallyNoetherian L]
    (n : N ⟶ L) (p : E ⟶ L) [IsFinite n] [IsFinite p]
    (hnormal : ∀ z : N, IsDomain (N.presheaf.stalk z) ∧
      IsIntegrallyClosed (N.presheaf.stalk z))
    (henormal : ∀ z : E, IsDomain (E.presheaf.stalk z) ∧
      IsIntegrallyClosed (E.presheaf.stalk z))
    (U : L.Opens)
    (hn : Dense (↑(n ⁻¹ᵁ U) : Set N))
    (hp : Dense (↑(p ⁻¹ᵁ U) : Set E))
    [IsIso (n ∣_ U)] [IsIso (p ∣_ U)] :
    ∃! e : N ≅ E, e.hom ≫ p = n := by
  let e := asIso (n ∣_ U) ≪≫ (asIso (p ∣_ U)).symm
  have he : e.hom ≫ (p ∣_ U) = n ∣_ U := by simp [e]
  obtain ⟨e', he'⟩ := Scheme.finite_normal_iso_of_dense_open n p hnormal henormal U hn hp e he
  refine ⟨e', he', ?_⟩
  intro e'' he''
  apply Iso.ext
  have (z : N) : _root_.IsReduced (N.presheaf.stalk z) := by
    have := (hnormal z).1
    infer_instance
  have : IsReduced N := isReduced_of_isReduced_stalk N
  have : IsDominant (n ⁻¹ᵁ U).ι := by
    rw [isDominant_iff, DenseRange, Scheme.Opens.range_ι]
    exact hn
  apply ext_of_isDominant_of_isSeparated p (he''.trans he'.symm) (n ⁻¹ᵁ U).ι
  let H := isPullback_morphismRestrict p U
  let a := H.lift (n ∣_ U) ((n ⁻¹ᵁ U).ι ≫ e''.hom) (by
    rw [morphismRestrict_ι, Category.assoc, he''])
  let b := H.lift (n ∣_ U) ((n ⁻¹ᵁ U).ι ≫ e'.hom) (by
    rw [morphismRestrict_ι, Category.assoc, he'])
  have hab : a = b := by
    apply (cancel_mono (p ∣_ U)).mp
    simp [a, b]
  have ha : a ≫ (p ⁻¹ᵁ U).ι = (n ⁻¹ᵁ U).ι ≫ e''.hom := by simp [a]
  have hb : b ≫ (p ⁻¹ᵁ U).ι = (n ⁻¹ᵁ U).ι ≫ e'.hom := by simp [b]
  exact ha.symm.trans ((congrArg (fun f ↦ f ≫ (p ⁻¹ᵁ U).ι) hab).trans hb)

private theorem normal_stalk_of_openImmersion {Y X : Scheme.{u}}
    (f : Y ⟶ X) [IsOpenImmersion f]
    (hnormal : ∀ x : X, IsDomain (X.presheaf.stalk x) ∧
      IsIntegrallyClosed (X.presheaf.stalk x)) (y : Y) :
    IsDomain (Y.presheaf.stalk y) ∧ IsIntegrallyClosed (Y.presheaf.stalk y) := by
  let e := (asIso (f.stalkMap y)).commRingCatIsoToRingEquiv
  have := (hnormal (f y)).1
  have := (hnormal (f y)).2
  exact ⟨e.symm.toMulEquiv.isDomain, IsIntegrallyClosed.of_equiv e⟩

private theorem normal_pullback_spec {k : Type u} [Field k]
    (R : CommRingCat.{u}) (φ : CommRingCat.of k ⟶ R)
    (hnormal : ∀ x : Spec R, IsDomain ((Spec R).presheaf.stalk x) ∧
      IsIntegrallyClosed ((Spec R).presheaf.stalk x))
    (K : Type u) [Field K] [Algebra k K] (hK : Algebra.IsSeparableExtension k K)
    (z : (pullback (Spec.map φ)
      (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u})) :
    IsDomain ((pullback (Spec.map φ)
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))).presheaf.stalk z) ∧
    IsIntegrallyClosed ((pullback (Spec.map φ)
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))).presheaf.stalk z) := by
  algebraize [φ.hom]
  have hR (p : Ideal R) [p.IsPrime] :
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p) := by
    let x : PrimeSpectrum R := ⟨p, inferInstance⟩
    let e := (Spec.stalkIso R x).commRingCatIsoToRingEquiv
    have := (hnormal x).1
    have := (hnormal x).2
    exact ⟨e.symm.toMulEquiv.isDomain, IsIntegrallyClosed.of_equiv e⟩
  have hn := Algebra.isNormal_tensorProduct_of_separableExtension k R K hK hR
  have hT (x : Spec (CommRingCat.of (TensorProduct k R K))) :
      IsDomain ((Spec (CommRingCat.of (TensorProduct k R K))).presheaf.stalk x) ∧
      IsIntegrallyClosed ((Spec (CommRingCat.of (TensorProduct k R K))).presheaf.stalk x) := by
    let e := (Spec.stalkIso (CommRingCat.of (TensorProduct k R K)) x).commRingCatIsoToRingEquiv
    have := (hn x.asIdeal).1
    have := (hn x.asIdeal).2
    exact ⟨e.toMulEquiv.isDomain, IsIntegrallyClosed.of_equiv e.symm⟩
  exact normal_stalk_of_openImmersion (pullbackSpecIso k R K).hom hT z

private theorem normal_pullback {k : Type u} [Field k]
    (X : Scheme.{u}) (q : X ⟶ Spec (.of k))
    (hnormal : ∀ x : X, IsDomain (X.presheaf.stalk x) ∧
      IsIntegrallyClosed (X.presheaf.stalk x))
    (K : Type u) [Field K] [Algebra k K] (hK : Algebra.IsSeparableExtension k K)
    (z : (pullback q
      (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u})) :
    IsDomain ((pullback q
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))).presheaf.stalk z) ∧
    IsIntegrallyClosed ((pullback q
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))).presheaf.stalk z) := by
  let g := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let C : (pullback q g).OpenCover :=
    X.affineCover.pullback₁ (pullback.fst q g)
  obtain ⟨i, y, rfl⟩ := C.exists_eq z
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (X.affineCover.f i ≫ q)
  have hi := normal_stalk_of_openImmersion (X.affineCover.f i) hnormal
  have hs := normal_pullback_spec _ φ hi K hK
  let e : C.X i ≅ pullback (Spec.map φ) g := pullbackSymmetry _ _ ≪≫
    pullbackRightPullbackFstIso q g (X.affineCover.f i) ≪≫
    pullback.congrHom hφ.symm rfl
  have hy := normal_stalk_of_openImmersion e.hom hs y
  let t := (asIso ((C.f i).stalkMap y)).commRingCatIsoToRingEquiv
  have := hy.1
  have := hy.2
  exact ⟨t.toMulEquiv.isDomain, IsIntegrallyClosed.of_equiv t.symm⟩

private theorem isIso_restrict_pullback {A B C D : Scheme.{u}}
    {a : A ⟶ B} {b : A ⟶ C} {f : B ⟶ D} {g : C ⟶ D}
    (H : IsPullback a b f g) (U : D.Opens) [IsIso (f ∣_ U)] :
    IsIso (b ∣_ (g ⁻¹ᵁ U)) := by
  have hA := isPullback_morphismRestrict b (g ⁻¹ᵁ U)
  have hpaste := hA.paste_vert H.flip
  have hs : IsPullback ((b ⁻¹ᵁ (g ⁻¹ᵁ U)).ι ≫ a)
      (b ∣_ (g ⁻¹ᵁ U)) f ((g ∣_ U) ≫ U.ι) := by
    rw [morphismRestrict_ι]
    exact hpaste.flip
  have ht := (isPullback_morphismRestrict f U).flip
  exact (IsPullback.of_right' hs ht).flip.isIso_fst_of_isIso

private theorem reduced_baseChange {k : Type u} [Field k]
    (X : Scheme.{u}) (q : X ⟶ Spec (.of k)) [IsReduced X]
    [LocallyOfFiniteType q] [QuasiCompact q]
    (K : Type u) [Field K] [Algebra k K] (hK : Algebra.IsSeparableExtension k K) :
    IsReduced (pullback q (Spec.map (CommRingCat.ofHom (algebraMap k K)))) := by
  let g := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let ν := X.fromReducedNormalization
  have : IsFinite ν := finite_normalization X q
  have : Surjective ν := surjective_normalization X
  have : IsSchemeTheoreticallyDominant ν := .of_isDominant ν
  have : Flat g := (Flat.SpecMap_iff).mpr (by
    change (algebraMap k K).Flat
    exact RingHom.flat_algebraMap_iff.mpr inferInstance)
  let n : pullback (ν ≫ q) g ⟶ pullback q g :=
    pullback.lift (pullback.fst _ _ ≫ ν) (pullback.snd _ _)
      (by rw [Category.assoc, pullback.condition])
  have H : IsPullback (pullback.fst (ν ≫ q) g) n ν (pullback.fst q g) :=
    IsPullback.of_bot (by simpa [n] using IsPullback.of_hasPullback (ν ≫ q) g)
      (by simp [n]) (IsPullback.of_hasPullback q g)
  have : IsSchemeTheoreticallyDominant n := .of_isPullback H
  have : IsFinite n := MorphismProperty.of_isPullback H inferInstance
  have hn := normal_pullback X.reducedNormalization (ν ≫ q) (normal_normalization X) K hK
  have (z : (pullback (ν ≫ q) g : Scheme.{u})) : _root_.IsReduced
      ((pullback (ν ≫ q) g).presheaf.stalk z) := by
    have := (hn z).1
    infer_instance
  have : IsReduced (pullback (ν ≫ q) g) := isReduced_of_isReduced_stalk _
  exact IsSchemeTheoreticallyDominant.isReduced n

/-- A dense open meets every irreducible component when there are finitely many. -/
theorem component_meets_dense_open (X : Scheme.{u})
    (hfinite : (irreducibleComponents X).Finite) (U : X.Opens) (hU : Dense (U : Set X))
    (Z : irreducibleComponents X) : (Z.1 ∩ (U : Set X)).Nonempty := by
  let V : X.Opens := ⟨(⋃₀ (irreducibleComponents X \ {Z.1}))ᶜ, by
    rw [Set.sUnion_eq_biUnion, isOpen_compl_iff]
    exact hfinite.sdiff.isClosed_biUnion
      (fun W hW ↦ isClosed_of_mem_irreducibleComponents W hW.1)⟩
  have hcl : closure (V : Set X) = Z.1 :=
    closure_sUnion_irreducibleComponents_sdiff_singleton hfinite Z.1 Z.2
  have hV : (V : Set X).Nonempty := by
    by_contra hv
    have hz := Z.2.1.1
    rw [Set.not_nonempty_iff_eq_empty] at hv
    rw [hv, closure_empty] at hcl
    exact Set.not_nonempty_empty (hcl.symm ▸ hz)
  obtain ⟨x, hxV, hxU⟩ := hU.inter_open_nonempty V V.isOpen hV
  exact ⟨x, hcl ▸ subset_closure hxV, hxU⟩

set_option backward.isDefEq.respectTransparency false in
/-- The inverse image of a dense open under componentwise normalization is dense. -/
theorem dense_preimage_normalization {k : Type u} [Field k]
    (X : Scheme.{u}) (q : X ⟶ Spec (.of k))
    [LocallyOfFiniteType q] [QuasiCompact q]
    (U : X.Opens) (hU : Dense (U : Set X)) :
    Dense (X.fromReducedNormalization ⁻¹ᵁ U : Set X.reducedNormalization) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian q
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace q
  have : IsNoetherian X := ⟨⟩
  let C (Z : irreducibleComponents X) := (X.reducedNormalizationComponent Z).normalization
  rw [dense_iff_closure_eq, Set.eq_univ_iff_forall]
  intro z
  obtain ⟨Z, y, rfl⟩ := (sigmaOpenCover C).exists_eq z
  change irreducibleComponents X at Z
  change C Z at y
  change (Sigma.ι C Z) y ∈ _
  let i := (Scheme.IdealSheafData.vanishingIdeal
    ⟨Z.1, isClosed_of_mem_irreducibleComponents _ Z.2⟩).subschemeι
  let n := (X.reducedNormalizationComponent Z).fromNormalization
  have hne : ((n ≫ i) ⁻¹ᵁ U : Set (C Z)).Nonempty := by
    obtain ⟨x, hxZ, hxU⟩ := component_meets_dense_open X
      finite_irreducibleComponents_of_isNoetherian U hU Z
    have hx : x ∈ Set.range i := by
      rw [Scheme.IdealSheafData.range_subschemeι]
      exact hxZ
    obtain ⟨w, hw⟩ := hx
    obtain ⟨v, hv⟩ := n.surjective w
    exact ⟨v, by change i (n v) ∈ U; rw [hv, hw]; exact hxU⟩
  have hd : Dense ((n ≫ i) ⁻¹ᵁ U : Set (C Z)) :=
    ((n ≫ i) ⁻¹ᵁ U).isOpen.dense hne
  have hy := image_closure_subset_closure_image (Sigma.ι C Z).continuous
    (Set.mem_image_of_mem _ (hd y))
  apply closure_mono (s := (Sigma.ι C Z) '' ((n ≫ i) ⁻¹ᵁ U : Set (C Z))) ?_ hy
  rintro _ ⟨v, hv, rfl⟩
  change X.fromReducedNormalization ((Sigma.ι C Z) v) ∈ U
  have he : (Sigma.ι C Z) ≫ X.fromReducedNormalization = n ≫ i := by
    exact Sigma.ι_comp_desc _ Z
  have he' := congrArg (fun f : C Z ⟶ X ↦ f v) he
  exact he'.symm ▸ hv

private theorem dense_preimage_of_dense_iso_open {E L : Scheme.{u}} (p : E ⟶ L)
    (U : L.Opens) (hU : Dense (p ⁻¹ᵁ U : Set E)) [IsIso (p ∣_ U)]
    (V : L.Opens) (hV : Dense (V : Set L)) : Dense (p ⁻¹ᵁ V : Set E) := by
  have hi : DenseRange (p ⁻¹ᵁ U).ι := by
    simpa [DenseRange, Scheme.Opens.range_ι] using hU
  have hd : Dense (((p ∣_ U) ≫ U.ι) ⁻¹' (V : Set L)) :=
    hV.preimage (((p ∣_ U) ≫ U.ι).isOpenEmbedding.isOpenMap)
  apply hi.dense_of_mapsTo (p ⁻¹ᵁ U).ι.continuous hd
  intro x hx
  change p ((p ⁻¹ᵁ U).ι x) ∈ V
  change ((p ∣_ U) ≫ U.ι) x ∈ V at hx
  simpa only [← Scheme.Hom.comp_apply, morphismRestrict_ι] using hx

private theorem compare_normalization {k : Type u} [Field k]
    (X : Scheme.{u}) (q : X ⟶ Spec (.of k))
    [LocallyOfFiniteType q] [QuasiCompact q]
    (hbir : ∃ V : X.Opens, Dense (V : Set X) ∧
      IsIso (X.fromReducedNormalization ∣_ V))
    {E : Scheme.{u}} (p : E ⟶ X) [IsFinite p]
    (hnormal : ∀ z : E, IsDomain (E.presheaf.stalk z) ∧
      IsIntegrallyClosed (E.presheaf.stalk z))
    (U : X.Opens) (hUd : Dense (U : Set X))
    (hU : Dense (p ⁻¹ᵁ U : Set E)) [IsIso (p ∣_ U)] :
    ∃! e : X.reducedNormalization ≅ E, e.hom ≫ p = X.fromReducedNormalization := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian q
  have : IsFinite X.fromReducedNormalization := finite_normalization X q
  obtain ⟨V, hV, hiV⟩ := hbir
  have : IsIso (X.fromReducedNormalization ∣_ V) := hiV
  have : IsIso (X.fromReducedNormalization ∣_ (U ⊓ V)) :=
    isIso_morphismRestrict_of_le _ inf_le_right hiV
  have : IsIso (p ∣_ (U ⊓ V)) :=
    isIso_morphismRestrict_of_le _ inf_le_left inferInstance
  have hUV : Dense ((U ⊓ V : X.Opens) : Set X) :=
    hUd.inter_of_isOpen_left hV U.isOpen
  apply finite_normal_unique_iso X.fromReducedNormalization p (normal_normalization X)
    hnormal (U ⊓ V) (dense_preimage_normalization X q _ hUV)
  have hpV := dense_preimage_of_dense_iso_open p U hU V hV
  exact hU.inter_of_isOpen_left hpV (p ⁻¹ᵁ U).isOpen

private theorem field_comparison {k : Type u} [Field k]
    (X : Scheme.{u}) (q : X ⟶ Spec (.of k)) [IsReduced X]
    [LocallyOfFiniteType q] [QuasiCompact q]
    (hbir : ∃ U : X.Opens, Dense (U : Set X) ∧
      IsIso (X.fromReducedNormalization ∣_ U))
    (K : Type u) [Field K] [Algebra k K] (hK : Algebra.IsSeparableExtension k K)
    (hbirK : ∃ U : (pullback q
        (Spec.map (CommRingCat.ofHom (algebraMap k K)))).Opens,
      Dense (U : Set (pullback q (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u})) ∧
        IsIso ((pullback q
          (Spec.map (CommRingCat.ofHom (algebraMap k K)))).fromReducedNormalization ∣_ U)) :
    ∃! e : (pullback q (Spec.map (CommRingCat.ofHom (algebraMap k K)))).reducedNormalization ≅
        pullback (X.fromReducedNormalization ≫ q)
          (Spec.map (CommRingCat.ofHom (algebraMap k K))),
      (e.hom ≫ pullback.fst _ _ ≫ X.fromReducedNormalization =
        (pullback q (Spec.map (CommRingCat.ofHom (algebraMap k K)))).fromReducedNormalization ≫
          pullback.fst _ _) ∧
      (e.hom ≫ pullback.snd _ _ =
        (pullback q (Spec.map (CommRingCat.ofHom (algebraMap k K)))).fromReducedNormalization ≫
          pullback.snd _ _) := by
  let g := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let Y := pullback q g
  let ν := X.fromReducedNormalization
  let E := pullback (ν ≫ q) g
  let p : E ⟶ Y := pullback.lift (pullback.fst _ _ ≫ ν) (pullback.snd _ _)
    (by rw [Category.assoc, pullback.condition])
  have H : IsPullback (pullback.fst (ν ≫ q) g) p ν (pullback.fst q g) :=
    IsPullback.of_bot (by simpa [p] using IsPullback.of_hasPullback (ν ≫ q) g)
      (by simp [p, ν]) (IsPullback.of_hasPullback q g)
  have : IsFinite ν := finite_normalization X q
  have : IsFinite p := MorphismProperty.of_isPullback H inferInstance
  obtain ⟨U, hUd, hiU⟩ := hbir
  have : IsIso (ν ∣_ U) := hiU
  let V := pullback.fst q g ⁻¹ᵁ U
  have : IsIso (p ∣_ V) := isIso_restrict_pullback H U
  have hV : Dense (V : Set Y) := hUd.preimage (pullback.fst q g).isOpenMap
  have hpre : p ⁻¹ᵁ V = pullback.fst (ν ≫ q) g ⁻¹ᵁ (ν ⁻¹ᵁ U) := by
    dsimp only [V]
    rw [← Scheme.Hom.comp_preimage, ← H.w, Scheme.Hom.comp_preimage]
  have hpV : Dense (p ⁻¹ᵁ V : Set E) := by
    rw [hpre]
    exact (dense_preimage_normalization X q U hUd).preimage
      (pullback.fst (ν ≫ q) g).isOpenMap
  obtain ⟨e, he, hu⟩ := compare_normalization Y (pullback.snd q g) hbirK p
    (normal_pullback X.reducedNormalization (ν ≫ q) (normal_normalization X) K hK) V hV hpV
  have hiff (e' : Y.reducedNormalization ≅ E) :
      e'.hom ≫ p = Y.fromReducedNormalization ↔
        (e'.hom ≫ pullback.fst _ _ ≫ ν =
          Y.fromReducedNormalization ≫ pullback.fst q g) ∧
        (e'.hom ≫ pullback.snd _ _ =
          Y.fromReducedNormalization ≫ pullback.snd q g) := by
    constructor
    · intro h
      constructor
      · simpa [p, Category.assoc] using congrArg (fun f ↦ f ≫ pullback.fst q g) h
      · simpa [p, Category.assoc] using congrArg (fun f ↦ f ≫ pullback.snd q g) h
    · rintro ⟨hf, hs⟩
      apply pullback.hom_ext
      · simpa [p, Category.assoc] using hf
      · simpa [p, Category.assoc] using hs
  exact ⟨e, (hiff e).mp he, fun e' he' ↦ hu e' ((hiff e').mpr he')⟩

private theorem normal_locus_from_local_criterion {k : Type u} [Field k]
    (X : Scheme.{u}) (q : X ⟶ Spec (.of k)) [IsReduced X]
    [LocallyOfFiniteType q] [QuasiCompact q]
    (hlocal : ∀ x : X, IsDomain (X.presheaf.stalk x) →
      IsIntegrallyClosed (X.presheaf.stalk x) →
        ∃ U : X.Opens, x ∈ U ∧ IsIso (X.fromReducedNormalization ∣_ U)) :
    ∃ N : X.Opens,
      (∀ x : X, x ∈ N ↔
        IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x)) ∧
      Dense (N : Set X) ∧ IsIso (X.fromReducedNormalization ∣_ N) := by
  let ν := X.fromReducedNormalization
  let N := ν.maximalIsomorphismOpen
  have hi : IsIso (ν ∣_ N) := ν.isIso_restrict_maximalIsomorphismOpen
  have hn (x : X) : x ∈ N ↔
      IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x) := by
    constructor
    · intro hx
      have hN := normal_stalk_of_openImmersion
        (inv (ν ∣_ N) ≫ (ν ⁻¹ᵁ N).ι) (normal_normalization X) (⟨x, hx⟩ : N)
      let e := (N.stalkIso ⟨x, hx⟩).commRingCatIsoToRingEquiv
      have := hN.1
      have := hN.2
      exact ⟨e.symm.toMulEquiv.isDomain, IsIntegrallyClosed.of_equiv e⟩
    · rintro ⟨hd, hc⟩
      obtain ⟨U, hxU, hU⟩ := hlocal x hd hc
      exact ν.le_maximalIsomorphismOpen hU hxU
  refine ⟨N, hn, ?_, hi⟩
  apply dense_of_genericPoints_subset
  intro x hx
  apply (hn x).mpr
  let := (isField_stalk_of_closure_mem_irreducibleComponents X x hx).toField
  exact ⟨inferInstance, inferInstance⟩

private theorem open_comparison {k : Type u} [Field k]
    (X : Scheme.{u}) (q : X ⟶ Spec (.of k)) [IsReduced X]
    [LocallyOfFiniteType q] [QuasiCompact q]
    (hbir : ∃ U : X.Opens, Dense (U : Set X) ∧
      IsIso (X.fromReducedNormalization ∣_ U))
    (W : X.Opens)
    (hbirW : ∃ U : W.toScheme.Opens, Dense (U : Set W.toScheme) ∧
      IsIso (W.toScheme.fromReducedNormalization ∣_ U)) :
    ∃! e : W.toScheme.reducedNormalization ≅
        (X.fromReducedNormalization ⁻¹ᵁ W).toScheme,
      e.hom ≫ (X.fromReducedNormalization ∣_ W) = W.toScheme.fromReducedNormalization := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian q
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace q
  have : IsNoetherian X := ⟨⟩
  have : IsFinite X.fromReducedNormalization := finite_normalization X q
  obtain ⟨U, hUd, hiU⟩ := hbir
  have : IsIso (X.fromReducedNormalization ∣_ U) := hiU
  let p := X.fromReducedNormalization ∣_ W
  let V := W.ι ⁻¹ᵁ U
  have H := (isPullback_morphismRestrict X.fromReducedNormalization W).flip
  have : IsIso (p ∣_ V) := isIso_restrict_pullback H U
  have hV : Dense (V : Set W.toScheme) := hUd.preimage W.ι.isOpenEmbedding.isOpenMap
  have hp : Dense (p ⁻¹ᵁ V : Set (X.fromReducedNormalization ⁻¹ᵁ W).toScheme) := by
    have he : p ⁻¹ᵁ V = (X.fromReducedNormalization ⁻¹ᵁ W).ι ⁻¹ᵁ
        (X.fromReducedNormalization ⁻¹ᵁ U) := by
      dsimp only [V, p]
      rw [← Scheme.Hom.comp_preimage, morphismRestrict_ι, Scheme.Hom.comp_preimage]
    rw [he]
    exact (dense_preimage_normalization X q U hUd).preimage
      (X.fromReducedNormalization ⁻¹ᵁ W).ι.isOpenEmbedding.isOpenMap
  exact compare_normalization W.toScheme (W.ι ≫ q) hbirW p
    (normal_stalk_of_openImmersion (X.fromReducedNormalization ⁻¹ᵁ W).ι
      (normal_normalization X)) V hV hp

set_option backward.isDefEq.respectTransparency false in
private theorem integral_neighborhood (X : Scheme.{u}) [IsLocallyNoetherian X]
    (x : X) [IsDomain (X.presheaf.stalk x)] :
    ∃ V : X.Opens, x ∈ V ∧ IsIntegral V.toScheme := by
  obtain ⟨V, hx, hV, hinj⟩ := X.exists_germ_injective x
  have : Nonempty V.toScheme := ⟨⟨x, hx⟩⟩
  have : IsDomain Γ(X, V) := Function.Injective.isDomain
    (X.presheaf.germ V x hx).hom hinj
  have : IsAffine V.toScheme := hV
  have : IsDomain Γ(V.toScheme, ⊤) :=
    (Scheme.Opens.topIso V).commRingCatIsoToRingEquiv.toMulEquiv.isDomain
  exact ⟨V, hx, isIntegral_of_isAffine_of_isDomain _⟩

set_option backward.isDefEq.respectTransparency false in
private theorem unique_component_of_integral_open (X : Scheme.{u})
    (V : X.Opens) [IsIntegral V.toScheme] :
    ∃ Z : irreducibleComponents X,
      (V : Set X) ⊆ Z.1 ∧
      ∀ T : irreducibleComponents X,
        (T.1 ∩ (V : Set X)).Nonempty → T = Z := by
  have hirr : IsIrreducible (V : Set X) := by
    have h := (IrreducibleSpace.isIrreducible_univ V.toScheme).image V.ι
      V.ι.continuous.continuousOn
    rwa [Set.image_univ, Scheme.Opens.range_ι] at h
  obtain ⟨Z, hZ, hVZ⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible _ hirr
  refine ⟨⟨Z, hZ⟩, hVZ, ?_⟩
  intro T hT
  apply Subtype.ext
  have hpre := preimage_mem_irreducibleComponents T.2 V.ι.isOpenEmbedding
    (by simpa only [Scheme.Opens.range_ι] using hT)
  have he : V.ι ⁻¹' T.1 = Set.univ := by
    simpa only [irreducibleComponents_eq_singleton, Set.mem_singleton_iff] using hpre
  have hc := closure_image_preimage_of_isPreirreducible V.ι V.ι.isOpenMap T.1
    (he.symm ▸ Set.univ_nonempty) T.2.1.2
    (isClosed_of_mem_irreducibleComponents _ T.2)
  have hTZ : T.1 ⊆ Z := by
    rw [← hc, he, Set.image_univ, Scheme.Opens.range_ι]
    exact closure_minimal hVZ (isClosed_of_mem_irreducibleComponents _ hZ)
  exact (T.2.eq_of_ge hZ.1 hTZ).symm

set_option backward.isDefEq.respectTransparency false in
private theorem dominant_fromSpecStalk (Y : Scheme.{u}) [IsIntegral Y] (y : Y) :
    IsDominant (Y.fromSpecStalk y) := by
  rw [isDominant_iff, DenseRange, Scheme.range_fromSpecStalk]
  refine dense_iff_closure_eq.mpr (Set.eq_univ_of_univ_subset ?_)
  rw [← (genericPoint_spec Y).def]
  exact closure_mono (Set.singleton_subset_iff.mpr
    ((genericPoint_spec Y).specializes trivial))

set_option backward.isDefEq.respectTransparency false in
private theorem local_lift_normalization (X : Scheme.{u}) [IsNoetherian X]
    (x : X) [IsDomain (X.presheaf.stalk x)] [IsIntegrallyClosed (X.presheaf.stalk x)] :
    ∃ (V : X.Opens) (_hxV : x ∈ V) (Z : irreducibleComponents X)
      (a : Spec (X.presheaf.stalk x) ⟶ (X.reducedNormalizationComponent Z).normalization),
      IsDominant a ∧
      (∀ T : irreducibleComponents X, (T.1 ∩ (V : Set X)).Nonempty → T = Z) ∧
      (a ≫ Sigma.ι (fun T : irreducibleComponents X ↦
        (X.reducedNormalizationComponent T).normalization) Z) ≫
          X.fromReducedNormalization = X.fromSpecStalk x := by
  obtain ⟨V, hxV, hV⟩ := integral_neighborhood X x
  have : IsIntegral V.toScheme := hV
  obtain ⟨Z, hVZ, hunique⟩ := unique_component_of_integral_open X V
  let I := Scheme.IdealSheafData.vanishingIdeal
    ⟨Z.1, isClosed_of_mem_irreducibleComponents _ Z.2⟩
  let i : X.reducedNormalizationComponent Z ⟶ X := I.subschemeι
  have hi : Surjective (i ∣_ V) := by
    refine ⟨fun y ↦ ?_⟩
    change V at y
    have hr : y.1 ∈ Set.range i := by
      change y.1 ∈ Set.range I.subschemeι
      rw [I.range_subschemeι]
      exact hVZ y.2
    obtain ⟨z, hz⟩ := hr
    have hzV : z ∈ i ⁻¹ᵁ V := by
      change i z ∈ V
      exact hz.symm ▸ y.2
    refine ⟨⟨z, hzV⟩, ?_⟩
    apply V.ι.isOpenEmbedding.injective
    calc
      V.ι ((i ∣_ V) ⟨z, hzV⟩) = i ((i ⁻¹ᵁ V).ι ⟨z, hzV⟩) := by
        exact congrArg (fun f : (i ⁻¹ᵁ V).toScheme ⟶ X ↦ f ⟨z, hzV⟩)
          (morphismRestrict_ι i V)
      _ = V.ι y := hz
  have : IsIso (i ∣_ V) := isIso_of_isClosedImmersion_of_surjective _
  let j : V.toScheme ⟶ X.reducedNormalizationComponent Z :=
    inv (i ∣_ V) ≫ (i ⁻¹ᵁ V).ι
  have hj : j ≫ i = V.ι := by simp [j, ← morphismRestrict_ι]
  have : IsDominant j := by
    refine ⟨?_⟩
    have : Nonempty V.toScheme := inferInstance
    have : (Set.range j).Nonempty := Set.range_nonempty j
    exact (j.isOpenEmbedding.isOpen_range).dense this
  have : IsDominant (V.toScheme.fromSpecStalk ⟨x, hxV⟩) := dominant_fromSpecStalk _ _
  have : IsDominant (V.fromSpecStalkOfMem x hxV) := by
    unfold Scheme.Opens.fromSpecStalkOfMem
    infer_instance
  let l := V.fromSpecStalkOfMem x hxV ≫ j
  have hnormal (y : Spec (X.presheaf.stalk x)) :
      IsIntegrallyClosed ((Spec (X.presheaf.stalk x)).presheaf.stalk y) := by
    have : IsIntegrallyClosed (Localization.AtPrime y.asIdeal) :=
      isIntegrallyClosed_of_isLocalization _ y.asIdeal.primeCompl
        y.asIdeal.primeCompl_le_nonZeroDivisors
    exact IsIntegrallyClosed.of_equiv
      (Spec.stalkIso (X.presheaf.stalk x) y).commRingCatIsoToRingEquiv.symm
  obtain ⟨a, ⟨ha, had⟩, _⟩ := Scheme.existsUnique_lift_normalization_of_dominant hnormal l
  refine ⟨V, hxV, Z, a, had, hunique, ?_⟩
  have hι : Sigma.ι (fun T : irreducibleComponents X ↦
      (X.reducedNormalizationComponent T).normalization) Z ≫
      X.fromReducedNormalization = (X.reducedNormalizationComponent Z).fromNormalization ≫ i := by
    exact Sigma.ι_comp_desc _ Z
  rw [Category.assoc, hι, ← Category.assoc, ha]
  simp [l, Category.assoc, hj]

set_option backward.isDefEq.respectTransparency false in
private theorem local_iso_of_lift (X : Scheme.{u}) [IsNoetherian X]
    [IsFinite X.fromReducedNormalization]
    (hn : ∀ z : X.reducedNormalization, _root_.IsReduced
      (X.reducedNormalization.presheaf.stalk z))
    (x : X) [IsDomain (X.presheaf.stalk x)] [IsIntegrallyClosed (X.presheaf.stalk x)] :
    ∃ U : X.Opens, x ∈ U ∧ IsIso (X.fromReducedNormalization ∣_ U) := by
  let C (T : irreducibleComponents X) := (X.reducedNormalizationComponent T).normalization
  let ν := X.fromReducedNormalization
  let ι (T : irreducibleComponents X) : C T ⟶ X.reducedNormalization := Sigma.ι C T
  obtain ⟨V, hxV, Z, a, had, hunique, ha⟩ := local_lift_normalization X x
  have : IsDominant a := had
  obtain ⟨W, hxW, s, hsa, hs⟩ := spread_out_of_isGermInjective' (𝟙 X) ν
    (a ≫ ι Z) (by simpa [ν] using ha)
  let U := W ⊓ V
  have hxU : x ∈ U := ⟨hxW, hxV⟩
  let sU := X.homOfLE (show U ≤ W from inf_le_left) ≫ s
  have hsU : sU ≫ ν = U.ι := by simp [sU, Category.assoc, hs]
  let H := isPullback_morphismRestrict ν U
  let t := H.lift (𝟙 U.toScheme) sU (by simpa using hsU.symm)
  have ht : t ≫ (ν ∣_ U) = 𝟙 U.toScheme := by simp [t]
  have htι : t ≫ (ν ⁻¹ᵁ U).ι = sU := by simp [t]
  have hsub : Set.range (ν ⁻¹ᵁ U).ι ⊆ Set.range (ι Z) := by
    rintro _ ⟨z, rfl⟩
    obtain ⟨T, y, hy⟩ := (sigmaOpenCover C).exists_eq ((ν ⁻¹ᵁ U).ι z)
    change irreducibleComponents X at T
    change C T at y
    change (ι T) y = (ν ⁻¹ᵁ U).ι z at hy
    have hmem : ν ((ι T) y) ∈ T.1 := by
      change (Sigma.desc _ : X.reducedNormalization ⟶ X) ((Sigma.ι C T) y) ∈ T.1
      rw [← Scheme.Hom.comp_apply, Sigma.ι_comp_desc, Scheme.Hom.comp_apply]
      exact ((X.reducedNormalizationComponent T).fromNormalization y).2
    have hz : ν ((ν ⁻¹ᵁ U).ι z) ∈ U := z.2
    have hT : T = Z := hunique T ⟨ν ((ν ⁻¹ᵁ U).ι z), hy ▸ hmem, hz.2⟩
    subst T
    exact ⟨y, hy⟩
  let b := IsOpenImmersion.lift (ι Z) (ν ⁻¹ᵁ U).ι hsub
  have hb : b ≫ ι Z = (ν ⁻¹ᵁ U).ι := IsOpenImmersion.lift_fac _ _ _
  have : IsOpenImmersion b := by
    infer_instance
  have hUfactor : U.fromSpecStalkOfMem x hxU ≫ X.homOfLE
      (show U ≤ W from inf_le_left) = W.fromSpecStalkOfMem x hxW := by
    apply (cancel_mono W.ι).mp
    simp
  have hsaU : a ≫ ι Z = U.fromSpecStalkOfMem x hxU ≫ sU := by
    simp only [sU, ← Category.assoc, hUfactor, ← hsa]
  have he : U.fromSpecStalkOfMem x hxU ≫ t ≫ b = a := by
    apply (cancel_mono (ι Z)).mp
    rw [Category.assoc, Category.assoc, hb, htι]
    exact hsaU.symm
  have : IsDominant (U.fromSpecStalkOfMem x hxU ≫ t ≫ b) := he.symm ▸ had
  have : IsDominant (t ≫ b) :=
    IsDominant.of_comp (U.fromSpecStalkOfMem x hxU) (t ≫ b)
  have : IsDominant t := IsDominant.of_comp_of_isOpenImmersion t b
  have : IsClosedImmersion t := by
    have : IsClosedImmersion (t ≫ (ν ∣_ U)) := ht.symm ▸ inferInstance
    exact IsClosedImmersion.of_comp t (ν ∣_ U)
  have : Surjective t := surjective_of_isDominant_of_isClosed_range t
    t.isClosedEmbedding.isClosed_range
  have (z : X.reducedNormalization) :
      _root_.IsReduced (X.reducedNormalization.presheaf.stalk z) := hn z
  have : IsReduced X.reducedNormalization := isReduced_of_isReduced_stalk _
  have : IsIso t := isIso_of_isClosedImmersion_of_surjective t
  have : IsIso (ν ∣_ U) := by
    have : IsIso (t ≫ (ν ∣_ U)) := ht.symm ▸ inferInstance
    exact IsIso.of_isIso_comp_left t _
  exact ⟨U, hxU, this⟩

private theorem all_normal_locus
    {k : Type u} [Field k] (X : Scheme.{u}) (q : X ⟶ Spec (.of k))
    [IsReduced X] [LocallyOfFiniteType q] [QuasiCompact q] :
    ∃ N : X.Opens,
      (∀ x : X, x ∈ N ↔
        IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x)) ∧
      Dense (N : Set X) ∧ IsIso (X.fromReducedNormalization ∣_ N) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian q
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace q
  have : IsNoetherian X := ⟨⟩
  have : IsFinite X.fromReducedNormalization := finite_normalization X q
  apply normal_locus_from_local_criterion X q
  intro x hd hc
  have := hd
  have := hc
  apply local_iso_of_lift X ?_ x
  intro z
  have := (normal_normalization X z).1
  infer_instance

end AlgebraicGeometry

namespace Algebra
private theorem separable_of_perfect (k K : Type u) [Field k] [Field K]
    [Algebra k K] [PerfectField k] : IsSeparableExtension k K := by
  intro F hF
  have : Algebra.EssFiniteType k F := (IntermediateField.essFiniteType_iff.mpr hF)
  obtain ⟨s, hs, hsep⟩ := exists_isTranscendenceBasis_and_isSeparable_of_perfectField k F
  exact ⟨(s : Set F), hs, hsep⟩
end Algebra

namespace AlgebraicGeometry

/-- For a reduced scheme `X` of finite type over a field `k`, componentwise normalization is
finite, surjective, an isomorphism over the dense open normal locus, compatible with restriction
to opens, and compatible with separable field change (with any field change when `k` is
algebraically closed). Each comparison isomorphism is unique subject to its projection
equations. -/
theorem reduced_algebraic_normalization_field_change
    {k : Type u} [Field k] (X : Scheme.{u}) (q : X ⟶ Spec (.of k))
    [IsReduced X] [LocallyOfFiniteType q] [QuasiCompact q] :
    IsFinite X.fromReducedNormalization ∧ Surjective X.fromReducedNormalization ∧
    (∃ N : X.Opens,
      (∀ x : X, x ∈ N ↔
        IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x)) ∧
      Dense (N : Set X) ∧ IsIso (X.fromReducedNormalization ∣_ N)) ∧
    (∀ W : X.Opens,
      ∃! e : W.toScheme.reducedNormalization ≅
          (X.fromReducedNormalization ⁻¹ᵁ W).toScheme,
        e.hom ≫ (X.fromReducedNormalization ∣_ W) = W.toScheme.fromReducedNormalization) ∧
    (∀ (K : Type u) [Field K] [Algebra k K], Algebra.IsSeparableExtension k K →
      ∃! e : (pullback q (Spec.map (CommRingCat.ofHom (algebraMap k K)))).reducedNormalization ≅
          pullback (X.fromReducedNormalization ≫ q)
            (Spec.map (CommRingCat.ofHom (algebraMap k K))),
        (e.hom ≫ pullback.fst _ _ ≫ X.fromReducedNormalization =
          (pullback q (Spec.map (CommRingCat.ofHom (algebraMap k K)))).fromReducedNormalization ≫
            pullback.fst q (Spec.map (CommRingCat.ofHom (algebraMap k K)))) ∧
        (e.hom ≫ pullback.snd _ _ =
          (pullback q (Spec.map (CommRingCat.ofHom (algebraMap k K)))).fromReducedNormalization ≫
            pullback.snd q (Spec.map (CommRingCat.ofHom (algebraMap k K))))) ∧
    (IsAlgClosed k → ∀ (K : Type u) [Field K] [Algebra k K],
      ∃! e : (pullback q (Spec.map (CommRingCat.ofHom (algebraMap k K)))).reducedNormalization ≅
          pullback (X.fromReducedNormalization ≫ q)
            (Spec.map (CommRingCat.ofHom (algebraMap k K))),
        (e.hom ≫ pullback.fst _ _ ≫ X.fromReducedNormalization =
          (pullback q (Spec.map (CommRingCat.ofHom (algebraMap k K)))).fromReducedNormalization ≫
            pullback.fst q (Spec.map (CommRingCat.ofHom (algebraMap k K)))) ∧
        (e.hom ≫ pullback.snd _ _ =
          (pullback q (Spec.map (CommRingCat.ofHom (algebraMap k K)))).fromReducedNormalization ≫
            pullback.snd q (Spec.map (CommRingCat.ofHom (algebraMap k K)))))  := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian q
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace q
  have : IsNoetherian X := ⟨⟩
  obtain ⟨N, hn, hNd, hNi⟩ := all_normal_locus X q
  have hbir : ∃ U : X.Opens, Dense (U : Set X) ∧
      IsIso (X.fromReducedNormalization ∣_ U) := ⟨N, hNd, hNi⟩
  have hopen (W : X.Opens) := all_normal_locus W.toScheme (W.ι ≫ q)
  have hsep (K : Type u) [Field K] [Algebra k K]
      (hK : Algebra.IsSeparableExtension k K) :
      ∃! e : (pullback q (Spec.map (CommRingCat.ofHom (algebraMap k K)))).reducedNormalization ≅
          pullback (X.fromReducedNormalization ≫ q)
            (Spec.map (CommRingCat.ofHom (algebraMap k K))),
        (e.hom ≫ pullback.fst _ _ ≫ X.fromReducedNormalization =
          (pullback q (Spec.map (CommRingCat.ofHom (algebraMap k K)))).fromReducedNormalization ≫
            pullback.fst q (Spec.map (CommRingCat.ofHom (algebraMap k K)))) ∧
        (e.hom ≫ pullback.snd _ _ =
          (pullback q (Spec.map (CommRingCat.ofHom (algebraMap k K)))).fromReducedNormalization ≫
            pullback.snd q (Spec.map (CommRingCat.ofHom (algebraMap k K)))) := by
    have : IsReduced (pullback q (Spec.map (CommRingCat.ofHom (algebraMap k K)))) :=
      reduced_baseChange X q K hK
    obtain ⟨V, _, hVd, hVi⟩ := all_normal_locus
      (pullback q (Spec.map (CommRingCat.ofHom (algebraMap k K)))) (pullback.snd _ _)
    exact field_comparison X q hbir K hK ⟨V, hVd, hVi⟩
  refine ⟨finite_normalization X q, surjective_normalization X,
    ⟨N, hn, hNd, hNi⟩, ?_, hsep, ?_⟩
  · intro W
    obtain ⟨V, _, hVd, hVi⟩ := hopen W
    exact open_comparison X q hbir W ⟨V, hVd, hVi⟩
  · intro hk K _ _
    let := hk
    exact hsep K (Algebra.separable_of_perfect k K)

end AlgebraicGeometry
