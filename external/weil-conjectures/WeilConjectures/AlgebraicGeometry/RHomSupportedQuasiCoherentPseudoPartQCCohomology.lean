/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PseudoCoherentComplex
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.AlgebraicGeometry.FiniteFreeHomComplexQCCohomology
import WeilConjectures.AlgebraicGeometry.DerivedInternalHomRestrictOpen
import WeilConjectures.Algebra.Homology.BoundedBelowInjectiveResolution
import WeilConjectures.FromJoel.Algebra.Homology.Embedding.StupidTrunc

/-! # Cohomology sheaves of internal Hom out of a pseudo-coherent complex

The degreewise calculation behind the quasi-coherence clause of the pseudo-coherent
internal-Hom lemma: locally, each cohomology sheaf of the Hom complex is computed by a
truncation of a bounded-above finite free model (Stacks Project, Tag 0A6H, clause (1)). -/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

private theorem homFunctor_preservesZeroMorphisms
    {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{u})
    (M : SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
    ((SheafOfModules.homFunctor R).obj (op M)).PreservesZeroMorphisms := by
  constructor
  intro A B
  apply SheafOfModules.hom_ext
  ext V φ : 3
  change (PresheafOfModules.restrictOver R.obj V.unop).map (𝟙 M.val) ≫ φ ≫
    (PresheafOfModules.restrictOver R.obj V.unop).map 0 = 0
  ext W x
  rfl

private theorem product_map_isIso
    {C : Type*} [Category C] {ι : Type*}
    {A B : ι → C} {S T : C}
    (π : ∀ i, S ⟶ A i) (ρ : ∀ i, T ⟶ B i)
    (hS : IsLimit (Fan.mk S π)) (hT : IsLimit (Fan.mk T ρ))
    (a : ∀ i, A i ⟶ B i) [∀ i, IsIso (a i)]
    (f : S ⟶ T) (hf : ∀ i, f ≫ ρ i = π i ≫ a i) : IsIso f := by
  let g : T ⟶ S := hS.lift (Fan.mk T (fun i ↦ ρ i ≫ inv (a i)))
  have hg (i : ι) : g ≫ π i = ρ i ≫ inv (a i) := hS.fac _ ⟨i⟩
  refine ⟨⟨g, ?_, ?_⟩⟩
  · apply hS.hom_ext
    rintro ⟨i⟩
    change (f ≫ g) ≫ π i = (𝟙 S) ≫ π i
    rw [Category.assoc, hg, ← Category.assoc, hf]
    simp
  · apply hT.hom_ext
    rintro ⟨i⟩
    change (g ≫ f) ≫ ρ i = (𝟙 T) ≫ ρ i
    rw [Category.assoc, hf, ← Category.assoc, hg]
    simp

private theorem truncIndex (c i : ℤ) (hi : c ≤ i) :
    (ComplexShape.embeddingUpIntGE c).f (i - c).toNat = i := by
  simp only [ComplexShape.embeddingUpIntGE_f]
  rw [Int.toNat_of_nonneg (by omega)]
  omega

private theorem homComplex_trunc_component_isIso
    {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{u})
    (P I : CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ)
    (c m q : ℤ) [I.IsStrictlyGE m] (hc : c + q ≤ m) :
    IsIso (((homComplexFunctor (R := R)).map
      (P.ιStupidTrunc (ComplexShape.embeddingUpIntGE c)).op).app I |>.f q) := by
  classical
  let E := P.stupidTrunc (ComplexShape.embeddingUpIntGE c)
  let f := P.ιStupidTrunc (ComplexShape.embeddingUpIntGE c)
  obtain ⟨π, hπ, _hd, hmap⟩ := Classical.choose_spec
    (homComplex_exists (C := C) (J := J) (R := R))
  let a (p : ℤ) := SheafOfModules.homObjMap (R := R) (f.f p) (𝟙 (I.X (p + q)))
  have ha (p : ℤ) : IsIso (a p) := by
    by_cases hp : c ≤ p
    · have : IsIso (f.f p) := P.isIso_ιStupidTrunc_f _ (truncIndex c p hp)
      change IsIso (((SheafOfModules.homFunctor R).flip.obj (I.X (p + q))).map
        (f.f p).op)
      infer_instance
    · have hz := I.isZero_of_isStrictlyGE m (p + q) (by omega)
      have (M : SheafOfModules.{u}
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
          ((SheafOfModules.homFunctor R).obj (op M)).PreservesZeroMorphisms :=
        homFunctor_preservesZeroMorphisms J R M
      have hA := ((SheafOfModules.homFunctor R).obj (op (P.X p))).map_isZero hz
      have hB := ((SheafOfModules.homFunctor R).obj (op (E.X p))).map_isZero hz
      exact ⟨⟨0, hA.eq_of_src _ _, hB.eq_of_src _ _⟩⟩
  exact product_map_isIso
    (fun p ↦ π P I q p (p + q) rfl)
    (fun p ↦ π E I q p (p + q) rfl)
    (hπ P I q).some (hπ E I q).some a _ (fun p ↦ by
      simpa [a, f, homComplexFunctor] using hmap P E I I f (𝟙 I) q p (p + q) rfl)

private theorem homComplex_trunc_homology_isIso
    {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{u})
    (P I : CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ)
    (m n : ℤ) [I.IsStrictlyGE m] :
    IsIso (HomologicalComplex.homologyMap
      (((homComplexFunctor (R := R)).map
        (P.ιStupidTrunc (ComplexShape.embeddingUpIntGE (m - n - 1))).op).app I) n) := by
  let f := ((homComplexFunctor (R := R)).map
    (P.ιStupidTrunc (ComplexShape.embeddingUpIntGE (m - n - 1))).op).app I
  have hprev : IsIso (f.f ((ComplexShape.up ℤ).prev n)) :=
    homComplex_trunc_component_isIso J R P I _ m _ (by simp; omega)
  have hmid : IsIso (f.f n) :=
    homComplex_trunc_component_isIso J R P I _ m _ (by omega)
  have hnext : IsIso (f.f ((ComplexShape.up ℤ).next n)) :=
    homComplex_trunc_component_isIso J R P I _ m _ (by simp)
  change IsIso (ShortComplex.homologyMap
    ((HomologicalComplex.shortComplexFunctor _ (.up ℤ) n).map f))
  exact ShortComplex.isIso_homologyMap_of_epi_of_isIso_of_mono' _
    (show Epi (f.f ((ComplexShape.up ℤ).prev n)) from inferInstance)
    hmid (show Mono (f.f ((ComplexShape.up ℤ).next n)) from inferInstance)

set_option backward.isDefEq.respectTransparency false in
/-- The degreewise quasi-coherence calculation for RHom from a pseudo-coherent complex.

Source: Stacks Project, Tag 0A6H, clause (1), affine-local finite-free calculation.
Proof: choose the local bounded-above finite-free model P supplied by pseudo-coherence.
Restriction preserves the lower bound and quasi-coherent cohomology of L. Represent its
restriction by a bounded-below K-injective complex I with quasi-coherent cohomology.
If I vanishes below m, cutting P below m - n - 1 changes no Hom factors in degrees
n - 1, n, n + 1: discarded factors have zero target. The product universal properties
make the comparison an isomorphism in these three degrees, hence on H^n. The truncated
source is a bounded finite-free complex, so finiteFree_homComplex_qc_cohomology applies.
The K-injective RHom computation and restriction comparison identify this with the
restriction of the desired cohomology sheaf. Quasi-coherence glues along the chosen cover.
(blueprint: new-lem-sc-rhom-supported-qcoherent-pseudo-part-qc-cohomology). -/
theorem rhom_supported_quasiCoherent_pseudo_part_qc_cohomology
    (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (K L : schemeDerivedCategory X)
    (hL : schemeDerivedQCohProperty X L)
    (hK : Scheme.IsPseudoCoherent X K) (hGE : ∃ a : ℤ, L.IsGE a)
    (n : ℤ) :
    ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).obj
      ((derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
        X.toRingedSpace.sheaf).obj (op K, L))).IsQuasicoherent := by
  classical
  -- Reuse the site instances in both the local calculation and the final gluing.
  let J := Opens.grothendieckTopology X.toRingedSpace
  have : HasSheafify J AddCommGrpCat.{u} := inferInstance
  have : J.WEqualsLocallyBijective AddCommGrpCat.{u} := inferInstance
  have : ∀ V, HasSheafify (J.over V) AddCommGrpCat.{u} := inferInstance
  have : ∀ V, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{u} := inferInstance
  have : ∀ V W, HasSheafify ((J.over V).over W) AddCommGrpCat.{u} := inferInstance
  have : ∀ V W, ((J.over V).over W).WEqualsLocallyBijective AddCommGrpCat.{u} := inferInstance
  choose U hx P hb hf he using hK
  let H := (DerivedCategory.homologyFunctor
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).obj
      ((derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
        X.toRingedSpace.sheaf).obj (op K, L))
  have hlocal (x : X) : (H.over (U x)).IsQuasicoherent := by
    let V := U x
    let D := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V)
    let : Category.{w} (@DerivedCategory (SheafOfModules.{u}
        ((sheafCompose ((Opens.grothendieckTopology X.toRingedSpace).over V)
          (forget₂ CommRingCat RingCat)).obj (X.toRingedSpace.sheaf.over V))) _ _
        (inferInstanceAs (HasDerivedCategory.{w} D))) :=
      inferInstanceAs (Category.{w} (DerivedCategory D))
    let F := SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) V
    let QU := DerivedCategory.Q (C := D)
    obtain ⟨eP⟩ := he x
    obtain ⟨a, ha⟩ := hGE
    have hLU : (F.mapDerivedCategory.obj L).IsGE a := by
      rw [DerivedCategory.isGE_iff]
      intro i hi
      exact (F.map_isZero ((DerivedCategory.isGE_iff L a).mp ha i hi)).of_iso
        ((F.mapDerivedCategoryHomologyFunctorIso i).app L).symm
    let := hLU
    obtain ⟨G, hG, ⟨eG⟩⟩ :=
      (F.mapDerivedCategory.obj L).exists_iso_Q_obj_of_isGE a
    obtain ⟨I, i, hi, ⟨m, hm⟩, _hinj, hI⟩ :=
      SheafOfModules.exists_boundedBelow_injective_resolution
        ((Opens.grothendieckTopology X.toRingedSpace).over V)
        (X.toRingedSpace.sheaf.over V) G ⟨a, hG⟩
    let := hi
    let := hm
    let := hI
    let eI : QU.obj I ≅ F.mapDerivedCategory.obj L :=
      (asIso (QU.map i)).symm ≪≫ eG.symm
    have hIq (q : ℤ) : (I.homology q).IsQuasicoherent := by
      have : ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) q).obj L).IsQuasicoherent :=
        hL q
      have hq := SheafOfModules.isQuasicoherent_over
        ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) q).obj L) V
      exact (SheafOfModules.isQuasicoherent ((moduleRings X.toRingedSpace).over V)).prop_of_iso
        (((DerivedCategory.homologyFunctorFactors D q).app I).symm ≪≫
          (DerivedCategory.homologyFunctor D q).mapIso eI ≪≫
          ((F.mapDerivedCategoryHomologyFunctorIso q).app L).symm).symm hq
    let c := m - n - 1
    let E := (P x).stupidTrunc (ComplexShape.embeddingUpIntGE c)
    have hz (q : ℤ) (hq : q < c) : IsZero (E.X q) :=
      (P x).isZero_stupidTrunc_X _ q (by
        intro k hk
        simp only [ComplexShape.embeddingUpIntGE_f] at hk
        omega)
    have hEb : ∃ a b : ℤ, ∀ q : ℤ, q < a ∨ b < q → IsZero (E.X q) := by
      obtain ⟨b, hbound⟩ := hb x
      refine ⟨c, b, ?_⟩
      intro q hq
      by_cases hqc : q < c
      · exact hz q hqc
      · exact (hbound q (hq.resolve_left hqc)).of_iso
          ((P x).stupidTruncXIso _ (truncIndex c q (by omega)))
    have hEf (q : ℤ) : ∃ r : ℕ, Nonempty (E.X q ≅ SheafOfModules.free
        (R := (moduleRings X.toRingedSpace).over V) (ULift.{u} (Fin r))) := by
      by_cases hq : c ≤ q
      · obtain ⟨r, ⟨e⟩⟩ := hf x q
        exact ⟨r, ⟨(P x).stupidTruncXIso _ (truncIndex c q hq) ≪≫ e⟩⟩
      · have hzero : IsZero (SheafOfModules.free
            (R := (moduleRings X.toRingedSpace).over V) (ULift.{u} (Fin 0))) := by
          apply (IsZero.iff_id_eq_zero _).mpr
          apply (SheafOfModules.freeHomEquiv _).injective
          funext k
          exact Fin.elim0 k.down
        exact ⟨0, ⟨(hz q (by omega)).iso hzero⟩⟩
    have hqc := finiteFree_homComplex_qc_cohomology X V E I hEb hEf hIq n
    let f := ((homComplexFunctor (R := X.toRingedSpace.sheaf.over V)).map
      ((P x).ιStupidTrunc (ComplexShape.embeddingUpIntGE c)).op).app I
    have : IsIso (HomologicalComplex.homologyMap f n) :=
      homComplex_trunc_homology_isIso
        ((Opens.grothendieckTopology X.toRingedSpace).over V)
        (X.toRingedSpace.sheaf.over V) (P x) I m n
    have hPI :
        ((homComplex (R := X.toRingedSpace.sheaf.over V) (P x) I).homology n).IsQuasicoherent :=
      (SheafOfModules.isQuasicoherent ((moduleRings X.toRingedSpace).over V)).prop_of_iso
        (asIso (HomologicalComplex.homologyMap f n)).symm hqc
    obtain ⟨eHom⟩ := @derivedInternalHom_obj_iso.{u, w} (Over V) _
      ((Opens.grothendieckTopology X.toRingedSpace).over V)
      (X.toRingedSpace.sheaf.over V)
      (inferInstanceAs (HasDerivedCategory.{w} D))
      (F.mapDerivedCategory.obj K) (F.mapDerivedCategory.obj L)
      (P x) I inferInstance eP.symm eI
    obtain ⟨eR⟩ := derivedInternalHom_restrict_open X.toRingedSpace V K L
    exact (SheafOfModules.isQuasicoherent ((moduleRings X.toRingedSpace).over V)).prop_of_iso
      (((F.mapDerivedCategoryHomologyFunctorIso n).app _) ≪≫
        (DerivedCategory.homologyFunctor D n).mapIso (eR.symm ≪≫ eHom) ≪≫
        ((DerivedCategory.homologyFunctorFactors D n).app
          (homComplex (R := X.toRingedSpace.sheaf.over V) (P x) I))).symm hPI
  have : ∀ x : X, (H.over (U x)).IsQuasicoherent := hlocal
  apply SheafOfModules.IsQuasicoherent.of_coversTop H U
  apply (Opens.coversTop_iff _ U).mpr
  apply eq_top_iff.mpr
  intro x _
  exact Opens.mem_iSup.mpr ⟨x, hx x⟩

end AlgebraicGeometry
