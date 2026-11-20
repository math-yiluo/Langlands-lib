import Langlands.GroupScheme.Derived.CentralIntersectionReduction
import Langlands.GroupScheme.Derived.CenterReduction
import Langlands.GroupScheme.HomScheme.ArtinianCentralizerParameterSmooth
import Langlands.GroupScheme.Rational.FiniteFieldMaximalTorusTransporterReduction
import Langlands.GroupScheme.Rational.SemigroupIntersectionGeometry
import Langlands.GroupScheme.Rational.TorusCentralizerFactorization
import Langlands.GroupScheme.Rational.UnipotentSmoothCenter
import Langlands.GroupScheme.Reductive.CenterBaseChangeProof
import Langlands.GroupScheme.SubgroupFunctor.FpqcDescent
import Langlands.GroupScheme.Torus.MaximalBaseChangeProof
import Langlands.GroupScheme.Torus.MultiplicativeTypeLargestSubtorusProof
import Langlands.GroupScheme.Torus.MultiplicativeTypeSubgroups
import Langlands.GroupScheme.Torus.RelativeFieldComparison
import Langlands.GroupScheme.Torus.SeparatedCentralizerModel

/-! # Field extension and reflection of torus centralizers -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.GroupScheme.TorusSubgroupModuli

open SubgroupFunctor

/-- A torus-centralizer range remains a torus-centralizer range after base change. -/
theorem IsTorusCentralizer.baseChange {S S' : Scheme.{u}} {G : GroupScheme S}
    {F : SubgroupFunctor G} (hF : IsTorusCentralizer F) (b : S' ⟶ S) :
    IsTorusCentralizer (F.baseChange b) := by
  obtain ⟨T, t, ht, hT, hEq⟩ := hF
  refine ⟨_, (GroupScheme.baseChange b).map t, ht.baseChange b, hT.baseChange b, ?_⟩
  rw [hEq, SubgroupFunctor.centralizer_baseChange, range_baseChangeHom]

private theorem isTorusCentralizer_comp_iso {S : Scheme.{u}} {H G G' : GroupScheme S}
    (i : H ⟶ G) (e : G ≅ G') (h : IsTorusCentralizer (range i)) :
    IsTorusCentralizer (range (i ≫ e.hom)) := by
  obtain ⟨T, t, ht, hT, he⟩ := h
  refine ⟨T, t ≫ e.hom, ht.comp_iso e, hT, ?_⟩
  rw [range_comp_iso, he]
  simpa only [Iso.symm_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id] using
    (centralizer_range_eq_comap_of_iso (t ≫ e.hom) e.symm).symm

/-- Ambient isomorphisms preserve and reflect the torus-centralizer condition. -/
theorem isTorusCentralizer_comp_iso_iff {S : Scheme.{u}} {H G G' : GroupScheme S}
    (i : H ⟶ G) (e : G ≅ G') :
    IsTorusCentralizer (range (i ≫ e.hom)) ↔ IsTorusCentralizer (range i) := by
  refine ⟨fun h => ?_, isTorusCentralizer_comp_iso i e⟩
  simpa only [Iso.symm_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id] using
    isTorusCentralizer_comp_iso (i ≫ e.hom) e.symm h

section Field

variable {k : Type u} [Field k]

local notation "S" => Spec (CommRingCat.of k)

private theorem range_le_center_comap {H M T : GroupScheme S} {g : T ⟶ M} {m : M ⟶ H}
    (hc : IsCentral (g ≫ m)) : range g ≤ (center H).comap m := by
  intro U x hx
  obtain ⟨y, rfl⟩ := mem_range.mp hx
  apply mem_comap.mpr
  apply (isCentral_iff_range_le_center _).mp hc U
  exact mem_range.mpr ⟨y, by rw [Grp.comp_hom_hom, Category.assoc]⟩

private theorem isCentral_of_range_le_center_comap {H M T : GroupScheme S}
    {g : T ⟶ M} {m : M ⟶ H} (h : range g ≤ (center H).comap m) : IsCentral (g ≫ m) := by
  apply (isCentral_iff_range_le_center _).mpr
  intro U x hx
  obtain ⟨y, rfl⟩ := mem_range.mp hx
  have hy : y ≫ g.hom.hom ∈ (range g).carrier U := ⟨y, rfl⟩
  simpa only [Grp.comp_hom_hom, Category.assoc] using mem_comap.mp (h U hy)

set_option maxHeartbeats 1200000 in
/-- The central subtori of a smooth affine group over a field lie in one
central torus, with the same universal property after every field extension. -/
theorem exists_centralTorus_containing_over_extensions (H : GroupScheme S)
    [Smooth H.X.hom] [IsAffineHom H.X.hom] :
    ∃ (Z : GroupScheme S) (z : Z ⟶ H), IsClosedSubgroup z ∧ RelativeTorus.IsTorus Z ∧
      IsCentral z ∧ ∀ (K : Type u) [Field K] [Algebra k K],
        let Q := baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))
        ∀ (T : GroupScheme (Spec (CommRingCat.of K))) (t : T ⟶ Q.obj H),
          IsClosedSubgroup t → RelativeTorus.IsTorus T → IsCentral t →
          ∃ f : T ⟶ Q.obj Z, f ≫ Q.map z = t := by
  obtain ⟨M, m, hm⟩ := TorusExistence.exists_isMaximalTorus H
  obtain ⟨C, c, hc, hC⟩ := center_hasClosedRepresentative (G := H)
  let P := subgroupIntersection m c
  let p := subgroupIntersectionFst m c
  have hp : IsClosedSubgroup p := MorphismProperty.of_isPullback (P := @IsClosedImmersion)
    (subgroupIntersection_isPullback_scheme m c).flip hc
  have hrep := hC.comap_subgroupIntersectionFst hc m
  have hpc : IsCentral (p ≫ m) := isCentral_of_range_le_center_comap hrep.2.le
  have hpmt : IsMultiplicativeType P := hm.1.isMultiplicativeType.of_isClosedSubgroup p hp
  have hsub := multiplicativeTypeLargestSubtorus k P hpmt
  obtain ⟨Z, z, hz⟩ := hsub.1
  refine ⟨Z, z ≫ p ≫ m, hz.2.1.comp (hp.comp hm.2.1), hz.1.isRelativeTorus, hpc.comp z, ?_⟩
  intro K _ _ Q T t ht hT htc
  let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let H' := Q.obj H
  let m' := Q.map m
  let p' := Q.map p
  have : Smooth H'.X.hom := MorphismProperty.pullback_snd (P := @Smooth) _ _ inferInstance
  have : IsAffineHom H'.X.hom := MorphismProperty.pullback_snd (P := @IsAffineHom) _ _ inferInstance
  have hm' : IsMaximalTorus (T := (CommGroupScheme.baseChange b).obj M) m' :=
    (maximalTorusBaseChange k K H M m hm.1 hm.2.1).mp hm
  obtain ⟨g, hg⟩ := htc.exists_factor_of_isMaximalTorus hT.isTorus hm'
  have hc' : IsCentral (g ≫ m') := hg.symm ▸ htc
  have hrep' : ((center H').comap m').IsRepresentedBy p' := by
    change ((center ((baseChange b).obj H)).comap ((baseChange b).map m)).IsRepresentedBy
      ((baseChange b).map p)
    rw [center_baseChange, ← SubgroupFunctor.comap_baseChange]
    exact hrep.baseChange b
  let r := hrep'.factorHom g (range_le_center_comap hc')
  have hr : r ≫ p' = g := hrep'.factorHom_comp _ _
  have he : r ≫ (p' ≫ m') = t := by rw [← Category.assoc, hr, hg]
  have hr' : IsClosedSubgroup r :=
    ((hp.baseChange b).comp (hm.2.1.baseChange b)).of_comp (he.symm ▸ ht)
  obtain ⟨f, hf⟩ := (hsub.2.2.1 K Z z hz).2.2 T r hT.isTorus hr'
  refine ⟨f, ?_⟩
  rw [Functor.map_comp, ← Category.assoc, hf, Functor.map_comp, he]

private theorem range_le_centralizer_comp {H G T : GroupScheme S}
    {z : T ⟶ H} (hz : IsCentral z) (i : H ⟶ G) : range i ≤ (range (z ≫ i)).centralizer := by
  have htop : (⊤ : SubgroupFunctor H) ≤ (range z).centralizer := by
    rw [le_centralizer_iff, centralizer_top]
    exact (isCentral_iff_range_le_center z).mp hz
  intro U x hx
  obtain ⟨y, rfl⟩ := hx
  have hy : y ∈ (⊤ : SubgroupFunctor H).carrier U := trivial
  exact centralizer_range_le_comap z i U (htop U hy)

set_option maxHeartbeats 1400000 in
private theorem isTorusCentralizer_of_extension (K : Type u) [Field K] [Algebra k K]
    {G H : GroupScheme S} [IsAffineHom G.X.hom] [Smooth H.X.hom]
    (i : H ⟶ G) (hi : IsClosedSubgroup i)
    (h : IsTorusCentralizer
      (range ((baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map i))) :
    IsTorusCentralizer (range i) := by
  let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let Q := baseChange b
  obtain ⟨T, t, ht, hT, he⟩ := h
  let B := hT.commGroupScheme
  let tb : B.toGrp ⟶ Q.obj G := t
  have hi' : IsClosedImmersion (Q.map i).hom.hom.left := hi.baseChange b
  let hrep : (torusCentralizer tb).IsRepresentedBy (Q.map i) :=
    ⟨Over.mono_of_mono_left _, he.trans (torusCentralizer_eq_centralizer_range tb).symm⟩
  let s := torusCentralizerFactor tb hrep
  have hs : IsClosedSubgroup s := isClosedSubgroup_torusCentralizerFactor tb hrep hi' ht
  have hsc : IsCentral s := isCentral_torusCentralizerFactor tb hrep
  have hst : s ≫ Q.map i = tb := torusCentralizerFactor_comp tb hrep
  have : IsClosedImmersion i.hom.hom.left := hi
  have : IsAffineHom H.X.hom := by rw [← Over.w i.hom.hom]; infer_instance
  obtain ⟨Z, z, hz, hZ, hzc, hL⟩ := exists_centralTorus_containing_over_extensions H
  obtain ⟨f, hf⟩ := hL K T s hs hT hsc
  let v := z ≫ i
  have hEq : range (Q.map i) = (range (Q.map v)).centralizer := by
    apply le_antisymm
    · rw [Functor.map_comp]
      exact range_le_centralizer_comp (hzc.baseChange b) (Q.map i)
    · rw [he]
      have hfac : f ≫ Q.map v = t := by rw [Functor.map_comp, ← Category.assoc, hf, hst]
      intro U x hx V a y hy
      apply hx V a y
      obtain ⟨w, rfl⟩ := mem_range.mp hy
      exact mem_range.mpr ⟨w ≫ f.hom.hom, by rw [Category.assoc, ← Grp.comp_hom_hom, hfac]⟩
  let D := hZ.commGroupScheme
  let d : D.toGrp ⟶ G := v
  obtain ⟨C, c, hc, hclosed⟩ := relativeTorusCentralizer_isClosedRepresentable_of_separated d hZ
  have hc' : range c = (range v).centralizer := hc.2.trans (torusCentralizer_eq_centralizer_range d)
  refine ⟨Z, v, hz.comp hi, hZ, ?_⟩
  have : IsClosedImmersion c.hom.hom.left := hclosed
  have : Mono c.hom.hom := Over.mono_of_mono_left _
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  obtain ⟨hbs, hbf, hbq⟩ := fieldExtension_fpqc k K
  rw [← hc']
  apply range_eq_of_baseChange_eq b i c
  rw [← range_baseChangeHom, hc', SubgroupFunctor.centralizer_baseChange, ← range_baseChangeHom]
  exact hEq

end Field

/-- The torus-centralizer condition for a smooth closed subgroup of an affine
field group is equivalent to the same condition after any field extension. -/
def TorusCentralizerFieldReflectionStatement : Prop :=
  ∀ (k K : Type u) [Field k] [Field K] [Algebra k K]
    (G H : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom] [Smooth H.X.hom]
    (i : H ⟶ G), IsClosedSubgroup i →
    (IsTorusCentralizer (range i) ↔ IsTorusCentralizer
      (range ((baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map i)))

theorem torusCentralizerFieldReflection : TorusCentralizerFieldReflectionStatement.{u} := by
  intro k K _ _ _ G H _ _ i hi
  let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
  constructor
  · intro h
    rw [range_baseChangeHom]
    exact h.baseChange b
  · exact isTorusCentralizer_of_extension K i hi

/-- The field comparison also applies to a specified map of field spectra. -/
theorem isTorusCentralizer_of_fieldMap_iff {k K : Type u} [Field k] [Field K]
    {G H : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom] [Smooth H.X.hom]
    (i : H ⟶ G) (hi : IsClosedSubgroup i) (b : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k)) :
    IsTorusCentralizer (range ((baseChange b).map i)) ↔ IsTorusCentralizer (range i) := by
  let : Algebra k K := (Spec.preimage b).hom.toAlgebra
  have hb : Spec.map (CommRingCat.ofHom (algebraMap k K)) = b := Spec.map_preimage b
  rw [← hb]
  exact (torusCentralizerFieldReflection k K G H i hi).symm

end Langlands.GroupScheme.TorusSubgroupModuli
