import Langlands.GroupScheme.IdentityJetProjectionGeometry
import Langlands.GroupScheme.Absolute.ParabolicTransport
import Langlands.GroupScheme.HomScheme.TorusSubgroupModuli
import Langlands.GroupScheme.IdentityJetStabilizerParameter
import Langlands.GroupScheme.Rational.SplitUnipotentTransport

/-! # The finite closed jet of a smooth subgroup as an actual parameter point -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.GroupScheme.IdentityJet

open Langlands.AlgebraicGeometry.FiniteFlatSubschemeParameter TorusSubgroupModuli SubgroupFunctor

variable {S : Scheme.{u}} (G : GroupScheme S) [IsSeparated G.X.hom]
  (n : ℕ) {T U : Over S} {H : GroupScheme T.left}

/-- The canonical actual comparison with the jet pulled back from the original base. -/
def ambientJetPullbackIso (T : Over S) :
    scheme ((baseChange T.hom).obj G) n ≅ ((Over.pullback T.hom).obj (overScheme G n)).left :=
  (baseChange_isPullback G T.hom n).isoPullback

/-- The actual closed-subgroup jet in the pulled-back ambient jet. -/
def subgroupJetMap (i : H ⟶ (baseChange T.hom).obj G) :
    scheme H n ⟶ ((Over.pullback T.hom).obj (overScheme G n)).left :=
  map i n ≫ (ambientJetPullbackIso G n T).hom

@[reassoc (attr := simp)]
theorem subgroupJetMap_fst (i : H ⟶ (baseChange T.hom).obj G) :
    subgroupJetMap G n i ≫ pullback.fst (overScheme G n).hom T.hom =
      map i n ≫ baseChangeMap G T.hom n := by
  rw [subgroupJetMap, Category.assoc]
  change map i n ≫ (baseChange_isPullback G T.hom n).isoPullback.hom ≫
    pullback.fst (projection G n) T.hom = _
  rw [IsPullback.isoPullback_hom_fst]

@[reassoc (attr := simp)]
theorem subgroupJetMap_snd (i : H ⟶ (baseChange T.hom).obj G) :
    subgroupJetMap G n i ≫ pullback.snd (overScheme G n).hom T.hom = projection H n := by
  rw [subgroupJetMap, Category.assoc]
  change map i n ≫ (baseChange_isPullback G T.hom n).isoPullback.hom ≫
    pullback.snd (projection G n) T.hom = _
  rw [IsPullback.isoPullback_hom_snd, map_projection]

/-- The ideal defining the actual subgroup jet inside the pulled-back ambient jet. -/
def subgroupJetIdeal (i : H ⟶ (baseChange T.hom).obj G) :
    ((Over.pullback T.hom).obj (overScheme G n)).left.IdealSheafData :=
  (subgroupJetMap G n i).ker

private theorem subgroupJetMap_isClosedImmersion (i : H ⟶ (baseChange T.hom).obj G)
    (hi : IsClosedSubgroup i) : IsClosedImmersion (subgroupJetMap G n i) := by
  let : IsClosedImmersion i.hom.hom.left := hi
  let : IsClosedImmersion (map i n) := map_isClosedImmersion i n
  dsimp [subgroupJetMap]
  infer_instance

/-- The scheme defined by a closed subgroup's jet ideal is its actual identity jet. -/
def subgroupJetIso (i : H ⟶ (baseChange T.hom).obj G) (hi : IsClosedSubgroup i) :
    scheme H n ≅ (subgroupJetIdeal G n i).subscheme :=
  haveI := subgroupJetMap_isClosedImmersion G n i hi
  asIso (subgroupJetMap G n i).toImage

@[reassoc (attr := simp)]
theorem subgroupJetIso_hom_subschemeι (i : H ⟶ (baseChange T.hom).obj G) (hi : IsClosedSubgroup i) :
    (subgroupJetIso G n i hi).hom ≫ (subgroupJetIdeal G n i).subschemeι = subgroupJetMap G n i :=
  (subgroupJetMap G n i).toImage_imageι

/-- A supplied finite-flat subscheme parameter classifies the jet of each smooth closed subgroup. -/
theorem existsUnique_subgroupJetPoint (D : Parameter (overScheme G n))
    [Smooth H.X.hom] (i : H ⟶ (baseChange T.hom).obj G) (hi : IsClosedSubgroup i) :
    ∃! g : T ⟶ D.base, D.eval (overScheme G n) g = subgroupJetIdeal G n i := by
  have : IsClosedImmersion i.hom.hom.left := hi
  have : IsSeparated H.X.hom := by
    have : IsSeparated ((baseChange T.hom).obj G).X.hom :=
      inferInstanceAs (IsSeparated (pullback.snd G.X.hom T.hom))
    rw [← Over.w i.hom.hom]
    infer_instance
  obtain ⟨_, hflat, hfp⟩ := projection_geometry H n
  let I := subgroupJetIdeal G n i
  let p := I.subschemeι ≫ pullback.snd (overScheme G n).hom T.hom
  let e := subgroupJetIso G n i hi
  have hp : e.hom ≫ p = projection H n := by
    rw [← Category.assoc, subgroupJetIso_hom_subschemeι, subgroupJetMap_snd]
  have hp' : e.inv ≫ projection H n = p := by rw [← hp, e.inv_hom_id_assoc]
  have hf : Flat p := hp' ▸ inferInstanceAs (Flat (e.inv ≫ projection H n))
  have hq : LocallyOfFinitePresentation p :=
    hp' ▸ inferInstanceAs (LocallyOfFinitePresentation (e.inv ≫ projection H n))
  exact D.classifies T I hf hq

omit [IsSeparated G.X.hom] in
private theorem familyHom_fst (i : H ⟶ (baseChange T.hom).obj G) (a : U ⟶ T) :
    (familyHom i a).hom.hom.left ≫ pullback.fst G.X.hom U.hom =
      pullback.fst H.X.hom a.left ≫ i.hom.hom.left ≫ pullback.fst G.X.hom T.hom := by
  simp only [familyHom, Grp.comp_hom_hom, Over.comp_left, Category.assoc,
    Descent.pullbackComparison_hom_fst]
  exact (reassoc_of% (RelativeIdentityComponent.overPullback_isPullback a.left i.hom.hom).w)
    (pullback.fst G.X.hom T.hom)

private theorem subgroupJetMap_testMap [IsSeparated H.X.hom]
    (i : H ⟶ (baseChange T.hom).obj G) (a : U ⟶ T) :
    subgroupJetMap G n (familyHom i a) ≫ testMap (overScheme G n) a =
      baseChangeMap H a.left n ≫ subgroupJetMap G n i := by
  apply pullback.hom_ext
  · simp only [Category.assoc, testMap_fst, subgroupJetMap_fst]
    have : Mono (inclusion G n) := inferInstanceAs (Mono (ideal G n).subschemeι)
    apply (cancel_mono (inclusion G n)).mp
    simp only [Category.assoc, baseChangeMap_inclusion, map_inclusion_assoc,
      baseChangeMap_inclusion_assoc, familyHom_fst]
  · rw [Category.assoc, testMap_snd, subgroupJetMap_snd_assoc, Category.assoc, subgroupJetMap_snd]
    exact (baseChange_isPullback H a.left n).w.symm

/-- The ideal of the subgroup jet pulls back to the actual ideal on every test. -/
theorem subgroupJetIdeal_testMap (i : H ⟶ (baseChange T.hom).obj G) (hi : IsClosedSubgroup i)
    (a : U ⟶ T) : (subgroupJetIdeal G n i).comap (testMap (overScheme G n) a) =
      subgroupJetIdeal G n (familyHom i a) := by
  have : IsClosedImmersion i.hom.hom.left := hi
  have : IsSeparated H.X.hom := by
    have : IsSeparated ((baseChange T.hom).obj G).X.hom :=
      inferInstanceAs (IsSeparated (pullback.snd G.X.hom T.hom))
    rw [← Over.w i.hom.hom]
    infer_instance
  have : IsClosedImmersion (subgroupJetMap G n i) := subgroupJetMap_isClosedImmersion G n i hi
  have h := baseChange_isPullback H a.left n
  have hp : IsPullback (subgroupJetMap G n (familyHom i a)) (baseChangeMap H a.left n)
      (testMap (overScheme G n) a) (subgroupJetMap G n i) := by
    refine (IsPullback.of_bot ?_ (subgroupJetMap_testMap G n i a).symm
      (testMap_isPullback (overScheme G n) a)).flip
    simpa only [subgroupJetMap_snd] using h
  rw [subgroupJetIdeal, subgroupJetIdeal, ← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion,
    ← hp.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso]

/-- The subgroup jet and the scheme of its ambient ideal agree over the test. -/
def subgroupJetOverIso (i : H ⟶ (baseChange T.hom).obj G) (hi : IsClosedSubgroup i) :
    overScheme H n ≅ subschemeOver G n T (subgroupJetIdeal G n i) :=
  Over.isoMk (subgroupJetIso G n i hi) (by
    change (subgroupJetIso G n i hi).hom ≫
      (subgroupJetIdeal G n i).subschemeι ≫ pullback.snd (overScheme G n).hom T.hom = projection H n
    rw [subgroupJetIso_hom_subschemeι_assoc, subgroupJetMap_snd])

/-- The canonical jet isomorphism respects the inclusions of both descriptions in the actual group. -/
theorem subgroupJetIso_comp_subschemeToGroup (i : H ⟶ (baseChange T.hom).obj G) (hi : IsClosedSubgroup i) :
    (subgroupJetOverIso G n i hi).hom ≫
      subschemeToGroup G n T (subgroupJetIdeal G n i) = toGroup i n := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · simp only [subgroupJetOverIso, Over.comp_left, Over.isoMk_hom_left, Category.assoc, subschemeToGroup_fst,
      subgroupJetIso_hom_subschemeι_assoc, subgroupJetMap_fst_assoc, toGroup_left]
    change map i n ≫ baseChangeMap G T.hom n ≫ inclusion G n = _
    rw [baseChangeMap_inclusion, map_inclusion_assoc]
  · exact Over.w (_ ≫ _ ) |>.trans (Over.w (toGroup i n)).symm

private theorem subgroupJetIdeal_le_of_range_le
    {K : GroupScheme T.left} {i : H ⟶ (baseChange T.hom).obj G} {j : K ⟶ (baseChange T.hom).obj G}
    (hi : IsClosedSubgroup i) (hj : IsClosedSubgroup j) (h : range i ≤ range j) :
    subgroupJetIdeal G n j ≤ subgroupJetIdeal G n i := by
  have : IsClosedImmersion i.hom.hom.left := hi
  have : IsClosedImmersion j.hom.hom.left := hj
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  have : Mono j.hom.hom := Over.mono_of_mono_left _
  obtain ⟨f, hf⟩ := exists_factor_of_range_le h
  have he : subgroupJetMap G n i = map f n ≫ subgroupJetMap G n j := by
    simp only [subgroupJetMap, ← Category.assoc, ← map_comp, hf]
  rw [subgroupJetIdeal, subgroupJetIdeal, he]
  exact (map f n).le_ker_comp (subgroupJetMap G n j)

/-- Equal closed subgroup functors have the same ideal for their actual jet. -/
theorem subgroupJetIdeal_eq_of_range_eq
    {K : GroupScheme T.left} {i : H ⟶ (baseChange T.hom).obj G} {j : K ⟶ (baseChange T.hom).obj G}
    (hi : IsClosedSubgroup i) (hj : IsClosedSubgroup j) (h : range i = range j) :
    subgroupJetIdeal G n i = subgroupJetIdeal G n j :=
  le_antisymm (subgroupJetIdeal_le_of_range_le G n hj hi h.ge)
    (subgroupJetIdeal_le_of_range_le G n hi hj h.le)

private theorem conjugationStabilizer_eq_of_source_iso {B : Scheme.{u}} {L : GroupScheme B}
    {X Y : Over B} (e : X ≅ Y) (x : X ⟶ L.X) (y : Y ⟶ L.X) (h : e.hom ≫ y = x) :
    conjugationStabilizer x = conjugationStabilizer y := by
  have he (W : Over B) : schemePointRange x W = schemePointRange y W := by
    apply Set.ext
    intro z
    constructor
    · rintro ⟨t, rfl⟩
      refine ⟨t ≫ e.hom, ?_⟩
      change (t ≫ e.hom) ≫ y = t ≫ x
      rw [Category.assoc, h]
    · rintro ⟨t, rfl⟩
      refine ⟨t ≫ e.inv, ?_⟩
      change (t ≫ e.inv) ≫ x = t ≫ y
      rw [Category.assoc, ← h, e.inv_hom_id_assoc]
  apply SubgroupFunctor.ext
  intro W
  ext z
  change (∀ V a x', x' ∈ schemePointRange x V → _) ↔
    (∀ V a x', x' ∈ schemePointRange y V → _)
  simp only [he]

private theorem conjugationStabilizer_le_comap {B : Scheme.{u}} {K L : GroupScheme B}
    {Z : Over B} (z : Z ⟶ K.X) (f : K ⟶ L) :
    conjugationStabilizer z ≤ (conjugationStabilizer (z ≫ f.hom.hom)).comap f := by
  intro W g hg
  rw [mem_comap]
  intro V a x hx
  obtain ⟨y, rfl⟩ := hx
  obtain ⟨⟨v, hv⟩, ⟨w, hw⟩⟩ := hg V a (y ≫ z) ⟨y, rfl⟩
  change v ≫ z = _ at hv
  change w ≫ z = _ at hw
  refine ⟨⟨v, ?_⟩, ⟨w, ?_⟩⟩
  · change v ≫ (z ≫ f.hom.hom) = _
    rw [← Category.assoc, hv]
    simp only [MonObj.mul_comp, GrpObj.inv_comp, Category.assoc]
  · change w ≫ (z ≫ f.hom.hom) = _
    rw [← Category.assoc, hw]
    simp only [MonObj.mul_comp, GrpObj.inv_comp, Category.assoc]

private theorem conjugationStabilizer_comp_iso {B : Scheme.{u}} {K L : GroupScheme B}
    {Z : Over B} (z : Z ⟶ K.X) (e : K ≅ L) :
    conjugationStabilizer (z ≫ e.hom.hom.hom) = (conjugationStabilizer z).comap e.inv := by
  have he : (z ≫ e.hom.hom.hom) ≫ e.inv.hom.hom = z := by
    rw [Category.assoc, ← Grp.comp_hom_hom, e.hom_inv_id, Grp.id_hom_hom, Category.comp_id]
  apply le_antisymm
  · have hh := conjugationStabilizer_le_comap (z ≫ e.hom.hom.hom) e.inv
    rwa [he] at hh
  · intro W g hg
    have hh : g ≫ e.inv.hom.hom ∈
        ((conjugationStabilizer (z ≫ e.hom.hom.hom)).comap e.hom).carrier W :=
      conjugationStabilizer_le_comap z e.hom W (mem_comap.mp hg)
    rwa [mem_comap, Category.assoc, ← Grp.comp_hom_hom, e.inv_hom_id,
      Grp.id_hom_hom, Category.comp_id] at hh

/-- A jet parameter point evaluates the universal stabilizer to the actual
jet stabilizer of its classified subgroup, by the specified ambient comparison. -/
theorem subgroupJetStabilizer_eval (D : Parameter (overScheme G n)) (a : T ⟶ D.base)
    (i : H ⟶ (baseChange T.hom).obj G) (hi : IsClosedSubgroup i)
    (h : D.eval (overScheme G n) a = subgroupJetIdeal G n i) :
    (conjugationStabilizer (subschemeToGroup G n D.base D.ideal)).baseChange a.left =
      (stabilizer i n).comap
        (Descent.pullbackComparison D.base.hom a.left T.hom (Over.w a) G).hom := by
  rw [subschemeStabilizer_eval, h]
  let e := Descent.pullbackComparison D.base.hom a.left T.hom (Over.w a) G
  let b := subgroupJetOverIso G n i hi
  have hb : b.hom ≫ subschemeToGroup G n T (subgroupJetIdeal G n i) = toGroup i n :=
    subgroupJetIso_comp_subschemeToGroup G n i hi
  rw [← conjugationStabilizer_eq_of_source_iso b _ _ (by rw [← Category.assoc, hb])]
  exact conjugationStabilizer_comp_iso (toGroup i n) e.symm

/-- Pullback of a represented universal stabilizer represents the specified
subgroup's actual jet stabilizer over the test. -/
theorem isRepresentedBy_subgroupJetStabilizer (D : Parameter (overScheme G n))
    {N : GroupScheme D.base.left} (j : N ⟶ (baseChange D.base.hom).obj G)
    (hj : IsClosedSubgroup j)
    (hrep : (conjugationStabilizer (subschemeToGroup G n D.base D.ideal)).IsRepresentedBy j)
    (a : T ⟶ D.base) (i : H ⟶ (baseChange T.hom).obj G) (hi : IsClosedSubgroup i)
    (h : D.eval (overScheme G n) a = subgroupJetIdeal G n i) :
    (stabilizer i n).IsRepresentedBy (familyHom j a) := by
  have : IsClosedImmersion (familyHom j a).hom.hom.left := isClosedSubgroup_familyHom j hj a
  refine ⟨Over.mono_of_mono_left _, ?_⟩
  let e := Descent.pullbackComparison D.base.hom a.left T.hom (Over.w a) G
  have he : range ((baseChange a.left).map j) = (stabilizer i n).comap e.hom := by
    rw [range_baseChangeHom, hrep.2]
    exact subgroupJetStabilizer_eval G n D a i hi h
  rw [show familyHom j a = (baseChange a.left).map j ≫ e.hom from rfl, range_comp_iso,
    he, ← comap_comp, e.inv_hom_id, comap_id]

end Langlands.GroupScheme.IdentityJet
