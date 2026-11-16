import Langlands.GroupScheme.Torus.WeylImageContainment
import Langlands.GroupScheme.Torus.WeylPointTransport
import Langlands.GroupScheme.Torus.GenericSelfCentralizing
import Langlands.GroupScheme.Torus.NormalizerComponents
import Langlands.GroupScheme.Reductive.SplitDataBaseChange
import Langlands.GroupScheme.Reductive.SmoothTargetGenericClosure

/-! # Closed fibres of a reductive open subgroup with the same generic fibre -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

namespace SplitOpenGenericIsomorphism

section Local

variable {R K : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    {M G : GroupScheme (Spec (CommRingCat.of R))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (hM : IsReductive M) (f : M ⟶ G) [Mono f.hom.hom.left]
    [hgeneric : IsIso ((baseChange (Spec.algebraMap R K)).map f)]
    (I : Type u) [Fintype I]
    (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ M)
    (hi : IsClosedSubgroup i)
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)

include hM hi hmax hgeneric

omit [IsLocalRing R] in
/-- Generic equality with the reductive source determines the entire torus
centralizer in the smooth ambient group over the original local domain. -/
theorem centralizer_eq_range :
    torusCentralizer (T := splitTorus.commGroupScheme _ I) (i ≫ f) =
      SubgroupFunctor.range (i ≫ f) := by
  let : Smooth M.X.hom := hM.smooth
  let : IsAffineHom M.X.hom := hM.isAffineHom
  let : IsClosedImmersion i.hom.hom.left := hi
  let : Mono f.hom.hom := Over.mono_of_mono_left _
  let : Mono i.hom.hom := Over.mono_of_mono_left _
  let : Mono (i ≫ f).hom.hom := by
    change Mono (i.hom.hom ≫ f.hom.hom)
    infer_instance
  have ht : IsClosedSubgroup (i ≫ f) :=
    (isSplitTorus_splitTorus I).isClosedSubgroup_of_mono (i ≫ f)
  let b := Spec.algebraMap R K
  let e := asIso ((baseChange b).map f)
  have hGK : IsConnectedReductive ((baseChange b).obj G) :=
    (hM.isConnectedReductive_algebraMap K).of_iso e.symm
  have hmaxK : IsMaximalTorus
      (T := (CommGroupScheme.baseChange b).obj (splitTorus.commGroupScheme _ I))
      ((baseChange b).map (i ≫ f)) := by
    rw [Functor.map_comp]
    exact (hmax.fieldPoint (T := splitTorus.commGroupScheme _ I) b).comp_iso e
  exact splitTorusCentralizer_eq_range_of_genericMaximal
    (K := K) (T := splitTorus.commGroupScheme _ I)
    (isSplitTorus_splitTorus I) (i ≫ f) ht hGK hmaxK

omit [IsDomain R] [IsFractionRing R K] in
/-- On a closed-fibre field, the ambient Weyl quotient has no larger order
than that of the reductive open source. -/
theorem closedField_weylOrder_le
    (k : Type u) [Field k] [Algebra R k]
    (hk : algebraBaseMap R k (IsLocalRing.closedPoint k) = IsLocalRing.closedPoint R) :
    Nat.card (relativeWeylGroup (T := splitTorus.commGroupScheme _ I)
      (splitTorus.baseChangeHom (K := k) G I (i ≫ f))) ≤
    Nat.card (relativeWeylGroup (T := splitTorus.commGroupScheme _ I)
      (splitTorus.baseChangeHom (K := k) M I i)) := by
  classical
  let : Smooth M.X.hom := hM.smooth
  let : IsAffineHom M.X.hom := hM.isAffineHom
  let : IsClosedImmersion i.hom.hom.left := hi
  let : Mono f.hom.hom := Over.mono_of_mono_left _
  let : Mono i.hom.hom := Over.mono_of_mono_left _
  let : Mono (i ≫ f).hom.hom := by
    change Mono (i.hom.hom ≫ f.hom.hom)
    infer_instance
  have ht : IsClosedSubgroup (i ≫ f) :=
    (isSplitTorus_splitTorus I).isClosedSubgroup_of_mono (i ≫ f)
  let : IsClosedImmersion (i ≫ f).hom.hom.left := ht
  let l := AlgebraicClosure K
  let : IsScalarTower R K l := inferInstance
  let b := algebraBaseMap R l
  have hfb : IsIso ((baseChange b).map f) := by
    dsimp [b]
    rw [← splitTorus.algebraBaseMap_scalarTower (R := R) (A := K) (B := l)]
    exact (TorusIsomorphismLocus.isIso_comp_baseChange_iff
      (algebraBaseMap R K) (algebraBaseMap K l) f).mpr inferInstance
  let := hfb
  let e := asIso ((baseChange b).map f)
  let il := splitTorus.baseChangeHom (K := l) M I i
  let jl := splitTorus.baseChangeHom (K := l) G I (i ≫ f)
  have hsquare : il ≫ e.hom =
      CommGroupScheme.groupHom (Iso.refl (splitTorus.commGroupScheme _ I)).hom ≫ jl := by
    change il ≫ e.hom = jl
    simp [il, jl, e, b, splitTorus.baseChangeHom, Functor.map_comp, Category.assoc]
  have horder : Nat.card (relativeWeylGroup (T := splitTorus.commGroupScheme _ I) il) =
      Nat.card (relativeWeylGroup (T := splitTorus.commGroupScheme _ I) jl) :=
    Nat.card_congr (relativeWeylTransportEquiv (Iso.refl _) e hsquare).toEquiv
  have hmono (L : Type u) [Field L] [Algebra R L] :
      Mono (splitTorus.baseChangeHom (K := L) G I (i ≫ f)).hom.hom.left := by
    dsimp [splitTorus.baseChangeHom]
    have : Mono (i ≫ f).hom.hom := Over.mono_of_mono_left _
    have : Mono ((baseChange (algebraBaseMap R L)).map (i ≫ f)).hom.hom :=
      inferInstanceAs (Mono ((Over.pullback (algebraBaseMap R L)).map (i ≫ f).hom.hom))
    infer_instance
  let := hmono k
  let := hmono l
  have hbound := LocalSplitCorootTransport.natCard_relativeWeylGroup_le_of_closedField
    I G (i ≫ f) inferInstance k hk l
    ((ht.baseChange b).iso_comp (splitTorus.baseChangeIso b I).symm)
  have hl := natCard_relativeWeylGroup_eq_localSplitWeylOrder I hM i hi hmax l
  have hkorder := natCard_relativeWeylGroup_eq_localSplitWeylOrder I hM i hi hmax k
  exact hbound.trans_eq (horder.symm.trans (hl.trans hkorder.symm))

/-- The full normalizer on a closed-field fibre lies in the reductive source. -/
theorem closedField_normalizerPoints_le_range
    (k : Type u) [Field k] [Algebra R k]
    (hk : algebraBaseMap R k (IsLocalRing.closedPoint k) = IsLocalRing.closedPoint R) :
    normalizerPoints (T := splitTorus.commGroupScheme _ I)
        (splitTorus.baseChangeHom (K := k) G I (i ≫ f)) ≤
      (SubgroupFunctor.range ((baseChange (algebraBaseMap R k)).map f)).carrier
        (Over.mk (𝟙 (Spec (CommRingCat.of k)))) := by
  let : Smooth M.X.hom := hM.smooth
  let : IsAffineHom M.X.hom := hM.isAffineHom
  let : IsClosedImmersion i.hom.hom.left := hi
  let : Mono f.hom.hom := Over.mono_of_mono_left _
  let : Mono i.hom.hom := Over.mono_of_mono_left _
  let : Mono (i ≫ f).hom.hom := by
    change Mono (i.hom.hom ≫ f.hom.hom)
    infer_instance
  have ht : IsClosedSubgroup (i ≫ f) :=
    (isSplitTorus_splitTorus I).isClosedSubgroup_of_mono (i ≫ f)
  let b := algebraBaseMap R k
  let ik := splitTorus.baseChangeHom (K := k) M I i
  let fk := (baseChange b).map f
  have hcomp : ik ≫ fk = splitTorus.baseChangeHom (K := k) G I (i ≫ f) := by
    simp only [ik, fk, b, splitTorus.baseChangeHom, Functor.map_comp, Category.assoc]
  have hik : IsClosedSubgroup ik :=
    (hi.baseChange b).iso_comp (splitTorus.baseChangeIso b I).symm
  have htk : IsClosedSubgroup (ik ≫ fk) := by
    rw [hcomp]
    exact (ht.baseChange b).iso_comp (splitTorus.baseChangeIso b I).symm
  let : IsClosedImmersion ik.hom.hom.left := hik
  let : IsClosedImmersion (ik ≫ fk).hom.hom.left := htk
  let : Mono ik.hom.hom.left :=
    SurjectiveOnStalks.mono_of_injective ik.hom.hom.left.isClosedEmbedding.injective
  let : Mono (ik ≫ fk).hom.hom.left :=
    SurjectiveOnStalks.mono_of_injective (ik ≫ fk).hom.hom.left.isClosedEmbedding.injective
  let : Smooth ((baseChange b).obj G).X.hom :=
    inferInstanceAs (Smooth (pullback.snd G.X.hom b))
  let : IsAffineHom ((baseChange b).obj G).X.hom :=
    inferInstanceAs (IsAffineHom (pullback.snd G.X.hom b))
  have hZeq : torusCentralizer (T := splitTorus.commGroupScheme _ I) (ik ≫ fk) =
      SubgroupFunctor.range (ik ≫ fk) := by
    rw [hcomp]
    change torusCentralizer (T := splitTorus.commGroupScheme _ I)
        ((splitTorus.baseChangeIso b I).inv ≫ (baseChange b).map (i ≫ f)) = _
    have hsource := torusCentralizer_iso_comp
        (T := (CommGroupScheme.baseChange b).obj (splitTorus.commGroupScheme _ I))
        (T' := splitTorus.commGroupScheme _ I) (splitTorus.baseChangeIso b I).symm
        ((baseChange b).map (i ≫ f))
    simp only [Iso.symm_hom] at hsource
    rw [hsource,
      torusCentralizer_baseChange (T := splitTorus.commGroupScheme _ I),
      centralizer_eq_range (K := K) hM f I i hi hmax,
      ← SubgroupFunctor.range_baseChangeHom]
    exact (SubgroupFunctor.range_iso_comp (splitTorus.baseChangeIso b I).symm
      ((baseChange b).map (i ≫ f))).symm
  have hZ : torusCentralizer (T := splitTorus.commGroupScheme _ I) (ik ≫ fk) ≤
      SubgroupFunctor.range fk := by
    rw [hZeq]
    intro U x hx
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    exact SubgroupFunctor.mem_range.mpr ⟨y ≫ ik.hom.hom, by
      simp only [Grp.comp_hom_hom, Category.assoc]⟩
  have hbound : Nat.card (relativeWeylGroup (T := splitTorus.commGroupScheme _ I)
      (ik ≫ fk)) ≤ Nat.card (relativeWeylGroup (T := splitTorus.commGroupScheme _ I) ik) := by
    rw [hcomp]
    exact closedField_weylOrder_le (K := K) hM f I i hi hmax k hk
  rw [← hcomp]
  exact normalizerPoints_le_range_of_natCard_le
    (T := splitTorus.commGroupScheme _ I) ik fk (isSplitTorus_splitTorus I)
    htk hbound hZ

/-- The actual isomorphism on an algebraically closed closed-field fibre
of a generically equal reductive open subgroup. -/
def closedFieldIso [IsOpenImmersion f.hom.hom.left]
    (k : Type u) [Field k] [IsAlgClosed k] [Algebra R k]
    (hk : algebraBaseMap R k (IsLocalRing.closedPoint k) = IsLocalRing.closedPoint R) :
    (baseChange (algebraBaseMap R k)).obj M ≅ (baseChange (algebraBaseMap R k)).obj G := by
  let b := algebraBaseMap R k
  let Mk := (baseChange b).obj M
  let Gk := (baseChange b).obj G
  let fk : Mk ⟶ Gk := (baseChange b).map f
  let ik := splitTorus.baseChangeHom (K := k) M I i
  let : Smooth Gk.X.hom := inferInstanceAs (Smooth (pullback.snd G.X.hom b))
  let : IsAffineHom Gk.X.hom := inferInstanceAs (IsAffineHom (pullback.snd G.X.hom b))
  let : Smooth M.X.hom := hM.smooth
  let : IsAffineHom M.X.hom := hM.isAffineHom
  let : Smooth Mk.X.hom := inferInstanceAs (Smooth (pullback.snd M.X.hom b))
  let : IsAffineHom Mk.X.hom := inferInstanceAs (IsAffineHom (pullback.snd M.X.hom b))
  let : ConnectedSpace Mk.X.left := (hM.isConnectedReductive_baseChange b).connectedSpace
  let : Mono f.hom.hom := Over.mono_of_mono_left _
  let : Mono fk.hom.hom :=
    inferInstanceAs (Mono ((Over.pullback b).map f.hom.hom))
  let : IsOpenImmersion fk.hom.hom.left :=
    MorphismProperty.overPullbackMap (P := @IsOpenImmersion) b f.hom.hom inferInstance
  let : IsClosedImmersion fk.hom.hom.left := HomImage.isClosedSubgroup_of_mono fk
  let e : Mk ≅ identityComponent Gk := IdentityComponent.isoOfIsOpenImmersion Gk fk
  have he : e.hom ≫ identityComponentι Gk = fk :=
    IdentityComponent.isoOfIsOpenImmersion_hom_identityComponentι Gk fk
  let t := ik ≫ e.hom
  have ht : IsMaximalTorus (T := splitTorus.commGroupScheme _ I) t :=
    (splitTorus.isMaximalTorus_baseChangeHom_of_fibrewise I M i hmax k).comp_iso e
  have hN : normalizerPoints (T := splitTorus.commGroupScheme _ I)
      (t ≫ identityComponentι Gk) ≤
      (SubgroupFunctor.range (identityComponentι Gk)).carrier
        (Over.mk (𝟙 (Spec (CommRingCat.of k)))) := by
    have hcomp : t ≫ identityComponentι Gk =
        splitTorus.baseChangeHom (K := k) G I (i ≫ f) := by
      simp only [t, Category.assoc, he, ik, fk, splitTorus.baseChangeHom,
        Functor.map_comp, Category.assoc, b]
    rw [hcomp]
    have hRange : SubgroupFunctor.range fk = SubgroupFunctor.range (identityComponentι Gk) := by
      rw [← he, SubgroupFunctor.range_iso_comp e]
    rw [← hRange]
    exact closedField_normalizerPoints_le_range (K := K) hM f I i hi hmax k hk
  exact e ≪≫ identityComponentIsoOfNormalizerPoints
    (T := splitTorus.commGroupScheme _ I) t ht hN

@[simp]
theorem closedFieldIso_hom [IsOpenImmersion f.hom.hom.left]
    (k : Type u) [Field k] [IsAlgClosed k] [Algebra R k]
    (hk : algebraBaseMap R k (IsLocalRing.closedPoint k) = IsLocalRing.closedPoint R) :
    (closedFieldIso (K := K) hM f I i hi hmax k hk).hom =
      (baseChange (algebraBaseMap R k)).map f := by
  simp only [closedFieldIso, Iso.trans_hom, identityComponentIsoOfNormalizerPoints_hom,
    IdentityComponent.isoOfIsOpenImmersion_hom_identityComponentι]

end Local

end SplitOpenGenericIsomorphism

end Langlands.GroupScheme
