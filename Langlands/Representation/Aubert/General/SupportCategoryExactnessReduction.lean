import Langlands.Representation.Aubert.General.SupportCategoryStatements

/-! # Exactness detection on support categories from zero detection -/

noncomputable section

open CategoryTheory

namespace Langlands.Aubert.General.ExactnessDetection

open SmoothRep

universe uI uG uH uV

section Smooth

variable {G : Type uG} [Group G] [TopologicalSpace G]
  {H : Type uH} [Group H] [TopologicalSpace H]

/-- The actual surjection onto the invariant image. -/
def imageProjection {A B : SmoothRep.{0, uG, uV} ℂ G} (f : A ⟶ B) : A ⟶ image f :=
  ofHom {
    toLinearMap := (hom f).toLinearMap.rangeRestrict
    isIntertwining' := fun g => by
      ext v
      exact Subtype.ext (Representation.IntertwiningMap.isIntertwining _ _ (hom f) g v) }

theorem imageProjection_surjective {A B : SmoothRep.{0, uG, uV} ℂ G} (f : A ⟶ B) :
    Function.Surjective (hom (imageProjection f)) := by
  rintro ⟨_, v, hv⟩
  exact ⟨v, Subtype.ext hv⟩

theorem imageProjection_imageι {A B : SmoothRep.{0, uG, uV} ℂ G} (f : A ⟶ B) :
    imageProjection f ≫ imageι f = f := rfl

/-- Full preservation of actual short exact sequences, with no length premise. -/
def MapsShortExact (F : SmoothRep.{0, uG, uV} ℂ G ⥤ SmoothRep.{0, uH, uV} ℂ H) : Prop :=
  ∀ {A B C} (f : A ⟶ B) (g : B ⟶ C), IsShortExact (hom f) (hom g) →
    IsShortExact (hom (F.map f)) (hom (F.map g))

variable (F : SmoothRep.{0, uG, uV} ℂ G ⥤ SmoothRep.{0, uH, uV} ℂ H)
  (hF : MapsShortExact F)

include hF in
theorem map_injective {A B : SmoothRep.{0, uG, uV} ℂ G} (f : A ⟶ B)
    (hf : Function.Injective (hom f)) : Function.Injective (hom (F.map f)) := by
  exact (hF f (cokernelπ f) ⟨hf, mkQ_surjective _ _, (Submodule.ker_mkQ _).symm⟩).1

include hF in
theorem map_surjective {A B : SmoothRep.{0, uG, uV} ℂ G} (f : A ⟶ B)
    (hf : Function.Surjective (hom f)) : Function.Surjective (hom (F.map f)) := by
  exact (hF (kernelι f) f ⟨subtype_injective _ _, hf, Submodule.range_subtype _⟩).2.1

theorem map_comp_apply {A B C : SmoothRep.{0, uG, uV} ℂ G}
    (f : A ⟶ B) (g : B ⟶ C) (x : F.obj A) :
    hom (F.map (f ≫ g)) x = hom (F.map g) (hom (F.map f) x) := by
  rw [F.map_comp]
  rfl

include hF in
/-- Short exactness suffices for preservation of arbitrary range-kernel exactness. -/
theorem map_exact {A B C : SmoothRep.{0, uG, uV} ℂ G}
    (f : A ⟶ B) (g : B ⟶ C) (hex : Function.Exact (hom f) (hom g)) :
    Function.Exact (hom (F.map f)) (hom (F.map g)) := by
  have hmid : IsShortExact (hom (imageι f)) (hom (imageProjection g)) := by
    refine ⟨subtype_injective _ _, imageProjection_surjective g, ?_⟩
    ext x
    change (∃ v : (hom f).range.toSubmodule, v.val = x) ↔
      (hom (imageProjection g)) x = 0
    constructor
    · rintro ⟨⟨_, a, rfl⟩, rfl⟩
      apply Subtype.ext
      exact hex.apply_apply_eq_zero a
    · intro hx
      have hg : hom g x = 0 := congrArg Subtype.val hx
      obtain ⟨a, ha⟩ := (hex x).mp hg
      exact ⟨⟨x, ⟨a, ha⟩⟩, rfl⟩
  have hm := hF (imageι f) (imageProjection g) hmid
  have he : Function.Exact (hom (F.map (imageι f)))
      (hom (F.map (imageProjection g))) :=
    (LinearMap.exact_iff (f := (hom (F.map (imageι f))).toLinearMap)
      (g := (hom (F.map (imageProjection g))).toLinearMap)).mpr hm.2.2.symm
  have hp := map_surjective F hF (imageProjection f) (imageProjection_surjective f)
  have hi := map_injective F hF (imageι g) (subtype_injective _ _)
  have hf (x : F.obj A) :
      hom (F.map (imageι f)) (hom (F.map (imageProjection f)) x) = hom (F.map f) x :=
    (map_comp_apply F (imageProjection f) (imageι f) x).symm
  have hg (x : F.obj B) :
      hom (F.map (imageι g)) (hom (F.map (imageProjection g)) x) = hom (F.map g) x :=
    (map_comp_apply F (imageProjection g) (imageι g) x).symm
  intro x
  constructor
  · intro hx
    have hx' : hom (F.map (imageProjection g)) x = 0 := hi (by rw [hg, map_zero, hx])
    obtain ⟨y, hy⟩ := (he x).mp hx'
    obtain ⟨a, rfl⟩ := hp y
    exact ⟨a, (hf a).symm.trans hy⟩
  · rintro ⟨a, rfl⟩
    rw [← hf a, ← hg]
    rw [he.apply_apply_eq_zero, map_zero]

/-- The actual outgoing map descended through the quotient by the preceding range. -/
def cokernelDesc {A B C : SmoothRep.{0, uG, uV} ℂ G}
    (f : A ⟶ B) (g : B ⟶ C) (hfg : f ≫ g = 0) : cokernel f ⟶ C :=
  ofHom {
    toLinearMap := (hom f).range.toSubmodule.liftQ (hom g).toLinearMap (by
      rintro _ ⟨v, rfl⟩
      exact congrArg (fun h => hom h v) hfg)
    isIntertwining' := fun a => by
      apply Submodule.linearMap_qext
      ext v
      exact Representation.IntertwiningMap.isIntertwining _ _ (hom g) a v }

theorem cokernelπ_cokernelDesc {A B C : SmoothRep.{0, uG, uV} ℂ G}
    (f : A ⟶ B) (g : B ⟶ C) (hfg : f ≫ g = 0) :
    cokernelπ f ≫ cokernelDesc f g hfg = g := rfl

end Smooth

section Jacquet

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G] {P M U : Subgroup G}

/-- On coinvariant representatives the normalized Jacquet functor maps zero to zero. -/
theorem jacquet_map_zero (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
    (A B : SmoothRep.{0, uG, uV} ℂ G) :
    (jacquetFunctor.{uG, uV} h hU).map (0 : A ⟶ B) = 0 := by
  apply ObjectProperty.hom_ext
  ext x
  obtain ⟨v, rfl⟩ := Jacquet.Localization.mk_surjective A.representation U 1 x
  change Jacquet.Localization.mk B.representation U 1 (0 : B) = 0
  exact map_zero _

end Jacquet

section Reduction

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G]
variable {ι : Type uI}
variable {P M U : Finset ι → Subgroup G}
  {h : ∀ I, IsSemidirectDecomposition (P I) (M I) (U I)}
  {hU : ∀ I, IsClosed (U I : Set G)}
  {hM : ∀ I, IsClosed (M I : Set G)}
  {hL : ∀ (I : Finset ι) (K : Finset I),
    IsSemidirectDecomposition ((P (leviIndex I K)).subgroupOf (M I))
      ((M (leviIndex I K)).subgroupOf (M I)) ((U (leviIndex I K)).subgroupOf (M I))}
  {IsAssociate : Finset ι → Finset ι → G → Prop}
  (hUc : ∀ J, Jacquet.Localization.IsLimitOfCompactSubgroups (U J))
  (hdet : SupportCategoryZeroDetectionTarget.{uI, uG, uV}
    P M U h hU hM hL IsAssociate)

include hUc hdet

/-- Zero detection reflects injectivity for a source in the support category. -/
theorem injective_of_jacquet {I : Finset ι}
    {A B : SmoothRep.{0, uG, max uG uV} ℂ G} (f : A ⟶ B)
    (hA : IsInSupportCategory P M U h hU IsAssociate I (hM I) (hL I) A)
    (hf : ∀ J n, IsAssociate I J n →
      (∀ x : G, x ∈ M J ↔ n⁻¹ * x * n ∈ M I) →
      Function.Injective (hom ((jacquetFunctor (h J) (hU J)).map f))) :
    Function.Injective (hom f) := by
  have hK := hA.of_isSubquotient
    (subrepresentation_isSubrepresentation (hom f).ker).isSubquotient
  have hcomp : kernelι f ≫ f = 0 := by
    apply ObjectProperty.hom_ext
    ext v
    exact v.2
  have hzero : ∀ J n, IsAssociate I J n →
      (∀ x : G, x ∈ M J ↔ n⁻¹ * x * n ∈ M I) →
      Subsingleton ((jacquetFunctor (h J) (hU J)).obj (kernel f)) := by
    intro J n hJ hn
    let r := jacquetFunctor.{uG, max uG uV} (h J) (hU J)
    have hi := map_injective r
      (jacquetFunctor_map_isShortExact (h J) (hU J) (hUc J))
      (kernelι f) (subtype_injective _ _)
    have hz (x : r.obj (kernel f)) : x = 0 := by
      apply hi
      apply hf J n hJ hn
      rw [map_zero, map_zero]
      rw [← map_comp_apply, hcomp, jacquet_map_zero]
      rfl
    exact ⟨fun x y => (hz x).trans (hz y).symm⟩
  have hsub : Subsingleton (kernel f) := hdet I (kernel f) hK hzero
  let : Subsingleton (hom f).ker.toSubmodule := hsub
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro v hv
  exact congrArg Subtype.val (Subsingleton.elim (⟨v, hv⟩ : (hom f).ker.toSubmodule) 0)

/-- A map from a support object vanishes if all detecting Jacquet maps vanish. -/
theorem eq_zero_of_jacquet {I : Finset ι}
    {A B : SmoothRep.{0, uG, max uG uV} ℂ G} (f : A ⟶ B)
    (hA : IsInSupportCategory P M U h hU IsAssociate I (hM I) (hL I) A)
    (hf : ∀ J n, IsAssociate I J n →
      (∀ x : G, x ∈ M J ↔ n⁻¹ * x * n ∈ M I) →
      ∀ x, hom ((jacquetFunctor (h J) (hU J)).map f) x = 0) :
    f = 0 := by
  have hIm := hA.of_isSubquotient
    (IsQuotient.isSubquotient ⟨imageProjection f, imageProjection_surjective f⟩)
  have hzero : ∀ J n, IsAssociate I J n →
      (∀ x : G, x ∈ M J ↔ n⁻¹ * x * n ∈ M I) →
      Subsingleton ((jacquetFunctor (h J) (hU J)).obj (image f)) := by
    intro J n hJ hn
    let r := jacquetFunctor.{uG, max uG uV} (h J) (hU J)
    have hi := map_injective r
      (jacquetFunctor_map_isShortExact (h J) (hU J) (hUc J))
      (imageι f) (subtype_injective _ _)
    have hp := map_surjective r
      (jacquetFunctor_map_isShortExact (h J) (hU J) (hUc J))
      (imageProjection f) (imageProjection_surjective f)
    have hz (x : r.obj (image f)) : x = 0 := by
      apply hi
      rw [map_zero]
      obtain ⟨a, rfl⟩ := hp x
      rw [← map_comp_apply, imageProjection_imageι]
      exact hf J n hJ hn a
    exact ⟨fun x y => (hz x).trans (hz y).symm⟩
  have hsub : Subsingleton (image f) := hdet I (image f) hIm hzero
  apply ObjectProperty.hom_ext
  ext v
  exact congrArg Subtype.val (@Subsingleton.elim _ hsub (hom (imageProjection f) v) 0)

/-- Full Jacquet exactness and zero detection imply exactness detection, including
the complex condition, for arbitrary endpoint objects. -/
theorem supportCategoryExactnessDetection_of_zeroDetection :
    SupportCategoryExactnessDetectionTarget.{uI, uG, uV}
      P M U h hU hM hL IsAssociate := by
  intro I A B C f g hB
  constructor
  · intro hex J n _ _
    exact map_exact _ (jacquetFunctor_map_isShortExact (h J) (hU J) (hUc J)) f g hex
  · intro hex
    have hIm := hB.of_isSubquotient
      (subrepresentation_isSubrepresentation (hom f).range).isSubquotient
    have hrest : imageι f ≫ g = 0 := by
      apply eq_zero_of_jacquet hUc hdet _ hIm
      intro J n hJ hn x
      let r := jacquetFunctor.{uG, max uG uV} (h J) (hU J)
      have hp := map_surjective r
        (jacquetFunctor_map_isShortExact (h J) (hU J) (hUc J))
        (imageProjection f) (imageProjection_surjective f)
      obtain ⟨a, rfl⟩ := hp x
      change hom (r.map (imageι f ≫ g)) (hom (r.map (imageProjection f)) a) = 0
      rw [map_comp_apply r, ← map_comp_apply r (imageProjection f) (imageι f),
        imageProjection_imageι]
      exact (hex J n hJ hn).apply_apply_eq_zero a
    have hfg : f ≫ g = 0 := by
      rw [← imageProjection_imageι f, Category.assoc, hrest]
      apply ObjectProperty.hom_ext
      ext
      rfl
    let q := cokernelπ f
    let t := cokernelDesc f g hfg
    have hQ := hB.of_isSubquotient
      (quotient_isQuotient (hom f).range).isSubquotient
    have ht : Function.Injective (hom t) := by
      apply injective_of_jacquet hUc hdet t hQ
      intro J n hJ hn
      let r := jacquetFunctor.{uG, max uG uV} (h J) (hU J)
      have hq := map_surjective r
        (jacquetFunctor_map_isShortExact (h J) (hU J) (hUc J))
        q (mkQ_surjective _ _)
      have he : Function.Exact (hom (r.map f)) (hom (r.map q)) :=
        map_exact r (jacquetFunctor_map_isShortExact (h J) (hU J) (hUc J))
          f q (LinearMap.exact_iff.mpr (Submodule.ker_mkQ _))
      apply LinearMap.ker_eq_bot.mp
      apply LinearMap.ker_eq_bot'.mpr
      intro x hx
      obtain ⟨y, rfl⟩ := hq x
      have hcomm (y : r.obj B) :
          hom (r.map t) (hom (r.map q) y) = hom (r.map g) y :=
        (map_comp_apply r q t y).symm
      change hom (r.map t) (hom (r.map q) y) = 0 at hx
      rw [hcomm] at hx
      obtain ⟨a, ha⟩ := (hex J n hJ hn y).mp hx
      rw [← ha]
      exact he.apply_apply_eq_zero a
    intro v
    constructor
    · intro hv
      have hqv : hom q v = 0 := ht (by
        change hom g v = hom t 0
        rw [map_zero, hv])
      exact (Submodule.Quotient.mk_eq_zero (hom f).range.toSubmodule).mp hqv
    · rintro ⟨a, rfl⟩
      exact congrArg (fun z => hom z a) hfg

end Reduction

end Langlands.Aubert.General.ExactnessDetection
