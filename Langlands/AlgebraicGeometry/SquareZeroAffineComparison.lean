import Langlands.AlgebraicGeometry.SquareZeroAffinePairs

/-! # Comparing lifts with split infinitesimal points -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.SquareZeroAffinePairs

open scoped SquareZeroAffinePairs

section Compare

variable {C : Type u} [CommRing C] (J : Ideal C) (hJ : J ^ 2 = ⊥)
  {X : Scheme.{u}}

local notation "π₀" => specMap (projection (C := C) (M := J))
local notation "π₁" => specMap (evaluation J hJ)
local notation "ι" => specMap (Ideal.Quotient.mk J)

/-- The map on the pair test determined by two lifts with the same reduction. -/
def pairMap (g h : Spec (CommRingCat.of C) ⟶ X) (he : ι ≫ g = ι ≫ h) :
    Spec (CommRingCat.of (TrivSqZeroExt C J)) ⟶ X := (pushout_pairs J hJ).desc g h he

@[reassoc (attr := simp)] theorem projection_pairMap
    (g h : Spec (CommRingCat.of C) ⟶ X) (he : ι ≫ g = ι ≫ h) :
    π₀ ≫ pairMap J hJ g h he = g := (pushout_pairs J hJ).inl_desc _ _ _

@[reassoc (attr := simp)] theorem evaluation_pairMap
    (g h : Spec (CommRingCat.of C) ⟶ X) (he : ι ≫ g = ι ≫ h) :
    π₁ ≫ pairMap J hJ g h he = h := (pushout_pairs J hJ).inr_desc _ _ _

@[reassoc] theorem pairMap_comp {Y : Scheme.{u}} (g h : Spec (CommRingCat.of C) ⟶ X)
    (he : ι ≫ g = ι ≫ h) (a : X ⟶ Y) :
    pairMap J hJ g h he ≫ a = pairMap J hJ (g ≫ a) (h ≫ a) (by
      simpa only [Category.assoc] using congrArg (· ≫ a) he) := by
  apply (pushout_pairs J hJ).hom_ext
  · rw [projection_pairMap_assoc, projection_pairMap]
  · rw [evaluation_pairMap_assoc, evaluation_pairMap]

private theorem evaluation_comp_inclusion :
    (evaluation J hJ).comp (inclusion (C := C) (M := J)) = RingHom.id C := by
  ext c
  change c + (0 : C) = c
  simp

@[reassoc] theorem pairMap_same (g : Spec (CommRingCat.of C) ⟶ X) :
    pairMap J hJ g g rfl = specMap (inclusion (C := C) (M := J)) ≫ g := by
  apply (pushout_pairs J hJ).hom_ext
  · rw [projection_pairMap, ← specMap_comp_assoc]
    exact (Category.id_comp g).symm.trans (congrArg (· ≫ g) (Spec.map_id _).symm)
  · rw [evaluation_pairMap, ← specMap_comp_assoc, evaluation_comp_inclusion]
    exact (Category.id_comp g).symm.trans (congrArg (· ≫ g) (Spec.map_id _).symm)

variable {D : Type u} [CommRing D] [Module D J] (r : C →+* D)
  (hr : Function.Surjective r) (hsmul : ∀ (c : C) (x : J), r c • x = c • x)

local notation "σ" => specMap (splitReduction J r hsmul)
local notation "πD" => specMap (projection (C := D) (M := J))

/-- The difference as a split point with the restriction of the first lift to `Spec D`
as its constant term. -/
def splitPoint (g h : Spec (CommRingCat.of C) ⟶ X) (he : ι ≫ g = ι ≫ h) :
    Spec (CommRingCat.of (TrivSqZeroExt D J)) ⟶ X := σ ≫ pairMap J hJ g h he

@[reassoc (attr := simp)] theorem projection_splitPoint
    (g h : Spec (CommRingCat.of C) ⟶ X) (he : ι ≫ g = ι ≫ h) :
    πD ≫ splitPoint J hJ r hsmul g h he = specMap r ≫ g := by
  rw [splitPoint, ← Category.assoc, ← specMap_comp, show
    (projection (C := D) (M := J)).comp (splitReduction J r hsmul) =
        r.comp (projection (C := C) (M := J)) from rfl, specMap_comp, Category.assoc,
    projection_pairMap]

@[reassoc] theorem splitPoint_same (g : Spec (CommRingCat.of C) ⟶ X) :
    splitPoint J hJ r hsmul g g rfl = specMap (inclusion (C := D) (M := J)) ≫ specMap r ≫ g := by
  rw [splitPoint, pairMap_same, ← Category.assoc, ← specMap_comp, ← specMap_comp_assoc]
  rfl

private def glue (g : Spec (CommRingCat.of C) ⟶ X)
    (v : Spec (CommRingCat.of (TrivSqZeroExt D J)) ⟶ X)
    (hv : specMap r ≫ g = πD ≫ v) : Spec (CommRingCat.of (TrivSqZeroExt C J)) ⟶ X :=
  (pushout_splitReduction J r hsmul hr).desc g v hv

/-- Change a lift by the derivation encoded by a split infinitesimal point. -/
def update (g : Spec (CommRingCat.of C) ⟶ X)
    (v : Spec (CommRingCat.of (TrivSqZeroExt D J)) ⟶ X)
    (hv : specMap r ≫ g = πD ≫ v) : Spec (CommRingCat.of C) ⟶ X :=
  π₁ ≫ glue J r hr hsmul g v hv

@[reassoc] theorem reduction_update (g : Spec (CommRingCat.of C) ⟶ X)
    (v : Spec (CommRingCat.of (TrivSqZeroExt D J)) ⟶ X)
    (hv : specMap r ≫ g = πD ≫ v) :
    ι ≫ update J hJ r hr hsmul g v hv = ι ≫ g := by
  rw [update, ← Category.assoc, ← (pushout_pairs J hJ).w, Category.assoc]
  rw [glue, (pushout_splitReduction J r hsmul hr).inl_desc]

@[simp] theorem update_splitPoint (g h : Spec (CommRingCat.of C) ⟶ X)
    (he : ι ≫ g = ι ≫ h) :
    update J hJ r hr hsmul g (splitPoint J hJ r hsmul g h he)
      (projection_splitPoint J hJ r hsmul g h he).symm = h := by
  have hg : glue J r hr hsmul g (splitPoint J hJ r hsmul g h he)
      (projection_splitPoint J hJ r hsmul g h he).symm = pairMap J hJ g h he := by
    apply (pushout_splitReduction J r hsmul hr).hom_ext
    · rw [glue, (pushout_splitReduction J r hsmul hr).inl_desc, projection_pairMap]
    · rw [glue, (pushout_splitReduction J r hsmul hr).inr_desc, splitPoint]
  rw [update, hg, evaluation_pairMap]

@[simp] theorem splitPoint_update (g : Spec (CommRingCat.of C) ⟶ X)
    (v : Spec (CommRingCat.of (TrivSqZeroExt D J)) ⟶ X)
    (hv : specMap r ≫ g = πD ≫ v) :
    splitPoint J hJ r hsmul g (update J hJ r hr hsmul g v hv)
      (reduction_update J hJ r hr hsmul g v hv).symm = v := by
  have hg : pairMap J hJ g (update J hJ r hr hsmul g v hv)
      (reduction_update J hJ r hr hsmul g v hv).symm =
      glue J r hr hsmul g v hv := by
    apply (pushout_pairs J hJ).hom_ext
    · rw [projection_pairMap, glue, (pushout_splitReduction J r hsmul hr).inl_desc]
    · rw [evaluation_pairMap, update]
  rw [splitPoint, hg, glue, (pushout_splitReduction J r hsmul hr).inr_desc]

theorem update_comp {Y : Scheme.{u}} (g : Spec (CommRingCat.of C) ⟶ X)
    (v : Spec (CommRingCat.of (TrivSqZeroExt D J)) ⟶ X)
    (hv : specMap r ≫ g = πD ≫ v) (a : X ⟶ Y) :
    update J hJ r hr hsmul g v hv ≫ a = update J hJ r hr hsmul (g ≫ a) (v ≫ a) (by
      simpa only [Category.assoc] using congrArg (· ≫ a) hv) := by
  rw [update, update, Category.assoc]
  congr 1
  apply (pushout_splitReduction J r hsmul hr).hom_ext
  · simp only [glue, IsPushout.inl_desc_assoc, IsPushout.inl_desc]
  · simp only [glue, IsPushout.inr_desc_assoc, IsPushout.inr_desc]

/-- Three lifts yield a split test encoding the two successive derivations and their sum. -/
theorem exists_splitTriple (hkill : ∀ x : J, r x = 0)
    (g h l : Spec (CommRingCat.of C) ⟶ X) (egh : ι ≫ g = ι ≫ h) (ehl : ι ≫ h = ι ≫ l) :
    ∃ v : Spec (CommRingCat.of (TrivSqZeroExt D (J × J))) ⟶ X,
      specMap (first D J) ≫ v = splitPoint J hJ r hsmul g h egh ∧
      specMap (second D J) ≫ v = splitPoint J hJ r hsmul h l ehl ∧
      specMap (total D J) ≫ v = splitPoint J hJ r hsmul g l (egh.trans ehl) := by
  let w := (pushout_triple J hJ).desc (pairMap J hJ g h egh) (pairMap J hJ h l ehl)
    (by rw [evaluation_pairMap, projection_pairMap])
  have w₁ : specMap (first C J) ≫ w = pairMap J hJ g h egh :=
    (pushout_triple J hJ).inl_desc _ _ _
  have w₂ : specMap (shiftedSecond J hJ) ≫ w = pairMap J hJ h l ehl :=
    (pushout_triple J hJ).inr_desc _ _ _
  have w₃ : specMap (total C J) ≫ w = pairMap J hJ g l (egh.trans ehl) := by
    apply (pushout_pairs J hJ).hom_ext
    · rw [projection_pairMap, ← specMap_comp_assoc, projection_comp_total, specMap_comp_assoc,
        w₁, projection_pairMap]
    · rw [evaluation_pairMap, ← specMap_comp_assoc, evaluation_comp_total, specMap_comp_assoc,
        w₂, evaluation_pairMap]
  refine ⟨specMap (splitReductionTriple J r hsmul) ≫ w, ?_, ?_, ?_⟩
  · rw [← specMap_comp_assoc, ← splitReduction_comp_first, specMap_comp_assoc, w₁, splitPoint]
  · rw [← specMap_comp_assoc, ← splitReduction_comp_shiftedSecond _ _ _ hJ hkill,
      specMap_comp_assoc, w₂, splitPoint]
  · rw [← specMap_comp_assoc, ← splitReduction_comp_total, specMap_comp_assoc, w₃, splitPoint]

@[reassoc] theorem splitPoint_comp {Y : Scheme.{u}} (g h : Spec (CommRingCat.of C) ⟶ X)
    (he : ι ≫ g = ι ≫ h) (a : X ⟶ Y) :
    splitPoint J hJ r hsmul g h he ≫ a =
      splitPoint J hJ r hsmul (g ≫ a) (h ≫ a) (by
        simpa only [Category.assoc] using congrArg (· ≫ a) he) := by
  simp only [splitPoint, Category.assoc, pairMap_comp]

section Naturality

variable {C' D' : Type u} [CommRing C'] [CommRing D']
  (J' : Ideal C') (hJ' : J' ^ 2 = ⊥) [Module D' J'] (r' : C' →+* D')
  (hsmul' : ∀ (c : C') (x : J'), r' c • x = c • x)
  (a : C →+* C') (ha : J.map a ≤ J')
  (b : D →+* D') (hb : r'.comp a = b.comp r)

/-- The coefficient map induced by a ring map carrying the source ideal into the target ideal. -/
def mapIdeal : J →ₛₗ[a] J' where
  toFun x := ⟨a x, ha (Ideal.mem_map_of_mem a x.property)⟩
  map_add' x y := Subtype.ext (map_add a (x : C) (y : C))
  map_smul' c x := Subtype.ext (map_mul a c (x : C))

/-- The coefficient map is also semilinear over the reduced base. -/
def mapReducedIdeal : J →ₛₗ[b] J' where
  toFun := mapIdeal J J' a ha
  map_add' := map_add (mapIdeal J J' a ha)
  map_smul' d x := by
    obtain ⟨c, rfl⟩ := hr d
    have h : r' (a c) = b (r c) := RingHom.congr_fun hb c
    rw [← h, hsmul, hsmul', map_smulₛₗ]

private theorem reduction_map_w :
    (Ideal.Quotient.mk J').comp a = (Ideal.quotientMap J' a
      (fun _ hx ↦ ha (Ideal.mem_map_of_mem a hx))).comp (Ideal.Quotient.mk J) := rfl

include ha in
theorem map_reduced_agree (g h : Spec (CommRingCat.of C) ⟶ X) (he : ι ≫ g = ι ≫ h) :
    specMap (Ideal.Quotient.mk J') ≫ specMap a ≫ g =
      specMap (Ideal.Quotient.mk J') ≫ specMap a ≫ h := by
  rw [← specMap_comp_assoc, ← specMap_comp_assoc, reduction_map_w J J' a ha,
    specMap_comp_assoc, specMap_comp_assoc, he]

theorem pairMap_natural (g h : Spec (CommRingCat.of C) ⟶ X) (he : ι ≫ g = ι ≫ h) :
    specMap (splitMap a (mapIdeal J J' a ha)) ≫ pairMap J hJ g h he =
      pairMap J' hJ' (specMap a ≫ g) (specMap a ≫ h) (map_reduced_agree J J' a ha g h he) := by
  apply (pushout_pairs J' hJ').hom_ext
  · rw [projection_pairMap, ← specMap_comp_assoc, show
        (projection (C := C') (M := J')).comp (splitMap a (mapIdeal J J' a ha)) =
          a.comp (projection (C := C) (M := J)) from rfl, specMap_comp_assoc, projection_pairMap]
  · rw [evaluation_pairMap, ← specMap_comp_assoc, show
        (evaluation J' hJ').comp (splitMap a (mapIdeal J J' a ha)) =
          a.comp (evaluation J hJ) from RingHom.ext (fun z ↦ (map_add a z.fst z.snd.val).symm),
        specMap_comp_assoc, evaluation_pairMap]

theorem splitPoint_natural (g h : Spec (CommRingCat.of C) ⟶ X) (he : ι ≫ g = ι ≫ h) :
    specMap (splitMap b (mapReducedIdeal J r hr hsmul J' r' hsmul' a ha b hb)) ≫
        splitPoint J hJ r hsmul g h he =
      splitPoint J' hJ' r' hsmul' (specMap a ≫ g) (specMap a ≫ h)
        (map_reduced_agree J J' a ha g h he) := by
  have hw : (splitMap b (mapReducedIdeal J r hr hsmul J' r' hsmul' a ha b hb)).comp
      (splitReduction J r hsmul) = (splitReduction J' r' hsmul').comp
        (splitMap a (mapIdeal J J' a ha)) := by
    ext z
    · exact (RingHom.congr_fun hb z.fst).symm
    · rfl
  rw [splitPoint, splitPoint, ← specMap_comp_assoc, hw, specMap_comp_assoc,
    pairMap_natural]

end Naturality

end Compare

end Langlands.AlgebraicGeometry.SquareZeroAffinePairs
