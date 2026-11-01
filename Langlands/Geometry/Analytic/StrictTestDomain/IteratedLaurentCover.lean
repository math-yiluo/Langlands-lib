import Langlands.Geometry.Analytic.StrictTestDomain.BinaryLaurentCover
import Langlands.Geometry.Analytic.StrictTestDomain.RationalRelativeComparison

/-! # Finite iterated unit-radius Laurent covers -/

noncomputable section

universe u

namespace Langlands.Analytic.StrictTestDomain.RationalData

open CategoryTheory

variable {K : Type u} [NormedField K] [IsUltrametricDist K]
  {P Q : PresentedStrictAffinoidAlgebra K} {m : ℕ}

/-- `false` selects the upper inequality, and `true` selects the lower one. -/
def laurentChoice (g : P) (b : Bool) : RationalData K P :=
  if b then laurentLower g else laurentUpper g

@[simp]
theorem laurentChoice_false (g : P) : laurentChoice g false = laurentUpper g := rfl

@[simp]
theorem laurentChoice_true (g : P) : laurentChoice g true = laurentLower g := rfl

@[simp]
theorem mem_locus_laurentChoice (g : P) (b : Bool) (x : BanachSpectrum P) :
    x ∈ (laurentChoice g b).locus ↔ if b then 1 ≤ x g else x g ≤ 1 := by
  cases b <;> simp

@[simp]
theorem pullback_laurentChoice (g : P) (b : Bool) (φ : BoundedAlgHom K P Q) :
    (laurentChoice g b).pullback φ = laurentChoice (φ g) b := by
  cases b <;> simp

variable [CompleteSpace K]

/-- The chosen leaf of a finite Laurent cover is an actual rational datum.
The empty tuple gives `whole`, and no empty locus is removed. -/
def iteratedLaurent : {m : ℕ} → (Fin m → P) → (Fin m → Bool) → RationalData K P
  | 0, _, _ => whole K P
  | m + 1, g, ε =>
      (laurentChoice (g 0) (ε 0)).inter
        (iteratedLaurent (fun i : Fin m => g i.succ) (fun i => ε i.succ))

@[simp]
theorem iteratedLaurent_zero (g : Fin 0 → P) (ε : Fin 0 → Bool) :
    iteratedLaurent g ε = whole K P := rfl

theorem iteratedLaurent_succ (g : Fin (m + 1) → P) (ε : Fin (m + 1) → Bool) :
    iteratedLaurent g ε =
      (laurentChoice (g 0) (ε 0)).inter
        (iteratedLaurent (fun i : Fin m => g i.succ) (fun i => ε i.succ)) := rfl

/-- Exact conjunction of the selected unit-radius Laurent inequalities. -/
theorem mem_locus_iteratedLaurent (g : Fin m → P) (ε : Fin m → Bool)
    (x : BanachSpectrum P) :
    x ∈ (iteratedLaurent g ε).locus ↔
      ∀ i, if ε i then 1 ≤ x (g i) else x (g i) ≤ 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [iteratedLaurent_succ, locus_inter]
      simp only [Set.mem_inter_iff, mem_locus_laurentChoice, ih, Fin.forall_fin_succ]

/-- Every actual spectrum point belongs to a leaf, also for an empty tuple. -/
theorem iteratedLaurent_covers (g : Fin m → P) (x : BanachSpectrum P) :
    ∃ ε, x ∈ (iteratedLaurent g ε).locus := by
  classical
  refine ⟨fun i => if x (g i) ≤ 1 then false else true, ?_⟩
  rw [mem_locus_iteratedLaurent]
  intro i
  by_cases h : x (g i) ≤ 1
  · simp [h]
  · simpa [h] using le_of_not_ge h

theorem iteratedLaurent_familyCovers (g : Fin m → P) :
    FamilyCovers (whole K P)
      (fun ε : ULift.{u} (Fin m → Bool) => iteratedLaurent g ε.down) := by
  intro x _
  obtain ⟨ε, hε⟩ := iteratedLaurent_covers g x
  exact ⟨⟨ε⟩, hε⟩

/-- Inclusion in each selected binary factor. -/
def iteratedLaurentFactor (g : Fin m → P) (ε : Fin m → Bool) (i : Fin m) :
    iteratedLaurent g ε ⟶ laurentChoice (g i) (ε i) :=
  ⟨fun x hx => (mem_locus_laurentChoice _ _ _).mpr
    ((mem_locus_iteratedLaurent g ε x).mp hx i)⟩

/-- Pulling a leaf back and constructing the leaf of the mapped tuple give
equal actual loci, without requiring equal chosen presentations. -/
theorem locus_iteratedLaurent_pullback (g : Fin m → P) (ε : Fin m → Bool)
    (φ : BoundedAlgHom K P Q) :
    ((iteratedLaurent g ε).pullback φ).locus =
      (iteratedLaurent (fun i => φ (g i)) ε).locus := by
  ext x
  rw [mem_locus_pullback, mem_locus_iteratedLaurent, mem_locus_iteratedLaurent]
  rfl

private def isoOfLocusEq {d e : RationalData K P} (h : d.locus = e.locus) : d ≅ e where
  hom := ⟨h.le⟩
  inv := ⟨h.ge⟩
  hom_inv_id := (inferInstance : Subsingleton (Inclusion d d)).elim _ _
  inv_hom_id := (inferInstance : Subsingleton (Inclusion e e)).elim _ _

private def quotientEquivOfIso {d e : RationalData K P} (i : d ≅ e) :
    BoundedAlgEquiv K d.algebra e.algebra :=
  BoundedAlgEquiv.ofHomInv i.inv.restriction i.hom.restriction
    (fun a => congrArg (fun φ : BoundedAlgHom K d.algebra d.algebra => φ a)
      (show i.hom.restriction.comp i.inv.restriction = BoundedAlgHom.id K d.algebra from by
      rw [← Inclusion.restriction_comp, i.hom_inv_id, Inclusion.restriction_id]))
    (fun a => congrArg (fun φ : BoundedAlgHom K e.algebra e.algebra => φ a)
      (show i.inv.restriction.comp i.hom.restriction = BoundedAlgHom.id K e.algebra from by
      rw [← Inclusion.restriction_comp, i.inv_hom_id, Inclusion.restriction_id]))

/-- The actual isomorphism of rational loci for base change of a leaf. -/
def iteratedLaurentPullbackIso (g : Fin m → P) (ε : Fin m → Bool)
    (φ : BoundedAlgHom K P Q) :
    (iteratedLaurent g ε).pullback φ ≅ iteratedLaurent (fun i => φ (g i)) ε :=
  isoOfLocusEq (locus_iteratedLaurent_pullback g ε φ)

/-- The induced bounded map between the actual quotients of the two leaves. -/
def iteratedLaurentComparison (g : Fin m → P) (ε : Fin m → Bool)
    (φ : BoundedAlgHom K P Q) :
    BoundedAlgHom K (iteratedLaurent g ε).algebra
      (iteratedLaurent (fun i => φ (g i)) ε).algebra :=
  (iteratedLaurentPullbackIso g ε φ).inv.restriction.comp
    ((iteratedLaurent g ε).comparison φ)

theorem iteratedLaurentComparison_comp_baseMap (g : Fin m → P) (ε : Fin m → Bool)
    (φ : BoundedAlgHom K P Q) :
    (iteratedLaurentComparison g ε φ).comp (iteratedLaurent g ε).baseMap =
      (iteratedLaurent (fun i => φ (g i)) ε).baseMap.comp φ := by
  rw [iteratedLaurentComparison, BoundedAlgHom.comp_assoc, comparison_comp_baseMap,
    ← BoundedAlgHom.comp_assoc, Inclusion.restriction_comp_baseMap]

/-- Transport any inclusion from a leaf to the leaf of the mapped tuple. -/
def iteratedLaurentPullbackInclusion (g : Fin m → P) (ε : Fin m → Bool)
    {d : RationalData K P} (h : iteratedLaurent g ε ⟶ d) (φ : BoundedAlgHom K P Q) :
    iteratedLaurent (fun i => φ (g i)) ε ⟶ d.pullback φ :=
  (iteratedLaurentPullbackIso g ε φ).inv ≫ h.pullback φ

/-- The actual restriction square for every inclusion from a Laurent leaf. -/
theorem iteratedLaurentComparison_restriction (g : Fin m → P) (ε : Fin m → Bool)
    {d : RationalData K P} (h : iteratedLaurent g ε ⟶ d) (φ : BoundedAlgHom K P Q) :
    (iteratedLaurentPullbackInclusion g ε h φ).restriction.comp (d.comparison φ) =
      (iteratedLaurentComparison g ε φ).comp h.restriction := by
  apply d.hom_ext
  rw [BoundedAlgHom.comp_assoc, comparison_comp_baseMap, ← BoundedAlgHom.comp_assoc,
    Inclusion.restriction_comp_baseMap, BoundedAlgHom.comp_assoc,
    Inclusion.restriction_comp_baseMap, iteratedLaurentComparison_comp_baseMap]

/-- Inclusion of a nonempty leaf in its first binary branch. -/
def iteratedLaurentHead (g : Fin (m + 1) → P) (ε : Fin (m + 1) → Bool) :
    iteratedLaurent g ε ⟶ laurentChoice (g 0) (ε 0) :=
  iteratedLaurentFactor g ε 0

/-- Inclusion of a nonempty leaf in its tail leaf. -/
def iteratedLaurentTail (g : Fin (m + 1) → P) (ε : Fin (m + 1) → Bool) :
    iteratedLaurent g ε ⟶
      iteratedLaurent (fun i : Fin m => g i.succ) (fun i => ε i.succ) :=
  ⟨fun x hx => (mem_locus_iteratedLaurent _ _ x).mpr
    (fun i => (mem_locus_iteratedLaurent g ε x).mp hx i.succ)⟩

/-- On the quotient of a first binary branch, the pulled-back full leaf is
the tail cover of the images of the remaining functions. -/
def iteratedLaurentBranchIso (g : Fin (m + 1) → P) (ε : Fin (m + 1) → Bool) :
    (iteratedLaurent g ε).pullback (laurentChoice (g 0) (ε 0)).baseMap ≅
      iteratedLaurent (fun i : Fin m => (laurentChoice (g 0) (ε 0)).baseMap (g i.succ))
        (fun i => ε i.succ) := by
  apply isoOfLocusEq
  ext x
  rw [mem_locus_pullback, iteratedLaurent_succ, locus_inter]
  change (_ ∧ _) ↔ _
  have h := (laurentChoice (g 0) (ε 0)).baseMap_hasImageIn x
  rw [and_iff_right h, mem_locus_iteratedLaurent, mem_locus_iteratedLaurent]
  rfl

/-- Actual bounded quotient equivalence supporting induction on the number
of binary Laurent splits. -/
def iteratedLaurentBranchEquiv (g : Fin (m + 1) → P) (ε : Fin (m + 1) → Bool) :
    BoundedAlgEquiv K (iteratedLaurent g ε).algebra
      (iteratedLaurent (fun i : Fin m => (laurentChoice (g 0) (ε 0)).baseMap (g i.succ))
        (fun i => ε i.succ)).algebra :=
  (iteratedLaurentHead g ε).relativeEquiv.trans
    (quotientEquivOfIso (iteratedLaurentBranchIso g ε))

theorem iteratedLaurentBranchEquiv_comp_baseMap
    (g : Fin (m + 1) → P) (ε : Fin (m + 1) → Bool) :
    (iteratedLaurentBranchEquiv g ε).toBoundedAlgHom.comp (iteratedLaurent g ε).baseMap =
    (iteratedLaurent (fun i : Fin m => (laurentChoice (g 0) (ε 0)).baseMap (g i.succ))
      (fun i => ε i.succ)).baseMap.comp (laurentChoice (g 0) (ε 0)).baseMap := by
  apply BoundedAlgHom.ext
  intro a
  change (iteratedLaurentBranchIso g ε).inv.restriction
    ((iteratedLaurent g ε).comparison (laurentChoice (g 0) (ε 0)).baseMap
      ((iteratedLaurent g ε).baseMap a)) = _
  have h := congrArg (fun φ => φ a)
    ((iteratedLaurent g ε).comparison_comp_baseMap (laurentChoice (g 0) (ε 0)).baseMap)
  rw [show (iteratedLaurent g ε).comparison (laurentChoice (g 0) (ε 0)).baseMap
    ((iteratedLaurent g ε).baseMap a) =
    ((iteratedLaurent g ε).pullback (laurentChoice (g 0) (ε 0)).baseMap).baseMap
      ((laurentChoice (g 0) (ε 0)).baseMap a) from h]
  exact congrArg (fun φ => φ ((laurentChoice (g 0) (ε 0)).baseMap a))
    (iteratedLaurentBranchIso g ε).inv.restriction_comp_baseMap

/-- The equivalence identifies restriction from the first branch with the
structural map of the tail quotient over that branch. -/
theorem iteratedLaurentBranchEquiv_restriction_head
    (g : Fin (m + 1) → P) (ε : Fin (m + 1) → Bool) :
    (iteratedLaurentBranchEquiv g ε).toBoundedAlgHom.comp
      (iteratedLaurentHead g ε).restriction =
    (iteratedLaurent (fun i : Fin m => (laurentChoice (g 0) (ε 0)).baseMap (g i.succ))
      (fun i => ε i.succ)).baseMap := by
  apply (laurentChoice (g 0) (ε 0)).hom_ext
  rw [BoundedAlgHom.comp_assoc, Inclusion.restriction_comp_baseMap,
    iteratedLaurentBranchEquiv_comp_baseMap]

/-- Restriction from the old tail becomes its actual base-change comparison. -/
theorem iteratedLaurentBranchEquiv_restriction_tail
    (g : Fin (m + 1) → P) (ε : Fin (m + 1) → Bool) :
    (iteratedLaurentBranchEquiv g ε).toBoundedAlgHom.comp
      (iteratedLaurentTail g ε).restriction =
    iteratedLaurentComparison (fun i : Fin m => g i.succ) (fun i => ε i.succ)
      (laurentChoice (g 0) (ε 0)).baseMap := by
  apply (iteratedLaurent (fun i : Fin m => g i.succ) (fun i => ε i.succ)).hom_ext
  rw [BoundedAlgHom.comp_assoc, Inclusion.restriction_comp_baseMap,
    iteratedLaurentBranchEquiv_comp_baseMap, iteratedLaurentComparison_comp_baseMap]

/-- The pullback of a pairwise leaf intersection has the locus of the
intersection of the two mapped leaves. -/
def iteratedLaurentOverlapPullbackIso (g : Fin m → P) (ε η : Fin m → Bool)
    (φ : BoundedAlgHom K P Q) :
    ((iteratedLaurent g ε).inter (iteratedLaurent g η)).pullback φ ≅
      (iteratedLaurent (fun i => φ (g i)) ε).inter
        (iteratedLaurent (fun i => φ (g i)) η) :=
  isoOfLocusEq (by
    rw [locus_pullback_inter, locus_iteratedLaurent_pullback,
      locus_iteratedLaurent_pullback, locus_inter])

/-- Actual bounded base change on a pairwise leaf overlap. -/
def iteratedLaurentOverlapComparison (g : Fin m → P) (ε η : Fin m → Bool)
    (φ : BoundedAlgHom K P Q) :
    BoundedAlgHom K ((iteratedLaurent g ε).inter (iteratedLaurent g η)).algebra
      ((iteratedLaurent (fun i => φ (g i)) ε).inter
        (iteratedLaurent (fun i => φ (g i)) η)).algebra :=
  (iteratedLaurentOverlapPullbackIso g ε η φ).inv.restriction.comp
    (((iteratedLaurent g ε).inter (iteratedLaurent g η)).comparison φ)

theorem iteratedLaurentOverlapComparison_comp_baseMap (g : Fin m → P)
    (ε η : Fin m → Bool) (φ : BoundedAlgHom K P Q) :
    (iteratedLaurentOverlapComparison g ε η φ).comp
      ((iteratedLaurent g ε).inter (iteratedLaurent g η)).baseMap =
    ((iteratedLaurent (fun i => φ (g i)) ε).inter
      (iteratedLaurent (fun i => φ (g i)) η)).baseMap.comp φ := by
  rw [iteratedLaurentOverlapComparison, BoundedAlgHom.comp_assoc,
    comparison_comp_baseMap, ← BoundedAlgHom.comp_assoc,
    Inclusion.restriction_comp_baseMap]

theorem iteratedLaurentOverlapComparison_left (g : Fin m → P)
    (ε η : Fin m → Bool) (φ : BoundedAlgHom K P Q) :
    (iteratedLaurentOverlapComparison g ε η φ).comp
      (interLeft (iteratedLaurent g ε) (iteratedLaurent g η)).restriction =
    (interLeft (iteratedLaurent (fun i => φ (g i)) ε)
      (iteratedLaurent (fun i => φ (g i)) η)).restriction.comp
        (iteratedLaurentComparison g ε φ) := by
  apply (iteratedLaurent g ε).hom_ext
  rw [BoundedAlgHom.comp_assoc, Inclusion.restriction_comp_baseMap,
    iteratedLaurentOverlapComparison_comp_baseMap, BoundedAlgHom.comp_assoc,
    iteratedLaurentComparison_comp_baseMap, ← BoundedAlgHom.comp_assoc,
    Inclusion.restriction_comp_baseMap]

theorem iteratedLaurentOverlapComparison_right (g : Fin m → P)
    (ε η : Fin m → Bool) (φ : BoundedAlgHom K P Q) :
    (iteratedLaurentOverlapComparison g ε η φ).comp
      (interRight (iteratedLaurent g ε) (iteratedLaurent g η)).restriction =
    (interRight (iteratedLaurent (fun i => φ (g i)) ε)
      (iteratedLaurent (fun i => φ (g i)) η)).restriction.comp
        (iteratedLaurentComparison g η φ) := by
  apply (iteratedLaurent g η).hom_ext
  rw [BoundedAlgHom.comp_assoc, Inclusion.restriction_comp_baseMap,
    iteratedLaurentOverlapComparison_comp_baseMap, BoundedAlgHom.comp_assoc,
    iteratedLaurentComparison_comp_baseMap, ← BoundedAlgHom.comp_assoc,
    Inclusion.restriction_comp_baseMap]

/-- Compatibility of actual leaf sections is preserved by arbitrary bounded
base change, with the explicit chosen intersections on both bases. -/
theorem iteratedLaurent_compatible_comparison (g : Fin m → P)
    (s : ∀ ε, (iteratedLaurent g ε).algebra)
    (hs : ∀ ε η, (interLeft (iteratedLaurent g ε) (iteratedLaurent g η)).restriction (s ε) =
      (interRight (iteratedLaurent g ε) (iteratedLaurent g η)).restriction (s η))
    (φ : BoundedAlgHom K P Q) :
    ∀ ε η,
      (interLeft (iteratedLaurent (fun i => φ (g i)) ε)
        (iteratedLaurent (fun i => φ (g i)) η)).restriction
          (iteratedLaurentComparison g ε φ (s ε)) =
      (interRight (iteratedLaurent (fun i => φ (g i)) ε)
        (iteratedLaurent (fun i => φ (g i)) η)).restriction
          (iteratedLaurentComparison g η φ (s η)) := by
  intro ε η
  have hl := congrArg (fun ψ => ψ (s ε)) (iteratedLaurentOverlapComparison_left g ε η φ)
  have hr := congrArg (fun ψ => ψ (s η)) (iteratedLaurentOverlapComparison_right g ε η φ)
  exact hl.symm.trans
    ((congrArg (iteratedLaurentOverlapComparison g ε η φ) (hs ε η)).trans hr)

private def relativeEquivOfIso {d e : RationalData K P} (h : e ⟶ d)
    {t : RationalData K d.algebra} (i : e.pullback d.baseMap ≅ t) :
    BoundedAlgEquiv K e.algebra t.algebra :=
  h.relativeEquiv.trans (quotientEquivOfIso i)

private theorem relativeEquivOfIso_baseMap {d e : RationalData K P} (h : e ⟶ d)
    {t : RationalData K d.algebra} (i : e.pullback d.baseMap ≅ t) :
    (relativeEquivOfIso h i).toBoundedAlgHom.comp e.baseMap =
      t.baseMap.comp d.baseMap := by
  apply BoundedAlgHom.ext
  intro a
  change i.inv.restriction (e.comparison d.baseMap (e.baseMap a)) = _
  have he := congrArg (fun ψ => ψ a) (e.comparison_comp_baseMap d.baseMap)
  change e.comparison d.baseMap (e.baseMap a) =
    (e.pullback d.baseMap).baseMap (d.baseMap a) at he
  rw [he]
  exact congrArg (fun ψ => ψ (d.baseMap a)) i.inv.restriction_comp_baseMap

/-- Extend any rational prefix by a binary Laurent split. In particular `d`
can be any recursively constructed `iteratedLaurent` prefix. -/
abbrev laurentChild (d : RationalData K P) (g : P) (b : Bool) : RationalData K P :=
  d.inter (laurentChoice g b)

theorem laurentChild_covers (d : RationalData K P) (g : P)
    (x : BanachSpectrum P) (hx : x ∈ d.locus) :
    ∃ b, x ∈ (laurentChild d g b).locus := by
  rcases mem_laurentUpper_or_mem_laurentLower g x with h | h
  · exact ⟨false, by simpa [laurentChild] using And.intro hx h⟩
  · exact ⟨true, by simpa [laurentChild] using And.intro hx h⟩

/-- Each global binary child pulled back to its prefix quotient has exactly
the locus of the ordinary binary Laurent domain of the image of `g`. -/
def laurentChildPullbackIso (d : RationalData K P) (g : P) (b : Bool) :
    (laurentChild d g b).pullback d.baseMap ≅ laurentChoice (d.baseMap g) b := by
  apply isoOfLocusEq
  ext x
  rw [mem_locus_pullback, laurentChild, locus_inter]
  change (_ ∧ _) ↔ _
  rw [and_iff_right (d.baseMap_hasImageIn x),
    mem_locus_laurentChoice, mem_locus_laurentChoice]
  rfl

/-- Actual bounded equivalence between a global child and the local binary
Laurent quotient over the prefix algebra. -/
def laurentChildEquiv (d : RationalData K P) (g : P) (b : Bool) :
    BoundedAlgEquiv K (laurentChild d g b).algebra
      (laurentChoice (d.baseMap g) b).algebra :=
  relativeEquivOfIso (interLeft d (laurentChoice g b)) (laurentChildPullbackIso d g b)

theorem laurentChildEquiv_comp_baseMap (d : RationalData K P) (g : P) (b : Bool) :
    (laurentChildEquiv d g b).toBoundedAlgHom.comp (laurentChild d g b).baseMap =
      (laurentChoice (d.baseMap g) b).baseMap.comp d.baseMap :=
  relativeEquivOfIso_baseMap _ _

/-- The global restriction from the prefix is the local branch base map. -/
theorem laurentChildEquiv_restriction (d : RationalData K P) (g : P) (b : Bool) :
    (laurentChildEquiv d g b).toBoundedAlgHom.comp
      (interLeft d (laurentChoice g b)).restriction =
      (laurentChoice (d.baseMap g) b).baseMap := by
  apply d.hom_ext
  rw [BoundedAlgHom.comp_assoc, Inclusion.restriction_comp_baseMap,
    laurentChildEquiv_comp_baseMap]

/-- The chosen overlap of the two global binary children of a prefix. -/
abbrev laurentChildrenOverlap (d : RationalData K P) (g : P) : RationalData K P :=
  (laurentChild d g false).inter (laurentChild d g true)

private def laurentChildrenOverlapInclusion (d : RationalData K P) (g : P) :
    laurentChildrenOverlap d g ⟶ d :=
  interLeft _ _ ≫ interLeft _ _

/-- The global child overlap pulled back to the prefix quotient is the
intersection of the two ordinary local Laurent domains. -/
def laurentChildrenOverlapPullbackIso (d : RationalData K P) (g : P) :
    (laurentChildrenOverlap d g).pullback d.baseMap ≅
      (laurentChoice (d.baseMap g) false).inter (laurentChoice (d.baseMap g) true) := by
  apply isoOfLocusEq
  ext x
  simp only [mem_locus_pullback, laurentChildrenOverlap, laurentChild, locus_inter,
    Set.mem_inter_iff, mem_locus_laurentChoice]
  simp only [d.baseMap_hasImageIn x, true_and]
  rfl

/-- Actual bounded equivalence for the binary overlap over a prefix quotient. -/
def laurentChildrenOverlapEquiv (d : RationalData K P) (g : P) :
    BoundedAlgEquiv K (laurentChildrenOverlap d g).algebra
      ((laurentChoice (d.baseMap g) false).inter (laurentChoice (d.baseMap g) true)).algebra :=
  relativeEquivOfIso (laurentChildrenOverlapInclusion d g)
    (laurentChildrenOverlapPullbackIso d g)

theorem laurentChildrenOverlapEquiv_comp_baseMap (d : RationalData K P) (g : P) :
    (laurentChildrenOverlapEquiv d g).toBoundedAlgHom.comp
      (laurentChildrenOverlap d g).baseMap =
    ((laurentChoice (d.baseMap g) false).inter
      (laurentChoice (d.baseMap g) true)).baseMap.comp d.baseMap :=
  relativeEquivOfIso_baseMap _ _

theorem laurentChildrenOverlapEquiv_left (d : RationalData K P) (g : P) :
    (laurentChildrenOverlapEquiv d g).toBoundedAlgHom.comp
      (interLeft (laurentChild d g false) (laurentChild d g true)).restriction =
    (interLeft (laurentChoice (d.baseMap g) false)
      (laurentChoice (d.baseMap g) true)).restriction.comp
        (laurentChildEquiv d g false).toBoundedAlgHom := by
  apply (laurentChild d g false).hom_ext
  rw [BoundedAlgHom.comp_assoc, Inclusion.restriction_comp_baseMap,
    laurentChildrenOverlapEquiv_comp_baseMap, BoundedAlgHom.comp_assoc,
    laurentChildEquiv_comp_baseMap, ← BoundedAlgHom.comp_assoc,
    Inclusion.restriction_comp_baseMap]

theorem laurentChildrenOverlapEquiv_right (d : RationalData K P) (g : P) :
    (laurentChildrenOverlapEquiv d g).toBoundedAlgHom.comp
      (interRight (laurentChild d g false) (laurentChild d g true)).restriction =
    (interRight (laurentChoice (d.baseMap g) false)
      (laurentChoice (d.baseMap g) true)).restriction.comp
        (laurentChildEquiv d g true).toBoundedAlgHom := by
  apply (laurentChild d g true).hom_ext
  rw [BoundedAlgHom.comp_assoc, Inclusion.restriction_comp_baseMap,
    laurentChildrenOverlapEquiv_comp_baseMap, BoundedAlgHom.comp_assoc,
    laurentChildEquiv_comp_baseMap, ← BoundedAlgHom.comp_assoc,
    Inclusion.restriction_comp_baseMap]

end Langlands.Analytic.StrictTestDomain.RationalData
