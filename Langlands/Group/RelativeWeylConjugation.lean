import Langlands.Group.RelativeWeyl

/-!
# Relative Weyl conjugation of actual subgroups

Conjugation descends from the normalizer to its full-centralizer quotient
on subgroups containing that centralizer. This concerns subgroup images;
conjugation maps on their elements still use a normalizer lift.
-/

namespace Langlands.Group.RelativeWeyl

universe u

variable {G : Type u} [Group G]

/-- The actual image subgroup under forward conjugation. -/
def conjugateSubgroup (g : G) (L : Subgroup G) : Subgroup G :=
  L.map (MulAut.conj g : G →* G)

@[simp]
theorem conjugateSubgroup_one (L : Subgroup G) :
    conjugateSubgroup 1 L = L := by
  have h : (MulAut.conj (1 : G) : G →* G) = MonoidHom.id G := by
    ext x
    simp
  change L.map (MulAut.conj (1 : G) : G →* G) = L
  rw [h, Subgroup.map_id]

theorem conjugateSubgroup_mul (g h : G) (L : Subgroup G) :
    conjugateSubgroup (g * h) L =
      conjugateSubgroup g (conjugateSubgroup h L) := by
  simp only [conjugateSubgroup, Subgroup.map_map]
  congr 1
  ext x
  simp [mul_assoc]

/-- Inner conjugation by an element of a subgroup preserves that subgroup. -/
theorem conjugateSubgroup_eq_self {L : Subgroup G} {g : G} (hg : g ∈ L) :
    conjugateSubgroup g L = L :=
  Subgroup.mem_normalizer_iff_map_conj_eq.mp (L.le_normalizer hg)

/-- The full centralizer is normalized by the actual normalizer. -/
theorem conjugateSubgroup_centralizer (T : Subgroup G) (n : normalizer T) :
    conjugateSubgroup (n : G) (centralizer T) = centralizer T := by
  apply Subgroup.mem_normalizer_iff_map_conj_eq.mp
  exact (Subgroup.le_normalizer_of_normal_subgroupOf
    (Subgroup.centralizer_le_normalizer (T : Set G))) n.property

/-- A normalizer conjugate of an overgroup of the centralizer is again such
an overgroup. -/
theorem centralizer_le_conjugateSubgroup (T L : Subgroup G)
    (hZL : centralizer T ≤ L) (n : normalizer T) :
    centralizer T ≤ conjugateSubgroup (n : G) L := by
  rw [← conjugateSubgroup_centralizer T n]
  exact Subgroup.map_mono hZL

/-- Subgroup conjugation is independent of the normalizer lift. This does
not assert equality of the corresponding maps on subgroup elements. -/
theorem conjugateSubgroup_eq_of_mk_eq (T L : Subgroup G)
    (hZL : centralizer T ≤ L) (n m : normalizer T)
    (hnm : (QuotientGroup.mk n : Weyl T) = QuotientGroup.mk m) :
    conjugateSubgroup (n : G) L = conjugateSubgroup (m : G) L := by
  have hc : (n : G)⁻¹ * (m : G) ∈ centralizer T :=
    (QuotientGroup.eq.mp hnm : n⁻¹ * m ∈ denominator T)
  symm
  calc
    conjugateSubgroup (m : G) L =
        conjugateSubgroup ((n : G) * ((n : G)⁻¹ * (m : G))) L := by
      simp
    _ = conjugateSubgroup (n : G)
        (conjugateSubgroup ((n : G)⁻¹ * (m : G)) L) :=
      conjugateSubgroup_mul _ _ _
    _ = conjugateSubgroup (n : G) L := by
      rw [conjugateSubgroup_eq_self (hZL hc)]

/-- Actual subgroups of `G` which contain the full centralizer of `T`. -/
abbrev CentralizerOvergroup (T : Subgroup G) :=
  {L : Subgroup G // centralizer T ≤ L}

/-- The lift-independent conjugate subgroup, retaining its centralizer
containment. -/
def weylConjugate (T : Subgroup G) (w : Weyl T)
    (L : CentralizerOvergroup T) : CentralizerOvergroup T :=
  Quotient.liftOn' w
    (fun n : normalizer T =>
      ⟨conjugateSubgroup (n : G) L.val,
        centralizer_le_conjugateSubgroup T L.val L.property n⟩)
    (fun n m hnm => Subtype.ext
      (conjugateSubgroup_eq_of_mk_eq T L.val L.property n m
        (Quotient.sound' hnm)))

@[simp]
theorem weylConjugate_mk (T : Subgroup G) (n : normalizer T)
    (L : CentralizerOvergroup T) :
    (weylConjugate T (QuotientGroup.mk n) L).val =
      conjugateSubgroup (n : G) L.val :=
  rfl

/-- The actual relative Weyl group acts on actual centralizer overgroups. -/
instance weylConjugationAction (T : Subgroup G) :
    MulAction (Weyl T) (CentralizerOvergroup T) where
  smul := weylConjugate T
  one_smul L := Subtype.ext (conjugateSubgroup_one L.val)
  mul_smul w v L := by
    induction w using Quotient.inductionOn' with
    | h n =>
      induction v using Quotient.inductionOn' with
      | h m =>
        exact Subtype.ext (conjugateSubgroup_mul (n : G) (m : G) L.val)

@[simp]
theorem mk_smul_overgroup (T : Subgroup G) (n : normalizer T)
    (L : CentralizerOvergroup T) :
    ((QuotientGroup.mk n : Weyl T) • L).val =
      L.val.map (MulAut.conj (n : G) : G →* G) :=
  rfl

/-- The actual subgroup Weyl quotient fixes its own overgroup under the
ambient Weyl conjugation action. -/
theorem inclusion_smul_overgroup (T L : Subgroup G)
    (hZL : centralizer T ≤ L) (w : WeylIn T L) :
    inclusion T L w • (⟨L, hZL⟩ : CentralizerOvergroup T) = ⟨L, hZL⟩ := by
  induction w using Quotient.inductionOn' with
  | h n =>
    exact Subtype.ext (conjugateSubgroup_eq_self n.property.2)

/-- The actual Weyl transporter set, with forward conjugation convention. -/
def weylTransporters (T : Subgroup G) (L L' : CentralizerOvergroup T) :
    Set (Weyl T) :=
  {w | w • L = L'}

@[simp]
theorem mem_weylTransporters_mk (T : Subgroup G) (n : normalizer T)
    (L L' : CentralizerOvergroup T) :
    (QuotientGroup.mk n : Weyl T) ∈ weylTransporters T L L' ↔
      L.val.map (MulAut.conj (n : G) : G →* G) = L'.val := by
  change weylConjugate T (QuotientGroup.mk n) L = L' ↔ _
  exact Subtype.ext_iff

end Langlands.Group.RelativeWeyl
