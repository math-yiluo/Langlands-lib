import Langlands.Cohomology.Tate.SplitComparison
import Langlands.Cohomology.Tate.TransferProof

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Tate

set_option backward.isDefEq.respectTransparency false

variable {R G : Type u} [CommRing R] [Group G] [Fintype G]

lemma scalarSplit_delta_up (S : ShortComplex (Rep.{u} R G))
    (s : (S.map (forget₂ (Rep.{u} R G) (ModuleCat.{u} R))).Splitting) (n : ℤ) :
    TateCohomology.δ (scalarSplit_shortExact S s) n =
      (tateCohomologyFunctor n).map (splitSequenceToShiftUp S s).τ₃ ≫
        (shiftUpIso S.X₁ n).hom := by
  have h := TateCohomology.δ_naturality (scalarSplit_shortExact S s)
    (shiftUpSequence_shortExact S.X₁) (splitSequenceToShiftUp S s) n
  change TateCohomology.δ (scalarSplit_shortExact S s) n ≫
    (tateCohomologyFunctor (n + 1)).map (𝟙 S.X₁) =
      (tateCohomologyFunctor n).map (splitSequenceToShiftUp S s).τ₃ ≫
        (shiftUpIso S.X₁ n).hom at h
  rw [(tateCohomologyFunctor (n + 1)).map_id, Category.comp_id] at h
  exact h

lemma scalarSplit_delta_down (S : ShortComplex (Rep.{u} R G))
    (s : (S.map (forget₂ (Rep.{u} R G) (ModuleCat.{u} R))).Splitting) (n : ℤ) :
    TateCohomology.δ (scalarSplit_shortExact S s) n =
      (shiftDownIso S.X₃ n).hom ≫
        (tateCohomologyFunctor (n + 1)).map (shiftDownToSplitSequence S s).τ₁ := by
  have h := TateCohomology.δ_naturality (shiftDownSequence_shortExact S.X₃)
    (scalarSplit_shortExact S s) (shiftDownToSplitSequence S s) n
  change (shiftDownIso S.X₃ n).hom ≫
    (tateCohomologyFunctor (n + 1)).map (shiftDownToSplitSequence S s).τ₁ =
      (tateCohomologyFunctor n).map (𝟙 S.X₃) ≫
    TateCohomology.δ (scalarSplit_shortExact S s) n at h
  rw [(tateCohomologyFunctor n).map_id, Category.id_comp] at h
  exact h.symm

variable (H : Subgroup G) [Fintype H] [Fintype (G ⧸ H)]

omit [Fintype G] [Fintype (G ⧸ H)] in
lemma scalarSplit_restricted_delta_up (S : ShortComplex (Rep.{u} R G))
    (s : (S.map (forget₂ (Rep.{u} R G) (ModuleCat.{u} R))).Splitting) (n : ℤ) :
    TateCohomology.δ
        ((scalarSplit_shortExact S s).map_of_exact (Rep.resFunctor H.subtype)) n =
      (tateCohomologyFunctor n).map
          ((Rep.resFunctor H.subtype).map (splitSequenceToShiftUp S s).τ₃) ≫
        (restrictedShiftUpIso H S.X₁ n).hom := by
  have h := TateCohomology.δ_naturality
    ((scalarSplit_shortExact S s).map_of_exact (Rep.resFunctor H.subtype))
    (restrictedShiftUpSequence_shortExact H S.X₁)
    ((Rep.resFunctor H.subtype).mapShortComplex.map (splitSequenceToShiftUp S s)) n
  change TateCohomology.δ
      ((scalarSplit_shortExact S s).map_of_exact (Rep.resFunctor H.subtype)) n ≫
    (tateCohomologyFunctor (n + 1)).map ((Rep.resFunctor H.subtype).map (𝟙 S.X₁)) =
      (tateCohomologyFunctor n).map
          ((Rep.resFunctor H.subtype).map (splitSequenceToShiftUp S s).τ₃) ≫
        (restrictedShiftUpIso H S.X₁ n).hom at h
  rw [(Rep.resFunctor H.subtype).map_id] at h
  have hi := (tateCohomologyFunctor (R := R) (G := H) (n + 1)).map_id
    (Rep.res H.subtype S.X₁)
  exact (Category.comp_id _).symm.trans
    ((congrArg
      (fun f => TateCohomology.δ
        ((scalarSplit_shortExact S s).map_of_exact (Rep.resFunctor H.subtype)) n ≫ f)
      hi).symm.trans h)

omit [Fintype (G ⧸ H)] in
lemma scalarSplit_restricted_delta_down (S : ShortComplex (Rep.{u} R G))
    (s : (S.map (forget₂ (Rep.{u} R G) (ModuleCat.{u} R))).Splitting) (n : ℤ) :
    TateCohomology.δ
        ((scalarSplit_shortExact S s).map_of_exact (Rep.resFunctor H.subtype)) n =
      (restrictedShiftDownIso H S.X₃ n).hom ≫
        (tateCohomologyFunctor (n + 1)).map
          ((Rep.resFunctor H.subtype).map (shiftDownToSplitSequence S s).τ₁) := by
  have h := TateCohomology.δ_naturality
    (restrictedShiftDownSequence_shortExact H S.X₃)
    ((scalarSplit_shortExact S s).map_of_exact (Rep.resFunctor H.subtype))
    ((Rep.resFunctor H.subtype).mapShortComplex.map (shiftDownToSplitSequence S s)) n
  change (restrictedShiftDownIso H S.X₃ n).hom ≫
      (tateCohomologyFunctor (n + 1)).map
        ((Rep.resFunctor H.subtype).map (shiftDownToSplitSequence S s).τ₁) =
    (tateCohomologyFunctor n).map ((Rep.resFunctor H.subtype).map (𝟙 S.X₃)) ≫
      TateCohomology.δ
      ((scalarSplit_shortExact S s).map_of_exact (Rep.resFunctor H.subtype)) n at h
  rw [(Rep.resFunctor H.subtype).map_id,
    (tateCohomologyFunctor (R := R) (G := H) n).map_id,
    Category.id_comp] at h
  exact h.symm

/-- Restriction commutes with every scalar-split connecting map in nonnegative degree. -/
lemma restrictionNonneg_scalarSplit_delta (S : ShortComplex (Rep.{u} R G))
    (s : (S.map (forget₂ (Rep.{u} R G) (ModuleCat.{u} R))).Splitting) (n : ℕ)
    (x : tateCohomology S.X₃ n) :
    restrictionNonneg H (n + 1) S.X₁
        (TateCohomology.δ (scalarSplit_shortExact S s) n x) =
      TateCohomology.δ
        ((scalarSplit_shortExact S s).map_of_exact (Rep.resFunctor H.subtype)) n
        (restrictionNonneg H n S.X₃ x) := by
  rw [scalarSplit_delta_up S s (n : ℤ), scalarSplit_restricted_delta_up H S s (n : ℤ)]
  change restrictionNonneg H (n + 1) S.X₁
    ((shiftUpIso S.X₁ n).hom
      ((tateCohomologyFunctor n).map (splitSequenceToShiftUp S s).τ₃ x)) = _
  exact (restrictionNonneg_shift H n S.X₁ _).trans
    (congrArg (fun y => (restrictedShiftUpIso H S.X₁ n).hom y)
      (restrictionNonneg_naturality H n (splitSequenceToShiftUp S s).τ₃ x).symm)

/-- Corestriction commutes with every scalar-split connecting map in nonnegative degree. -/
lemma corestrictionNonneg_scalarSplit_delta (S : ShortComplex (Rep.{u} R G))
    (s : (S.map (forget₂ (Rep.{u} R G) (ModuleCat.{u} R))).Splitting) (n : ℕ)
    (x : tateCohomology (Rep.res H.subtype S.X₃) n) :
    corestrictionNonneg H (n + 1) S.X₁
        (TateCohomology.δ
          ((scalarSplit_shortExact S s).map_of_exact (Rep.resFunctor H.subtype)) n x) =
      TateCohomology.δ (scalarSplit_shortExact S s) n
        (corestrictionNonneg H n S.X₃ x) := by
  rw [scalarSplit_restricted_delta_up H S s (n : ℤ), scalarSplit_delta_up S s (n : ℤ)]
  change corestrictionNonneg H (n + 1) S.X₁
    ((restrictedShiftUpIso H S.X₁ n).hom
      ((tateCohomologyFunctor n).map
        ((Rep.resFunctor H.subtype).map (splitSequenceToShiftUp S s).τ₃) x)) = _
  exact (corestrictionNonneg_shift H n S.X₁ _).trans
    (congrArg (fun y => (shiftUpIso S.X₁ n).hom y)
      (corestrictionNonneg_naturality H n (splitSequenceToShiftUp S s).τ₃ x).symm)

omit [Fintype H] [Fintype (G ⧸ H)] in
lemma tateMap_degreeTransport {A B : Rep.{u} R G} (f : A ⟶ B)
    {i j : ℤ} (h : i = j) :
    (tateCohomologyFunctor i).map f ≫ eqToHom (congrArg (tateCohomology B) h) =
      eqToHom (congrArg (tateCohomology A) h) ≫ (tateCohomologyFunctor j).map f := by
  subst j
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp]

omit [Fintype H] [Fintype (G ⧸ H)] in
/-- The actual connecting map, with consecutive negative degrees normalized. -/
def scalarSplitDeltaNegative (S : ShortComplex (Rep.{u} R G))
    (s : (S.map (forget₂ (Rep.{u} R G) (ModuleCat.{u} R))).Splitting) (n : ℕ) :
    tateCohomology S.X₃ (-(n + 1 : ℤ)) ⟶ tateCohomology S.X₁ (-(n : ℤ)) :=
  TateCohomology.δ (scalarSplit_shortExact S s) (-(n + 1 : ℤ)) ≫
    eqToHom (congrArg (tateCohomology S.X₁) (show -(n + 1 : ℤ) + 1 = -(n : ℤ) by omega))

omit [Fintype (G ⧸ H)] in
/-- The same normalized connecting map after restriction to a subgroup. -/
def scalarSplitRestrictedDeltaNegative (S : ShortComplex (Rep.{u} R G))
    (s : (S.map (forget₂ (Rep.{u} R G) (ModuleCat.{u} R))).Splitting) (n : ℕ) :
    tateCohomology (Rep.res H.subtype S.X₃) (-(n + 1 : ℤ)) ⟶
      tateCohomology (Rep.res H.subtype S.X₁) (-(n : ℤ)) :=
  TateCohomology.δ
      ((scalarSplit_shortExact S s).map_of_exact (Rep.resFunctor H.subtype)) (-(n + 1 : ℤ)) ≫
    eqToHom (congrArg (tateCohomology (Rep.res H.subtype S.X₁))
      (show -(n + 1 : ℤ) + 1 = -(n : ℤ) by omega))

omit [Fintype H] [Fintype (G ⧸ H)] in
lemma scalarSplitDeltaNegative_factor (S : ShortComplex (Rep.{u} R G))
    (s : (S.map (forget₂ (Rep.{u} R G) (ModuleCat.{u} R))).Splitting) (n : ℕ) :
    scalarSplitDeltaNegative S s n =
      (shiftDownNegativeIso S.X₃ n).hom ≫
        (tateCohomologyFunctor (-(n : ℤ))).map (shiftDownToSplitSequence S s).τ₁ := by
  rw [scalarSplitDeltaNegative, scalarSplit_delta_down S s, Category.assoc,
    tateMap_degreeTransport (shiftDownToSplitSequence S s).τ₁
      (show -(n + 1 : ℤ) + 1 = -(n : ℤ) by omega), ← Category.assoc]
  rfl

omit [Fintype (G ⧸ H)] in
lemma scalarSplitRestrictedDeltaNegative_factor (S : ShortComplex (Rep.{u} R G))
    (s : (S.map (forget₂ (Rep.{u} R G) (ModuleCat.{u} R))).Splitting) (n : ℕ) :
    scalarSplitRestrictedDeltaNegative H S s n =
      (restrictedShiftDownNegativeIso H S.X₃ n).hom ≫
        (tateCohomologyFunctor (-(n : ℤ))).map
          ((Rep.resFunctor H.subtype).map (shiftDownToSplitSequence S s).τ₁) := by
  rw [scalarSplitRestrictedDeltaNegative, scalarSplit_restricted_delta_down H S s, Category.assoc,
    tateMap_degreeTransport ((Rep.resFunctor H.subtype).map (shiftDownToSplitSequence S s).τ₁)
      (show -(n + 1 : ℤ) + 1 = -(n : ℤ) by omega), ← Category.assoc]
  rfl

/-- Restriction commutes with every scalar-split connecting map in negative degree. -/
lemma restrictionNonpos_scalarSplit_delta (S : ShortComplex (Rep.{u} R G))
    (s : (S.map (forget₂ (Rep.{u} R G) (ModuleCat.{u} R))).Splitting) (n : ℕ)
    (x : tateCohomology S.X₃ (-(n + 1 : ℤ))) :
    restrictionNonpos H n S.X₁ (scalarSplitDeltaNegative S s n x) =
      scalarSplitRestrictedDeltaNegative H S s n
        (restrictionNonpos H (n + 1) S.X₃ x) := by
  rw [scalarSplitDeltaNegative_factor S s n, scalarSplitRestrictedDeltaNegative_factor H S s n]
  change restrictionNonpos H n S.X₁
      ((tateCohomologyFunctor (-(n : ℤ))).map (shiftDownToSplitSequence S s).τ₁
        ((shiftDownNegativeIso S.X₃ n).hom x)) = _
  exact (restrictionNonpos_naturality H n (shiftDownToSplitSequence S s).τ₁ _).symm.trans
    (congrArg
      (fun y => (tateCohomologyFunctor (-(n : ℤ))).map
        ((Rep.resFunctor H.subtype).map (shiftDownToSplitSequence S s).τ₁) y)
      (restrictionNonpos_shift H n S.X₃ x).symm)

/-- Corestriction commutes with every scalar-split connecting map in negative degree. -/
lemma corestrictionNonpos_scalarSplit_delta (S : ShortComplex (Rep.{u} R G))
    (s : (S.map (forget₂ (Rep.{u} R G) (ModuleCat.{u} R))).Splitting) (n : ℕ)
    (x : tateCohomology (Rep.res H.subtype S.X₃) (-(n + 1 : ℤ))) :
    corestrictionNonpos H n S.X₁ (scalarSplitRestrictedDeltaNegative H S s n x) =
      scalarSplitDeltaNegative S s n
        (corestrictionNonpos H (n + 1) S.X₃ x) := by
  rw [scalarSplitRestrictedDeltaNegative_factor H S s n, scalarSplitDeltaNegative_factor S s n]
  change corestrictionNonpos H n S.X₁
      ((tateCohomologyFunctor (-(n : ℤ))).map
        ((Rep.resFunctor H.subtype).map (shiftDownToSplitSequence S s).τ₁)
        ((restrictedShiftDownNegativeIso H S.X₃ n).hom x)) = _
  exact (corestrictionNonpos_naturality H n (shiftDownToSplitSequence S s).τ₁ _).symm.trans
    (congrArg
      (fun y => (tateCohomologyFunctor (-(n : ℤ))).map
        (shiftDownToSplitSequence S s).τ₁ y)
      (corestrictionNonpos_shift H n S.X₃ x).symm)

lemma restriction_degreeTransport (A : Rep.{u} R G) {i j : ℤ} (h : i = j)
    (x : tateCohomology A i) :
    restriction H A j (eqToHom (congrArg (tateCohomology A) h) x) =
      eqToHom (congrArg (tateCohomology (Rep.res H.subtype A)) h) (restriction H A i x) := by
  subst j
  rfl

lemma corestriction_degreeTransport (A : Rep.{u} R G) {i j : ℤ} (h : i = j)
    (x : tateCohomology (Rep.res H.subtype A) i) :
    corestriction H A j (eqToHom (congrArg (tateCohomology (Rep.res H.subtype A)) h) x) =
      eqToHom (congrArg (tateCohomology A) h) (corestriction H A i x) := by
  subst j
  rfl

lemma restriction_neg_nat (A : Rep.{u} R G) (n : ℕ) :
    restriction H A (-(n : ℤ)) = restrictionNonpos H n A := by
  cases n <;> rfl

lemma corestriction_neg_nat (A : Rep.{u} R G) (n : ℕ) :
    corestriction H A (-(n : ℤ)) = corestrictionNonpos H n A := by
  cases n <;> rfl

/-- Restriction commutes with the actual connecting map in every integer degree. -/
lemma restriction_scalarSplit_delta (S : ShortComplex (Rep.{u} R G))
    (s : (S.map (forget₂ (Rep.{u} R G) (ModuleCat.{u} R))).Splitting) (n : ℤ)
    (x : tateCohomology S.X₃ n) :
    restriction H S.X₁ (n + 1) (TateCohomology.δ (scalarSplit_shortExact S s) n x) =
      TateCohomology.δ
        ((scalarSplit_shortExact S s).map_of_exact (Rep.resFunctor H.subtype)) n
        (restriction H S.X₃ n x) := by
  cases n with
  | ofNat n => exact restrictionNonneg_scalarSplit_delta H S s n x
  | negSucc n =>
    have hn : Int.negSucc n + 1 = -(n : ℤ) := by omega
    apply (eqToIso (congrArg (tateCohomology (Rep.res H.subtype S.X₁)) hn)).toLinearEquiv.injective
    change eqToHom (congrArg (tateCohomology (Rep.res H.subtype S.X₁)) hn)
      (restriction H S.X₁ (Int.negSucc n + 1)
        (TateCohomology.δ (scalarSplit_shortExact S s) (Int.negSucc n) x)) = _
    rw [← restriction_degreeTransport H S.X₁ hn]
    change restriction H S.X₁ (-(n : ℤ)) (scalarSplitDeltaNegative S s n x) =
      scalarSplitRestrictedDeltaNegative H S s n (restrictionNonpos H (n + 1) S.X₃ x)
    rw [restriction_neg_nat]
    exact restrictionNonpos_scalarSplit_delta H S s n x

/-- Corestriction commutes with the actual connecting map in every integer degree. -/
lemma corestriction_scalarSplit_delta (S : ShortComplex (Rep.{u} R G))
    (s : (S.map (forget₂ (Rep.{u} R G) (ModuleCat.{u} R))).Splitting) (n : ℤ)
    (x : tateCohomology (Rep.res H.subtype S.X₃) n) :
    corestriction H S.X₁ (n + 1)
        (TateCohomology.δ
          ((scalarSplit_shortExact S s).map_of_exact (Rep.resFunctor H.subtype)) n x) =
      TateCohomology.δ (scalarSplit_shortExact S s) n
        (corestriction H S.X₃ n x) := by
  cases n with
  | ofNat n => exact corestrictionNonneg_scalarSplit_delta H S s n x
  | negSucc n =>
    have hn : Int.negSucc n + 1 = -(n : ℤ) := by omega
    apply (eqToIso (congrArg (tateCohomology S.X₁) hn)).toLinearEquiv.injective
    change eqToHom (congrArg (tateCohomology S.X₁) hn)
      (corestriction H S.X₁ (Int.negSucc n + 1)
        (TateCohomology.δ
          ((scalarSplit_shortExact S s).map_of_exact (Rep.resFunctor H.subtype))
          (Int.negSucc n) x)) = _
    rw [← corestriction_degreeTransport H S.X₁ hn]
    change corestriction H S.X₁ (-(n : ℤ)) (scalarSplitRestrictedDeltaNegative H S s n x) =
      scalarSplitDeltaNegative S s n (corestrictionNonpos H (n + 1) S.X₃ x)
    rw [corestriction_neg_nat]
    exact corestrictionNonpos_scalarSplit_delta H S s n x

end Langlands.Tate
