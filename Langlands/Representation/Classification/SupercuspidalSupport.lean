import Langlands.Representation.Classification.Segments
import Langlands.Representation.Category.Subquotients
import Langlands.Weil.Representation.IsomorphismInvarianceProof

/-!
# Supercuspidal support for `GL_n`

Zelevinsky's support of an irreducible representation `ω` of `GL_n(F)`: a finite
multiset `{ρ_1, …, ρ_k}` of supercuspidal classes such that `ω` is an irreducible
subquotient of `ρ_1 × ⋯ × ρ_k` (Zelevinsky 1980, 1.10). The support is recorded by
relations on a given representation. Existence of a support, its uniqueness and the
existence of an ordering into which `ω` embeds are not asserted.

The subquotient relation of `Category/Subquotients` is characterized by an
injective and a surjective morphism, which gives its invariance under isomorphisms
of either argument.
-/

noncomputable section

open CategoryTheory

namespace Langlands

universe uR uG uV uF

namespace SmoothRep

variable {R : Type uR} {G : Type uG} [CommRing R] [Group G] [TopologicalSpace G]

theorem hom_hom_injective {A B : SmoothRep.{uR, uG, uV} R G} (e : A ≅ B) :
    Function.Injective (hom e.hom) := fun x y hxy => by
  have hx := congrArg (fun f => hom f x) e.hom_inv_id
  have hy := congrArg (fun f => hom f y) e.hom_inv_id
  simp only [hom_comp, hom_id, Representation.IntertwiningMap.comp_apply,
    Representation.IntertwiningMap.id_apply] at hx hy
  rw [← hx, ← hy, hxy]

theorem hom_hom_surjective {A B : SmoothRep.{uR, uG, uV} R G} (e : A ≅ B) :
    Function.Surjective (hom e.hom) := fun y => ⟨hom e.inv y, by
  have hy := congrArg (fun f => hom f y) e.inv_hom_id
  simpa only [hom_comp, hom_id, Representation.IntertwiningMap.comp_apply,
    Representation.IntertwiningMap.id_apply] using hy⟩

/-- `B` is a subquotient of `A` exactly when some smooth representation embeds in
`A` and maps onto `B`. -/
theorem isSubquotient_iff_exists {B A : SmoothRep.{uR, uG, uV} R G} :
    IsSubquotient B A ↔ ∃ (C : SmoothRep.{uR, uG, uV} R G) (i : C ⟶ A) (q : C ⟶ B),
      Function.Injective (hom i) ∧ Function.Surjective (hom q) := by
  constructor
  · rintro ⟨S, T, ⟨e⟩⟩
    refine ⟨subrepresentation A S, subtype A S,
      (mkQ (subrepresentation A S) T : subrepresentation A S ⟶ subquotient A S T) ≫ e.inv,
      subtype_injective A S, ?_⟩
    show Function.Surjective ((hom e.inv).comp (hom (mkQ (subrepresentation A S) T)))
    exact (hom_hom_surjective e.symm).comp (mkQ_surjective _ T)
  · rintro ⟨C, i, q, hi, hq⟩
    let S : Subrepresentation A.representation := (hom i).range
    let j : C.representation.IntertwiningMap (subrepresentation A S).representation :=
      { toLinearMap := (hom i).toLinearMap.rangeRestrict
        isIntertwining' := fun g => by
          ext v
          exact Subtype.ext (Representation.IntertwiningMap.isIntertwining _ _ (hom i) g v) }
    have hj : Function.Bijective j :=
      ⟨fun a b hab => hi (congrArg Subtype.val hab),
        fun ⟨_, v, hv⟩ => ⟨v, Subtype.ext hv⟩⟩
    let eC : C ≅ subrepresentation A S := mkIso (j.ofBijective hj)
    let q' := hom (eC.inv ≫ q)
    have hq' : Function.Surjective q' := by
      change Function.Surjective ((hom q).comp (hom eC.inv))
      exact hq.comp (hom_hom_surjective eC.symm)
    let eB : (subquotient A S q'.ker).representation.Equiv B.representation :=
      Representation.Equiv.mk (q'.toLinearMap.quotKerEquivOfSurjective hq') fun g => by
        apply Submodule.linearMap_qext
        ext v
        exact Representation.IntertwiningMap.isIntertwining _ _ q' g v
    exact ⟨S, q'.ker, ⟨(mkIso eB).symm⟩⟩

theorem IsSubquotient.of_iso_right {B A A' : SmoothRep.{uR, uG, uV} R G}
    (h : IsSubquotient B A) (e : A ≅ A') : IsSubquotient B A' := by
  obtain ⟨C, i, q, hi, hq⟩ := isSubquotient_iff_exists.mp h
  refine isSubquotient_iff_exists.mpr ⟨C, i ≫ e.hom, q, ?_, hq⟩
  rw [hom_comp]
  exact (hom_hom_injective e).comp hi

theorem IsSubquotient.of_iso_left {B B' A : SmoothRep.{uR, uG, uV} R G}
    (e : B ≅ B') (h : IsSubquotient B A) : IsSubquotient B' A := by
  obtain ⟨C, i, q, hi, hq⟩ := isSubquotient_iff_exists.mp h
  refine isSubquotient_iff_exists.mpr ⟨C, i, q ≫ e.hom, hi, ?_⟩
  rw [hom_comp]
  exact (hom_hom_surjective e).comp hq

theorem isSubquotient_iff_of_iso {B B' A A' : SmoothRep.{uR, uG, uV} R G}
    (eB : B ≅ B') (eA : A ≅ A') : IsSubquotient B A ↔ IsSubquotient B' A' :=
  ⟨fun h => IsSubquotient.of_iso_right (IsSubquotient.of_iso_left eB h) eA,
    fun h => IsSubquotient.of_iso_right (IsSubquotient.of_iso_left eB.symm h) eA.symm⟩

theorem IsSubrepresentation.isSubquotient {B A : SmoothRep.{uR, uG, uV} R G}
    (h : IsSubrepresentation B A) : IsSubquotient B A := by
  obtain ⟨j, hj⟩ := h
  exact isSubquotient_iff_exists.mpr ⟨B, j, 𝟙 B, hj, fun y => ⟨y, rfl⟩⟩

theorem IsQuotient.isSubquotient {B A : SmoothRep.{uR, uG, uV} R G}
    (h : IsQuotient B A) : IsSubquotient B A := by
  obtain ⟨q, hq⟩ := h
  exact isSubquotient_iff_exists.mpr ⟨A, 𝟙 A, q, fun _ _ h => h, hq⟩

end SmoothRep

namespace PadicField.TopologicalData

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-- The ordered block shape `(r_1, …, r_k)` of a finite family of cuspidal data of
ranks `r_i`, for any `n` equal to the sum of the ranks. -/
def cuspidalShape {k : ℕ} (ρ : Fin k → CuspidalDatum.{uV, uF} T) {n : ℕ}
    (h : ∑ i, (ρ i).rank = n) : GeneralLinear.BlockShape n where
  length := k
  size i := (ρ i).rank
  positive i := (ρ i).rank_pos
  sum_eq := h

@[simp]
theorem cuspidalShape_length {k : ℕ} (ρ : Fin k → CuspidalDatum.{uV, uF} T) {n : ℕ}
    (h : ∑ i, (ρ i).rank = n) : (T.cuspidalShape ρ h).length = k := rfl

@[simp]
theorem cuspidalShape_size {k : ℕ} (ρ : Fin k → CuspidalDatum.{uV, uF} T) {n : ℕ}
    (h : ∑ i, (ρ i).rank = n) (i : Fin k) : (T.cuspidalShape ρ h).size i = (ρ i).rank :=
  rfl

/-- `A_1 × ⋯ × A_k`: normalized parabolic induction, from the standard upper block
parabolic of shape `(r_1, …, r_k)`, of supercuspidal representations `A_i` of
`GL_(r_i)(F)`. -/
def cuspidalProductInduced {k : ℕ} (ρ : Fin k → CuspidalDatum.{uV, uF} T) {n : ℕ}
    (h : ∑ i, (ρ i).rank = n)
    (A : letI := T.topology
      ∀ i, GeneralLinear.SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := (ρ i).rank)) :
    letI := T.topology
    SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier) :=
  letI := T.topology
  (T.normalizedProductInductionFunctor (T.cuspidalShape ρ h)).obj fun i => (A i).obj

theorem cuspidalProductInduced_representation {k : ℕ}
    (ρ : Fin k → CuspidalDatum.{uV, uF} T) {n : ℕ} (h : ∑ i, (ρ i).rank = n)
    (A : letI := T.topology
      ∀ i, GeneralLinear.SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := (ρ i).rank)) :
    letI := T.topology
    (T.cuspidalProductInduced ρ h A).representation =
      T.normalizedProductInduced (T.cuspidalShape ρ h)
        (fun i => (A i).obj.representation) :=
  rfl

/-- Representatives of the same cuspidal data induce isomorphic representations. -/
def cuspidalProductInducedIsoOfRepresented {k : ℕ} {ρ : Fin k → CuspidalDatum.{uV, uF} T}
    {n : ℕ} (h : ∑ i, (ρ i).rank = n)
    {A A' : letI := T.topology
      ∀ i, GeneralLinear.SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := (ρ i).rank)}
    (hA : ∀ i, (ρ i).IsRepresentedBy (A i)) (hA' : ∀ i, (ρ i).IsRepresentedBy (A' i)) :
    T.cuspidalProductInduced ρ h A ≅ T.cuspidalProductInduced ρ h A' :=
  letI := T.topology
  (T.normalizedProductInductionFunctor (T.cuspidalShape ρ h)).mapIso
    (Pi.isoMk fun i =>
      (GeneralLinear.supercuspidalProperty (F := F.Carrier) (n := (ρ i).rank)).ι.mapIso
        (Classical.choice
          ((GeneralLinear.SupercuspidalRep.isoClass_eq_iff (A i) (A' i)).mp
            ((hA i).trans (hA' i).symm))))

variable {T}

/-- `π` is an irreducible subquotient of `ρ_1 × ⋯ × ρ_k` for actual supercuspidal
representatives of the cuspidal data `ρ_i`, whose ranks add up to `n`. This is
Zelevinsky's `ω ∈ JH(ρ_1 × ⋯ × ρ_k)`. -/
def IsCuspidalConstituent {k : ℕ} (ρ : Fin k → CuspidalDatum.{uV, uF} T) {n : ℕ}
    (π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)) : Prop :=
  letI := T.topology
  ∃ (h : ∑ i, (ρ i).rank = n)
    (A : ∀ i, GeneralLinear.SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := (ρ i).rank)),
    (∀ i, (ρ i).IsRepresentedBy (A i)) ∧ π.IsIrreducible ∧
      SmoothRep.IsSubquotient π (T.cuspidalProductInduced ρ h A)

/-- `π` is an irreducible subrepresentation of `ρ_1 × ⋯ × ρ_k` for actual
supercuspidal representatives of the cuspidal data `ρ_i`, in the given order. -/
def IsCuspidalSubrepresentation {k : ℕ} (ρ : Fin k → CuspidalDatum.{uV, uF} T) {n : ℕ}
    (π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)) : Prop :=
  letI := T.topology
  ∃ (h : ∑ i, (ρ i).rank = n)
    (A : ∀ i, GeneralLinear.SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := (ρ i).rank)),
    (∀ i, (ρ i).IsRepresentedBy (A i)) ∧
      Classification.IsIrreducibleSubrepresentation
        (T.cuspidalProductInduced ρ h A).representation π.representation

/-- The constituent relation does not depend on the chosen representatives. -/
theorem isCuspidalConstituent_iff {k : ℕ} (ρ : Fin k → CuspidalDatum.{uV, uF} T) {n : ℕ}
    (π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier))
    (h : ∑ i, (ρ i).rank = n)
    (A : letI := T.topology
      ∀ i, GeneralLinear.SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := (ρ i).rank))
    (hA : ∀ i, (ρ i).IsRepresentedBy (A i)) :
    letI := T.topology
    T.IsCuspidalConstituent ρ π ↔
      π.IsIrreducible ∧ SmoothRep.IsSubquotient π (T.cuspidalProductInduced ρ h A) := by
  let := T.topology
  constructor
  · rintro ⟨h', A', hA', hπ, hs⟩
    exact ⟨hπ, SmoothRep.IsSubquotient.of_iso_right hs
      (T.cuspidalProductInducedIsoOfRepresented h hA' hA)⟩
  · rintro ⟨hπ, hs⟩
    exact ⟨h, A, hA, hπ, hs⟩

/-- The subrepresentation relation does not depend on the chosen representatives. -/
theorem isCuspidalSubrepresentation_iff {k : ℕ} (ρ : Fin k → CuspidalDatum.{uV, uF} T)
    {n : ℕ}
    (π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier))
    (h : ∑ i, (ρ i).rank = n)
    (A : letI := T.topology
      ∀ i, GeneralLinear.SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := (ρ i).rank))
    (hA : ∀ i, (ρ i).IsRepresentedBy (A i)) :
    letI := T.topology
    T.IsCuspidalSubrepresentation ρ π ↔
      Classification.IsIrreducibleSubrepresentation
        (T.cuspidalProductInduced ρ h A).representation π.representation := by
  let := T.topology
  constructor
  · rintro ⟨h', A', hA', hs⟩
    exact Classification.IsIrreducibleSubrepresentation.of_equiv
      (SmoothRep.equivOfIso (T.cuspidalProductInducedIsoOfRepresented h hA' hA)) hs
  · intro hs
    exact ⟨h, A, hA, hs⟩

/-- An irreducible subrepresentation of `ρ_1 × ⋯ × ρ_k` is an irreducible
subquotient of it. -/
theorem IsCuspidalSubrepresentation.isCuspidalConstituent {k : ℕ}
    {ρ : Fin k → CuspidalDatum.{uV, uF} T} {n : ℕ}
    {π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)}
    (hs : T.IsCuspidalSubrepresentation ρ π) : T.IsCuspidalConstituent ρ π := by
  let := T.topology
  obtain ⟨h, A, hA, hπ, j, hj⟩ := hs
  exact ⟨h, A, hA, hπ,
    SmoothRep.IsSubrepresentation.isSubquotient ⟨SmoothRep.ofHom j, hj⟩⟩

/-- The constituent relation is invariant under isomorphism of `π`. -/
theorem IsCuspidalConstituent.of_iso {k : ℕ} {ρ : Fin k → CuspidalDatum.{uV, uF} T}
    {n : ℕ}
    {π π' : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)}
    (hs : T.IsCuspidalConstituent ρ π) (e : π ≅ π') : T.IsCuspidalConstituent ρ π' := by
  let := T.topology
  obtain ⟨h, A, hA, hπ, hsub⟩ := hs
  exact ⟨h, A, hA,
    (Weil.IsomorphismInvariance.irreducible_iff (SmoothRep.equivOfIso e)).mp hπ,
    SmoothRep.IsSubquotient.of_iso_left e hsub⟩

/-- The subrepresentation relation is invariant under isomorphism of `π`. -/
theorem IsCuspidalSubrepresentation.of_iso {k : ℕ} {ρ : Fin k → CuspidalDatum.{uV, uF} T}
    {n : ℕ}
    {π π' : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)}
    (hs : T.IsCuspidalSubrepresentation ρ π) (e : π ≅ π') :
    T.IsCuspidalSubrepresentation ρ π' := by
  let := T.topology
  obtain ⟨h, A, hA, hπ, j, hj⟩ := hs
  let e' := SmoothRep.equivOfIso e
  exact ⟨h, A, hA, (Weil.IsomorphismInvariance.irreducible_iff e').mp hπ,
    j.comp e'.symm.toIntertwiningMap, fun x y hxy => e'.symm.injective (hj hxy)⟩

/-- `s` is a supercuspidal support of `π`: some ordering `ρ_1, …, ρ_k` of the multiset
`s` of cuspidal data has `π` as an irreducible subquotient of `ρ_1 × ⋯ × ρ_k`
(Zelevinsky 1980, 1.10). -/
def IsSupercuspidalSupport {n : ℕ}
    (π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier))
    (s : Multiset (CuspidalDatum.{uV, uF} T)) : Prop :=
  ∃ (k : ℕ) (ρ : Fin k → CuspidalDatum.{uV, uF} T),
    (List.ofFn ρ : Multiset (CuspidalDatum.{uV, uF} T)) = s ∧ T.IsCuspidalConstituent ρ π

/-- Some ordering `ρ_1, …, ρ_k` of the multiset `s` has `π` as an irreducible
subrepresentation of `ρ_1 × ⋯ × ρ_k`. -/
def IsSupercuspidalEmbeddingSupport {n : ℕ}
    (π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier))
    (s : Multiset (CuspidalDatum.{uV, uF} T)) : Prop :=
  ∃ (k : ℕ) (ρ : Fin k → CuspidalDatum.{uV, uF} T),
    (List.ofFn ρ : Multiset (CuspidalDatum.{uV, uF} T)) = s ∧
      T.IsCuspidalSubrepresentation ρ π

theorem IsSupercuspidalEmbeddingSupport.isSupercuspidalSupport {n : ℕ}
    {π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)}
    {s : Multiset (CuspidalDatum.{uV, uF} T)}
    (hs : T.IsSupercuspidalEmbeddingSupport π s) : T.IsSupercuspidalSupport π s := by
  obtain ⟨k, ρ, hρ, h⟩ := hs
  exact ⟨k, ρ, hρ, h.isCuspidalConstituent⟩

theorem IsSupercuspidalSupport.of_iso {n : ℕ}
    {π π' : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)}
    {s : Multiset (CuspidalDatum.{uV, uF} T)}
    (hs : T.IsSupercuspidalSupport π s) (e : π ≅ π') : T.IsSupercuspidalSupport π' s := by
  obtain ⟨k, ρ, hρ, h⟩ := hs
  exact ⟨k, ρ, hρ, h.of_iso e⟩

theorem IsSupercuspidalEmbeddingSupport.of_iso {n : ℕ}
    {π π' : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)}
    {s : Multiset (CuspidalDatum.{uV, uF} T)}
    (hs : T.IsSupercuspidalEmbeddingSupport π s) (e : π ≅ π') :
    T.IsSupercuspidalEmbeddingSupport π' s := by
  obtain ⟨k, ρ, hρ, h⟩ := hs
  exact ⟨k, ρ, hρ, h.of_iso e⟩

/-- The ranks of a supercuspidal support add up to `n`. -/
theorem IsSupercuspidalSupport.sum_rank {n : ℕ}
    {π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)}
    {s : Multiset (CuspidalDatum.{uV, uF} T)}
    (hs : T.IsSupercuspidalSupport π s) : (s.map CuspidalDatum.rank).sum = n := by
  obtain ⟨k, ρ, rfl, h, -⟩ := hs
  rw [Multiset.map_coe, Multiset.sum_coe, List.map_ofFn, List.sum_ofFn]
  exact h

/-- A chosen supercuspidal support of `π`, and `0` if `π` has none. It is described
only when `π` has a support (`isSupercuspidalSupport_supercuspidalSupport`) and is
the support when supports of `π` are unique
(`IsSupercuspidalSupport.eq_supercuspidalSupport`). -/
def supercuspidalSupport {n : ℕ}
    (π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)) :
    Multiset (CuspidalDatum.{uV, uF} T) := by
  classical
  exact if h : ∃ s, T.IsSupercuspidalSupport π s then h.choose else 0

theorem isSupercuspidalSupport_supercuspidalSupport {n : ℕ}
    {π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)}
    (h : ∃ s, T.IsSupercuspidalSupport π s) :
    T.IsSupercuspidalSupport π (T.supercuspidalSupport π) := by
  classical
  unfold supercuspidalSupport
  split_ifs
  exact h.choose_spec

theorem IsSupercuspidalSupport.eq_supercuspidalSupport {n : ℕ}
    {π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)}
    {s : Multiset (CuspidalDatum.{uV, uF} T)}
    (huniq : ∀ s s', T.IsSupercuspidalSupport π s → T.IsSupercuspidalSupport π s' → s = s')
    (hs : T.IsSupercuspidalSupport π s) : s = T.supercuspidalSupport π :=
  huniq _ _ hs (isSupercuspidalSupport_supercuspidalSupport ⟨s, hs⟩)

end PadicField.TopologicalData

end Langlands
