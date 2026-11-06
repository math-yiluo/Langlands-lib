import Langlands.Cohomology.SupercuspidalRestriction.Statement
import Langlands.Representation.Category.FiniteIndexRestriction
import Langlands.Representation.Schur.CountableDimensionProof
import Langlands.Representation.CompactCoefficient.Subquotients
import Langlands.Cohomology.SupercuspidalRestriction.CompactCoefficientRestriction

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Cohomology.SupercuspidalRestriction

open Langlands.Cohomology.SupercuspidalExt (restriction HasCompactCoefficients)

namespace CompactModCenterProof

section Schur

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SigmaCompactSpace G]
  {V : Type} [AddCommGroup V] [Module ℂ V]

/-- An irreducible smooth representation of a σ-compact group has countable dimension:
the orbit of a nonzero vector spans, and it is countable because a compact set moves a
smooth vector to finitely many vectors. -/
theorem rank_le_aleph0 (ρ : Representation ℂ G V) (hρ : IsSmooth ρ) (hirr : ρ.IsIrreducible) :
    Module.rank ℂ V ≤ Cardinal.aleph0 := by
  obtain ⟨v, hv⟩ := FiniteIndexRestriction.exists_ne_zero ρ hirr
  obtain ⟨K, hK⟩ := hρ v
  have hfix : ∀ k : K.toSubgroup, ρ k v = v := fun k => hK k
  have hfin : ∀ n, ((fun g => ρ g v) '' compactCovering G n).Finite := by
    intro n
    have hc : IsCompact ((QuotientGroup.mk : G → G ⧸ K.toSubgroup) '' compactCovering G n) :=
      (isCompact_compactCovering G n).image QuotientGroup.continuous_mk
    refine (hc.finite_of_discrete.image fun q => ρ q.out v).subset ?_
    rintro _ ⟨g, hg, rfl⟩
    refine ⟨QuotientGroup.mk g, ⟨g, hg, rfl⟩, ?_⟩
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K.toSubgroup g
    show ρ (QuotientGroup.mk g : G ⧸ K.toSubgroup).out v = ρ g v
    rw [hk, map_mul, Module.End.mul_apply, hfix k]
  have hcount : (Set.range fun g => ρ g v).Countable := by
    rw [← Set.image_univ, ← iUnion_compactCovering, Set.image_iUnion]
    exact Set.countable_iUnion fun n => (hfin n).countable
  calc Module.rank ℂ V = Module.rank ℂ (⊤ : Submodule ℂ V) := (rank_top ℂ V).symm
    _ = Module.rank ℂ (Submodule.span ℂ (Set.range fun g => ρ g v)) := by
      rw [FiniteIndexRestriction.span_orbit_eq_top ρ hirr hv]
    _ ≤ Cardinal.mk (Set.range fun g => ρ g v) := rank_span_le _
    _ ≤ Cardinal.aleph0 := Cardinal.mk_le_aleph0_iff.mpr hcount.to_subtype

/-- Schur's lemma for countable dimension: the centre of a σ-compact group acts by
scalars on an irreducible smooth complex representation. -/
theorem center_acts_by_scalars (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (hirr : ρ.IsIrreducible) :
    ∀ z : Subgroup.center G, ∃ c : ℂ, ∀ v : V, ρ z v = c • v := by
  intro z
  obtain ⟨c, hc, -⟩ := countableDimensionalSchur ρ (rank_le_aleph0 ρ hρ hirr) hirr
    (Representation.IntertwiningMap.centralMul ρ (z : G) z.2)
  exact ⟨c, fun v => congrArg (fun f : ρ.IntertwiningMap ρ => f v) hc⟩

end Schur

section Lattice

/-- Greedy selection: if each `A i` is either disjoint from or below every finite
supremum of the family, then a subfamily of `t` is independent with the same supremum. -/
theorem exists_supIndep_subset {α ι : Type*} [Lattice α] [OrderBot α] [IsModularLattice α]
    [DecidableEq ι] (A : ι → α)
    (hA : ∀ i (s : Finset ι), Disjoint (A i) (s.sup A) ∨ A i ≤ s.sup A) (t : Finset ι) :
    ∃ s ⊆ t, s.SupIndep A ∧ s.sup A = t.sup A := by
  induction t using Finset.induction_on with
  | empty => exact ⟨∅, Finset.Subset.refl _, Finset.supIndep_empty _, rfl⟩
  | insert i t hi ih =>
    obtain ⟨s, hst, hs, hsup⟩ := ih
    rcases hA i s with h | h
    · exact ⟨insert i s, Finset.insert_subset_insert i hst, hs.insert h, by
        rw [Finset.sup_insert, Finset.sup_insert, hsup]⟩
    · refine ⟨s, hst.trans (Finset.subset_insert i t), hs, ?_⟩
      rw [Finset.sup_insert, ← hsup, sup_eq_right.mpr h]

end Lattice

section Decomposition

variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module ℂ V]

/-- Clifford with the centre acting by scalars: the restriction to `H` is the internal
direct sum of finitely many irreducible subrepresentations. -/
theorem exists_independent_irreducible (ρ : Representation ℂ G V) (H : Subgroup G) [H.Normal]
    [(Subgroup.center G ⊔ H).FiniteIndex] (hirr : ρ.IsIrreducible)
    (hscalar : ∀ z : Subgroup.center G, ∃ c : ℂ, ∀ v : V, ρ z v = c • v) :
    ∃ (m : ℕ) (W : Fin m → _root_.Subrepresentation (ρ.comp H.subtype)),
      (∀ i, (W i).toRepresentation.IsIrreducible) ∧
        iSupIndep (fun i => (W i).toSubmodule) ∧ (⨆ i, (W i).toSubmodule) = ⊤ := by
  classical
  have : (H ⊔ Subgroup.center G).FiniteIndex := by rw [sup_comm]; infer_instance
  obtain ⟨n, W₀, hW₀, hsup⟩ :=
    FiniteIndexRestriction.exists_finite_atoms ρ (H ⊔ Subgroup.center G) hirr
  let e := FiniteIndexRestriction.supCenterOrderIso ρ H hscalar
  let W₁ : Fin n → _root_.Subrepresentation (ρ.comp H.subtype) := fun i => e (W₀ i)
  have hW₁ : ∀ i, IsAtom (W₁ i) := fun i => (e.isAtom_iff _).mpr (hW₀ i)
  let A : Fin n → Submodule ℂ V := fun i => (W₁ i).toSubmodule
  have hsupA : ∀ s : Finset (Fin n), s.sup A = (⨆ i ∈ s, W₁ i).toSubmodule := by
    intro s
    rw [Finset.sup_eq_iSup, Langlands.Subrepresentation.toSubmodule_iSup]
    simp_rw [Langlands.Subrepresentation.toSubmodule_iSup]
    rfl
  have hA : ∀ i (s : Finset (Fin n)), Disjoint (A i) (s.sup A) ∨ A i ≤ s.sup A := by
    intro i s
    rcases (hW₁ i).le_iff.mp (inf_le_left : W₁ i ⊓ (⨆ j ∈ s, W₁ j) ≤ W₁ i) with h | h
    · left
      rw [hsupA, disjoint_iff, ← _root_.Subrepresentation.toSubmodule_inf, h]
      rfl
    · right
      rw [hsupA]
      exact fun x hx => (inf_eq_left.mp h) hx
  obtain ⟨s, -, hs, hssup⟩ := exists_supIndep_subset A hA Finset.univ
  refine ⟨s.card, fun j => W₁ (s.equivFin.symm j), fun j => ?_, ?_, ?_⟩
  · exact FiniteIndexRestriction.isIrreducible_toRepresentation_of_isAtom _ (hW₁ _)
  · exact hs.independent.comp s.equivFin.symm.injective
  · have h1 : (⨆ j, A (s.equivFin.symm j)) = s.sup A := by
      rw [Finset.sup_eq_iSup]
      apply le_antisymm
      · exact iSup_le fun j =>
          le_iSup₂_of_le (f := fun i (_ : i ∈ s) => A i) (s.equivFin.symm j).val
            (s.equivFin.symm j).property le_rfl
      · exact iSup₂_le fun i hi => le_iSup_of_le (s.equivFin ⟨i, hi⟩) (by simp)
    have h2 : Finset.univ.sup A = ⊤ := by
      rw [Finset.sup_univ_eq_iSup]
      exact hsup
    exact h1.trans (hssup.trans h2)

end Decomposition

section Projection

variable {H : Type} [Group H] {V : Type} [AddCommGroup V] [Module ℂ V]
  {ρ : Representation ℂ H V} {m : ℕ} (W : Fin m → _root_.Subrepresentation ρ)
  (hind : iSupIndep fun i => (W i).toSubmodule) (htop : (⨆ i, (W i).toSubmodule) = ⊤)

include hind htop in
theorem isCompl_iSup_ne (k : Fin m) :
    IsCompl (W k).toSubmodule (⨆ j ≠ k, (W j).toSubmodule) := by
  refine ⟨hind k, codisjoint_iff.mpr (top_unique ?_)⟩
  rw [← htop]
  refine iSup_le fun j => ?_
  by_cases h : j = k
  · subst h
    exact le_sup_left
  · exact le_sup_of_le_right (le_iSup₂_of_le (f := fun j (_ : j ≠ k) => (W j).toSubmodule)
      j h le_rfl)

/-- The projection onto the `k`-th summand along the others. -/
def proj (k : Fin m) : V →ₗ[ℂ] (W k).toSubmodule :=
  Submodule.projectionOnto _ _ (isCompl_iSup_ne W hind htop k)

theorem proj_of_mem (k : Fin m) {x : V} (hx : x ∈ (W k).toSubmodule) :
    proj W hind htop k x = ⟨x, hx⟩ :=
  Submodule.projectionOnto_apply_of_mem_left _ hx

theorem proj_of_mem_ne {j k : Fin m} (hjk : j ≠ k) {x : V} (hx : x ∈ (W j).toSubmodule) :
    proj W hind htop k x = 0 :=
  Submodule.projectionOnto_apply_of_mem_right _
    (le_iSup₂_of_le (f := fun j (_ : j ≠ k) => (W j).toSubmodule) j hjk le_rfl hx)

theorem sum_proj (x : V) : ∑ k, (proj W hind htop k x : V) = x := by
  have hx : x ∈ ⨆ i, (W i).toSubmodule := htop ▸ Submodule.mem_top
  refine Submodule.iSup_induction (fun i => (W i).toSubmodule)
    (motive := fun x => ∑ k, (proj W hind htop k x : V) = x) hx ?_ ?_ ?_
  · intro j y hy
    rw [Finset.sum_eq_single j]
    · rw [proj_of_mem W hind htop j hy]
    · intro k _ hkj
      rw [proj_of_mem_ne W hind htop (Ne.symm hkj) hy]
      rfl
    · simp
  · simp
  · intro y z hy hz
    simp only [map_add, Submodule.coe_add, Finset.sum_add_distrib, hy, hz]

theorem proj_apply (k : Fin m) (h : H) (x : V) :
    proj W hind htop k (ρ h x) = (W k).toRepresentation h (proj W hind htop k x) := by
  have hx : x ∈ ⨆ i, (W i).toSubmodule := htop ▸ Submodule.mem_top
  refine Submodule.iSup_induction (fun i => (W i).toSubmodule)
    (motive := fun x => proj W hind htop k (ρ h x) =
      (W k).toRepresentation h (proj W hind htop k x)) hx ?_ ?_ ?_
  · intro j y hy
    have hy' : ρ h y ∈ (W j).toSubmodule := (W j).apply_mem_toSubmodule h hy
    by_cases hjk : j = k
    · subst hjk
      rw [proj_of_mem W hind htop j hy', proj_of_mem W hind htop j hy]
      rfl
    · rw [proj_of_mem_ne W hind htop hjk hy', proj_of_mem_ne W hind htop hjk hy, map_zero]
  · simp
  · intro y z hy hz
    simp only [map_add, hy, hz]

end Projection

section Biproduct

variable {H : Type} [Group H] [TopologicalSpace H]

theorem hom_ext' {A B : SmoothRep.{0, 0, 0} ℂ H} {f g : A ⟶ B}
    (h : ∀ x, SmoothRep.hom f x = SmoothRep.hom g x) : f = g := by
  rw [← SmoothRep.ofHom_hom f, ← SmoothRep.ofHom_hom g]
  congr 1
  exact Representation.IntertwiningMap.ext (LinearMap.ext h)

/-- `SmoothRep.hom` as an additive map. -/
def homAddHom (A B : SmoothRep.{0, 0, 0} ℂ H) :
    (A ⟶ B) →+ A.representation.IntertwiningMap B.representation where
  toFun := SmoothRep.hom
  map_zero' := rfl
  map_add' _ _ := rfl

theorem hom_sum {A B : SmoothRep.{0, 0, 0} ℂ H} {ι : Type} (s : Finset ι) (f : ι → (A ⟶ B)) :
    SmoothRep.hom (∑ k ∈ s, f k) = ∑ k ∈ s, SmoothRep.hom (f k) :=
  map_sum (homAddHom A B) f s

/-- A subrepresentation of a smooth representation, as a smooth representation. -/
abbrev subSmooth (X : SmoothRep.{0, 0, 0} ℂ H) (S : _root_.Subrepresentation X.representation) :
    SmoothRep.{0, 0, 0} ℂ H :=
  SmoothRep.of S.toRepresentation fun w => by
    obtain ⟨K, hK⟩ := X.isSmooth w.val
    exact ⟨K, fun k => Subtype.ext (hK k)⟩

/-- The inclusion of a subrepresentation. -/
def incl (X : SmoothRep.{0, 0, 0} ℂ H) (S : _root_.Subrepresentation X.representation) :
    subSmooth X S ⟶ X :=
  SmoothRep.ofHom ⟨S.toSubmodule.subtype, fun _ => LinearMap.ext fun _ => rfl⟩

variable (X : SmoothRep.{0, 0, 0} ℂ H) {m : ℕ} (W : Fin m → _root_.Subrepresentation X.representation)
  (hind : iSupIndep fun i => (W i).toSubmodule) (htop : (⨆ i, (W i).toSubmodule) = ⊤)

include hind htop in
/-- The equivariant projection onto a summand. -/
def projHom (k : Fin m) : X ⟶ subSmooth X (W k) :=
  SmoothRep.ofHom ⟨proj W hind htop k, fun h => LinearMap.ext fun x => proj_apply W hind htop k h x⟩

include hind htop in
attribute [local instance] Abelian.hasFiniteBiproducts in
/-- An internal direct sum decomposition of a smooth representation is a biproduct. -/
theorem nonempty_iso_biproduct :
    Nonempty (X ≅ ⨁ fun k => subSmooth X (W k)) := by
  refine ⟨{ hom := biproduct.lift fun k => projHom X W hind htop k
            inv := biproduct.desc fun k => incl X (W k)
            hom_inv_id := ?_
            inv_hom_id := ?_ }⟩
  · rw [biproduct.lift_desc]
    apply hom_ext'
    intro x
    rw [hom_sum, Representation.IntertwiningMap.sum_apply]
    exact sum_proj W hind htop x
  · apply biproduct.hom_ext
    intro j
    apply biproduct.hom_ext'
    intro i
    simp only [Category.assoc, biproduct.lift_π, biproduct.ι_desc_assoc, Category.id_comp]
    rw [biproduct.ι_π]
    split_ifs with hij
    · subst hij
      apply hom_ext'
      intro x
      exact proj_of_mem W hind htop i x.property
    · apply hom_ext'
      intro x
      exact proj_of_mem_ne W hind htop hij x.property

end Biproduct

section Compact

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [LocallyCompactSpace G]

/-- Each summand of a direct sum decomposition of the restriction has compactly supported
matrix coefficients. -/
theorem hasCompactCoefficients_summand (H : Subgroup G) (hH : IsOpen (H : Set G))
    (hHZ : IsCompact ((H ⊓ Subgroup.center G : Subgroup G) : Set G))
    (π : SmoothRep.{0, 0, 0} ℂ G) (hπ : HasCompactSmoothCoefficientsModCenter π.representation)
    {m : ℕ} (W : Fin m → _root_.Subrepresentation ((restriction ℂ G H).obj π).representation)
    (hind : iSupIndep fun i => (W i).toSubmodule) (htop : (⨆ i, (W i).toSubmodule) = ⊤)
    (k : Fin m) : HasCompactCoefficients (subSmooth ((restriction ℂ G H).obj π) (W k)) := by
  have hX : HasCompactSmoothDualCoefficients ((restriction ℂ G H).obj π).representation :=
    fun v ℓ hℓ =>
      hasCompactSupport_restrict_matrixCoefficient H hH hHZ π.representation hπ ℓ hℓ v
  exact hX.of_surjective (SmoothRep.hom (projHom _ W hind htop k))
    fun w => ⟨w, proj_of_mem W hind htop k w.property⟩

end Compact

end CompactModCenterProof

open CompactModCenterProof in
/-- Proof of `CompactModCenterRestrictionStatement`. -/
theorem compactModCenterRestrictionStatement_proof (G : Type) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    [TotallyDisconnectedSpace G] [SigmaCompactSpace G] :
    CompactModCenterRestrictionStatement G := by
  intro H hN hH hHZ hfi π hirr hcmc
  have := hN
  have := hfi
  let X := (restriction ℂ G H).obj π
  have hirr' : π.representation.IsIrreducible := hirr
  obtain ⟨m, W, hWirr, hind, htop⟩ := exists_independent_irreducible π.representation H hirr'
    (center_acts_by_scalars π.representation π.isSmooth hirr')
  refine ⟨m, fun k => subSmooth X (W k), fun k => hWirr k,
    hasCompactCoefficients_summand H hH hHZ π hcmc W hind htop, ?_⟩
  exact nonempty_iso_biproduct X W hind htop

end Langlands.Cohomology.SupercuspidalRestriction
