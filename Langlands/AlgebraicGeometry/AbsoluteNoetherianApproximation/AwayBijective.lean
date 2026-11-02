import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.IsIso
import Mathlib.RingTheory.FiniteType

/-! # Localizations that are isomorphisms, pinched rings and finite type subrings

Three ring lemmas from Stacks Project Section 32.5 (absolute Noetherian approximation) and the
scheme statement they give.

* `bijective_awayMap_pinchedRing_snd` (More on Algebra, Lemma 15.5.3, Tag 01Z8, and the ring
  part of Limits, Lemma 32.5.2, Tag 01Z9): for the fibre product ring `B ×_R R'` of
  `s : B →+* R` and `t : R' →+* R`, and `h = (g, f)` with `s g = t f`, if `s` becomes an
  isomorphism after inverting `g`, then the projection to `R'` becomes one after inverting `h`.
* `exists_finiteType_subalgebra_bijective_awayMap` (the ring part of Limits, Lemma 32.5.1,
  Tag 01Z7): if finitely many localizations `R_{h_l}` are finite type `ℤ`-algebras, a finite
  type subring `A ⊆ R` containing the `h_l` (and any given finite set) has `A_{h_l} = R_{h_l}`.
* `isIso_SpecMap_restrict_iSup_basicOpen`: if `φ : A ⟶ R` becomes an isomorphism after
  inverting each `h_l`, then `Spec R → Spec A` is an isomorphism over `⋃ D(h_l)`.
-/

open CategoryTheory AlgebraicGeometry

universe u

noncomputable section

namespace Langlands.AlgebraicGeometry.AbsoluteNoetherianApproximation

section Pinched

variable {B R R' : Type*} [CommRing B] [CommRing R] [CommRing R']

/-- The fibre product ring `B ×_R R'` of `s : B →+* R` and `t : R' →+* R`: the subring of
`B × R'` of pairs `(b, r)` with `s b = t r`. -/
def pinchedRing (s : B →+* R) (t : R' →+* R) : Subring (B × R') :=
  RingHom.eqLocus (s.comp (RingHom.fst B R')) (t.comp (RingHom.snd B R'))

lemma mem_pinchedRing {s : B →+* R} {t : R' →+* R} {x : B × R'} :
    x ∈ pinchedRing s t ↔ s x.1 = t x.2 :=
  Iff.rfl

/-- The projection `B ×_R R' →+* B`. -/
def pinchedRing.fst (s : B →+* R) (t : R' →+* R) : pinchedRing s t →+* B :=
  (RingHom.fst B R').comp (pinchedRing s t).subtype

/-- The projection `B ×_R R' →+* R'`. -/
def pinchedRing.snd (s : B →+* R) (t : R' →+* R) : pinchedRing s t →+* R' :=
  (RingHom.snd B R').comp (pinchedRing s t).subtype

@[simp] lemma pinchedRing.fst_apply (s : B →+* R) (t : R' →+* R) (x : pinchedRing s t) :
    pinchedRing.fst s t x = (x : B × R').1 := rfl

@[simp] lemma pinchedRing.snd_apply (s : B →+* R) (t : R' →+* R) (x : pinchedRing s t) :
    pinchedRing.snd s t x = (x : B × R').2 := rfl

lemma pinchedRing.comp_fst_eq (s : B →+* R) (t : R' →+* R) :
    s.comp (pinchedRing.fst s t) = t.comp (pinchedRing.snd s t) :=
  RingHom.ext fun x => x.2

/-- Stacks, Lemma 15.5.3 (Tag 01Z8) together with Lemma 32.5.2 (Tag 01Z9) at ring level: let
`h = (g, f)` be an element of the fibre product ring `B ×_R R'`. If `B_g → R_{s g}` is bijective,
then `(B ×_R R')_h → R'_f` is bijective. -/
theorem bijective_awayMap_pinchedRing_snd (s : B →+* R) (t : R' →+* R) (h : pinchedRing s t)
    (hs : Function.Bijective (Localization.awayMap s (h : B × R').1)) :
    Function.Bijective (Localization.awayMap (pinchedRing.snd s t) h) := by
  have hs1 := Localization.awayMap_injective_iff.mp hs.1
  have hs2 := Localization.awayMap_surjective_iff.mp hs.2
  have hgf : s (h : B × R').1 = t (h : B × R').2 := mem_pinchedRing.mp h.2
  refine ⟨Localization.awayMap_injective_iff.mpr fun a ha => ?_,
    Localization.awayMap_surjective_iff.mpr fun a => ?_⟩
  · -- `a = (b, 0)` with `s b = 0`, so a power of `g` kills `b`.
    simp only [pinchedRing.snd_apply] at ha
    have hsa : s (a : B × R').1 = 0 := by
      rw [mem_pinchedRing.mp a.2, ha, map_zero]
    obtain ⟨n, hn⟩ := hs1 _ hsa
    refine ⟨n, Subtype.ext (Prod.ext ?_ ?_)⟩
    · simpa using hn
    · simp [ha]
  · -- Lift `t a` through `s` up to a power of `s g = t f`.
    obtain ⟨b, m, hb⟩ := hs2 (t a)
    refine ⟨⟨(b, (h : B × R').2 ^ m * a), ?_⟩, m, ?_⟩
    · rw [mem_pinchedRing]
      simp only [map_mul, map_pow, hb, hgf]
    · simp

end Pinched

section FiniteType

variable {R : Type u} [CommRing R]

/-- Stacks, Lemma 32.5.1 (Tag 01Z7) at ring level: let `h_l ∈ R` (finitely many) be such that
each localization `R_{h_l}` is a finite type `ℤ`-algebra, and let `T ⊆ R` be finite. Then there
is a finite type `ℤ`-subalgebra `A ⊆ R` containing `T` and all `h_l` such that every
`A_{h_l} → R_{h_l}` is bijective. -/
theorem exists_finiteType_subalgebra_bijective_awayMap {ι : Type*} [Finite ι] (h : ι → R)
    (hft : ∀ l, Algebra.FiniteType ℤ (Localization.Away (h l))) (T : Set R) (hT : T.Finite) :
    ∃ (A : Subalgebra ℤ R) (hA : ∀ l, h l ∈ A), Algebra.FiniteType ℤ A ∧ T ⊆ A ∧
      ∀ l, Function.Bijective (Localization.awayMap (A.val : A →+* R) ⟨h l, hA l⟩) := by
  classical
  have := Fintype.ofFinite ι
  -- Finite generating sets of the localizations, and numerators of their elements.
  choose S hS using fun l => (hft l).out
  have hnum : ∀ l (x : Localization.Away (h l)), ∃ (y : R) (n : ℕ),
      x = IsLocalization.mk' (Localization.Away (h l)) y
        (⟨h l ^ n, n, rfl⟩ : Submonoid.powers (h l)) := by
    intro l x
    obtain ⟨⟨y, m⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers (h l)) x
    obtain ⟨n, hn⟩ := Submonoid.mem_powers_iff _ _ |>.mp m.2
    exact ⟨y, n, congrArg (IsLocalization.mk' _ y) (Subtype.ext hn.symm)⟩
  choose num pw hnum using hnum
  let G : Set R := T ∪ Set.range h ∪ ⋃ l, (fun x => num l x) '' (S l : Set (Localization.Away (h l)))
  have hG : G.Finite :=
    ((hT.union (Set.finite_range h)).union
      (Set.finite_iUnion fun l => (S l).finite_toSet.image _))
  let A : Subalgebra ℤ R := Algebra.adjoin ℤ G
  have hGA : G ⊆ A := Algebra.subset_adjoin
  have hA : ∀ l, h l ∈ A := fun l => hGA (Or.inl (Or.inr ⟨l, rfl⟩))
  refine ⟨A, hA, ?_, fun x hx => hGA (Or.inl (Or.inl hx)), fun l => ⟨?_, ?_⟩⟩
  · rw [← Subalgebra.fg_iff_finiteType]
    obtain ⟨F, hF⟩ := hG.exists_finset_coe
    exact ⟨F, by rw [hF]⟩
  · rw [Localization.awayMap_injective_iff]
    intro a ha
    exact ⟨0, by simpa using Subtype.ext ha⟩
  · -- The range is a subring containing the generators of `R_{h_l}`.
    let φ : Localization.Away (⟨h l, hA l⟩ : A) →+* Localization.Away (h l) :=
      Localization.awayMap (A.val : A →+* R) ⟨h l, hA l⟩
    change Function.Surjective φ
    have hrange : Subring.closure (S l : Set (Localization.Away (h l))) ≤ φ.range := by
      rw [Subring.closure_le]
      intro x hx
      have hy : num l x ∈ A := hGA (Or.inr (Set.mem_iUnion.mpr ⟨l, x, hx, rfl⟩))
      refine RingHom.mem_range.mpr
        ⟨IsLocalization.mk' (Localization.Away (⟨h l, hA l⟩ : A)) (⟨num l x, hy⟩ : A)
        ⟨_, pow_mem (Submonoid.mem_powers (⟨h l, hA l⟩ : A)) (pw l x)⟩, ?_⟩
      refine Eq.trans ?_ (hnum l x).symm
      simp only [φ, IsLocalization.Away.map]
      erw [IsLocalization.map_mk']
      rfl
    intro y
    have hy : y ∈ Algebra.adjoin ℤ (S l : Set (Localization.Away (h l))) := by
      rw [hS l]; trivial
    refine RingHom.mem_range.mp (Algebra.adjoin_induction
      (fun x hx => hrange (Subring.subset_closure hx)) (fun n => ?_)
      (fun _ _ _ _ hx hy => φ.range.add_mem hx hy) (fun _ _ _ _ hx hy => φ.range.mul_mem hx hy) hy)
    rw [eq_intCast]
    exact intCast_mem φ.range n

end FiniteType

section Scheme

/-- If `φ : A ⟶ R` becomes bijective after inverting each `h_l`, then `Spec R → Spec A` is an
isomorphism over the open `⋃ D(h_l)`. -/
theorem isIso_SpecMap_restrict_iSup_basicOpen {A R : CommRingCat.{u}} (φ : A ⟶ R)
    {ι : Type*} (h : ι → A)
    (hφ : ∀ l, Function.Bijective (Localization.awayMap φ.hom (h l))) :
    IsIso (Spec.map φ ∣_ (⨆ l, PrimeSpectrum.basicOpen (h l) : (Spec A).Opens)) := by
  let D : ι → (Spec A).Opens := fun l => PrimeSpectrum.basicOpen (h l)
  change IsIso (Spec.map φ ∣_ (⨆ l, D l))
  set V : (Spec A).Opens := ⨆ l, D l
  have hle : ∀ l, D l ≤ V := le_iSup D
  have hV : ⨆ l, V.ι ⁻¹ᵁ D l = ⊤ := by
    rw [← Scheme.Hom.preimage_iSup, Scheme.Opens.ι_preimage_self]
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (P := MorphismProperty.isomorphisms Scheme) _ hV
    fun l => ?_
  have himage : V.ι ''ᵁ (V.ι ⁻¹ᵁ D l) = D l := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact inf_eq_right.mpr (hle l)
  rw [(MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
    (morphismRestrictRestrict _ _ _ ≪≫ morphismRestrictEq _ himage ≪≫
      SpecMapRestrictBasicOpenIso φ (h l))]
  have : IsIso (CommRingCat.ofHom (Localization.awayMap φ.hom (h l))) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (hφ l)
  exact (inferInstance : IsIso (Spec.map (CommRingCat.ofHom (Localization.awayMap φ.hom (h l)))))

end Scheme

end Langlands.AlgebraicGeometry.AbsoluteNoetherianApproximation
