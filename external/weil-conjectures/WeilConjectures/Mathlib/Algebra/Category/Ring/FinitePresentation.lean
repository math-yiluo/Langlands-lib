/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Category.Ring.FinitePresentation
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Finitely presented algebras descend along filtered colimits of rings

Let `R = colim Rᵢ` be a filtered colimit of commutative rings and let `S` be an `R`-algebra
of finite presentation. Then `S` is already defined over one of the `Rᵢ`, i.e. there is an
index `i` and an `Rᵢ`-algebra `T` of finite presentation with `S ≅ T ⊗[Rᵢ] R`.

## Main results

- `CommRingCat.exists_isPushout_quotient_span`: if `S` is the quotient of a polynomial ring
  over `R` by relations that are defined over an `R`-algebra `A`, then `S` is the base change
  of the corresponding quotient over `A`.
- `CommRingCat.exists_isPushout_of_finitePresentation`: the descent statement above.
- `CommRingCat.exists_isPushout_of_finitePresentation_of_surjective`: if moreover `S` is a
  quotient of `R`, then `T` can be chosen to be a quotient of `Rᵢ`.

## References

- [Stacks: Tag 00R4](https://stacks.math.columbia.edu/tag/00R4)
- [EGA IV, 8.8.2]
-/

@[expose] public section

universe vJ uJ u

open CategoryTheory Limits

namespace CommRingCat

/-- Let `π : A[x₁, …, xₙ] ⊗_A R = R[x₁, …, xₙ] → S` be a surjection whose kernel is generated
by polynomials `r x` with coefficients in `A`. Then `S` is the base change along `A ⟶ R` of
the quotient of `A[x₁, …, xₙ]` by the `r x`. -/
lemma exists_isPushout_quotient_span {A R S : CommRingCat.{u}} (φ : A ⟶ R) {n : ℕ}
    {γ : Type*} (r : γ → MvPolynomial (Fin n) A) (π : of (MvPolynomial (Fin n) R) ⟶ S)
    (hπ : Function.Surjective π)
    (hr : RingHom.ker π.hom = Ideal.span (Set.range fun x ↦ MvPolynomial.map φ.hom (r x))) :
    ∃ h : of (MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range r)) ⟶ S,
      IsPushout φ (ofHom MvPolynomial.C ≫ ofHom (Ideal.Quotient.mk (Ideal.span (Set.range r))))
        (ofHom MvPolynomial.C ≫ π) h := by
  set K : Ideal (MvPolynomial (Fin n) A) := Ideal.span (Set.range r) with hK
  set q : of (MvPolynomial (Fin n) A) ⟶ of (MvPolynomial (Fin n) A ⧸ K) :=
    ofHom (Ideal.Quotient.mk K) with hq
  set ψ : of (MvPolynomial (Fin n) A) ⟶ of (MvPolynomial (Fin n) R) :=
    ofHom (MvPolynomial.map φ.hom) with hψ
  have hKle : K ≤ RingHom.ker (ψ ≫ π).hom := by
    rw [hK, Ideal.span_le]
    rintro _ ⟨x, rfl⟩
    change MvPolynomial.map φ.hom (r x) ∈ RingHom.ker π.hom
    rw [hr]
    exact Ideal.subset_span ⟨x, rfl⟩
  refine ⟨ofHom (Ideal.Quotient.lift K (ψ ≫ π).hom fun a ha ↦ RingHom.mem_ker.mp (hKle ha)), ?_⟩
  set h : of (MvPolynomial (Fin n) A ⧸ K) ⟶ S :=
    ofHom (Ideal.Quotient.lift K (ψ ≫ π).hom fun a ha ↦ RingHom.mem_ker.mp (hKle ha)) with hh
  -- The three facts about `q` and `h` that are used below.
  have hcomp : ∀ p : MvPolynomial (Fin n) A,
      h.hom (q.hom p) = π.hom (MvPolynomial.map φ.hom p) := by
    intro p
    rw [hh, hq]
    simp [hψ]
  have hqzero : ∀ x, q.hom (r x) = 0 := by
    intro x
    rw [hq]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hK ▸ Ideal.subset_span ⟨x, rfl⟩)
  -- Evaluating a polynomial with coefficients in `A` at a cocone can be done over `A`.
  have key : ∀ (W : CommRingCat.{u}) (u : R ⟶ W) (v : of (MvPolynomial (Fin n) A ⧸ K) ⟶ W),
      φ ≫ u = (ofHom MvPolynomial.C ≫ q) ≫ v → ∀ p : MvPolynomial (Fin n) A,
        MvPolynomial.eval₂ u.hom (fun k ↦ v.hom (q.hom (MvPolynomial.X k)))
          (MvPolynomial.map φ.hom p) = v.hom (q.hom p) := by
    intro W u v huv p
    rw [MvPolynomial.eval₂_map]
    have h1 : u.hom.comp φ.hom = v.hom.comp (q.hom.comp MvPolynomial.C) := by
      have := congrArg CommRingCat.Hom.hom huv
      simpa only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_assoc] using this
    have h2 : MvPolynomial.eval₂Hom (q.hom.comp MvPolynomial.C)
        (fun k ↦ q.hom (MvPolynomial.X k)) = q.hom :=
      MvPolynomial.ringHom_ext (fun a ↦ by simp) (fun k ↦ by simp)
    have h4 : MvPolynomial.eval₂Hom (v.hom.comp (q.hom.comp MvPolynomial.C))
        (fun k ↦ v.hom (q.hom (MvPolynomial.X k))) = v.hom.comp q.hom := by
      rw [← MvPolynomial.comp_eval₂Hom, h2]
    rw [h1]
    simpa using DFunLike.congr_fun h4 p
  -- The descent map out of `S` attached to a cocone, and its defining property.
  have hker : ∀ (W : CommRingCat.{u}) (u : R ⟶ W) (v : of (MvPolynomial (Fin n) A ⧸ K) ⟶ W),
      φ ≫ u = (ofHom MvPolynomial.C ≫ q) ≫ v → RingHom.ker π.hom ≤
        RingHom.ker (MvPolynomial.eval₂Hom u.hom fun k ↦ v.hom (q.hom (MvPolynomial.X k))) := by
    intro W u v huv
    rw [hr, Ideal.span_le, Set.range_subset_iff]
    intro x
    change MvPolynomial.eval₂ u.hom (fun k ↦ v.hom (q.hom (MvPolynomial.X k)))
      (MvPolynomial.map φ.hom (r x)) = 0
    rw [key _ u v huv, hqzero, map_zero]
  set desc : ∀ (W : CommRingCat.{u}) (u : R ⟶ W) (v : of (MvPolynomial (Fin n) A ⧸ K) ⟶ W),
      φ ≫ u = (ofHom MvPolynomial.C ≫ q) ≫ v → (S ⟶ W) :=
    fun W u v huv ↦ ofHom (RingHom.liftOfSurjective π.hom hπ ⟨_, hker W u v huv⟩) with hdescdef
  have hdesc : ∀ (W : CommRingCat.{u}) (u : R ⟶ W) (v : of (MvPolynomial (Fin n) A ⧸ K) ⟶ W)
      (huv : φ ≫ u = (ofHom MvPolynomial.C ≫ q) ≫ v) (p : MvPolynomial (Fin n) R),
      (desc W u v huv).hom (π.hom p) =
        MvPolynomial.eval₂ u.hom (fun k ↦ v.hom (q.hom (MvPolynomial.X k))) p := by
    intro W u v huv p
    rw [hdescdef]
    exact RingHom.liftOfSurjective_comp_apply π.hom hπ ⟨_, hker W u v huv⟩ p
  refine ⟨⟨?_⟩, ⟨PushoutCocone.IsColimit.mk _ (fun t ↦ desc _ t.inl t.inr t.condition)
    ?_ ?_ ?_⟩⟩
  · refine CommRingCat.hom_ext (RingHom.ext fun a ↦ ?_)
    change π.hom (MvPolynomial.C (φ.hom a)) = h.hom (q.hom (MvPolynomial.C a))
    rw [hcomp, MvPolynomial.map_C]
  · intro t
    refine CommRingCat.hom_ext (RingHom.ext fun a ↦ ?_)
    change (desc _ t.inl t.inr t.condition).hom (π.hom (MvPolynomial.C a)) = t.inl.hom a
    rw [hdesc _ t.inl t.inr t.condition, MvPolynomial.eval₂_C]
  · intro t
    refine CommRingCat.hom_ext (RingHom.ext fun x ↦ ?_)
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    change (desc _ t.inl t.inr t.condition).hom (h.hom (q.hom p)) = t.inr.hom (q.hom p)
    rw [hcomp, hdesc _ t.inl t.inr t.condition]
    exact key _ t.inl t.inr t.condition p
  · intro t m hm₁ hm₂
    have hmφ : m.hom.comp π.hom =
        MvPolynomial.eval₂Hom t.inl.hom (fun k ↦ t.inr.hom (q.hom (MvPolynomial.X k))) := by
      refine MvPolynomial.ringHom_ext (fun a ↦ ?_) (fun k ↦ ?_)
      · rw [MvPolynomial.eval₂Hom_C]
        exact congrArg (fun φ ↦ CommRingCat.Hom.hom φ a) hm₁
      · rw [MvPolynomial.eval₂Hom_X']
        change m.hom (π.hom (MvPolynomial.X k)) = t.inr.hom (q.hom (MvPolynomial.X k))
        rw [show π.hom (MvPolynomial.X k) = h.hom (q.hom (MvPolynomial.X k)) by
          rw [hcomp, MvPolynomial.map_X]]
        exact congrArg (fun φ ↦ CommRingCat.Hom.hom φ (q.hom (MvPolynomial.X k))) hm₂
    refine CommRingCat.hom_ext (RingHom.ext fun x ↦ ?_)
    obtain ⟨y, rfl⟩ := hπ x
    change m.hom (π.hom y) = (desc _ t.inl t.inr t.condition).hom (π.hom y)
    rw [hdesc _ t.inl t.inr t.condition]
    exact DFunLike.congr_fun hmφ y

variable {J : Type uJ} [Category.{vJ} J] [IsFiltered J] (F : J ⥤ CommRingCat.{u})
  (c : Cocone F) [PreservesColimit F (forget CommRingCat)] {σ : Type*}

omit [IsFiltered J] [PreservesColimit F (forget CommRingCat)] in
/-- The polynomials over `F.obj j` that are visible in the colimit only grow along the
transition maps. -/
lemma range_map_ι_app_subset {j k : J} (α : j ⟶ k) :
    Set.range (MvPolynomial.map (σ := σ) (c.ι.app j).hom) ⊆
      Set.range (MvPolynomial.map (σ := σ) (c.ι.app k).hom) := by
  have h : (c.ι.app k).hom.comp (F.map α).hom = (c.ι.app j).hom :=
    congrArg CommRingCat.Hom.hom (c.w α)
  rintro _ ⟨p, rfl⟩
  exact ⟨MvPolynomial.map (F.map α).hom p, by rw [MvPolynomial.map_map, h]; rfl⟩

variable (hc : IsColimit c)

include hc in
/-- Every polynomial over a filtered colimit of rings is defined over a finite stage. -/
lemma exists_mem_range_map_ι_app (p : MvPolynomial σ c.pt) :
    ∃ j, p ∈ Set.range (MvPolynomial.map (σ := σ) (c.ι.app j).hom) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    obtain ⟨j, y, hy⟩ :=
      Types.jointly_surjective_of_isColimit (isColimitOfPreserves (forget _) hc)
        (show ((forget CommRingCat).mapCocone c).pt from a)
    exact ⟨j, MvPolynomial.C y, by rw [MvPolynomial.map_C]; exact congrArg MvPolynomial.C hy⟩
  | add p q hp hq =>
    obtain ⟨j, p, rfl⟩ := hp
    obtain ⟨k, q, rfl⟩ := hq
    obtain ⟨p', hp'⟩ := range_map_ι_app_subset F c (IsFiltered.leftToMax j k) ⟨p, rfl⟩
    obtain ⟨q', hq'⟩ := range_map_ι_app_subset F c (IsFiltered.rightToMax j k) ⟨q, rfl⟩
    exact ⟨IsFiltered.max j k, p' + q', by rw [map_add]; exact congrArg₂ (· + ·) hp' hq'⟩
  | mul_X p n hp =>
    obtain ⟨j, p, rfl⟩ := hp
    exact ⟨j, p * MvPolynomial.X n, by
      rw [map_mul]
      exact congrArg (MvPolynomial.map (c.ι.app j).hom p * ·) (MvPolynomial.map_X _ _)⟩

include hc in
/-- Finitely many polynomials over a filtered colimit of rings are all defined over a common
finite stage. -/
lemma exists_forall_mem_range_map_ι_app (s : Finset (MvPolynomial σ c.pt)) :
    ∃ j, ∀ p ∈ s, p ∈ Set.range (MvPolynomial.map (σ := σ) (c.ι.app j).hom) := by
  classical
  choose j hj using fun p : s ↦ exists_mem_range_map_ι_app F c hc (p : MvPolynomial σ c.pt)
  obtain ⟨k, hk⟩ := IsFiltered.sup_objs_exists (Finset.univ.image j)
  refine ⟨k, fun p hp ↦ ?_⟩
  obtain ⟨α⟩ := hk (Finset.mem_image_of_mem j (Finset.mem_univ (⟨p, hp⟩ : s)))
  exact range_map_ι_app_subset F c α (hj ⟨p, hp⟩)

include hc in
/-- Finitely many elements of a filtered colimit of rings all lift to a common finite
stage. -/
lemma exists_forall_mem_range_ι_app (s : Finset c.pt) :
    ∃ j, ∀ x ∈ s, x ∈ Set.range (c.ι.app j) := by
  classical
  have key : ∀ x : s, ∃ (j : J) (y : F.obj j), (c.ι.app j).hom y = (x : c.pt) := by
    intro x
    obtain ⟨j, y, hy⟩ :=
      Types.jointly_surjective_of_isColimit (isColimitOfPreserves (forget _) hc)
        (show ((forget CommRingCat).mapCocone c).pt from (x : c.pt))
    exact ⟨j, y, hy⟩
  choose j y hy using key
  obtain ⟨k, hk⟩ := IsFiltered.sup_objs_exists (Finset.univ.image j)
  refine ⟨k, fun x hx ↦ ?_⟩
  obtain ⟨α⟩ := hk (Finset.mem_image_of_mem j (Finset.mem_univ (⟨x, hx⟩ : s)))
  have hw : ∀ a, (c.ι.app k).hom ((F.map α).hom a) = (c.ι.app (j ⟨x, hx⟩)).hom a := fun a ↦
    DFunLike.congr_fun (congrArg CommRingCat.Hom.hom (c.w α)) a
  exact ⟨(F.map α).hom (y ⟨x, hx⟩), (hw (y ⟨x, hx⟩)).trans (hy ⟨x, hx⟩)⟩

include hc in
/-- **Finitely presented algebras descend along filtered colimits of rings.**

If `S` is an algebra of finite presentation over the colimit `c.pt` of a filtered diagram `F`
of commutative rings, then `S` is the base change of an algebra `T` of finite presentation
over one of the `F.obj j`. -/
@[stacks 00R4]
theorem exists_isPushout_of_finitePresentation {S : CommRingCat.{u}} (f : c.pt ⟶ S)
    (hf : f.hom.FinitePresentation) :
    ∃ (j : J) (T : CommRingCat.{u}) (g : F.obj j ⟶ T) (_ : g.hom.FinitePresentation)
      (h : T ⟶ S), IsPushout (c.ι.app j) g f h := by
  classical
  let := f.hom.toAlgebra
  obtain ⟨n, hn⟩ := hf
  -- Present `S` as a quotient of a polynomial ring over `c.pt` by a finitely generated ideal.
  obtain ⟨π, rfl, hπ, s, hs⟩ :
      ∃ π : CommRingCat.of (MvPolynomial (Fin n) c.pt) ⟶ S,
        ofHom MvPolynomial.C ≫ π = f ∧ Function.Surjective π ∧ (RingHom.ker π.hom).FG := by
    obtain ⟨π, h₁, h₂⟩ := hn
    exact ⟨ofHom π, by ext1; exact π.comp_algebraMap, h₁, h₂⟩
  -- All of the finitely many relations are already defined over some stage `i`.
  obtain ⟨i, hi⟩ := exists_forall_mem_range_map_ι_app F c hc s
  choose lift hlift using fun p : s ↦ hi p p.2
  have hrange : (↑s : Set (MvPolynomial (Fin n) c.pt)) =
      Set.range fun x ↦ MvPolynomial.map (c.ι.app i).hom (lift x) := by
    refine Set.ext fun p ↦ ⟨fun hp ↦ ⟨⟨p, hp⟩, hlift ⟨p, hp⟩⟩, ?_⟩
    rintro ⟨x, hx⟩
    exact Set.mem_of_eq_of_mem (hx.symm.trans (hlift x)) (Finset.mem_coe.mpr x.2)
  obtain ⟨h, hpush⟩ := exists_isPushout_quotient_span (R := c.pt) (c.ι.app i) lift π hπ
    (by rw [← hs, hrange]; rfl)
  refine ⟨i, _, _, ?_, h, hpush⟩
  change ((Ideal.Quotient.mk (Ideal.span (Set.range lift))).comp MvPolynomial.C).FinitePresentation
  refine RingHom.FinitePresentation.comp
    (RingHom.FinitePresentation.of_surjective _ Ideal.Quotient.mk_surjective ?_) ?_
  · rw [Ideal.mk_ker]
    exact ⟨Finset.univ.image lift, by simp⟩
  · have := RingHom.finitePresentation_algebraMap
      (A := (F.obj i : Type u)) (B := MvPolynomial (Fin n) (F.obj i))
    rw [MvPolynomial.algebraMap_eq] at this
    exact this.mpr inferInstance

include hc in
/-- **Finitely presented quotients descend along filtered colimits of rings.**

If `S` is the quotient of the colimit `c.pt` of a filtered diagram `F` of commutative rings
by a finitely generated ideal — equivalently, `f : c.pt ⟶ S` is surjective and of finite
presentation — then `S` is the base change of a finitely presented quotient of one of the
`F.obj j`. -/
theorem exists_isPushout_of_finitePresentation_of_surjective {S : CommRingCat.{u}}
    (f : c.pt ⟶ S) (hf : f.hom.FinitePresentation) (hsurj : Function.Surjective f) :
    ∃ (j : J) (T : CommRingCat.{u}) (g : F.obj j ⟶ T) (_ : g.hom.FinitePresentation)
      (_ : Function.Surjective g) (h : T ⟶ S), IsPushout (c.ι.app j) g f h := by
  classical
  have hsurj' : Function.Surjective f.hom := hsurj
  -- The kernel of `f` is finitely generated.
  obtain ⟨s, hs⟩ : (RingHom.ker f.hom).FG := by
    let := f.hom.toAlgebra
    have : Algebra.FinitePresentation c.pt S := hf
    exact Algebra.FinitePresentation.ker_fG_of_surjective (Algebra.ofId c.pt S) hsurj'
  -- Lift the generators of the kernel to a common stage `j`.
  obtain ⟨j, hj⟩ := exists_forall_mem_range_ι_app F c hc s
  choose lift hlift₀ using fun x : s ↦ hj x x.2
  have hlift : ∀ x : s, (c.ι.app j).hom (lift x) = (x : c.pt) := fun x ↦ hlift₀ x
  set I : Ideal (F.obj j) := Ideal.span (Set.range lift) with hI
  -- The quotient by the lifted generators is a finitely presented quotient.
  have hmkfp : (Ideal.Quotient.mk I).FinitePresentation := by
    refine RingHom.FinitePresentation.of_surjective _ Ideal.Quotient.mk_surjective ?_
    rw [Ideal.mk_ker]
    exact ⟨s.attach.image lift, by rw [hI]; simp⟩
  -- The generators die in `S`, so the quotient maps to `S`.
  have hmem : ∀ x : s, f.hom (x : c.pt) = 0 := fun x ↦ by
    have hx : (x : c.pt) ∈ RingHom.ker f.hom := by rw [← hs]; exact Ideal.subset_span x.2
    exact RingHom.mem_ker.mp hx
  have hIle : I ≤ RingHom.ker (f.hom.comp (c.ι.app j).hom) := by
    rw [hI, Ideal.span_le]
    rintro - ⟨x, rfl⟩
    refine RingHom.mem_ker.mpr ?_
    change f.hom ((c.ι.app j).hom (lift x)) = 0
    rw [hlift x]
    exact hmem x
  set h : CommRingCat.of (F.obj j ⧸ I) ⟶ S :=
    ofHom (Ideal.Quotient.lift I (f.hom.comp (c.ι.app j).hom)
      fun a ha ↦ RingHom.mem_ker.mp (hIle ha)) with hhdef
  have hcomp : ∀ a : F.obj j, h.hom (Ideal.Quotient.mk I a) = f.hom ((c.ι.app j).hom a) :=
    fun a ↦ rfl
  -- The maps out of `S` induced by a pushout cocone, and their defining property.
  have hker_le : ∀ (W : CommRingCat.{u}) (u : c.pt ⟶ W) (v : CommRingCat.of (F.obj j ⧸ I) ⟶ W),
      c.ι.app j ≫ u = ofHom (Ideal.Quotient.mk I) ≫ v →
        RingHom.ker f.hom ≤ RingHom.ker u.hom := by
    intro W u v huv
    rw [← hs, Ideal.span_le]
    intro x hx
    refine RingHom.mem_ker.mpr ?_
    have h1 : u.hom ((c.ι.app j).hom (lift ⟨x, hx⟩)) =
        v.hom (Ideal.Quotient.mk I (lift ⟨x, hx⟩)) :=
      DFunLike.congr_fun (congrArg CommRingCat.Hom.hom huv) (lift ⟨x, hx⟩)
    have h2 : Ideal.Quotient.mk I (lift ⟨x, hx⟩) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (hI ▸ Ideal.subset_span ⟨⟨x, hx⟩, rfl⟩)
    change u.hom x = 0
    calc u.hom x = u.hom ((c.ι.app j).hom (lift ⟨x, hx⟩)) := by rw [hlift ⟨x, hx⟩]
      _ = v.hom (Ideal.Quotient.mk I (lift ⟨x, hx⟩)) := h1
      _ = 0 := by rw [h2, map_zero]
  set desc : ∀ (W : CommRingCat.{u}) (u : c.pt ⟶ W) (v : CommRingCat.of (F.obj j ⧸ I) ⟶ W),
      c.ι.app j ≫ u = ofHom (Ideal.Quotient.mk I) ≫ v → (S ⟶ W) :=
    fun W u v huv ↦ ofHom (RingHom.liftOfSurjective f.hom hsurj'
      ⟨u.hom, hker_le W u v huv⟩) with hdescdef
  have hdesc : ∀ (W : CommRingCat.{u}) (u : c.pt ⟶ W) (v : CommRingCat.of (F.obj j ⧸ I) ⟶ W)
      (huv : c.ι.app j ≫ u = ofHom (Ideal.Quotient.mk I) ≫ v) (a : c.pt),
      (desc W u v huv).hom (f.hom a) = u.hom a :=
    fun W u v huv a ↦ RingHom.liftOfSurjective_comp_apply f.hom hsurj' _ a
  refine ⟨j, CommRingCat.of (F.obj j ⧸ I), ofHom (Ideal.Quotient.mk I),
    (by simpa using hmkfp), Ideal.Quotient.mk_surjective, h, ⟨?_⟩,
    ⟨PushoutCocone.IsColimit.mk _ (fun t ↦ desc _ t.inl t.inr t.condition) ?_ ?_ ?_⟩⟩
  · exact CommRingCat.hom_ext (RingHom.ext fun a ↦ (hcomp a).symm)
  · intro t
    exact CommRingCat.hom_ext (RingHom.ext fun a ↦ hdesc _ t.inl t.inr t.condition a)
  · intro t
    refine CommRingCat.hom_ext (RingHom.ext fun x ↦ ?_)
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective (I := I) x
    change (desc _ t.inl t.inr t.condition).hom (h.hom (Ideal.Quotient.mk I a)) =
      t.inr.hom (Ideal.Quotient.mk I a)
    rw [hcomp a, hdesc _ t.inl t.inr t.condition]
    exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom t.condition) a
  · intro t m hm₁ hm₂
    refine CommRingCat.hom_ext (RingHom.ext fun x ↦ ?_)
    obtain ⟨a, rfl⟩ := hsurj' x
    rw [hdesc _ t.inl t.inr t.condition]
    exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom hm₁) a

end CommRingCat
