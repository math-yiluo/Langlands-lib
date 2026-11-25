/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.GrothendieckAbelian.CardinalGeneratedCover
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Subcomplex

/-!
# The acyclic swallowing lemma

Let `C` be a Grothendieck abelian category, `G : C` a separator and `κ` a regular cardinal
dominating `ℵ₀` and the cardinalities of the subobject lattices of the finite copowers of `G`.

We prove that in an *acyclic* cochain complex `Q`, every degreewise `κ`-generated subobject `S`
is contained in a degreewise `κ`-generated subobject which is itself acyclic.

The proof is an `ω`-iteration. At each stage, the cycles of the current subcomplex which are not
yet boundaries in it are `κ`-generated; the cover lemma
`CategoryTheory.exists_isCardinalGenerated_subobject_of_epi` produces a `κ`-generated family of
subobjects of `Q` whose image under the differential contains them, and the subcomplex generated
by that family is added to the current stage. The union of the resulting chain is acyclic because
intersections commute with directed joins of subobjects in a Grothendieck abelian category.

Everything takes place in the subobject lattices of the fixed objects `Q.X n`, so no
homology-versus-colimit machinery is needed.

## Main results

- `CochainComplex.degreewiseCardinalGenerated_iSup` and
  `CochainComplex.degreewiseCardinalGenerated_subcomplexClosure`: the remaining closure
  properties of `CochainComplex.degreewiseCardinalGenerated`.
- `CochainComplex.exists_acyclic_degreewiseCardinalGenerated_le`: the swallowing lemma.
-/

@[expose] public section

universe w v u

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
  (G : C) (κ : Cardinal.{w})

section Sup

/-- A join of two `κ`-generated subobjects is `κ`-generated. -/
private lemma isCardinalGenerated_sup [Fact κ.IsRegular] {X : C} (S T : Subobject X)
    (hS : isCardinalGenerated G κ (S : C)) (hT : isCardinalGenerated G κ (T : C)) :
    isCardinalGenerated G κ ((S ⊔ T : Subobject X) : C) := by
  have h : ⨆ (b : ULift.{w} Bool), (cond b.down S T) = S ⊔ T := by
    refine le_antisymm (iSup_le ?_) (sup_le (le_iSup_of_le ⟨true⟩ le_rfl)
      (le_iSup_of_le ⟨false⟩ le_rfl))
    rintro ⟨(_ | _)⟩
    · exact le_sup_right
    · exact le_sup_left
  rw [← h]
  refine isCardinalGenerated_iSup G κ _
    (hasCardinalLT_of_finite _ _ (Fact.out (p := κ.IsRegular)).aleph0_le) ?_
  rintro ⟨(_ | _)⟩
  · exact hT
  · exact hS

end Sup

section Cover

variable {X Y : C}

omit [IsGrothendieckAbelian.{w} C] in
/-- Along a monomorphism, image pushforward of subobjects agrees with `Subobject.map`. -/
private lemma exists_obj_eq_map_obj (m : X ⟶ Y) [Mono m] (S : Subobject X) :
    (Subobject.«exists» m).obj S = (Subobject.map m).obj S := by
  rw [Subobject.exists_obj_eq_imageSubobject, Subobject.map_obj_eq_mk, imageSubobject_mono]

omit [IsGrothendieckAbelian.{w} C] in
/-- A subobject `Z` of `Y` below a subobject `I` is the image of a subobject of `I`, with the
same underlying object. -/
private lemma exists_subobject_of_le (I Z : Subobject Y) (h : Z ≤ I) :
    ∃ Z' : Subobject (I : C), (Subobject.«exists» I.arrow).obj Z' = Z ∧
      Nonempty ((Z : C) ≅ (Z' : C)) := by
  refine ⟨(Subobject.pullback I.arrow).obj Z, ?_, ?_⟩
  · rw [exists_obj_eq_map_obj, ← Subobject.inf_eq_map_pullback, inf_eq_right.2 h]
  · have h₁ : (Subobject.map I.arrow).obj ((Subobject.pullback I.arrow).obj Z) = Z := by
      rw [← Subobject.inf_eq_map_pullback, inf_eq_right.2 h]
    have h₂ : Z = Subobject.mk (((Subobject.pullback I.arrow).obj Z).arrow ≫ I.arrow) :=
      h₁.symm.trans (Subobject.map_obj_eq_mk _ _)
    exact ⟨eqToIso (congrArg (fun T : Subobject Y ↦ (T : C)) h₂) ≪≫ Subobject.underlyingIso _⟩

/-- A `κ`-generated subobject of `Y` which is contained in the image of `f : X ⟶ Y` is the
image under `f` of a `κ`-generated subobject of `X`. -/
private lemma exists_cover_of_le_imageSubobject [Fact κ.IsRegular] (hκ : Cardinal.aleph0 < κ)
    (hG : IsSeparator G) (hsub : ∀ n : ℕ, HasCardinalLT (Subobject (∐ (fun (_ : Fin n) ↦ G))) κ)
    (f : X ⟶ Y) (Z : Subobject Y) (hZle : Z ≤ imageSubobject f)
    (hZ : isCardinalGenerated G κ (Z : C)) :
    ∃ W : Subobject X, isCardinalGenerated G κ (W : C) ∧
      (Subobject.«exists» f).obj W = Z := by
  obtain ⟨Z', hZ'eq, ⟨e⟩⟩ := exists_subobject_of_le (imageSubobject f) Z hZle
  obtain ⟨W, hW, hWe⟩ := exists_isCardinalGenerated_subobject_of_epi G κ hκ hG hsub
    (factorThruImageSubobject f) Z' ((isCardinalGenerated G κ).prop_of_iso e hZ)
  refine ⟨W, hW, ?_⟩
  rw [← imageSubobject_arrow_comp f, ← Subobject.exists_obj_comp, hWe, hZ'eq]

end Cover

end CategoryTheory

namespace CochainComplex

open CategoryTheory Limits HomologicalComplex

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
  (G : C) (κ : Cardinal.{w})

/-- The degree `n` part of a subobject of a cochain complex is `κ`-generated exactly when its
degreewise evaluation in degree `n` is. -/
private lemma isCardinalGenerated_subobjectEval_iff {B : CochainComplex C ℤ} (S : Subobject B)
    (n : ℤ) :
    isCardinalGenerated G κ ((subobjectEval B n S : C)) ↔
      isCardinalGenerated G κ ((S : CochainComplex C ℤ).X n) :=
  ⟨fun h ↦ (isCardinalGenerated G κ).prop_of_iso (subobjectEvalUnderlyingIso S) h,
    fun h ↦ (isCardinalGenerated G κ).prop_of_iso (subobjectEvalUnderlyingIso S).symm h⟩

/-- A subobject of a cochain complex is degreewise `κ`-generated exactly when all its degreewise
evaluations are. -/
private lemma degreewiseCardinalGenerated_iff {B : CochainComplex C ℤ} (S : Subobject B) :
    degreewiseCardinalGenerated G κ ((S : CochainComplex C ℤ)) ↔
      ∀ n, isCardinalGenerated G κ ((subobjectEval B n S : C)) :=
  forall_congr' fun n ↦ (isCardinalGenerated_subobjectEval_iff G κ S n).symm

set_option linter.unusedVariables false in
/-- A join of fewer than `κ` many degreewise `κ`-generated subcomplexes is degreewise
`κ`-generated.

The hypothesis `hκ` is part of the standing hypotheses of this development; it is not needed
here, since the regularity of `κ` already provides `Cardinal.aleph0 ≤ κ`. -/
lemma degreewiseCardinalGenerated_iSup [Fact κ.IsRegular] (hκ : Cardinal.aleph0 < κ)
    {B : CochainComplex C ℤ} {ι : Type w} (S : ι → Subobject B) (hι : HasCardinalLT ι κ)
    (hS : ∀ i, degreewiseCardinalGenerated G κ ((S i : CochainComplex C ℤ))) :
    degreewiseCardinalGenerated G κ ((⨆ i, S i : Subobject B) : CochainComplex C ℤ) := by
  refine (degreewiseCardinalGenerated_iff G κ _).2 fun n ↦ ?_
  rw [subobjectEval_iSup]
  exact isCardinalGenerated_iSup G κ _ hι
    fun i ↦ (degreewiseCardinalGenerated_iff G κ (S i)).1 (hS i) n

/-- The subcomplex generated by a degreewise family of `κ`-generated subobjects is degreewise
`κ`-generated. -/
lemma degreewiseCardinalGenerated_subcomplexClosure [Fact κ.IsRegular]
    {B : CochainComplex C ℤ} (W : ∀ (n : ℤ), Subobject (B.X n))
    (hW : ∀ n, isCardinalGenerated G κ ((W n : C))) :
    degreewiseCardinalGenerated G κ ((subcomplexClosure B W :
      Subobject B) : CochainComplex C ℤ) := by
  refine (degreewiseCardinalGenerated_iff G κ _).2 fun n ↦ ?_
  rw [subobjectEval_subcomplexClosure]
  refine isCardinalGenerated_sup G κ _ _ (hW n) ?_
  rw [Subobject.exists_obj_eq_imageSubobject]
  exact isCardinalGenerated_of_epi G κ (factorThruImageSubobject _) (hW (n - 1))

section Swallowing

variable {Q : CochainComplex C ℤ}

omit [IsGrothendieckAbelian.{w} C] in
/-- In an acyclic complex, the cycles in degree `n` are boundaries. -/
private lemma kernelSubobject_le_imageSubobject (hQ : Q.Acyclic) (n : ℤ) :
    kernelSubobject (Q.d n (n + 1)) ≤ imageSubobject (Q.d (n - 1) n) := by
  have h := hQ n
  rw [HomologicalComplex.exactAt_iff' _ (n - 1) n (n + 1) (by simp) (by simp),
    ShortComplex.exact_iff_image_eq_kernel] at h
  simp only [HomologicalComplex.shortComplexFunctor'_obj_f,
    HomologicalComplex.shortComplexFunctor'_obj_g] at h
  exact h.ge

/-- One step of the `ω`-iteration: a degreewise `κ`-generated subobject `V` of an acyclic
complex is contained in a degreewise `κ`-generated subobject `V'` in which all the cycles
of `V` have become boundaries. -/
private lemma exists_step [Fact κ.IsRegular] (hκ : Cardinal.aleph0 < κ) (hG : IsSeparator G)
    (hsub : ∀ n : ℕ, HasCardinalLT (Subobject (∐ (fun (_ : Fin n) ↦ G))) κ)
    (hQ : Q.Acyclic) (V : Subobject Q)
    (hV : degreewiseCardinalGenerated G κ (V : CochainComplex C ℤ)) :
    ∃ V' : Subobject Q, V ≤ V' ∧
      degreewiseCardinalGenerated G κ (V' : CochainComplex C ℤ) ∧
      ∀ n : ℤ, subobjectEval Q n V ⊓ kernelSubobject (Q.d n (n + 1)) ≤
        (Subobject.«exists» (Q.d (n - 1) n)).obj (subobjectEval Q (n - 1) V') := by
  have hgen : ∀ n : ℤ, isCardinalGenerated G κ
      ((subobjectEval Q n V ⊓ kernelSubobject (Q.d n (n + 1)) : Subobject (Q.X n)) : C) :=
    fun n ↦ isCardinalGenerated_of_mono G κ hκ hG hsub
      (Subobject.ofLE _ (subobjectEval Q n V) inf_le_left)
      ((degreewiseCardinalGenerated_iff G κ V).1 hV n)
  have hle : ∀ n : ℤ, subobjectEval Q (n + 1) V ⊓ kernelSubobject (Q.d (n + 1) (n + 1 + 1)) ≤
      imageSubobject (Q.d n (n + 1)) := by
    intro n
    have h : subobjectEval Q (n + 1) V ⊓ kernelSubobject (Q.d (n + 1) (n + 1 + 1)) ≤
        imageSubobject (Q.d (n + 1 - 1) (n + 1)) :=
      inf_le_right.trans (kernelSubobject_le_imageSubobject hQ (n + 1))
    rwa [show n + 1 - 1 = n by omega] at h
  choose W hW hWe using fun n : ℤ ↦ exists_cover_of_le_imageSubobject G κ hκ hG hsub
    (Q.d n (n + 1)) _ (hle n) (hgen (n + 1))
  refine ⟨V ⊔ subcomplexClosure Q W, le_sup_left, ?_, ?_⟩
  · refine (degreewiseCardinalGenerated_iff G κ _).2 fun n ↦ ?_
    rw [subobjectEval_sup]
    exact isCardinalGenerated_sup G κ _ _ ((degreewiseCardinalGenerated_iff G κ V).1 hV n)
      ((degreewiseCardinalGenerated_iff G κ _).1
        (degreewiseCardinalGenerated_subcomplexClosure G κ W hW) n)
  · intro n
    have h := hWe (n - 1)
    rw [show n - 1 + 1 = n by omega] at h
    rw [← h]
    exact Subobject.exists_obj_mono _
      ((le_subcomplexClosure Q W (n - 1)).trans
        (monotone_subobjectEval Q (n - 1) le_sup_right))

/-- **The acyclic swallowing lemma.** In an acyclic cochain complex `Q`, every degreewise
`κ`-generated subobject is contained in a degreewise `κ`-generated acyclic subobject. -/
lemma exists_acyclic_degreewiseCardinalGenerated_le [Fact κ.IsRegular] (hκ : Cardinal.aleph0 < κ)
    (hG : IsSeparator G)
    (hsub : ∀ n : ℕ, HasCardinalLT (Subobject (∐ (fun (_ : Fin n) ↦ G))) κ)
    (hQ : Q.Acyclic) (S : Subobject Q)
    (hS : degreewiseCardinalGenerated G κ (S : CochainComplex C ℤ)) :
    ∃ (V : Subobject Q), S ≤ V ∧
      degreewiseCardinalGenerated G κ (V : CochainComplex C ℤ) ∧
      HomologicalComplex.Acyclic (V : CochainComplex C ℤ) := by
  classical
  have hcard : HasCardinalLT (ULift.{w} ℕ) κ := by
    rw [hasCardinalLT_iff_cardinal_mk_lt]
    simpa using hκ
  have key : ∀ V : { V : Subobject Q // degreewiseCardinalGenerated G κ
      (V : CochainComplex C ℤ) },
      ∃ V' : { V : Subobject Q // degreewiseCardinalGenerated G κ (V : CochainComplex C ℤ) },
        V.1 ≤ V'.1 ∧ ∀ n : ℤ, subobjectEval Q n V.1 ⊓ kernelSubobject (Q.d n (n + 1)) ≤
          (Subobject.«exists» (Q.d (n - 1) n)).obj (subobjectEval Q (n - 1) V'.1) := by
    rintro ⟨V, hV⟩
    obtain ⟨V', hle, hgen, hkey⟩ := exists_step G κ hκ hG hsub hQ V hV
    exact ⟨⟨V', hgen⟩, hle, hkey⟩
  choose F hF₁ hF₂ using key
  set A : ℕ → { V : Subobject Q // degreewiseCardinalGenerated G κ (V : CochainComplex C ℤ) } :=
    fun k ↦ Nat.rec ⟨S, hS⟩ (fun _ x ↦ F x) k with hA
  have hAsucc : ∀ k, A (k + 1) = F (A k) := fun _ ↦ rfl
  have hAmono : Monotone (fun k ↦ (A k).1) :=
    monotone_nat_of_le_succ (fun k ↦ by rw [hAsucc]; exact hF₁ (A k))
  refine ⟨⨆ k : ULift.{w} ℕ, (A k.down).1, le_iSup_of_le ⟨0⟩ le_rfl,
    degreewiseCardinalGenerated_iSup G κ hκ _ hcard (fun k ↦ (A k.down).2), ?_⟩
  refine (HomologicalComplex.acyclic_subobject_iff Q _).2 fun n ↦ ?_
  have hne : Nonempty (ULift.{w} ℕ) := ⟨⟨0⟩⟩
  have hdir : Directed (· ≤ ·) (fun k : ULift.{w} ℕ ↦ subobjectEval Q n (A k.down).1) :=
    fun i j ↦ ⟨⟨max i.down j.down⟩,
      monotone_subobjectEval Q n (hAmono (le_max_left _ _)),
      monotone_subobjectEval Q n (hAmono (le_max_right _ _))⟩
  have hinf : subobjectEval Q n (⨆ k : ULift.{w} ℕ, (A k.down).1) ⊓
      kernelSubobject (Q.d n (n + 1)) =
      ⨆ k : ULift.{w} ℕ, (subobjectEval Q n (A k.down).1 ⊓
        kernelSubobject (Q.d n (n + 1))) := by
    rw [subobjectEval_iSup, inf_comm, IsGrothendieckAbelian.inf_iSup_of_directed _ _ hdir]
    exact iSup_congr fun k ↦ inf_comm _ _
  rw [hinf]
  refine iSup_le fun k ↦ (hF₂ (A k.down) n).trans (Subobject.exists_obj_mono _ ?_)
  refine monotone_subobjectEval Q (n - 1) (le_iSup_of_le ⟨k.down + 1⟩ (le_of_eq ?_))
  rw [hAsucc]

end Swallowing

end CochainComplex
