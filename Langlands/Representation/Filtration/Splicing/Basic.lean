import Langlands.Representation.Filtration.QuotientTail
import Langlands.Representation.Filtration.IsoTransport
import Mathlib.Data.Fin.Tuple.Basic

/-! Splicing and refinement of actual natural representation filtrations. -/

noncomputable section
open CategoryTheory

namespace Langlands

universe uR uG uV uC vC

variable {R : Type uR} [CommRing R] {G : Type uG} [Monoid G]
  {C : Type uC} [Category.{vC} C]
  {L M Q : C ⥤ Rep.{uV} R G}

namespace RepSubfunctor

@[ext]
theorem ext_obj {S T : RepSubfunctor M} (h : ∀ X, S.obj X = T.obj X) : S = T := by
  cases S
  cases T
  congr
  funext X
  exact h X

/-- The actual inverse images of invariant submodules under a natural map. -/
def inverseImage (S : RepSubfunctor Q) (π : M ⟶ Q) : RepSubfunctor M where
  obj X :=
    { toSubmodule := (S.obj X).toSubmodule.comap (π.app X).hom.toLinearMap
      apply_mem_toSubmodule := by
        intro g v hv
        change (π.app X).hom ((M.obj X).ρ g v) ∈ S.obj X
        rw [Rep.hom_comm_apply]
        exact (S.obj X).apply_mem_toSubmodule g hv }
  map_mem := by
    intro X Y f v hv
    change (π.app Y).hom ((M.map f).hom v) ∈ S.obj Y
    have he := congrArg (fun k => k.hom v) (π.naturality f)
    change (π.app Y).hom ((M.map f).hom v) =
      (Q.map f).hom ((π.app X).hom v) at he
    rw [he]
    exact S.map_mem f hv

@[simp]
theorem mem_inverseImage (S : RepSubfunctor Q) (π : M ⟶ Q) (X : C) (v : M.obj X) :
    v ∈ (S.inverseImage π).obj X ↔ (π.app X).hom v ∈ S.obj X := Iff.rfl

/-- Restriction of the ambient map to an inverse image and its target subfunctor. -/
def inverseImageHom (S : RepSubfunctor Q) (π : M ⟶ Q) :
    (S.inverseImage π).toFunctor ⟶ S.toFunctor where
  app X := Rep.ofHom
    { toLinearMap :=
        { toFun := fun v => ⟨(π.app X).hom v, v.property⟩
          map_add' := by intros; apply Subtype.ext; exact map_add _ _ _
          map_smul' := by intros; apply Subtype.ext; exact map_smul _ _ _ }
      isIntertwining' := by
        intro g
        ext v
        exact Rep.hom_comm_apply (π.app X) g v }
  naturality := by
    intro X Y f
    ext v
    apply Subtype.ext
    exact congrArg (fun k => k.hom (v : (S.inverseImage π).representation X).val)
      (π.naturality f)

theorem inverseImageHom_surjective (S : RepSubfunctor Q) (π : M ⟶ Q)
    (hsurj : ∀ X, Function.Surjective (π.app X).hom) (X : C) :
    Function.Surjective ((S.inverseImageHom π).app X).hom := by
  intro v
  obtain ⟨w, hw⟩ := hsurj X (v : S.representation X).val
  refine ⟨⟨w, ?_⟩, Subtype.ext hw⟩
  change (π.app X).hom w ∈ S.obj X
  rw [hw]
  exact v.property

/-- Quotients of two inverse images are naturally the corresponding quotients
when the ambient map is componentwise surjective. -/
def inverseImageQuotientIso (S T : RepSubfunctor Q) (π : M ⟶ Q)
    (hsurj : ∀ X, Function.Surjective (π.app X).hom) :
    (S.inverseImage π).quotientFunctor (T.inverseImage π) ≅ S.quotientFunctor T := by
  let α := T.inverseImageHom π ≫ S.quotientNatProjection T
  apply (S.inverseImage π).quotientNatIsoOfSurjective (T.inverseImage π) α
  · intro X v
    change (π.app X).hom v ∈ S.obj X ↔
      (Submodule.Quotient.mk
        (⟨(π.app X).hom v, v.property⟩ : T.representation X) :
          S.quotientObj T X) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    rfl
  · intro X v
    obtain ⟨w, rfl⟩ := S.quotientProjection_surjective T X v
    obtain ⟨v, rfl⟩ := T.inverseImageHom_surjective π hsurj X w
    exact ⟨v, rfl⟩

/-- An injection preserves all actual successive quotients of image subfunctors. -/
def injectiveImageQuotientIso (S T : RepSubfunctor L) (ι : L ⟶ M)
    (hinj : ∀ X, Function.Injective (ι.app X).hom) :
    (S.directImage ι).quotientFunctor (T.directImage ι) ≅ S.quotientFunctor T :=
  (S.directImageQuotientIso T ι (by
    intro X v hv
    have he : v = 0 := hinj X (hv.trans (map_zero _).symm)
    rw [he]
    exact (S.obj X).toSubmodule.zero_mem)).symm

end RepSubfunctor

namespace RepFunctorFiltration

variable {n m : ℕ}

/-- Indices of the first block of steps, including the junction. -/
def spliceLeftStep (n m : ℕ) (i : Fin (n + 1)) : Fin (n + m + 1) :=
  ⟨i.val, by omega⟩

/-- Indices of the second block of steps, including the junction. -/
def spliceRightStep (n m : ℕ) (i : Fin (m + 1)) : Fin (n + m + 1) :=
  ⟨n + i.val, by omega⟩

/-- Images before the junction and inverse images after it. -/
def spliceStep (sL : RepFunctorFiltration L n) (sQ : RepFunctorFiltration Q m)
    (ι : L ⟶ M) (π : M ⟶ Q) (i : Fin (n + m + 1)) : RepSubfunctor M :=
  if h : i.val ≤ n then (sL.step ⟨i.val, by omega⟩).directImage ι
  else (sQ.step ⟨i.val - n, by omega⟩).inverseImage π

theorem spliceStep_left (sL : RepFunctorFiltration L n)
    (sQ : RepFunctorFiltration Q m) (ι : L ⟶ M) (π : M ⟶ Q)
    (i : Fin (n + 1)) :
    spliceStep sL sQ ι π (spliceLeftStep n m i) = (sL.step i).directImage ι := by
  simp [spliceStep, spliceLeftStep, show i.val ≤ n by omega]

/-- Exactness identifies the two actual subfunctors at the junction. -/
theorem splice_junction (sL : RepFunctorFiltration L n)
    (sQ : RepFunctorFiltration Q m) (ι : L ⟶ M) (π : M ⟶ Q)
    (hexact : ∀ X, LinearMap.range (ι.app X).hom.toLinearMap =
      LinearMap.ker (π.app X).hom.toLinearMap) :
    (sL.step (Fin.last n)).directImage ι = (sQ.step 0).inverseImage π := by
  apply RepSubfunctor.ext_obj
  intro X
  apply SetLike.ext
  intro v
  change (∃ w ∈ (sL.step (Fin.last n)).obj X, (ι.app X).hom w = v) ↔
    (π.app X).hom v ∈ (sQ.step 0).obj X
  rw [sL.top X, sQ.zero X]
  change (∃ w ∈ (⊤ : Subrepresentation (L.obj X).ρ), (ι.app X).hom w = v) ↔
    (π.app X).hom v = 0
  constructor
  · rintro ⟨w, _, rfl⟩
    have hm : (ι.app X).hom w ∈ LinearMap.range (ι.app X).hom.toLinearMap :=
      ⟨w, rfl⟩
    rw [hexact X] at hm
    exact hm
  · intro hv
    have hm : v ∈ LinearMap.range (ι.app X).hom.toLinearMap := by
      rw [hexact X]
      exact hv
    obtain ⟨w, rfl⟩ := hm
    exact ⟨w, trivial, rfl⟩

theorem spliceStep_right (sL : RepFunctorFiltration L n)
    (sQ : RepFunctorFiltration Q m) (ι : L ⟶ M) (π : M ⟶ Q)
    (hexact : ∀ X, LinearMap.range (ι.app X).hom.toLinearMap =
      LinearMap.ker (π.app X).hom.toLinearMap) (i : Fin (m + 1)) :
    spliceStep sL sQ ι π (spliceRightStep n m i) = (sQ.step i).inverseImage π := by
  by_cases h : i.val = 0
  · have hi : i = 0 := Fin.ext h
    subst i
    have he : spliceRightStep n m 0 = spliceLeftStep n m (Fin.last n) :=
      Fin.ext (by simp [spliceRightStep, spliceLeftStep])
    rw [he, spliceStep_left, splice_junction sL sQ ι π hexact]
  · simp [spliceStep, spliceRightStep, show ¬n + i.val ≤ n by omega]

/-- Splice two actual natural flags across a componentwise exact sequence.
The construction itself needs only the range-kernel equality. -/
def splice (sL : RepFunctorFiltration L n) (sQ : RepFunctorFiltration Q m)
    (ι : L ⟶ M) (π : M ⟶ Q)
    (hexact : ∀ X, LinearMap.range (ι.app X).hom.toLinearMap =
      LinearMap.ker (π.app X).hom.toLinearMap) : RepFunctorFiltration M (n + m) where
  step := spliceStep sL sQ ι π
  monotone X := by
    intro i j hij
    change i.val ≤ j.val at hij
    by_cases hi : i.val ≤ n
    · by_cases hj : j.val ≤ n
      · simp only [spliceStep, dite_eq_left hi, dite_eq_left hj]
        exact RepSubfunctor.directImage_mono ι _ _ (fun X => sL.monotone X hij) X
      · simp only [spliceStep, dite_eq_left hi, dite_eq_right hj]
        rintro v ⟨w, hw, rfl⟩
        have hk : (π.app X).hom ((ι.app X).hom w) = 0 := by
          have hm : (ι.app X).hom w ∈ LinearMap.ker (π.app X).hom.toLinearMap := by
            rw [← hexact X]
            exact ⟨w, rfl⟩
          exact hm
        change (π.app X).hom ((ι.app X).hom w) ∈ (sQ.step _).obj X
        rw [hk]
        exact (sQ.step _).obj X |>.toSubmodule.zero_mem
    · have hj : ¬j.val ≤ n := by omega
      simp only [spliceStep, dite_eq_right hi, dite_eq_right hj]
      intro v hv
      exact sQ.monotone X (show (⟨i.val - n, by omega⟩ : Fin (m + 1)) ≤
        ⟨j.val - n, by omega⟩ by change i.val - n ≤ j.val - n; omega) hv
  zero X := by
    have he : (0 : Fin (n + m + 1)) = spliceLeftStep n m 0 := Fin.ext rfl
    rw [he, spliceStep_left]
    apply SetLike.ext
    intro v
    change (∃ w ∈ (sL.step 0).obj X, (ι.app X).hom w = v) ↔ v = 0
    rw [sL.zero X]
    change (∃ w, w = 0 ∧ (ι.app X).hom w = v) ↔ v = 0
    simp [eq_comm]
  top X := by
    have he : Fin.last (n + m) = spliceRightStep n m (Fin.last m) := Fin.ext rfl
    rw [he, spliceStep_right sL sQ ι π hexact]
    apply SetLike.ext
    intro v
    change (π.app X).hom v ∈ (sQ.step (Fin.last m)).obj X ↔
      v ∈ (⊤ : Subrepresentation (M.obj X).ρ)
    rw [sQ.top X]
    exact iff_of_true trivial trivial

/-- The left grade index is unchanged. -/
def spliceLeft (n m : ℕ) (i : Fin n) : Fin (n + m) := ⟨i.val, by omega⟩

/-- The right grade index is shifted by the complete first length. -/
def spliceRight (n m : ℕ) (i : Fin m) : Fin (n + m) := ⟨n + i.val, by omega⟩

/-- Every grade belongs to exactly one block, including when a block is empty. -/
def spliceIndexEquiv (n m : ℕ) : Fin (n + m) ≃ Fin n ⊕ Fin m :=
  finSumFinEquiv.symm

@[simp]
theorem spliceIndexEquiv_left (i : Fin n) :
    spliceIndexEquiv n m (spliceLeft n m i) = Sum.inl i :=
  finSumFinEquiv.symm_apply_apply (Sum.inl i)

@[simp]
theorem spliceIndexEquiv_right (i : Fin m) :
    spliceIndexEquiv n m (spliceRight n m i) = Sum.inr i :=
  finSumFinEquiv.symm_apply_apply (Sum.inr i)

/-- Concatenation retains the complete two families, in their original order. -/
def concatPieces {A : Sort*} (p : Fin n → A) (q : Fin m → A) : Fin (n + m) → A :=
  Sum.elim p q ∘ spliceIndexEquiv n m

@[simp]
theorem concatPieces_left {A : Sort*} (p : Fin n → A) (q : Fin m → A) (i : Fin n) :
    concatPieces p q (spliceLeft n m i) = p i := by simp [concatPieces]

@[simp]
theorem concatPieces_right {A : Sort*} (p : Fin n → A) (q : Fin m → A) (i : Fin m) :
    concatPieces p q (spliceRight n m i) = q i := by simp [concatPieces]

/-- Natural comparison of every grade of the image block. -/
def spliceLeftGradedIso (sL : RepFunctorFiltration L n)
    (sQ : RepFunctorFiltration Q m) (ι : L ⟶ M) (π : M ⟶ Q)
    (hexact : ∀ X, LinearMap.range (ι.app X).hom.toLinearMap =
      LinearMap.ker (π.app X).hom.toLinearMap)
    (hinj : ∀ X, Function.Injective (ι.app X).hom) (i : Fin n) :
    (splice sL sQ ι π hexact).graded (spliceLeft n m i) ≅ sL.graded i := by
  change (spliceStep sL sQ ι π (spliceLeftStep n m i.castSucc)).quotientFunctor
    (spliceStep sL sQ ι π (spliceLeftStep n m i.succ)) ≅ _
  rw [spliceStep_left, spliceStep_left]
  exact RepSubfunctor.injectiveImageQuotientIso _ _ ι hinj

/-- Natural comparison of every grade of the inverse-image block. -/
def spliceRightGradedIso (sL : RepFunctorFiltration L n)
    (sQ : RepFunctorFiltration Q m) (ι : L ⟶ M) (π : M ⟶ Q)
    (hexact : ∀ X, LinearMap.range (ι.app X).hom.toLinearMap =
      LinearMap.ker (π.app X).hom.toLinearMap)
    (hsurj : ∀ X, Function.Surjective (π.app X).hom) (i : Fin m) :
    (splice sL sQ ι π hexact).graded (spliceRight n m i) ≅ sQ.graded i := by
  change (spliceStep sL sQ ι π (spliceRightStep n m i.castSucc)).quotientFunctor
    (spliceStep sL sQ ι π (spliceRightStep n m i.succ)) ≅ _
  rw [spliceStep_right sL sQ ι π hexact, spliceStep_right sL sQ ι π hexact]
  exact RepSubfunctor.inverseImageQuotientIso _ _ π hsurj

/-- One natural comparison for the full concatenated grade family. -/
def spliceGradedIso (sL : RepFunctorFiltration L n)
    (sQ : RepFunctorFiltration Q m) (ι : L ⟶ M) (π : M ⟶ Q)
    (hexact : ∀ X, LinearMap.range (ι.app X).hom.toLinearMap =
      LinearMap.ker (π.app X).hom.toLinearMap)
    (hinj : ∀ X, Function.Injective (ι.app X).hom)
    (hsurj : ∀ X, Function.Surjective (π.app X).hom) (i : Fin (n + m)) :
    (splice sL sQ ι π hexact).graded i ≅ concatPieces sL.graded sQ.graded i := by
  generalize he : spliceIndexEquiv n m i = j
  have hi : i = (spliceIndexEquiv n m).symm j := by
    rw [← he, Equiv.symm_apply_apply]
  rw [hi]
  cases j with
  | inl i =>
      change (splice sL sQ ι π hexact).graded (spliceLeft n m i) ≅
        concatPieces sL.graded sQ.graded (spliceLeft n m i)
      rw [concatPieces_left]
      exact spliceLeftGradedIso sL sQ ι π hexact hinj i
  | inr i =>
      change (splice sL sQ ι π hexact).graded (spliceRight n m i) ≅
        concatPieces sL.graded sQ.graded (spliceRight n m i)
      rw [concatPieces_right]
      exact spliceRightGradedIso sL sQ ι π hexact hsurj i

theorem HasGradedPieces.splice {sL : RepFunctorFiltration L n}
    {sQ : RepFunctorFiltration Q m}
    {p : Fin n → C ⥤ Rep.{uV} R G} {q : Fin m → C ⥤ Rep.{uV} R G}
    (hL : sL.HasGradedPieces p) (hQ : sQ.HasGradedPieces q)
    (ι : L ⟶ M) (π : M ⟶ Q)
    (hexact : ∀ X, LinearMap.range (ι.app X).hom.toLinearMap =
      LinearMap.ker (π.app X).hom.toLinearMap)
    (hinj : ∀ X, Function.Injective (ι.app X).hom)
    (hsurj : ∀ X, Function.Surjective (π.app X).hom) :
    (splice sL sQ ι π hexact).HasGradedPieces (concatPieces p q) := by
  intro i
  obtain ⟨i, rfl⟩ := (spliceIndexEquiv n m).symm.surjective i
  cases i with
  | inl i =>
      obtain ⟨e⟩ := hL i
      exact ⟨spliceLeftGradedIso sL sQ ι π hexact hinj i ≪≫
        e ≪≫ eqToIso (concatPieces_left p q i).symm⟩
  | inr i =>
      obtain ⟨e⟩ := hQ i
      exact ⟨spliceRightGradedIso sL sQ ι π hexact hsurj i ≪≫
        e ≪≫ eqToIso (concatPieces_right p q i).symm⟩

end RepFunctorFiltration

variable {n m : ℕ}
  {p : Fin n → C ⥤ Rep.{uV} R G} {q : Fin m → C ⥤ Rep.{uV} R G}

/-- Existence with the full ordered concatenation of the supplied pieces. -/
theorem HasOrderedFiltration.splice (hL : HasOrderedFiltration L p)
    (hQ : HasOrderedFiltration Q q) (ι : L ⟶ M) (π : M ⟶ Q)
    (hexact : ∀ X, LinearMap.range (ι.app X).hom.toLinearMap =
      LinearMap.ker (π.app X).hom.toLinearMap)
    (hinj : ∀ X, Function.Injective (ι.app X).hom)
    (hsurj : ∀ X, Function.Surjective (π.app X).hom) :
    HasOrderedFiltration M (RepFunctorFiltration.concatPieces p q) := by
  obtain ⟨sL, hL⟩ := hL
  obtain ⟨sQ, hQ⟩ := hQ
  exact ⟨sL.splice sQ ι π hexact, hL.splice hQ ι π hexact hinj hsurj⟩

/-- Gluing concatenates every piece; the two witnessing permutations act in blocks. -/
theorem IsGluedFrom.splice (hL : IsGluedFrom L p) (hQ : IsGluedFrom Q q)
    (ι : L ⟶ M) (π : M ⟶ Q)
    (hexact : ∀ X, LinearMap.range (ι.app X).hom.toLinearMap =
      LinearMap.ker (π.app X).hom.toLinearMap)
    (hinj : ∀ X, Function.Injective (ι.app X).hom)
    (hsurj : ∀ X, Function.Surjective (π.app X).hom) :
    IsGluedFrom M (RepFunctorFiltration.concatPieces p q) := by
  obtain ⟨eL, hL⟩ := hL
  obtain ⟨eQ, hQ⟩ := hQ
  let e := (RepFunctorFiltration.spliceIndexEquiv n m).trans
    ((Equiv.sumCongr eL eQ).trans (RepFunctorFiltration.spliceIndexEquiv n m).symm)
  refine ⟨e, ?_⟩
  have he : RepFunctorFiltration.concatPieces (p ∘ eL) (q ∘ eQ) =
      RepFunctorFiltration.concatPieces p q ∘ e := by
    funext i
    simp only [RepFunctorFiltration.concatPieces, Function.comp_apply,
      Equiv.trans_apply, e, Equiv.apply_symm_apply]
    cases (RepFunctorFiltration.spliceIndexEquiv n m) i <;> rfl
  rw [← he]
  exact hL.splice hQ ι π hexact hinj hsurj

end Langlands
