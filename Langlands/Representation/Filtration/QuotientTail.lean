import Langlands.Representation.Filtration.QuotientFirstIso

/-! Images of natural subfunctors and the surviving tail of a quotient filtration. -/

noncomputable section
open CategoryTheory

namespace Langlands

universe uR uG uV uC vC

variable {R : Type uR} [CommRing R] {G : Type uG} [Monoid G]
  {C : Type uC} [Category.{vC} C]
  {F H : C ⥤ Rep.{uV} R G}

namespace RepSubfunctor

/-- Actual objectwise images under a natural transformation. -/
def directImage (S : RepSubfunctor F) (α : F ⟶ H) : RepSubfunctor H where
  obj X :=
    { toSubmodule := (S.obj X).toSubmodule.map (α.app X).hom.toLinearMap
      apply_mem_toSubmodule := by
        intro g v hv
        obtain ⟨w, hw, rfl⟩ := hv
        exact ⟨(F.obj X).ρ g w, (S.obj X).apply_mem_toSubmodule g hw,
          Rep.hom_comm_apply (α.app X) g w⟩ }
  map_mem := by
    intro X Y f v hv
    obtain ⟨w, hw, rfl⟩ := hv
    exact ⟨(F.map f).hom w, S.map_mem f hw,
      congrArg (fun k => k.hom w) (α.naturality f)⟩

@[simp]
theorem mem_directImage (S : RepSubfunctor F) (α : F ⟶ H)
    (X : C) (v : H.obj X) :
    v ∈ (S.directImage α).obj X ↔
      ∃ w ∈ S.obj X, (α.app X).hom w = v := Iff.rfl

/-- The original transformation restricted to a subfunctor and its image. -/
def directImageHom (S : RepSubfunctor F) (α : F ⟶ H) :
    S.toFunctor ⟶ (S.directImage α).toFunctor where
  app X := Rep.ofHom
    { toLinearMap :=
        { toFun := fun v => ⟨(α.app X).hom v, ⟨v, v.property, rfl⟩⟩
          map_add' := by intros; apply Subtype.ext; exact map_add _ _ _
          map_smul' := by intros; apply Subtype.ext; exact map_smul _ _ _ }
      isIntertwining' := by
        intro g
        ext v
        exact Rep.hom_comm_apply (α.app X) g v }
  naturality := by
    intro X Y f
    ext v
    apply Subtype.ext
    exact congrArg (fun k => k.hom (v : S.representation X).val) (α.naturality f)

@[simp]
theorem directImageHom_apply (S : RepSubfunctor F) (α : F ⟶ H)
    (X : C) (v : S.representation X) :
    (((S.directImageHom α).app X).hom v :
      (S.directImage α).representation X).val = (α.app X).hom v := rfl

theorem directImageHom_surjective (S : RepSubfunctor F) (α : F ⟶ H) (X : C) :
    Function.Surjective ((S.directImageHom α).app X).hom := by
  intro v
  obtain ⟨w, hw, he⟩ := v.property
  exact ⟨⟨w, hw⟩, Subtype.ext he⟩

theorem directImage_mono (α : F ⟶ H) (S T : RepSubfunctor F)
    (h : ∀ X, S.obj X ≤ T.obj X) (X : C) :
    (S.directImage α).obj X ≤ (T.directImage α).obj X := by
  rintro v ⟨w, hw, rfl⟩
  exact ⟨w, h X hw, rfl⟩

/-- Once the ambient kernel is contained in the lower step, mapping both
steps to their images preserves their actual successive quotient naturally. -/
def directImageQuotientIso (S T : RepSubfunctor F) (α : F ⟶ H)
    (hker : ∀ (X : C) (v : F.obj X),
      (α.app X).hom v = 0 → v ∈ S.obj X) :
    S.quotientFunctor T ≅
      (S.directImage α).quotientFunctor (T.directImage α) := by
  let β := T.directImageHom α ≫
    (S.directImage α).quotientNatProjection (T.directImage α)
  apply S.quotientNatIsoOfSurjective T β
  · intro X v
    change (v : F.obj X) ∈ S.obj X ↔
      (Submodule.Quotient.mk
        (⟨(α.app X).hom v, ⟨v, v.property, rfl⟩⟩ :
          (T.directImage α).representation X) :
          (S.directImage α).quotientObj (T.directImage α) X) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    change (v : F.obj X) ∈ S.obj X ↔
      (α.app X).hom v ∈ (S.directImage α).obj X
    constructor
    · intro hv
      exact ⟨v, hv, rfl⟩
    · rintro ⟨w, hw, he⟩
      have he' : (α.app X).hom w = (α.app X).hom v := he
      have hk : (v : F.obj X) - w ∈ S.obj X :=
        hker X _ (by rw [map_sub, he', sub_self])
      change (v : F.obj X) ∈ (S.obj X).toSubmodule
      simpa only [sub_add_cancel] using (S.obj X).toSubmodule.add_mem hk hw
  · intro X v
    obtain ⟨w, rfl⟩ :=
      (S.directImage α).quotientProjection_surjective (T.directImage α) X v
    obtain ⟨v, rfl⟩ := T.directImageHom_surjective α X w
    exact ⟨v, rfl⟩

end RepSubfunctor

namespace RepFunctorFiltration

/-- The original filtration index of a step in the tail after `a` steps. -/
def tailIndex (a b : ℕ) (i : Fin (b + 1)) : Fin (a + b + 1) :=
  ⟨a + i.val, by omega⟩

/-- The image of the tail under an objectwise surjection whose kernel is
exactly its initial step is a zero-to-full natural filtration. -/
def quotientTail {a b : ℕ} (s : RepFunctorFiltration F (a + b)) (α : F ⟶ H)
    (hker : ∀ (X : C) (v : F.obj X),
      v ∈ (s.step (tailIndex a b 0)).obj X ↔ (α.app X).hom v = 0)
    (hsurj : ∀ X, Function.Surjective (α.app X).hom) :
    RepFunctorFiltration H b where
  step i := (s.step (tailIndex a b i)).directImage α
  monotone X := by
    intro i j hij v hv
    obtain ⟨w, hw, rfl⟩ := hv
    exact ⟨w, s.monotone X (show tailIndex a b i ≤ tailIndex a b j by
      change a + i.val ≤ a + j.val
      omega) hw, rfl⟩
  zero X := by
    apply SetLike.ext
    intro v
    change (∃ w ∈ (s.step (tailIndex a b 0)).obj X, (α.app X).hom w = v) ↔ v = 0
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact (hker X w).mp hw
    · rintro rfl
      exact ⟨0, (s.step _).obj X |>.toSubmodule.zero_mem, map_zero _⟩
  top X := by
    apply SetLike.ext
    intro v
    constructor
    · intro _
      trivial
    · intro _
      obtain ⟨w, rfl⟩ := hsurj X v
      refine ⟨w, ?_, rfl⟩
      have he : tailIndex a b (Fin.last b) = Fin.last (a + b) := Fin.ext rfl
      rw [he, s.top X]
      trivial

/-- A graded step of the quotient tail is naturally the corresponding
original graded step. -/
def quotientTailGradedIso {a b : ℕ} (s : RepFunctorFiltration F (a + b))
    (α : F ⟶ H)
    (hker : ∀ (X : C) (v : F.obj X),
      v ∈ (s.step (tailIndex a b 0)).obj X ↔ (α.app X).hom v = 0)
    (hsurj : ∀ X, Function.Surjective (α.app X).hom) (i : Fin b) :
    s.graded ⟨a + i.val, by omega⟩ ≅
      (s.quotientTail α hker hsurj).graded i := by
  apply (s.step (tailIndex a b i.castSucc)).directImageQuotientIso
    (s.step (tailIndex a b i.succ)) α
  intro X v hv
  exact s.monotone X (show tailIndex a b 0 ≤ tailIndex a b i.castSucc by
    change a + 0 ≤ a + i.val
    omega) ((hker X v).mpr hv)

theorem HasGradedPieces.quotientTail {a b : ℕ}
    {s : RepFunctorFiltration F (a + b)}
    {pieces : Fin (a + b) → C ⥤ Rep.{uV} R G}
    (h : s.HasGradedPieces pieces) (α : F ⟶ H)
    (hker : ∀ (X : C) (v : F.obj X),
      v ∈ (s.step (tailIndex a b 0)).obj X ↔ (α.app X).hom v = 0)
    (hsurj : ∀ X, Function.Surjective (α.app X).hom) :
    (s.quotientTail α hker hsurj).HasGradedPieces
      (fun i => pieces ⟨a + i.val, by omega⟩) := by
  intro i
  obtain ⟨e⟩ := h ⟨a + i.val, by omega⟩
  exact ⟨(s.quotientTailGradedIso α hker hsurj i).symm ≪≫ e⟩

end RepFunctorFiltration

end Langlands
