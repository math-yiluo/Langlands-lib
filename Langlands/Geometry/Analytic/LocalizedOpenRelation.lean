import Langlands.Geometry.Analytic.AnalyticImmersion

/-! # Equivalence relations of analytic spaces with open-immersion projections

A family of analytic spaces `Z m` with, for every pair `(m, n)`, an analytic space `S m n` and
open immersions `a : S m n → Z m`, `b : S m n → Z n` which form an equivalence relation on
morphisms from every test space. These are Berkovich's gluing data along open subspaces. -/

noncomputable section

universe u

namespace Langlands.Analytic.SaturatedAtlasPresentation

open CategoryTheory Set

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- An open immersion is a monomorphism. -/
theorem openImmersion.mono' {X Y : LocalizedCategory.{u, u, u} (K := K)} {φ : X ⟶ Y}
    (hφ : openImmersion φ) : Mono φ := by
  obtain ⟨U, hU, e, rfl⟩ := hφ
  infer_instance

/-- A morphism whose image lies in the image of an open immersion factors through it. -/
theorem openImmersion.exists_lift {X Y T : LocalizedCategory.{u, u, u} (K := K)}
    {f : X ⟶ Y} (hf : openImmersion f) (t : T ⟶ Y)
    (ht : ∀ z, localizedSpaceFunctor.map t z ∈ range (localizedSpaceFunctor.map f)) :
    ∃ g : T ⟶ X, g ≫ f = t := by
  obtain ⟨U, hU, e, rfl⟩ := hf
  let D := (presentationOf Y).openDomain U hU
  have hmem (z : localizedSpaceFunctor.obj T) :
      localizedSpaceFunctor.map t z ∈ D.carrier := by
    obtain ⟨x, hx⟩ := ht z
    rw [Functor.map_comp, TopCat.comp_app, domainι_apply] at hx
    exact hx ▸ (localizedSpaceFunctor.map e.hom x).property
  exact ⟨domainLift D t hmem ≫ e.inv, by
    rw [Category.assoc, Iso.inv_hom_id_assoc]; exact domainLift_comp D t hmem⟩

/-- Gluing data for analytic spaces along open subspaces, in relation form: analytic spaces
`Z m`, for each pair an analytic space `S m n` with open immersions `a m n : S m n → Z m` and
`b m n : S m n → Z n`, which are reflexive, symmetric and transitive. -/
structure LocalizedOpenRelation (K : Type u) [NormedField K] [IsUltrametricDist K]
    [CompleteSpace K] where
  /-- The index type of the pieces. -/
  M : Type u
  /-- The pieces. -/
  Z : M → LocalizedCategory.{u, u, u} (K := K)
  /-- The relation between two pieces. -/
  S : M → M → LocalizedCategory.{u, u, u} (K := K)
  /-- The first projection. -/
  a : ∀ m n, S m n ⟶ Z m
  /-- The second projection. -/
  b : ∀ m n, S m n ⟶ Z n
  a_open : ∀ m n, openImmersion (a m n)
  b_open : ∀ m n, openImmersion (b m n)
  refl : ∀ m, ∃ s : Z m ⟶ S m m, s ≫ a m m = 𝟙 _ ∧ s ≫ b m m = 𝟙 _
  symm : ∀ m n, ∃ s : S m n ⟶ S n m, s ≫ a n m = b m n ∧ s ≫ b n m = a m n
  trans : ∀ {m n l : M} {T : LocalizedCategory.{u, u, u} (K := K)} (s : T ⟶ S m n)
    (t : T ⟶ S n l), s ≫ b m n = t ≫ a n l →
      ∃ r : T ⟶ S m l, r ≫ a m l = s ≫ a m n ∧ r ≫ b m l = t ≫ b n l

namespace LocalizedOpenRelation

variable (R : LocalizedOpenRelation K)

instance mono_a (m n : R.M) : Mono (R.a m n) := openImmersion.mono' (R.a_open m n)

instance mono_b (m n : R.M) : Mono (R.b m n) := openImmersion.mono' (R.b_open m n)

/-- The two projections of the diagonal relation agree. -/
theorem a_self_eq_b_self (m : R.M) : R.a m m = R.b m m := by
  obtain ⟨s, hsa, hsb⟩ := R.refl m
  have h : R.a m m ≫ s = 𝟙 _ :=
    (cancel_mono (R.a m m)).1 (by rw [Category.assoc, hsa, Category.comp_id, Category.id_comp])
  calc R.a m m = R.a m m ≫ s ≫ R.b m m := by rw [hsb, Category.comp_id]
    _ = R.b m m := by rw [← Category.assoc, h, Category.id_comp]

/-! ## The relation on morphisms -/

/-- Morphisms `f : T → Z m` and `g : T → Z n` are related when they factor jointly through
`S m n`. -/
def Rel {m n : R.M} {T : LocalizedCategory.{u, u, u} (K := K)} (f : T ⟶ R.Z m)
    (g : T ⟶ R.Z n) : Prop :=
  ∃ s : T ⟶ R.S m n, s ≫ R.a m n = f ∧ s ≫ R.b m n = g

variable {R}
variable {T T' : LocalizedCategory.{u, u, u} (K := K)}

theorem Rel.refl {m : R.M} (f : T ⟶ R.Z m) : R.Rel f f := by
  obtain ⟨s, hsa, hsb⟩ := R.refl m
  exact ⟨f ≫ s, by rw [Category.assoc, hsa, Category.comp_id],
    by rw [Category.assoc, hsb, Category.comp_id]⟩

theorem Rel.symm {m n : R.M} {f : T ⟶ R.Z m} {g : T ⟶ R.Z n} (h : R.Rel f g) : R.Rel g f := by
  obtain ⟨s, rfl, rfl⟩ := h
  obtain ⟨σ, hσa, hσb⟩ := R.symm m n
  exact ⟨s ≫ σ, by rw [Category.assoc, hσa], by rw [Category.assoc, hσb]⟩

theorem Rel.trans {m n l : R.M} {f : T ⟶ R.Z m} {g : T ⟶ R.Z n} {k : T ⟶ R.Z l}
    (h : R.Rel f g) (h' : R.Rel g k) : R.Rel f k := by
  obtain ⟨s, rfl, hsb⟩ := h
  obtain ⟨t, hta, rfl⟩ := h'
  obtain ⟨r, hra, hrb⟩ := R.trans s t (hsb.trans hta.symm)
  exact ⟨r, hra, hrb⟩

theorem Rel.comp {m n : R.M} {f : T ⟶ R.Z m} {g : T ⟶ R.Z n} (h : R.Rel f g) (e : T' ⟶ T) :
    R.Rel (e ≫ f) (e ≫ g) := by
  obtain ⟨s, rfl, rfl⟩ := h
  exact ⟨e ≫ s, Category.assoc _ _ _, Category.assoc _ _ _⟩

/-- The relation is functional: a morphism is related to at most one morphism into a given
piece. -/
theorem Rel.unique {m n : R.M} {f : T ⟶ R.Z m} {g g' : T ⟶ R.Z n} (h : R.Rel f g)
    (h' : R.Rel f g') : g = g' := by
  obtain ⟨s, hsa, rfl⟩ := h
  obtain ⟨s', hsa', rfl⟩ := h'
  rw [(cancel_mono (R.a m n)).1 (hsa.trans hsa'.symm)]

theorem Rel.unique_left {m n : R.M} {f f' : T ⟶ R.Z m} {g : T ⟶ R.Z n} (h : R.Rel f g)
    (h' : R.Rel f' g) : f = f' :=
  h.symm.unique h'.symm

theorem rel_self_iff {m : R.M} {f g : T ⟶ R.Z m} : R.Rel f g ↔ f = g :=
  ⟨fun h => (h.unique (Rel.refl f)).symm, fun h => h ▸ Rel.refl f⟩

/-- The image of the first projection. -/
def domainSet (m n : R.M) : Set (localizedSpaceFunctor.obj (R.Z m)) :=
  range (localizedSpaceFunctor.map (R.a m n))

theorem isOpen_domainSet (m n : R.M) : IsOpen (R.domainSet m n) :=
  (openImmersion.isOpenEmbedding (R.a_open m n)).isOpen_range

theorem Rel.mem_domainSet {m n : R.M} {f : T ⟶ R.Z m} {g : T ⟶ R.Z n} (h : R.Rel f g)
    (x : localizedSpaceFunctor.obj T) : localizedSpaceFunctor.map f x ∈ R.domainSet m n := by
  obtain ⟨s, rfl, rfl⟩ := h
  exact ⟨localizedSpaceFunctor.map s x, by rw [Functor.map_comp, TopCat.comp_app]⟩

/-- A morphism into `Z m` with image in the domain of the relation with `Z n` is related to a
morphism into `Z n`. -/
theorem exists_rel {m n : R.M} (f : T ⟶ R.Z m)
    (hf : ∀ x, localizedSpaceFunctor.map f x ∈ R.domainSet m n) :
    ∃ g : T ⟶ R.Z n, R.Rel f g := by
  obtain ⟨s, hs⟩ := openImmersion.exists_lift (R.a_open m n) f hf
  exact ⟨s ≫ R.b m n, s, hs, rfl⟩

/-- The transfer of a morphism into `Z m` with image in the domain of the relation with
`Z n`: the unique related morphism into `Z n`. -/
def transfer {m : R.M} (n : R.M) (f : T ⟶ R.Z m)
    (hf : ∀ x, localizedSpaceFunctor.map f x ∈ R.domainSet m n) : T ⟶ R.Z n :=
  Classical.choose (exists_rel f hf)

theorem rel_transfer {m : R.M} (n : R.M) (f : T ⟶ R.Z m)
    (hf : ∀ x, localizedSpaceFunctor.map f x ∈ R.domainSet m n) :
    R.Rel f (transfer n f hf) :=
  Classical.choose_spec (exists_rel f hf)

theorem Rel.eq_transfer {m n : R.M} {f : T ⟶ R.Z m} {g : T ⟶ R.Z n} (h : R.Rel f g) :
    g = transfer n f h.mem_domainSet :=
  h.unique (rel_transfer n f _)

/-! ## The relation on points -/

variable (R) in
/-- Points `z` of `Z m` and `z'` of `Z n` are related when some point of `S m n` projects to
both. -/
def PointRel (p q : Σ m, localizedSpaceFunctor.obj (R.Z m)) : Prop :=
  ∃ σ : localizedSpaceFunctor.obj (R.S p.1 q.1),
    localizedSpaceFunctor.map (R.a p.1 q.1) σ = p.2 ∧
      localizedSpaceFunctor.map (R.b p.1 q.1) σ = q.2

theorem pointRel_refl (p : Σ m, localizedSpaceFunctor.obj (R.Z m)) : R.PointRel p p := by
  obtain ⟨s, hsa, hsb⟩ := R.refl p.1
  refine ⟨localizedSpaceFunctor.map s p.2, ?_, ?_⟩
  · rw [← TopCat.comp_app, ← Functor.map_comp, hsa, CategoryTheory.Functor.map_id, TopCat.id_app]
  · rw [← TopCat.comp_app, ← Functor.map_comp, hsb, CategoryTheory.Functor.map_id, TopCat.id_app]

theorem pointRel_symm {p q : Σ m, localizedSpaceFunctor.obj (R.Z m)} (h : R.PointRel p q) :
    R.PointRel q p := by
  obtain ⟨σ, hσa, hσb⟩ := h
  obtain ⟨s, hsa, hsb⟩ := R.symm p.1 q.1
  refine ⟨localizedSpaceFunctor.map s σ, ?_, ?_⟩
  · rw [← TopCat.comp_app, ← Functor.map_comp, hsa, hσb]
  · rw [← TopCat.comp_app, ← Functor.map_comp, hsb, hσa]

/-- An open immersion is injective on points. -/
theorem openImmersion.injective {X Y : LocalizedCategory.{u, u, u} (K := K)} {φ : X ⟶ Y}
    (hφ : openImmersion φ) : Function.Injective (localizedSpaceFunctor.map φ) :=
  (openImmersion.isOpenEmbedding hφ).injective

theorem pointRel_trans {p q r : Σ m, localizedSpaceFunctor.obj (R.Z m)} (h : R.PointRel p q)
    (h' : R.PointRel q r) : R.PointRel p r := by
  obtain ⟨σ, hσa, hσb⟩ := h
  obtain ⟨τ, hτa, hτb⟩ := h'
  let W : Set (localizedSpaceFunctor.obj (R.S p.1 q.1)) :=
    localizedSpaceFunctor.map (R.b p.1 q.1) ⁻¹' R.domainSet q.1 r.1
  have hW : IsOpen W :=
    (R.isOpen_domainSet q.1 r.1).preimage (localizedSpaceFunctor.map (R.b p.1 q.1)).hom.continuous
  have hσW : σ ∈ W := ⟨τ, hτa.trans hσb.symm⟩
  let D := (presentationOf (R.S p.1 q.1)).openDomain W hW
  let ι := domainι (R.S p.1 q.1) D
  have hmem : ∀ x, localizedSpaceFunctor.map (ι ≫ R.b p.1 q.1) x ∈ R.domainSet q.1 r.1 := by
    intro x
    rw [Functor.map_comp, TopCat.comp_app, domainι_apply]
    exact x.property
  obtain ⟨t, ht⟩ := openImmersion.exists_lift (R.a_open q.1 r.1) _ hmem
  obtain ⟨ρ, hρa, hρb⟩ := R.trans ι t ht.symm
  let x : localizedSpaceFunctor.obj (domainObj (R.S p.1 q.1) D) := ⟨σ, hσW⟩
  have hιx : localizedSpaceFunctor.map ι x = σ := domainι_apply _ x
  have htx : localizedSpaceFunctor.map t x = τ := by
    apply openImmersion.injective (R.a_open q.1 r.1)
    rw [← TopCat.comp_app, ← Functor.map_comp, ht, Functor.map_comp, TopCat.comp_app, hιx, hσb,
      hτa]
  refine ⟨localizedSpaceFunctor.map ρ x, ?_, ?_⟩
  · rw [← TopCat.comp_app, ← Functor.map_comp, hρa, Functor.map_comp, TopCat.comp_app, hιx, hσa]
  · rw [← TopCat.comp_app, ← Functor.map_comp, hρb, Functor.map_comp, TopCat.comp_app, htx, hτb]

variable (R) in
/-- The equivalence relation on the points of the pieces. -/
def pointSetoid : Setoid (Σ m, localizedSpaceFunctor.obj (R.Z m)) where
  r := R.PointRel
  iseqv := ⟨pointRel_refl, pointRel_symm, pointRel_trans⟩

end LocalizedOpenRelation

end Langlands.Analytic.SaturatedAtlasPresentation
