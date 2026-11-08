import Langlands.CategoryTheory.Renard.NoetherianReflection
import Mathlib.Order.Bounds.OrderIso

/-!
# Transfer of Renard finiteness along subobject order isomorphisms

Renard's finite-type and Noetherian conditions (A.I.2–A.I.3) only depend on
the order of the subobjects of an object. They therefore transfer along order
isomorphisms of subobject lattices. A fully faithful functor preserving
monomorphisms, through which every subobject of an image object comes from a
subobject of the source, induces such an isomorphism. Equivalences and
inclusions of full subcategories closed under subobjects are the two cases
used below.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory

namespace Langlands.Renard

universe uC vC uD vD

variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]

section OrderIso

variable {X : C} {Y : D}

/-- Subobject unions transfer along an order isomorphism of subobjects. -/
theorem hasSubobjectUnions_of_orderIso (e : Subobject X ≃o Subobject Y) (hY : HasSubobjectUnions Y) :
    HasSubobjectUnions X := by
  intro S
  obtain ⟨U, hU⟩ := hY (e '' S)
  exact ⟨e.symm U, (OrderIso.isLUB_image e).mp hU⟩

/-- Renard finite type transfers along an order isomorphism of subobjects. -/
theorem isFiniteTypeObject_of_orderIso (e : Subobject X ≃o Subobject Y) (hY : IsFiniteTypeObject Y) :
    IsFiniteTypeObject X := by
  refine ⟨hasSubobjectUnions_of_orderIso e hY.1, ?_⟩
  intro S hn hc hp htop
  apply hY.2 (e '' S) (hn.image e)
  · rintro _ ⟨P, hP, rfl⟩ _ ⟨Q, hQ, rfl⟩ hne
    rcases hc hP hQ (fun heq => hne (congrArg e heq)) with h | h
    · exact Or.inl (e.monotone h)
    · exact Or.inr (e.monotone h)
  · rintro _ ⟨P, hP, rfl⟩ h
    exact hp P hP (e.injective (by simpa using h))
  · simpa using (OrderIso.isLUB_image' e).mpr htop

/-- Renard Noetherianity transfers along an order isomorphism of subobjects. -/
theorem isNoetherianObject_of_orderIso (e : Subobject X ≃o Subobject Y) (hY : IsNoetherianObject Y) :
    IsNoetherianObject X := by
  intro S hS
  obtain ⟨Q, ⟨P, hP, rfl⟩, hmax⟩ := hY (e '' S) (hS.image e)
  refine ⟨P, hP, ?_⟩
  intro Q hQ hPQ
  exact e.injective (hmax (e Q) ⟨Q, hQ, rfl⟩ (e.monotone hPQ))

end OrderIso

section FullyFaithful

variable (F : C ⥤ D) [F.PreservesMonomorphisms]

/-- Every monomorphism into `F.obj X` is, up to isomorphism of its source,
the image of a monomorphism into `X`. -/
def SubobjectSurjective (X : C) : Prop :=
  ∀ (Y : D) (m : Y ⟶ F.obj X), Mono m →
    ∃ (Z : C) (n : Z ⟶ X) (_ : Mono n) (e : F.obj Z ≅ Y), e.hom ≫ m = F.map n

theorem functorSubobjectMap_surjective (X : C) (hX : SubobjectSurjective F X) :
    Function.Surjective (functorSubobjectMap F X) := by
  intro Q
  obtain ⟨Z, n, hn, e, he⟩ := hX _ Q.arrow inferInstance
  refine ⟨Subobject.mk n, ?_⟩
  change Subobject.mk (F.map (Subobject.mk n).arrow) = Q
  calc Subobject.mk (F.map (Subobject.mk n).arrow) = Subobject.mk (F.map n) :=
        (Subobject.mk_eq_mk_of_comm _ _ (F.mapIso (Subobject.underlyingIso n)) (by
          rw [Functor.mapIso_hom, ← F.map_comp,
            Subobject.underlyingIso_hom_comp_eq_mk]))
    _ = Subobject.mk Q.arrow := Subobject.mk_eq_mk_of_comm _ _ e he
    _ = Q := Subobject.mk_arrow Q

variable [F.Full] [F.Faithful]

/-- A fully faithful functor preserving monomorphisms reflects the order of
subobjects. -/
theorem functorSubobjectMap_le_iff (X : C) (P Q : Subobject X) :
    functorSubobjectMap F X P ≤ functorSubobjectMap F X Q ↔ P ≤ Q := by
  refine ⟨fun h => ?_, fun h => (functorSubobjectMap F X).monotone h⟩
  change Subobject.mk (F.map P.arrow) ≤ Subobject.mk (F.map Q.arrow) at h
  refine Subobject.le_of_comm (F.preimage (Subobject.ofMkLEMk _ _ h)) ?_
  apply F.map_injective
  rw [F.map_comp, F.map_preimage, Subobject.ofMkLEMk_comp]

/-- The order embedding of subobject lattices induced by a fully faithful
functor preserving monomorphisms. -/
def functorSubobjectEmbedding (X : C) : Subobject X ↪o Subobject (F.obj X) :=
  OrderEmbedding.ofMapLEIff (functorSubobjectMap F X) (functorSubobjectMap_le_iff F X)

@[simp]
theorem functorSubobjectEmbedding_apply (X : C) (P : Subobject X) :
    functorSubobjectEmbedding F X P = functorSubobjectMap F X P :=
  rfl

/-- The order isomorphism of subobject lattices induced by a fully faithful
functor preserving monomorphisms that is surjective on subobjects of `X`. -/
def functorSubobjectOrderIso (X : C) (hX : SubobjectSurjective F X) :
    Subobject X ≃o Subobject (F.obj X) :=
  OrderIso.ofSurjective (functorSubobjectEmbedding F X)
    (functorSubobjectMap_surjective F X hX)

theorem isFiniteTypeObject_iff_of_subobjectSurjective (X : C)
    (hX : SubobjectSurjective F X) :
    IsFiniteTypeObject X ↔ IsFiniteTypeObject (F.obj X) :=
  ⟨isFiniteTypeObject_of_orderIso (functorSubobjectOrderIso F X hX).symm,
    isFiniteTypeObject_of_orderIso (functorSubobjectOrderIso F X hX)⟩

theorem isNoetherianObject_iff_of_subobjectSurjective (X : C)
    (hX : SubobjectSurjective F X) :
    IsNoetherianObject X ↔ IsNoetherianObject (F.obj X) :=
  ⟨isNoetherianObject_of_orderIso (functorSubobjectOrderIso F X hX).symm,
    isNoetherianObject_of_orderIso (functorSubobjectOrderIso F X hX)⟩

end FullyFaithful

/-- An equivalence is surjective on subobjects of every object. -/
theorem subobjectSurjective_of_isEquivalence (F : C ⥤ D) [F.IsEquivalence]
    [F.PreservesMonomorphisms] (X : C) : SubobjectSurjective F X := by
  intro Y m hm
  let e := F.objObjPreimageIso Y
  refine ⟨F.objPreimage Y, F.preimage (e.hom ≫ m), ?_, e, by rw [F.map_preimage]⟩
  have : Mono (F.map (F.preimage (e.hom ≫ m))) := by
    rw [F.map_preimage]
    infer_instance
  exact F.mono_of_mono_map this

/-- The inclusion of a full subcategory closed under subobjects is surjective
on subobjects of every object. -/
theorem subobjectSurjective_ι (P : ObjectProperty C) [P.IsClosedUnderSubobjects]
    [P.ι.PreservesMonomorphisms] (X : P.FullSubcategory) :
    SubobjectSurjective P.ι X := by
  intro Y m hm
  refine ⟨⟨Y, P.prop_of_mono m X.property⟩, ObjectProperty.homMk m, ?_, Iso.refl _, ?_⟩
  · exact P.ι.mono_of_mono_map hm
  · simp

end Langlands.Renard
