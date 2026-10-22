import Langlands.Representation.Filtration.Definitions

/-! Transport of actual representation filtrations along natural isomorphisms. -/

open CategoryTheory

namespace Langlands

universe uR uG uV uC vC

variable {R : Type uR} [CommRing R] {G : Type uG} [Monoid G]
  {C : Type uC} [Category.{vC} C]
  {F F' : C ⥤ Rep.{uV} R G}

namespace RepSubfunctor

/-- Transport an actual subfunctor using inverse images under the inverse
components of a natural isomorphism. -/
def isoTransport (S : RepSubfunctor F) (e : F ≅ F') : RepSubfunctor F' where
  obj X :=
    { toSubmodule := (S.obj X).toSubmodule.comap (e.inv.app X).hom.toLinearMap
      apply_mem_toSubmodule := by
        intro g v hv
        change (e.inv.app X).hom ((F'.obj X).ρ g v) ∈ S.obj X
        rw [Rep.hom_comm_apply]
        exact (S.obj X).apply_mem_toSubmodule g hv }
  map_mem := by
    intro X Y f v hv
    change (e.inv.app Y).hom ((F'.map f).hom v) ∈ S.obj Y
    have h := congrArg (fun k => k.hom v) (e.inv.naturality f)
    change (e.inv.app Y).hom ((F'.map f).hom v) =
      (F.map f).hom ((e.inv.app X).hom v) at h
    rw [h]
    exact S.map_mem f hv

@[simp]
theorem mem_isoTransport (S : RepSubfunctor F) (e : F ≅ F') (X : C)
    (v : F'.obj X) :
    v ∈ (S.isoTransport e).obj X ↔ (e.inv.app X).hom v ∈ S.obj X := Iff.rfl

/-- The ambient forward component restricted to the transported subspace. -/
def isoTransportHom (S : RepSubfunctor F) (e : F ≅ F') (X : C) :
    S.representation X ⟶ (S.isoTransport e).representation X :=
  Rep.ofHom
    { toLinearMap :=
        { toFun := fun v => ⟨(e.hom.app X).hom v, by
            change (e.inv.app X).hom ((e.hom.app X).hom v) ∈ S.obj X
            simp⟩
          map_add' := by intros; apply Subtype.ext; exact map_add _ _ _
          map_smul' := by intros; apply Subtype.ext; exact map_smul _ _ _ }
      isIntertwining' := by
        intro g
        ext v
        exact Rep.hom_comm_apply (e.hom.app X) g v }

/-- The ambient inverse component restricted to the transported subspace. -/
def isoTransportInv (S : RepSubfunctor F) (e : F ≅ F') (X : C) :
    (S.isoTransport e).representation X ⟶ S.representation X :=
  Rep.ofHom
    { toLinearMap :=
        { toFun := fun v => ⟨(e.inv.app X).hom v, v.property⟩
          map_add' := by intros; apply Subtype.ext; exact map_add _ _ _
          map_smul' := by intros; apply Subtype.ext; exact map_smul _ _ _ }
      isIntertwining' := by
        intro g
        ext v
        exact Rep.hom_comm_apply (e.inv.app X) g v }

/-- A natural isomorphism of the actual restricted representation functors. -/
def isoTransportIso (S : RepSubfunctor F) (e : F ≅ F') :
    S.toFunctor ≅ (S.isoTransport e).toFunctor :=
  NatIso.ofComponents
    (fun X =>
      { hom := S.isoTransportHom e X
        inv := S.isoTransportInv e X
        hom_inv_id := by
          ext v
          apply Subtype.ext
          exact Rep.inv_hom_apply _ _ (e.app X) (v : S.representation X).val
        inv_hom_id := by
          ext v
          apply Subtype.ext
          exact Rep.hom_inv_apply _ _ (e.app X) (v : (S.isoTransport e).representation X).val })
    (by
      intro X Y f
      ext v
      apply Subtype.ext
      exact congrArg (fun k => k.hom (v : S.representation X).val) (e.hom.naturality f))

/-- Descend a natural map on upper subfunctors which preserves the lower
subspaces to the actual successive quotient functors. -/
def quotientNatMap (S T : RepSubfunctor F) (S' T' : RepSubfunctor F')
    (α : T.toFunctor ⟶ T'.toFunctor)
    (h : ∀ X (v : T.representation X), (v : F.obj X) ∈ S.obj X →
      ((α.app X).hom v : T'.representation X).val ∈ S'.obj X) :
    S.quotientFunctor T ⟶ S'.quotientFunctor T' where
  app X := Rep.ofHom
    { toLinearMap := Submodule.mapQ (S.lowerInUpper T X).toSubmodule
        (S'.lowerInUpper T' X).toSubmodule (α.app X).hom.toLinearMap (h X)
      isIntertwining' := by
        intro g
        apply LinearMap.ext
        intro v
        obtain ⟨v, rfl⟩ := S.quotientProjection_surjective T X v
        change (S'.quotientProjection T' X).hom
            ((α.app X).hom ((T.representation X).ρ g v)) =
          (S'.quotientProjection T' X).hom
            ((T'.representation X).ρ g ((α.app X).hom v))
        exact congrArg (S'.quotientProjection T' X).hom
          (Rep.hom_comm_apply (α.app X) g v) }
  naturality := by
    intro X Y f
    ext v
    obtain ⟨v, rfl⟩ := S.quotientProjection_surjective T X v
    exact congrArg (S'.quotientProjection T' Y).hom
      (congrArg (fun k => k.hom v) (α.naturality f))

@[simp]
theorem quotientNatMap_projection (S T : RepSubfunctor F)
    (S' T' : RepSubfunctor F') (α : T.toFunctor ⟶ T'.toFunctor)
    (h : ∀ X (v : T.representation X), (v : F.obj X) ∈ S.obj X →
      ((α.app X).hom v : T'.representation X).val ∈ S'.obj X)
    (X : C) (v : T.representation X) :
    ((S.quotientNatMap T S' T' α h).app X).hom
        ((S.quotientProjection T X).hom v) =
      (S'.quotientProjection T' X).hom ((α.app X).hom v) := rfl

/-- The ambient natural isomorphism descends to a natural isomorphism of
actual successive quotients. No containment assumption is needed. -/
def isoTransportQuotientIso (S T : RepSubfunctor F) (e : F ≅ F') :
    S.quotientFunctor T ≅ (S.isoTransport e).quotientFunctor (T.isoTransport e) where
  hom := S.quotientNatMap T (S.isoTransport e) (T.isoTransport e)
    (T.isoTransportIso e).hom (by
      intro X v hv
      change (e.inv.app X).hom ((e.hom.app X).hom v) ∈ S.obj X
      simpa using hv)
  inv := (S.isoTransport e).quotientNatMap (T.isoTransport e) S T
    (T.isoTransportIso e).inv (by
      intro X v hv
      exact hv)
  hom_inv_id := by
    ext X v
    obtain ⟨v, rfl⟩ := S.quotientProjection_surjective T X v
    change (S.quotientProjection T X).hom
        (((T.isoTransportIso e).inv.app X).hom
          (((T.isoTransportIso e).hom.app X).hom v)) =
      (S.quotientProjection T X).hom v
    exact congrArg (S.quotientProjection T X).hom
      (Rep.inv_hom_apply _ _ ((T.isoTransportIso e).app X) v)
  inv_hom_id := by
    ext X v
    obtain ⟨v, rfl⟩ := (S.isoTransport e).quotientProjection_surjective
      (T.isoTransport e) X v
    change ((S.isoTransport e).quotientProjection (T.isoTransport e) X).hom
        (((T.isoTransportIso e).hom.app X).hom
          (((T.isoTransportIso e).inv.app X).hom v)) =
      ((S.isoTransport e).quotientProjection (T.isoTransport e) X).hom v
    exact congrArg
      ((S.isoTransport e).quotientProjection (T.isoTransport e) X).hom
      (Rep.hom_inv_apply _ _ ((T.isoTransportIso e).app X) v)

end RepSubfunctor

namespace RepFunctorFiltration

variable {n : ℕ}

/-- Transport every actual step, preserving the order and both endpoints. -/
def isoTransport (s : RepFunctorFiltration F n) (e : F ≅ F') :
    RepFunctorFiltration F' n where
  step i := (s.step i).isoTransport e
  monotone X := by
    intro i j hij v hv
    exact s.monotone X hij hv
  zero X := by
    apply SetLike.ext
    intro v
    change (e.inv.app X).hom v ∈ (s.step 0).obj X ↔ v = 0
    rw [s.zero X]
    change (e.inv.app X).hom v = 0 ↔ v = 0
    constructor
    · intro h
      have h' := congrArg (e.hom.app X).hom h
      simpa using h'
    · rintro rfl
      exact map_zero _
  top X := by
    apply SetLike.ext
    intro v
    change (e.inv.app X).hom v ∈ (s.step (Fin.last n)).obj X ↔
      v ∈ (⊤ : Subrepresentation (F'.obj X).ρ)
    rw [s.top X]
    exact iff_of_true (Submodule.mem_top) (Submodule.mem_top)

@[simp]
theorem isoTransport_step_obj (s : RepFunctorFiltration F n) (e : F ≅ F')
    (i : Fin (n + 1)) (X : C) :
    ((s.isoTransport e).step i).obj X = ((s.step i).isoTransport e).obj X := rfl

/-- Each transported graded functor is naturally isomorphic to the original. -/
def isoTransportGradedIso (s : RepFunctorFiltration F n) (e : F ≅ F')
    (i : Fin n) : s.graded i ≅ (s.isoTransport e).graded i :=
  (s.step i.castSucc).isoTransportQuotientIso (s.step i.succ) e

/-- Transport graded identifications through ambient and piecewise isomorphisms. -/
theorem HasGradedPieces.isoTransport {s : RepFunctorFiltration F n}
    {pieces pieces' : Fin n → C ⥤ Rep.{uV} R G}
    (h : s.HasGradedPieces pieces) (e : F ≅ F')
    (a : ∀ i, pieces i ≅ pieces' i) :
    (s.isoTransport e).HasGradedPieces pieces' := by
  intro i
  obtain ⟨hi⟩ := h i
  exact ⟨(s.isoTransportGradedIso e i).symm ≪≫ hi ≪≫ a i⟩

end RepFunctorFiltration

variable {n : ℕ} {pieces pieces' : Fin n → C ⥤ Rep.{uV} R G}

/-- An ordered filtration can be transported without changing its index order. -/
theorem HasOrderedFiltration.iso (h : HasOrderedFiltration F pieces)
    (e : F ≅ F') (a : ∀ i, pieces i ≅ pieces' i) :
    HasOrderedFiltration F' pieces' := by
  obtain ⟨s, hs⟩ := h
  exact ⟨s.isoTransport e, hs.isoTransport e a⟩

/-- Ordered filtration existence is invariant under natural isomorphisms. -/
theorem hasOrderedFiltration_iso_iff (e : F ≅ F')
    (a : ∀ i, pieces i ≅ pieces' i) :
    HasOrderedFiltration F pieces ↔ HasOrderedFiltration F' pieces' :=
  ⟨fun h => h.iso e a, fun h => h.iso e.symm (fun i => (a i).symm)⟩

/-- Gluing can be transported using the same witnessing permutation. -/
theorem IsGluedFrom.iso (h : IsGluedFrom F pieces)
    (e : F ≅ F') (a : ∀ i, pieces i ≅ pieces' i) :
    IsGluedFrom F' pieces' := by
  obtain ⟨p, hp⟩ := h
  exact ⟨p, hp.iso e (fun i => a (p i))⟩

/-- Unordered gluing is invariant under ambient and piecewise natural isomorphisms. -/
theorem isGluedFrom_iso_iff (e : F ≅ F')
    (a : ∀ i, pieces i ≅ pieces' i) :
    IsGluedFrom F pieces ↔ IsGluedFrom F' pieces' :=
  ⟨fun h => h.iso e a, fun h => h.iso e.symm (fun i => (a i).symm)⟩

end Langlands
