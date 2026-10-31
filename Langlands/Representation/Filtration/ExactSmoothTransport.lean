import Langlands.Representation.Category.Subquotients
import Langlands.Representation.Filtration.QuotientFirstIso
import Langlands.Representation.Derivative.MirabolicMinusExactnessStatement
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero

/-! Actual natural filtrations transported by a supplied exact smooth functor. -/

noncomputable section
open CategoryTheory

namespace Langlands

universe uG uH uV uC vC

variable {G : Type uG} [Group G] [TopologicalSpace G]
  {H : Type uH} [Group H] [TopologicalSpace H]
  {C : Type uC} [Category.{vC} C]

namespace RepSubfunctor

variable {F : C ⥤ SmoothRep.{0,uG,uV} ℂ G}

/-- The canonical smooth lift of an actual subfunctor of a smooth functor. -/
def smoothFunctor (S : RepSubfunctor (F ⋙ SmoothRep.toRep)) :
    C ⥤ SmoothRep.{0,uG,uV} ℂ G where
  obj X := (F.obj X).subrepresentation (S.obj X)
  map f := ObjectProperty.homMk (S.map f)
  map_id X := by
    apply ObjectProperty.hom_ext
    exact S.toFunctor.map_id X
  map_comp f g := by
    apply ObjectProperty.hom_ext
    exact S.toFunctor.map_comp f g

/-- Forgetting the smooth subfunctor recovers the actual restricted functor. -/
def smoothFunctorForgetIso (S : RepSubfunctor (F ⋙ SmoothRep.toRep)) :
    S.smoothFunctor ⋙ SmoothRep.toRep ≅ S.toFunctor :=
  Iso.refl _

/-- The natural inclusion of the actual smooth subobjects. -/
def smoothInclusion (S : RepSubfunctor (F ⋙ SmoothRep.toRep)) :
    S.smoothFunctor ⟶ F where
  app X := (F.obj X).subtype (S.obj X)
  naturality _ _ _ := rfl

/-- The smooth lift uses the actual upper subrepresentation and its quotient. -/
def smoothQuotientFunctor (S T : RepSubfunctor (F ⋙ SmoothRep.toRep)) :
    C ⥤ SmoothRep.{0,uG,uV} ℂ G where
  obj X := (T.smoothFunctor.obj X).quotient (S.lowerInUpper T X)
  map f := ObjectProperty.homMk (S.quotientMap T f)
  map_id X := by
    apply ObjectProperty.hom_ext
    exact (S.quotientFunctor T).map_id X
  map_comp f g := by
    apply ObjectProperty.hom_ext
    exact (S.quotientFunctor T).map_comp f g

/-- The comparison is the identity on the actual quotient spaces and maps. -/
def smoothQuotientForgetIso (S T : RepSubfunctor (F ⋙ SmoothRep.toRep)) :
    S.smoothQuotientFunctor T ⋙ SmoothRep.toRep ≅ S.quotientFunctor T :=
  Iso.refl _

/-- The natural quotient projection, regarded as a smooth intertwiner. -/
def smoothQuotientProjection (S T : RepSubfunctor (F ⋙ SmoothRep.toRep)) :
    T.smoothFunctor ⟶ S.smoothQuotientFunctor T where
  app X := (T.smoothFunctor.obj X).mkQ (S.lowerInUpper T X)
  naturality _ _ _ := rfl

/-- Natural inclusion between two nested actual smooth subfunctors. -/
def smoothInclusionOfLE (S T : RepSubfunctor (F ⋙ SmoothRep.toRep))
    (h : ∀ X, S.obj X ≤ T.obj X) : S.smoothFunctor ⟶ T.smoothFunctor where
  app X := SmoothRep.ofHom
    { toLinearMap :=
        { toFun := fun v => ⟨v.val, h X v.property⟩
          map_add' := by intros; rfl
          map_smul' := by intros; rfl }
      isIntertwining' := fun _ => rfl }
  naturality _ _ _ := rfl

theorem smoothInclusionOfLE_injective
    (S T : RepSubfunctor (F ⋙ SmoothRep.toRep))
    (h : ∀ X, S.obj X ≤ T.obj X) (X : C) :
    Function.Injective (SmoothRep.hom ((S.smoothInclusionOfLE T h).app X)) := by
  change Function.Injective (fun v : S.representation X =>
    (⟨v.val, h X v.property⟩ : T.representation X))
  intro v w hvw
  exact Subtype.ext (congrArg (fun z : T.representation X => z.val) hvw)

theorem smoothInclusionOfLE_comp
    (S T : RepSubfunctor (F ⋙ SmoothRep.toRep))
    (h : ∀ X, S.obj X ≤ T.obj X) :
    S.smoothInclusionOfLE T h ≫ T.smoothInclusion = S.smoothInclusion := rfl

theorem smoothInclusionOfLE_range
    (S T : RepSubfunctor (F ⋙ SmoothRep.toRep))
    (h : ∀ X, S.obj X ≤ T.obj X) (X : C) :
    LinearMap.range
        (SmoothRep.hom ((S.smoothInclusionOfLE T h).app X)).toLinearMap =
      LinearMap.ker
        (SmoothRep.hom ((S.smoothQuotientProjection T).app X)).toLinearMap := by
  change LinearMap.range
    (show S.representation X →ₗ[ℂ] T.representation X from
      (SmoothRep.hom ((S.smoothInclusionOfLE T h).app X)).toLinearMap) =
    LinearMap.ker (S.lowerInUpper T X).toSubmodule.mkQ
  rw [Submodule.ker_mkQ]
  apply Submodule.ext
  intro v
  change (∃ w : S.representation X, (⟨w.val, h X w.property⟩ :
    T.representation X) = v) ↔ v.val ∈ S.obj X
  constructor
  · rintro ⟨w, rfl⟩
    exact w.property
  · intro hv
    exact ⟨⟨v.val, hv⟩, rfl⟩

end RepSubfunctor

namespace ExactSmoothTransport

variable (J : SmoothRep.{0,uG,uV} ℂ G ⥤ SmoothRep.{0,uH,uV} ℂ H)
  (hJ : Derivative.Mirabolic.MapsShortExactIntertwiners J)

include hJ in
/-- Generic short-exactness preserves every actual injective intertwiner. -/
theorem map_injective {A B : SmoothRep.{0,uG,uV} ℂ G}
    (f : A ⟶ B) (hf : Function.Injective (SmoothRep.hom f)) :
    Function.Injective (SmoothRep.hom (J.map f)) := by
  apply (hJ A B (B.quotient (SmoothRep.hom f).range) f
    (B.mkQ (SmoothRep.hom f).range) hf (B.mkQ_surjective _)
    ?_).1
  exact (Submodule.ker_mkQ _).symm

/-- The full inclusion lifts natural comparisons between smooth functors. -/
def liftNatIso {A B : C ⥤ SmoothRep.{0,uG,uV} ℂ G}
    (e : A ⋙ SmoothRep.toRep ≅ B ⋙ SmoothRep.toRep) : A ≅ B where
  hom :=
    { app := fun X => ObjectProperty.homMk (e.hom.app X)
      naturality := by
        intro X Y f
        apply ObjectProperty.hom_ext
        exact e.hom.naturality f }
  inv :=
    { app := fun X => ObjectProperty.homMk (e.inv.app X)
      naturality := by
        intro X Y f
        apply ObjectProperty.hom_ext
        exact e.inv.naturality f }
  hom_inv_id := by
    apply NatTrans.ext
    funext X
    apply ObjectProperty.hom_ext
    exact congrArg (fun k => k.app X) e.hom_inv_id
  inv_hom_id := by
    apply NatTrans.ext
    funext X
    apply ObjectProperty.hom_ext
    exact congrArg (fun k => k.app X) e.inv_hom_id

end ExactSmoothTransport

namespace RepSubfunctor

variable {F : C ⥤ SmoothRep.{0,uG,uV} ℂ G}
  (S T : RepSubfunctor (F ⋙ SmoothRep.toRep))
  (J : SmoothRep.{0,uG,uV} ℂ G ⥤ SmoothRep.{0,uH,uV} ℂ H)

/-- Apply the functor to the smooth inclusion and take its actual invariant image. -/
def exactImage : RepSubfunctor (F ⋙ J ⋙ SmoothRep.toRep) where
  obj X := (SmoothRep.hom (J.map (S.smoothInclusion.app X))).range
  map_mem := by
    intro X Y f v hv
    obtain ⟨w, rfl⟩ := hv
    refine ⟨SmoothRep.hom (J.map (S.smoothFunctor.map f)) w, ?_⟩
    exact congrArg (fun k => SmoothRep.hom k w)
      (by simpa only [Functor.map_comp] using
        congrArg J.map (S.smoothInclusion.naturality f))

/-- The canonical natural surjection from a mapped subfunctor to its image. -/
def exactImageHom :
    S.smoothFunctor ⋙ J ⋙ SmoothRep.toRep ⟶ (S.exactImage J).toFunctor where
  app X := Rep.ofHom
    { toLinearMap :=
        { toFun := fun v =>
            ⟨SmoothRep.hom (J.map (S.smoothInclusion.app X)) v, ⟨v, rfl⟩⟩
          map_add' := by intros; apply Subtype.ext; exact map_add _ _ _
          map_smul' := by intros; apply Subtype.ext; exact map_smul _ _ _ }
      isIntertwining' := by
        intro g
        ext v
        exact Rep.hom_comm_apply (J.map (S.smoothInclusion.app X)).hom g v }
  naturality := by
    intro X Y f
    ext v
    apply Subtype.ext
    exact congrArg (fun k => SmoothRep.hom k v)
      (by simpa only [Functor.map_comp] using
        congrArg J.map (S.smoothInclusion.naturality f))

@[simp]
theorem exactImageHom_apply (X : C) (v : J.obj (S.smoothFunctor.obj X)) :
    (((S.exactImageHom J).app X).hom v).val =
      SmoothRep.hom (J.map (S.smoothInclusion.app X)) v := rfl

theorem exactImageHom_surjective (X : C) :
    Function.Surjective ((S.exactImageHom J).app X).hom := by
  intro v
  obtain ⟨w, hw⟩ := v.property
  exact ⟨w, Subtype.ext hw⟩

/-- Exactness identifies the mapped smooth subobject naturally with its image. -/
def exactImageIso (hJ : Derivative.Mirabolic.MapsShortExactIntertwiners J) :
    S.smoothFunctor ⋙ J ⋙ SmoothRep.toRep ≅ (S.exactImage J).toFunctor :=
  NatIso.ofComponents
    (fun X => Rep.mkIso (((S.exactImageHom J).app X).hom.ofBijective
      ⟨fun _ _ h => ExactSmoothTransport.map_injective J hJ
          (S.smoothInclusion.app X) ((F.obj X).subtype_injective _) (congrArg
            (fun z : (S.exactImage J).representation X => z.val) h),
        S.exactImageHom_surjective J X⟩))
    (fun f => (S.exactImageHom J).naturality f)

/-- Containment is preserved by functoriality of the natural inclusions. -/
theorem exactImage_mono (h : ∀ X, S.obj X ≤ T.obj X) (X : C) :
    (S.exactImage J).obj X ≤ (T.exactImage J).obj X := by
  rintro v ⟨w, rfl⟩
  refine ⟨SmoothRep.hom (J.map ((S.smoothInclusionOfLE T h).app X)) w, ?_⟩
  exact congrArg (fun k => SmoothRep.hom k w)
    (by simpa only [NatTrans.comp_app, Functor.map_comp] using
      congrArg J.map (congrArg (fun k => k.app X) (S.smoothInclusionOfLE_comp T h)))

/-- The zero endpoint follows from zero-map preservation, with no chosen zero object. -/
theorem exactImage_zero [J.PreservesZeroMorphisms]
    (hS : ∀ X, S.obj X = ⊥) (X : C) : (S.exactImage J).obj X = ⊥ := by
  have hi : S.smoothInclusion.app X = 0 := by
    apply ObjectProperty.hom_ext
    ext v
    change v.val = 0
    exact (show S.obj X ≤ ⊥ from le_of_eq (hS X)) v.property
  apply SetLike.ext
  intro v
  change (∃ w, SmoothRep.hom (J.map (S.smoothInclusion.app X)) w = v) ↔ v = 0
  rw [hi, J.map_zero]
  change (∃ _, (0 : J.obj (F.obj X)) = v) ↔ v = 0
  simp only [exists_const]
  exact eq_comm

/-- A full step has an isomorphic inclusion, and hence a full mapped image. -/
theorem exactImage_top (hS : ∀ X, S.obj X = ⊤) (X : C) :
    (S.exactImage J).obj X = ⊤ := by
  have hs : Function.Surjective (SmoothRep.hom (S.smoothInclusion.app X)) := by
    intro v
    refine ⟨⟨v, ?_⟩, rfl⟩
    rw [hS X]
    trivial
  let e := SmoothRep.mkIso
    ((SmoothRep.hom (S.smoothInclusion.app X)).ofBijective
      ⟨(F.obj X).subtype_injective _, hs⟩)
  have hsurj : Function.Surjective (SmoothRep.hom (J.map (S.smoothInclusion.app X))) :=
    (SmoothRep.equivOfIso (J.mapIso e)).surjective
  apply SetLike.ext
  intro v
  change (∃ w, SmoothRep.hom (J.map (S.smoothInclusion.app X)) w = v) ↔ True
  exact ⟨fun _ => trivial, fun _ => hsurj v⟩

/-- The natural map from the upper image to the mapped actual quotient. -/
def exactImageQuotientMap
    (hJ : Derivative.Mirabolic.MapsShortExactIntertwiners J) :
    (T.exactImage J).toFunctor ⟶
      S.smoothQuotientFunctor T ⋙ J ⋙ SmoothRep.toRep :=
  (T.exactImageIso J hJ).inv ≫
    Functor.whiskerRight (S.smoothQuotientProjection T) (J ⋙ SmoothRep.toRep)

@[simp]
theorem exactImageQuotientMap_apply
    (hJ : Derivative.Mirabolic.MapsShortExactIntertwiners J)
    (X : C) (v : J.obj (T.smoothFunctor.obj X)) :
    ((S.exactImageQuotientMap T J hJ).app X).hom
        (((T.exactImageHom J).app X).hom v) =
      SmoothRep.hom (J.map ((S.smoothQuotientProjection T).app X)) v := by
  change SmoothRep.hom (J.map ((S.smoothQuotientProjection T).app X))
    (((T.exactImageIso J hJ).inv.app X).hom
      (((T.exactImageIso J hJ).hom.app X).hom v)) = _
  exact congrArg (SmoothRep.hom (J.map ((S.smoothQuotientProjection T).app X)))
    (Rep.inv_hom_apply _ _ ((T.exactImageIso J hJ).app X) v)

/-- Exactness identifies the kernel on the upper image with the actual lower image. -/
theorem exactImageQuotientMap_kernel
    (hJ : Derivative.Mirabolic.MapsShortExactIntertwiners J)
    (h : ∀ X, S.obj X ≤ T.obj X)
    (X : C) (v : (T.exactImage J).representation X) :
    v ∈ (S.exactImage J).lowerInUpper (T.exactImage J) X ↔
      ((S.exactImageQuotientMap T J hJ).app X).hom v = 0 := by
  obtain ⟨v, rfl⟩ := T.exactImageHom_surjective J X v
  rw [S.exactImageQuotientMap_apply T J hJ]
  have hex := (hJ _ _ _ ((S.smoothInclusionOfLE T h).app X)
    ((S.smoothQuotientProjection T).app X)
    (S.smoothInclusionOfLE_injective T h X)
    (S.quotientProjection_surjective T X)
    (S.smoothInclusionOfLE_range T h X)).2.1
  have hfac : J.map ((S.smoothInclusionOfLE T h).app X) ≫
      J.map (T.smoothInclusion.app X) = J.map (S.smoothInclusion.app X) := by
    simpa only [NatTrans.comp_app, Functor.map_comp] using
      congrArg J.map (congrArg (fun k => k.app X) (S.smoothInclusionOfLE_comp T h))
  change (∃ w, SmoothRep.hom (J.map (S.smoothInclusion.app X)) w =
      SmoothRep.hom (J.map (T.smoothInclusion.app X)) v) ↔
    v ∈ LinearMap.ker
      (SmoothRep.hom (J.map ((S.smoothQuotientProjection T).app X))).toLinearMap
  rw [← hex]
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨w, ?_⟩
    apply ExactSmoothTransport.map_injective J hJ
      (T.smoothInclusion.app X) ((F.obj X).subtype_injective _)
    exact (congrArg (fun k => SmoothRep.hom k w) hfac).trans hw
  · rintro ⟨w, rfl⟩
    exact ⟨w, (congrArg (fun k => SmoothRep.hom k w) hfac).symm⟩

theorem exactImageQuotientMap_surjective
    (hJ : Derivative.Mirabolic.MapsShortExactIntertwiners J)
    (h : ∀ X, S.obj X ≤ T.obj X) (X : C) :
    Function.Surjective ((S.exactImageQuotientMap T J hJ).app X).hom := by
  have hs := (hJ _ _ _ ((S.smoothInclusionOfLE T h).app X)
    ((S.smoothQuotientProjection T).app X)
    (S.smoothInclusionOfLE_injective T h X)
    (S.quotientProjection_surjective T X)
    (S.smoothInclusionOfLE_range T h X)).2.2
  intro v
  obtain ⟨w, rfl⟩ := hs v
  exact ⟨((T.exactImageHom J).app X).hom w,
    S.exactImageQuotientMap_apply T J hJ X w⟩

/-- The natural first-isomorphism comparison for actual successive quotients. -/
def exactImageQuotientIso
    (hJ : Derivative.Mirabolic.MapsShortExactIntertwiners J)
    (h : ∀ X, S.obj X ≤ T.obj X) :
    (S.exactImage J).quotientFunctor (T.exactImage J) ≅
      S.smoothQuotientFunctor T ⋙ J ⋙ SmoothRep.toRep :=
  (S.exactImage J).quotientNatIsoOfSurjective (T.exactImage J)
    (S.exactImageQuotientMap T J hJ)
    (S.exactImageQuotientMap_kernel T J hJ h)
    (S.exactImageQuotientMap_surjective T J hJ h)

end RepSubfunctor

namespace RepFunctorFiltration

variable {F : C ⥤ SmoothRep.{0,uG,uV} ℂ G} {n : ℕ}

/-- Transport the actual steps by mapped smooth inclusions and invariant images.
Every supplied index, including repeated and zero steps, is retained. -/
def exactSmoothTransport (s : RepFunctorFiltration (F ⋙ SmoothRep.toRep) n)
    (J : SmoothRep.{0,uG,uV} ℂ G ⥤ SmoothRep.{0,uH,uV} ℂ H)
    [J.PreservesZeroMorphisms] :
    RepFunctorFiltration (F ⋙ J ⋙ SmoothRep.toRep) n where
  step i := (s.step i).exactImage J
  monotone X := by
    intro i j hij
    exact (s.step i).exactImage_mono (s.step j) J (fun Y => s.monotone Y hij) X
  zero X := (s.step 0).exactImage_zero J s.zero X
  top X := (s.step (Fin.last n)).exactImage_top J s.top X

@[simp]
theorem exactSmoothTransport_step_obj
    (s : RepFunctorFiltration (F ⋙ SmoothRep.toRep) n)
    (J : SmoothRep.{0,uG,uV} ℂ G ⥤ SmoothRep.{0,uH,uV} ℂ H)
    [J.PreservesZeroMorphisms] (i : Fin (n + 1)) (X : C) :
    ((s.exactSmoothTransport J).step i).obj X =
      (SmoothRep.hom (J.map ((s.step i).smoothInclusion.app X))).range := rfl

/-- Canonical smooth lifts of the actual successive quotient functors. -/
def smoothGraded (s : RepFunctorFiltration (F ⋙ SmoothRep.toRep) n) (i : Fin n) :
    C ⥤ SmoothRep.{0,uG,uV} ℂ G :=
  (s.step i.castSucc).smoothQuotientFunctor (s.step i.succ)

/-- Forgetting the lift recovers the supplied actual grade naturally. -/
def smoothGradedForgetIso (s : RepFunctorFiltration (F ⋙ SmoothRep.toRep) n)
    (i : Fin n) : s.smoothGraded i ⋙ SmoothRep.toRep ≅ s.graded i :=
  (s.step i.castSucc).smoothQuotientForgetIso (s.step i.succ)

/-- Each transported grade is naturally the exact functor applied to the
canonical smooth lift of the original actual grade. -/
def exactSmoothTransportGradedIso
    (s : RepFunctorFiltration (F ⋙ SmoothRep.toRep) n)
    (J : SmoothRep.{0,uG,uV} ℂ G ⥤ SmoothRep.{0,uH,uV} ℂ H)
    [J.PreservesZeroMorphisms]
    (hJ : Derivative.Mirabolic.MapsShortExactIntertwiners J) (i : Fin n) :
    (s.exactSmoothTransport J).graded i ≅
      s.smoothGraded i ⋙ J ⋙ SmoothRep.toRep :=
  (s.step i.castSucc).exactImageQuotientIso (s.step i.succ) J hJ
    (fun X => s.step_le_next X i)

/-- The comparison sends the class of a mapped upper vector to its mapped
quotient class. This also fixes the canonical comparison on representatives. -/
@[simp]
theorem exactSmoothTransportGradedIso_projection
    (s : RepFunctorFiltration (F ⋙ SmoothRep.toRep) n)
    (J : SmoothRep.{0,uG,uV} ℂ G ⥤ SmoothRep.{0,uH,uV} ℂ H)
    [J.PreservesZeroMorphisms]
    (hJ : Derivative.Mirabolic.MapsShortExactIntertwiners J)
    (i : Fin n) (X : C) (v : J.obj ((s.step i.succ).smoothFunctor.obj X)) :
    ((s.exactSmoothTransportGradedIso J hJ i).hom.app X).hom
        ((((s.exactSmoothTransport J).step i.castSucc).quotientProjection
          ((s.exactSmoothTransport J).step i.succ) X).hom
          ((((s.step i.succ).exactImageHom J).app X).hom v)) =
      SmoothRep.hom
        (J.map (((s.step i.castSucc).smoothQuotientProjection
          (s.step i.succ)).app X)) v := by
  change (((s.step i.castSucc).exactImageQuotientMap
    (s.step i.succ) J hJ).app X).hom
      ((((s.step i.succ).exactImageHom J).app X).hom v) = _
  exact (s.step i.castSucc).exactImageQuotientMap_apply (s.step i.succ) J hJ X v

/-- A supplied algebraic grade identification lifts through the full smooth
inclusion and is then transported by the exact functor. -/
def exactSmoothTransportPieceIso
    (s : RepFunctorFiltration (F ⋙ SmoothRep.toRep) n)
    (J : SmoothRep.{0,uG,uV} ℂ G ⥤ SmoothRep.{0,uH,uV} ℂ H)
    [J.PreservesZeroMorphisms]
    (hJ : Derivative.Mirabolic.MapsShortExactIntertwiners J)
    (P : C ⥤ SmoothRep.{0,uG,uV} ℂ G) (i : Fin n)
    (e : s.graded i ≅ P ⋙ SmoothRep.toRep) :
    (s.exactSmoothTransport J).graded i ≅ P ⋙ J ⋙ SmoothRep.toRep :=
  s.exactSmoothTransportGradedIso J hJ i ≪≫
    Functor.isoWhiskerRight
      (ExactSmoothTransport.liftNatIso (s.smoothGradedForgetIso i ≪≫ e))
      (J ⋙ SmoothRep.toRep)

theorem HasGradedPieces.exactSmoothTransport
    {s : RepFunctorFiltration (F ⋙ SmoothRep.toRep) n}
    {P : Fin n → C ⥤ SmoothRep.{0,uG,uV} ℂ G}
    (h : s.HasGradedPieces (fun i => P i ⋙ SmoothRep.toRep))
    (J : SmoothRep.{0,uG,uV} ℂ G ⥤ SmoothRep.{0,uH,uV} ℂ H)
    [J.PreservesZeroMorphisms]
    (hJ : Derivative.Mirabolic.MapsShortExactIntertwiners J) :
    (s.exactSmoothTransport J).HasGradedPieces
      (fun i => P i ⋙ J ⋙ SmoothRep.toRep) := by
  intro i
  obtain ⟨e⟩ := h i
  exact ⟨s.exactSmoothTransportPieceIso J hJ (P i) i e⟩

end RepFunctorFiltration

theorem HasOrderedFiltration.exactSmoothTransport
    {F : C ⥤ SmoothRep.{0,uG,uV} ℂ G} {n : ℕ}
    {P : Fin n → C ⥤ SmoothRep.{0,uG,uV} ℂ G}
    (h : HasOrderedFiltration (F ⋙ SmoothRep.toRep) (fun i => P i ⋙ SmoothRep.toRep))
    (J : SmoothRep.{0,uG,uV} ℂ G ⥤ SmoothRep.{0,uH,uV} ℂ H)
    [J.PreservesZeroMorphisms]
    (hJ : Derivative.Mirabolic.MapsShortExactIntertwiners J) :
    HasOrderedFiltration (F ⋙ J ⋙ SmoothRep.toRep)
      (fun i => P i ⋙ J ⋙ SmoothRep.toRep) := by
  obtain ⟨s, hs⟩ := h
  exact ⟨s.exactSmoothTransport J, hs.exactSmoothTransport J hJ⟩

theorem IsGluedFrom.exactSmoothTransport
    {F : C ⥤ SmoothRep.{0,uG,uV} ℂ G} {n : ℕ}
    {P : Fin n → C ⥤ SmoothRep.{0,uG,uV} ℂ G}
    (h : IsGluedFrom (F ⋙ SmoothRep.toRep) (fun i => P i ⋙ SmoothRep.toRep))
    (J : SmoothRep.{0,uG,uV} ℂ G ⥤ SmoothRep.{0,uH,uV} ℂ H)
    [J.PreservesZeroMorphisms]
    (hJ : Derivative.Mirabolic.MapsShortExactIntertwiners J) :
    IsGluedFrom (F ⋙ J ⋙ SmoothRep.toRep)
      (fun i => P i ⋙ J ⋙ SmoothRep.toRep) := by
  obtain ⟨e, he⟩ := h
  exact ⟨e, HasOrderedFiltration.exactSmoothTransport (P := fun i => P (e i)) he J hJ⟩

end Langlands
