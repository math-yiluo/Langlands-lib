import Langlands.Representation.Filtration.OneStep
import Langlands.Representation.Filtration.ExactSmoothTransport
import Langlands.Representation.Derivative.ShortExactFunctorLaws

/-! Natural comparisons for actual smooth cokernels under exact functors. -/

noncomputable section
open CategoryTheory

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands

universe uG uH uV uC vC

variable {G : Type uG} [Group G] [TopologicalSpace G]
  {H : Type uH} [Group H] [TopologicalSpace H]
  {C : Type uC} [Category.{vC} C]

namespace RepSubfunctor

variable {F : C ⥤ SmoothRep.{0,uG,uV} ℂ G}

/-- Quotient the ambient smooth representation by the specified actual subfunctor. -/
def ambientQuotient (S : RepSubfunctor (F ⋙ SmoothRep.toRep)) :
    C ⥤ SmoothRep.{0,uG,uV} ℂ G where
  obj X := (F.obj X).quotient (S.obj X)
  map f := SmoothRep.ofHom
    { toLinearMap := Submodule.mapQ (S.obj _).toSubmodule (S.obj _).toSubmodule
        (SmoothRep.hom (F.map f)).toLinearMap (fun _ hv => S.map_mem f hv)
      isIntertwining' := by
        intro g
        apply LinearMap.ext
        intro v
        obtain ⟨v, rfl⟩ := (F.obj _).mkQ_surjective (S.obj _) v
        exact congrArg (S.obj _).toSubmodule.mkQ
          (Rep.hom_comm_apply (F.map f).hom g v) }
  map_id X := by
    apply ObjectProperty.hom_ext
    ext v
    obtain ⟨v, rfl⟩ := (F.obj X).mkQ_surjective (S.obj X) v
    exact congrArg (S.obj X).toSubmodule.mkQ
      (congrArg (fun k => SmoothRep.hom k v) (F.map_id X))
  map_comp f g := by
    apply ObjectProperty.hom_ext
    ext v
    obtain ⟨v, rfl⟩ := (F.obj _).mkQ_surjective (S.obj _) v
    exact congrArg (S.obj _).toSubmodule.mkQ
      (congrArg (fun k => SmoothRep.hom k v) (F.map_comp f g))

/-- The canonical natural projection onto the ambient quotient. -/
def ambientProjection (S : RepSubfunctor (F ⋙ SmoothRep.toRep)) :
    F ⟶ S.ambientQuotient where
  app X := (F.obj X).mkQ (S.obj X)
  naturality _ _ _ := rfl

/-- The ambient projection has the specified invariant submodule as kernel. -/
theorem ambientProjection_ker (S : RepSubfunctor (F ⋙ SmoothRep.toRep)) (X : C) :
    (S.obj X).toSubmodule =
      LinearMap.ker (SmoothRep.hom (S.ambientProjection.app X)).toLinearMap :=
  (Submodule.ker_mkQ _).symm

theorem ambientProjection_surjective (S : RepSubfunctor (F ⋙ SmoothRep.toRep))
    (X : C) : Function.Surjective (SmoothRep.hom (S.ambientProjection.app X)) :=
  (F.obj X).mkQ_surjective (S.obj X)

/-- Reuse the natural first isomorphism theorem on the full upper subfunctor. -/
def fullFirstIso (S : RepSubfunctor (F ⋙ SmoothRep.toRep))
    {Q : C ⥤ SmoothRep.{0,uG,uV} ℂ G} (π : F ⟶ Q)
    (hker : ∀ X, (S.obj X).toSubmodule =
      LinearMap.ker (SmoothRep.hom (π.app X)).toLinearMap)
    (hsurj : ∀ X, Function.Surjective (SmoothRep.hom (π.app X))) :
    S.quotientFunctor (full (F ⋙ SmoothRep.toRep)) ≅ Q ⋙ SmoothRep.toRep := by
  let T : RepSubfunctor (F ⋙ SmoothRep.toRep) := (full (F ⋙ SmoothRep.toRep))
  let q := Functor.whiskerRight π SmoothRep.toRep
  exact S.quotientNatIsoOfSurjective T (T.inclusion ≫ q)
      (by
        intro X v
        change v.val ∈ (S.obj X).toSubmodule ↔ SmoothRep.hom (π.app X) v.val = 0
        rw [hker X]
        rfl)
      (by
        intro X v
        obtain ⟨v, rfl⟩ := hsurj X v
        exact ⟨⟨v, trivial⟩, rfl⟩)

@[simp]
theorem fullFirstIso_hom_projection (S : RepSubfunctor (F ⋙ SmoothRep.toRep))
    {Q : C ⥤ SmoothRep.{0,uG,uV} ℂ G} (π : F ⟶ Q)
    (hker : ∀ X, (S.obj X).toSubmodule =
      LinearMap.ker (SmoothRep.hom (π.app X)).toLinearMap)
    (hsurj : ∀ X, Function.Surjective (SmoothRep.hom (π.app X)))
    (X : C) (v : F.obj X) :
    ((S.fullFirstIso π hker hsurj).hom.app X).hom
      ((S.quotientProjection (full (F ⋙ SmoothRep.toRep)) X).hom ⟨v, trivial⟩) =
        SmoothRep.hom (π.app X) v := rfl

@[simp]
theorem fullFirstIso_inv_projection (S : RepSubfunctor (F ⋙ SmoothRep.toRep))
    {Q : C ⥤ SmoothRep.{0,uG,uV} ℂ G} (π : F ⟶ Q)
    (hker : ∀ X, (S.obj X).toSubmodule =
      LinearMap.ker (SmoothRep.hom (π.app X)).toLinearMap)
    (hsurj : ∀ X, Function.Surjective (SmoothRep.hom (π.app X)))
    (X : C) (v : F.obj X) :
    ((S.fullFirstIso π hker hsurj).inv.app X).hom
      (SmoothRep.hom (π.app X) v) =
        (S.quotientProjection (full (F ⋙ SmoothRep.toRep)) X).hom ⟨v, trivial⟩ := by
  exact Rep.inv_hom_apply _ _ ((S.fullFirstIso π hker hsurj).app X)
    ((S.quotientProjection (full (F ⋙ SmoothRep.toRep)) X).hom ⟨v, trivial⟩)

/-- The natural first-isomorphism comparison on actual ambient quotients. -/
def ambientFirstIso (S : RepSubfunctor (F ⋙ SmoothRep.toRep))
    {Q : C ⥤ SmoothRep.{0,uG,uV} ℂ G} (π : F ⟶ Q)
    (hker : ∀ X, (S.obj X).toSubmodule =
      LinearMap.ker (SmoothRep.hom (π.app X)).toLinearMap)
    (hsurj : ∀ X, Function.Surjective (SmoothRep.hom (π.app X))) :
    S.ambientQuotient ≅ Q :=
  ExactSmoothTransport.liftNatIso
    ((S.fullFirstIso S.ambientProjection S.ambientProjection_ker
      S.ambientProjection_surjective).symm ≪≫ S.fullFirstIso π hker hsurj)

/-- The first-isomorphism comparison retains the original quotient map. -/
@[simp]
theorem ambientFirstIso_projection (S : RepSubfunctor (F ⋙ SmoothRep.toRep))
    {Q : C ⥤ SmoothRep.{0,uG,uV} ℂ G} (π : F ⟶ Q)
    (hker : ∀ X, (S.obj X).toSubmodule =
      LinearMap.ker (SmoothRep.hom (π.app X)).toLinearMap)
    (hsurj : ∀ X, Function.Surjective (SmoothRep.hom (π.app X)))
    (X : C) (v : F.obj X) :
    SmoothRep.hom ((S.ambientFirstIso π hker hsurj).hom.app X)
      (SmoothRep.hom (S.ambientProjection.app X) v) =
        SmoothRep.hom (π.app X) v := by
  change ((S.fullFirstIso π hker hsurj).hom.app X).hom
    (((S.fullFirstIso S.ambientProjection S.ambientProjection_ker
      S.ambientProjection_surjective).inv.app X).hom
        (SmoothRep.hom (S.ambientProjection.app X) v)) = _
  rw [fullFirstIso_inv_projection, fullFirstIso_hom_projection]

end RepSubfunctor

namespace SmoothNatCokernel

variable {A B Q : C ⥤ SmoothRep.{0,uG,uV} ℂ G}

/-- The invariant ranges of a natural transformation form an actual subfunctor. -/
def range (α : A ⟶ B) : RepSubfunctor (B ⋙ SmoothRep.toRep) where
  obj X := (SmoothRep.hom (α.app X)).range
  map_mem := by
    intro X Y f v hv
    obtain ⟨w, rfl⟩ := hv
    exact ⟨SmoothRep.hom (A.map f) w,
      congrArg (fun k => SmoothRep.hom k w) (α.naturality f)⟩

/-- The actual smooth module cokernel, with its actual induced natural maps. -/
abbrev functor (α : A ⟶ B) : C ⥤ SmoothRep.{0,uG,uV} ℂ G :=
  (range α).ambientQuotient

/-- The canonical natural cokernel projection. -/
abbrev projection (α : A ⟶ B) : B ⟶ functor α :=
  (range α).ambientProjection

/-- A natural surjection with the specified image kernel identifies its actual cokernel. -/
def isoOfSurjective (α : A ⟶ B) (π : B ⟶ Q)
    (hex : ∀ X, LinearMap.range (SmoothRep.hom (α.app X)).toLinearMap =
      LinearMap.ker (SmoothRep.hom (π.app X)).toLinearMap)
    (hsurj : ∀ X, Function.Surjective (SmoothRep.hom (π.app X))) :
    functor α ≅ Q :=
  (range α).ambientFirstIso π hex hsurj

@[simp]
theorem isoOfSurjective_projection (α : A ⟶ B) (π : B ⟶ Q)
    (hex : ∀ X, LinearMap.range (SmoothRep.hom (α.app X)).toLinearMap =
      LinearMap.ker (SmoothRep.hom (π.app X)).toLinearMap)
    (hsurj : ∀ X, Function.Surjective (SmoothRep.hom (π.app X)))
    (X : C) (v : B.obj X) :
    SmoothRep.hom ((isoOfSurjective α π hex hsurj).hom.app X)
      (SmoothRep.hom ((projection α).app X) v) =
        SmoothRep.hom (π.app X) v :=
  (range α).ambientFirstIso_projection π hex hsurj X v

end SmoothNatCokernel

namespace ExactSmoothTransport

variable (J : SmoothRep.{0,uG,uV} ℂ G ⥤ SmoothRep.{0,uH,uV} ℂ H)
  (hJ : Derivative.Mirabolic.MapsShortExactIntertwiners J)

include hJ in
/-- Short-exactness preserves middle exactness even when the incoming map is
not injective: factor it through its actual smooth image. -/
theorem map_range_eq_ker {A B Q : SmoothRep.{0,uG,uV} ℂ G}
    (f : A ⟶ B) (q : B ⟶ Q)
    (hex : LinearMap.range (SmoothRep.hom f).toLinearMap =
      LinearMap.ker (SmoothRep.hom q).toLinearMap)
    (hq : Function.Surjective (SmoothRep.hom q)) :
    LinearMap.range (SmoothRep.hom (J.map f)).toLinearMap =
      LinearMap.ker (SmoothRep.hom (J.map q)).toLinearMap := by
  let S := (SmoothRep.hom f).range
  let p : A ⟶ B.subrepresentation S := SmoothRep.ofHom
    { toLinearMap :=
        { toFun := fun v => ⟨SmoothRep.hom f v, ⟨v, rfl⟩⟩
          map_add' := by intros; apply Subtype.ext; exact map_add _ _ _
          map_smul' := by intros; apply Subtype.ext; exact map_smul _ _ _ }
      isIntertwining' := by
        intro g
        apply LinearMap.ext
        intro v
        apply Subtype.ext
        exact Rep.hom_comm_apply f.hom g v }
  have hp : Function.Surjective (SmoothRep.hom p) := by
    intro v
    obtain ⟨w, hw⟩ := v.property
    exact ⟨w, Subtype.ext hw⟩
  have hfac : p ≫ B.subtype S = f := rfl
  have hi := hJ _ _ _ (B.subtype S) q (B.subtype_injective S) hq
    (by
      change LinearMap.range S.toSubmodule.subtype = _
      rw [Submodule.range_subtype]
      exact hex)
  rw [← hi.2.1]
  rw [← hfac, J.map_comp]
  apply Submodule.ext
  intro v
  change (∃ w, SmoothRep.hom (J.map (B.subtype S))
    (SmoothRep.hom (J.map p) w) = v) ↔
      ∃ w, SmoothRep.hom (J.map (B.subtype S)) w = v
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨SmoothRep.hom (J.map p) w, rfl⟩
  · rintro ⟨w, rfl⟩
    obtain ⟨z, rfl⟩ := Derivative.LevelCalculus.map_surjective_of_exact hJ p hp w
    exact ⟨z, rfl⟩

/-- An exact smooth functor carries any natural cokernel presentation to the
actual cokernel of its mapped natural transformation. -/
def cokernelIso {A B Q : C ⥤ SmoothRep.{0,uG,uV} ℂ G}
    (α : A ⟶ B) (π : B ⟶ Q)
    (hex : ∀ X, LinearMap.range (SmoothRep.hom (α.app X)).toLinearMap =
      LinearMap.ker (SmoothRep.hom (π.app X)).toLinearMap)
    (hsurj : ∀ X, Function.Surjective (SmoothRep.hom (π.app X))) :
    SmoothNatCokernel.functor (Functor.whiskerRight α J) ≅ Q ⋙ J :=
  SmoothNatCokernel.isoOfSurjective (Functor.whiskerRight α J)
    (Functor.whiskerRight π J)
    (fun X => map_range_eq_ker J hJ (α.app X) (π.app X) (hex X) (hsurj X))
    (fun X => Derivative.LevelCalculus.map_surjective_of_exact hJ (π.app X) (hsurj X))

/-- The comparison commutes with the mapped presentation projection. -/
@[simp]
theorem cokernelIso_projection {A B Q : C ⥤ SmoothRep.{0,uG,uV} ℂ G}
    (α : A ⟶ B) (π : B ⟶ Q)
    (hex : ∀ X, LinearMap.range (SmoothRep.hom (α.app X)).toLinearMap =
      LinearMap.ker (SmoothRep.hom (π.app X)).toLinearMap)
    (hsurj : ∀ X, Function.Surjective (SmoothRep.hom (π.app X)))
    (X : C) (v : J.obj (B.obj X)) :
    SmoothRep.hom ((cokernelIso J hJ α π hex hsurj).hom.app X)
      (SmoothRep.hom ((SmoothNatCokernel.projection
        (Functor.whiskerRight α J)).app X) v) =
      SmoothRep.hom (J.map (π.app X)) v :=
  SmoothNatCokernel.isoOfSurjective_projection
    (Functor.whiskerRight α J) (Functor.whiskerRight π J)
    (fun X => map_range_eq_ker J hJ (α.app X) (π.app X) (hex X) (hsurj X))
    (fun X => Derivative.LevelCalculus.map_surjective_of_exact hJ (π.app X) (hsurj X))
    X v

end ExactSmoothTransport
end Langlands
