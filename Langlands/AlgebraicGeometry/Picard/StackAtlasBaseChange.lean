import Langlands.AlgebraicGeometry.Picard.StackAtlas
import Langlands.CategoryTheory.Sites.PseudofunctorPointFiberTransport
import Langlands.CategoryTheory.Sites.PseudofunctorPointFiberObjectIso
import Langlands.CategoryTheory.Sites.PseudofunctorPointFiberReindex
import Langlands.CategoryTheory.Sites.PseudofunctorReindexIso
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-! # Base change of smooth scheme atlases of the actual Picard stack -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Langlands.AlgebraicGeometry.Picard.PicardGroupoid

open Langlands.CategoryTheory

variable {S S' X X' : Scheme.{u}} {f : X ⟶ S} {g : X' ⟶ S'} {π : X' ⟶ X} {s : S' ⟶ S}
  (hπ : IsPullback π g f s)

/-- For `X'` the base change of `X` along `s`, the fibre product `T ×_{S'} X'` is
`T ×_S X`, naturally in `T`. -/
def baseChangeRelativeSpaceIso : relativeSpace g ≅ Over.map s ⋙ relativeSpace f :=
  NatIso.ofComponents
    (fun T ↦ ((IsPullback.of_hasPullback T.hom g).flip.paste_horiz hπ).flip.isoPullback)
    (by
      intro T₁ T₂ h
      apply pullback.hom_ext
      · simp [relativeSpace]
      · simp [relativeSpace])

/-- The comparison of the actual relative Picard pseudofunctors induced by
`baseChangeRelativeSpaceIso`: pull back along its inverse components. -/
abbrev baseChangeStrongTrans :
    Pseudofunctor.StrongTrans (relative g) (StackPullback.reindex (Over.map s) (relative f)) :=
  PseudofunctorReindexIso.strongTrans pseudofunctor (baseChangeRelativeSpaceIso hπ)

variable (s) in
/-- Iterated slices over `T` followed by `Over.map s` are iterated slices over the image
of `T`. -/
def iteratedSlicePostMapIso (T : Over S') :
    T.iteratedSliceBackward ⋙ Over.post (Over.map s) ≅
      ((Over.map s).obj T).iteratedSliceBackward :=
  NatIso.ofComponents
    (fun Z ↦ Over.isoMk (Over.isoMk (Iso.refl _) (by simp)) (by ext; simp))
    (by intro Z Z' q; ext; simp)

variable {U₀ : Over S} (L₀ : LineBundle ((relativeSpace f).obj U₀))

/-- The atlas line bundle over `U₀` pulled back along the counit of `Over.map s ⊣
Over.pullback s`, an object over `Over.map s` of the base change of `U₀`. -/
abbrev baseChangeCounitBundle :
    (StackPullback.reindex (Over.map s) (relative f)).obj
      (.mk (op ((Over.pullback s).obj U₀))) :=
  PseudofunctorPointFiberReindex.counitObj (relative f) (Over.mapPullbackAdj s) (Core.mk L₀)

/-- The base-changed atlas line bundle on `((Over.pullback s).obj U₀) ×_{S'} X'`. -/
def baseChangeAtlasBundle : LineBundle ((relativeSpace g).obj ((Over.pullback s).obj U₀)) :=
  ((PseudofunctorReindexIso.mapIsoEquivalence pseudofunctor
    ((baseChangeRelativeSpaceIso hπ).app ((Over.pullback s).obj U₀)).symm).inverse.obj
      (baseChangeCounitBundle (s := s) L₀)).of

variable {T : Over S'} (M : LineBundle ((relativeSpace g).obj T))

/-- A test line bundle on `T ×_{S'} X'`, transported to `T ×_S X`. -/
def baseChangeTestBundle : LineBundle ((relativeSpace f).obj ((Over.map s).obj T)) :=
  (((baseChangeStrongTrans hπ).app (.mk (op T))).toFunctor.obj (Core.mk M)).of

/-- The actual point-fibre presheaf of the base-changed atlas bundle at `M`, as a
presheaf on the full slice over `T`, is that of the original atlas at the
transported test bundle, restricted along `Over.post (Over.map s)`. -/
def baseChangePresheafIso :
    PseudofunctorPointFiber.presheaf (relative g)
        (Core.mk (baseChangeAtlasBundle hπ L₀)) (Core.mk M) ≅
      (Over.post (Over.map s)).op ⋙ PseudofunctorPointFiber.presheaf (relative f)
        (Core.mk L₀) (Core.mk (baseChangeTestBundle hπ M)) :=
  PseudofunctorPointFiberTransport.presheafIso (baseChangeStrongTrans hπ)
      (Core.mk (baseChangeAtlasBundle hπ L₀)) (Core.mk M)
      (fun Z ↦ PseudofunctorReindexIso.strongTransFullyFaithful pseudofunctor
        (baseChangeRelativeSpaceIso hπ) Z) ≪≫
    PseudofunctorPointFiberObjectIso.presheafIso
      (StackPullback.reindex (Over.map s) (relative f))
      ((PseudofunctorReindexIso.mapIsoEquivalence pseudofunctor
        ((baseChangeRelativeSpaceIso hπ).app ((Over.pullback s).obj U₀)).symm).counitIso.app
          (baseChangeCounitBundle (s := s) L₀))
      (Core.mk (baseChangeTestBundle hπ M)) ≪≫
    PseudofunctorPointFiberReindex.adjPresheafIso (relative f) (Over.mapPullbackAdj s)
      (Core.mk L₀) (Core.mk (baseChangeTestBundle hπ M))

/-- The full actual point-fibre presheaf on `Over T.left` is unchanged by base change. -/
def baseChangePointFiberIso :
    pointFiberPresheaf g (baseChangeAtlasBundle hπ L₀) M ≅
      pointFiberPresheaf f L₀ (baseChangeTestBundle hπ M) :=
  Functor.isoWhiskerRight
    (Functor.isoWhiskerLeft T.iteratedSliceBackward.op (baseChangePresheafIso hπ L₀ M) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (NatIso.op (iteratedSlicePostMapIso s T)).symm _)
    uliftFunctor.{u + 1}

include hπ in
/-- A smooth surjective scheme atlas, locally of finite type over the base, of the
actual Picard stack of `X / S` base changes to one of `X' / S'`. -/
theorem hasLocallyFiniteTypeSmoothSchemeAtlas_of_isPullback
    (h : HasLocallyFiniteTypeSmoothSchemeAtlas f) :
    HasLocallyFiniteTypeSmoothSchemeAtlas g := by
  obtain ⟨U₀, L₀, hU₀, hL₀⟩ := h
  refine ⟨(Over.pullback s).obj U₀, baseChangeAtlasBundle hπ L₀, ?_, ?_⟩
  · have : LocallyOfFiniteType U₀.hom := hU₀
    exact (inferInstance : LocallyOfFiniteType (pullback.snd U₀.hom s))
  · intro T M
    obtain ⟨P, ⟨e⟩, hsm, hsurj⟩ := hL₀ ((Over.map s).obj T) (baseChangeTestBundle hπ M)
    exact ⟨P, ⟨e ≪≫ (baseChangePointFiberIso hπ L₀ M).symm⟩, hsm, hsurj⟩

end Langlands.AlgebraicGeometry.Picard.PicardGroupoid
