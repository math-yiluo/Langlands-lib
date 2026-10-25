import Langlands.AlgebraicGeometry.FiniteEtale.MonoEpiConservativeStatements
import Langlands.AlgebraicGeometry.FiniteEtale.GeometricFiniteLimitsCoproductsProof
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
import Mathlib.Topology.Connected.Clopen

open CategoryTheory CategoryTheory.Limits

universe u

set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.FiniteEtale

open _root_.AlgebraicGeometry

section Helpers

variable {S : Scheme.{u}} [ConnectedSpace S]
  {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)

/-- Surjectivity on one geometric fibre detects surjectivity of a cover morphism. -/
theorem cover_surjective_of_fiber_surjective {X Y : Cover S} (f : X ⟶ Y)
    (h : Function.Surjective (fun x : Fiber s X => x ≫ f.hom)) :
    Surjective f.hom.left := by
  classical
  have hfcomp : f.hom.left ≫ Y.obj.hom = X.obj.hom := Over.w f.hom
  have : IsFinite (f.hom.left ≫ Y.obj.hom) := hfcomp.symm ▸ inferInstance
  have : Etale (f.hom.left ≫ Y.obj.hom) := hfcomp.symm ▸ inferInstance
  have : IsFinite f.hom.left := IsFinite.of_comp _ Y.obj.hom
  have : Etale f.hom.left := Etale.of_comp _ Y.obj.hom
  let bad : Set S := Y.obj.hom '' (Set.range f.hom.left)ᶜ
  have hbad : IsClopen bad :=
    ⟨Y.obj.hom.isClosedMap _ f.hom.left.isOpenMap.isOpen_range.isClosed_compl,
      Y.obj.hom.isOpenMap _ f.hom.left.isClosedMap.isClosed_range.isOpen_compl⟩
  have hs : s default ∉ bad := by
    rintro ⟨y, hy, heq⟩
    obtain ⟨a, ha, hay⟩ :=
      Scheme.exists_fac_of_etale_of_isSepClosed Y.obj.hom s y heq
    obtain ⟨b, hb⟩ := h (Over.homMk a ha)
    apply hy
    refine ⟨b.left (default : Spec (.of Ω)), ?_⟩
    have hab := congrArg (fun t : Fiber s Y => t.left (default : Spec (.of Ω))) hb
    exact hab.trans hay
  have hempty : bad = ∅ :=
    (isClopen_iff.mp hbad).resolve_right (fun hu => hs (hu.symm ▸ Set.mem_univ _))
  constructor
  intro y
  by_contra hy
  have hm : Y.obj.hom y ∈ bad := ⟨y, hy, rfl⟩
  rw [hempty] at hm
  exact hm

/-- Injectivity on one geometric fibre detects a scheme monomorphism. -/
theorem cover_mono_of_fiber_injective {X Y : Cover S} (f : X ⟶ Y)
    (h : Function.Injective (fun x : Fiber s X => x ≫ f.hom)) :
    Mono f.hom.left := by
  have hfcomp : f.hom.left ≫ Y.obj.hom = X.obj.hom := Over.w f.hom
  have : IsFinite (f.hom.left ≫ Y.obj.hom) := hfcomp.symm ▸ inferInstance
  have : Etale (f.hom.left ≫ Y.obj.hom) := hfcomp.symm ▸ inferInstance
  have : IsFinite f.hom.left := IsFinite.of_comp _ Y.obj.hom
  have : Etale f.hom.left := Etale.of_comp _ Y.obj.hom
  let p := pullback.fst f.hom.left f.hom.left ≫ X.obj.hom
  let P : Cover S := ⟨Over.mk p,
    by change IsFinite p; dsimp [p]; infer_instance,
    by change Etale p; dsimp [p]; infer_instance⟩
  let d : X ⟶ P := ObjectProperty.homMk
    (Over.homMk (pullback.diagonal f.hom.left) (by simp [P, p]))
  have hd : Surjective (pullback.diagonal f.hom.left) := by
    apply cover_surjective_of_fiber_surjective s d
    intro a
    have ha₁ : (a.left ≫ pullback.fst f.hom.left f.hom.left) ≫ X.obj.hom = s :=
      Over.w a
    have ha₂ : (a.left ≫ pullback.snd f.hom.left f.hom.left) ≫ X.obj.hom = s := by
      rw [Category.assoc, ← hfcomp, ← pullback.condition_assoc, hfcomp]
      exact ha₁
    let a₁ : Fiber s X := Over.homMk (a.left ≫ pullback.fst _ _) ha₁
    let a₂ : Fiber s X := Over.homMk (a.left ≫ pullback.snd _ _) ha₂
    have heq : a₁ ≫ f.hom = a₂ ≫ f.hom := by
      apply Over.OverMorphism.ext
      simp [a₁, a₂, Category.assoc, pullback.condition]
    have heq' : a.left ≫ pullback.fst f.hom.left f.hom.left =
        a.left ≫ pullback.snd f.hom.left f.hom.left :=
      congrArg CommaMorphism.left (h heq)
    refine ⟨a₁, ?_⟩
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · simp [a₁, d, Category.assoc]
    · simpa [a₁, d, Category.assoc] using heq'
  have : IsIso (pullback.diagonal f.hom.left) :=
    Flat.isIso_of_surjective_of_mono (pullback.diagonal f.hom.left)
  exact (pullback.isIso_diagonal_iff f.hom.left).mp inferInstance

end Helpers

/-- One geometric fibre reflects isomorphisms of actual finite étale covers. -/
theorem geometricFiberConservative {S : Scheme.{u}} [ConnectedSpace S]
    [IsLocallyNoetherian S] {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S)
    (hfin : ∀ Y : Cover S, Finite (Fiber s Y)) :
    GeometricFiberConservative s hfin := by
  constructor
  intro X Y f hf
  have hbij : Function.Bijective (fun x : Fiber s X => x ≫ f.hom) :=
    ConcreteCategory.bijective_of_isIso ((fiberFunctor s hfin).map f)
  have : Surjective f.hom.left := cover_surjective_of_fiber_surjective s f hbij.2
  have : Mono f.hom.left := cover_mono_of_fiber_injective s f hbij.1
  have hfcomp : f.hom.left ≫ Y.obj.hom = X.obj.hom := Over.w f.hom
  have : IsFinite (f.hom.left ≫ Y.obj.hom) := hfcomp.symm ▸ inferInstance
  have : Etale (f.hom.left ≫ Y.obj.hom) := hfcomp.symm ▸ inferInstance
  have : IsFinite f.hom.left := IsFinite.of_comp _ Y.obj.hom
  have : Etale f.hom.left := Etale.of_comp _ Y.obj.hom
  have : IsIso f.hom.left := Flat.isIso_of_surjective_of_mono f.hom.left
  have : IsIso ((Over.forget S).map f.hom) := by
    change IsIso f.hom.left
    infer_instance
  have : IsIso f.hom := isIso_of_reflects_iso f.hom (Over.forget S)
  have : IsIso ((inclusion S).map f) := by
    change IsIso f.hom
    infer_instance
  exact isIso_of_reflects_iso f (inclusion S)

end Langlands.AlgebraicGeometry.FiniteEtale
