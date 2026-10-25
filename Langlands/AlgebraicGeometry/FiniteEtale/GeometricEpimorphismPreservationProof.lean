import Langlands.AlgebraicGeometry.FiniteEtale.MonoEpiConservativeStatements
import Langlands.AlgebraicGeometry.FiniteEtale.GeometricFiniteLimitsCoproductsProof
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

open CategoryTheory CategoryTheory.Limits

universe u

set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.FiniteEtale.EpiPreservation

open _root_.AlgebraicGeometry Langlands.AlgebraicGeometry.FiniteEtale

variable {S : Scheme.{u}}

/-- The underlying morphism of schemes of a morphism of finite étale covers is finite étale. -/
theorem finiteEtale_hom_left {X Y : Cover S} (f : X ⟶ Y) : finiteEtale f.hom.left :=
  finiteEtale.of_postcomp (W' := finiteEtale) f.hom.left Y.obj.hom Y.property
    (by rw [Over.w f.hom]; exact X.property)

/-- The range of a morphism of finite étale covers is open and closed. -/
theorem isClopen_range_hom_left {X Y : Cover S} (f : X ⟶ Y) :
    IsClopen (Set.range f.hom.left) := by
  have := (finiteEtale_hom_left f).1
  have := (finiteEtale_hom_left f).2
  exact ⟨f.hom.left.isClosedMap.isClosed_range, f.hom.left.isOpenMap.isOpen_range⟩

/-- An epimorphism of finite étale covers is surjective on underlying points. -/
theorem surjective_hom_left_of_epi {X Y : Cover S} (f : X ⟶ Y) [Epi f] :
    Function.Surjective f.hom.left := by
  have hc := isClopen_range_hom_left f
  let U : Y.obj.left.Opens := ⟨Set.range f.hom.left, hc.isOpen⟩
  let V : Y.obj.left.Opens := ⟨(Set.range f.hom.left)ᶜ, hc.compl.isOpen⟩
  have hUV : IsCompl U.ι.opensRange V.ι.opensRange := by
    rw [Scheme.Opens.opensRange_ι, Scheme.Opens.opensRange_ι]
    simp only [isCompl_iff, disjoint_iff, codisjoint_iff, ← TopologicalSpace.Opens.coe_inj]
    simp [U, V]
  obtain ⟨hcol⟩ := nonempty_isColimit_binaryCofanMk_of_isCompl U.ι V.ι hUV
  have : Etale (coprod.desc Y.obj.hom Y.obj.hom) := etale_coprod_desc _ _
  let T : Cover S := cover (coprod.desc Y.obj.hom Y.obj.hom)
  let d : Y.obj.left ⟶ Y.obj.left ⨿ Y.obj.left :=
    hcol.desc (BinaryCofan.mk (U.ι ≫ coprod.inl) (V.ι ≫ coprod.inr))
  have hd₁ : U.ι ≫ d = U.ι ≫ coprod.inl := hcol.fac _ ⟨.left⟩
  have hd₂ : V.ι ≫ d = V.ι ≫ coprod.inr := hcol.fac _ ⟨.right⟩
  have hdw : d ≫ coprod.desc Y.obj.hom Y.obj.hom = Y.obj.hom := by
    refine BinaryCofan.IsColimit.hom_ext hcol ?_ ?_
    · simp [reassoc_of% hd₁]
    · simp [reassoc_of% hd₂]
  let g₁ : Y ⟶ T := ObjectProperty.homMk (Over.homMk (U := Y.obj) (V := T.obj)
    coprod.inl (by simp [T, cover]))
  let g₂ : Y ⟶ T := ObjectProperty.homMk (Over.homMk (U := Y.obj) (V := T.obj) d hdw)
  have hfac : IsOpenImmersion.lift U.ι f.hom.left (by rw [Scheme.Opens.range_ι]; rfl) ≫ U.ι =
      f.hom.left := IsOpenImmersion.lift_fac _ _ _
  have hg : g₁ = g₂ := by
    rw [← cancel_epi f]
    ext1
    apply Over.OverMorphism.ext
    change f.hom.left ≫ coprod.inl = f.hom.left ≫ d
    rw [← hfac, Category.assoc, Category.assoc, hd₁]
  have hV : V.ι ≫ coprod.inl = V.ι ≫ coprod.inr := by
    rw [← hd₂]
    have h : (coprod.inl : Y.obj.left ⟶ _) = d := congrArg (fun g => g.hom.left) hg
    rw [h]
  intro y
  by_contra hy
  have hpt := congrArg (fun φ => φ (⟨y, hy⟩ : V)) hV
  simp only [Scheme.Hom.comp_apply] at hpt
  exact inl_ne_inr _ _ _ _ hpt

variable {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)

/-- Every geometric point of the target of an epimorphism of finite étale covers lifts to its
source. -/
theorem exists_lift_of_epi {X Y : Cover S} (f : X ⟶ Y) [Epi f] (y : Fiber s Y) :
    ∃ x : Fiber s X, x ≫ f.hom = y := by
  have := (finiteEtale_hom_left f).1
  obtain ⟨pt⟩ : Nonempty (Spec (.of Ω)) := inferInstance
  obtain ⟨x, hx⟩ := surjective_hom_left_of_epi f (y.left pt)
  obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback x pt hx
  let g := pullback.snd f.hom.left y.left
  obtain ⟨p, -, hp⟩ := IsClosed.exists_closed_singleton isClosed_univ ⟨z, Set.mem_univ z⟩
  let σ := pointOfClosedPoint g p hp
  have hσ : σ ≫ g = 𝟙 _ := pointOfClosedPoint_comp g p hp
  have hy : y.left ≫ Y.obj.hom = s := Over.w y
  have hf : f.hom.left ≫ Y.obj.hom = X.obj.hom := Over.w f.hom
  have hlift : σ ≫ pullback.fst f.hom.left y.left ≫ f.hom.left = y.left := by
    rw [pullback.condition, ← Category.assoc]
    change (σ ≫ g) ≫ y.left = y.left
    rw [hσ, Category.id_comp]
  refine ⟨Over.homMk (U := Over.mk s) (V := X.obj) (σ ≫ pullback.fst f.hom.left y.left) ?_, ?_⟩
  · change (σ ≫ pullback.fst f.hom.left y.left) ≫ X.obj.hom = s
    rw [← hf, Category.assoc, reassoc_of% hlift, hy]
  · apply Over.OverMorphism.ext
    simpa using hlift

/-- The point functor of finite étale covers preserves epimorphisms. -/
theorem preservesEpimorphisms_pointFunctor :
    Functor.PreservesEpimorphisms (pointFunctor s) :=
  ⟨fun f _ => (epi_iff_surjective _).mpr fun y => exists_lift_of_epi s f y⟩

end Langlands.AlgebraicGeometry.FiniteEtale.EpiPreservation

namespace Langlands.AlgebraicGeometry.FiniteEtale

open _root_.AlgebraicGeometry

/-- The geometric fibre functor of finite étale covers preserves epimorphisms. -/
theorem geometricEpimorphismPreservation {S : Scheme.{u}} [ConnectedSpace S]
    [IsLocallyNoetherian S] {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) (hfin : ∀ Y : Cover S, Finite (Fiber s Y)) :
    GeometricEpimorphismPreservation s hfin := by
  have : Functor.PreservesEpimorphisms (fiberFunctor s hfin ⋙ FintypeCat.incl) :=
    EpiPreservation.preservesEpimorphisms_pointFunctor s
  exact Functor.preservesEpimorphisms_of_preserves_of_reflects (fiberFunctor s hfin)
    FintypeCat.incl

end Langlands.AlgebraicGeometry.FiniteEtale
