import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationPresentation
import Mathlib.CategoryTheory.Sites.LocallyInjective

/-! # Descent of maps along locally surjective maps from schemes

Let `a : h_V ⟶ F` be a locally surjective map from the functor of points of a scheme to an fppf
sheaf, with kernel pair represented by `t, s : R ⟶ V`. A map `b : h_V ⟶ G` to another fppf sheaf
with `h_t ≫ b = h_s ≫ b` factors uniquely through `a`. If `t, s` also represent the kernel pair of
`b`, the induced map `F ⟶ G` is injective on sections over every test scheme.
-/

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.AlgebraicSpace.KernelPairDescent

variable {S : Scheme.{u}}

/-- Two sections of `h_V` with the same image under `a` lift to a section of the kernel pair. -/
theorem exists_section_of_isPullback {V R : Over S} {F : Presheaf S}
    {a : (schemeYoneda S).obj V ⟶ F} {t s : R ⟶ V}
    (h : IsPullback ((schemeYoneda S).map t) ((schemeYoneda S).map s) a a)
    {T : (Over S)ᵒᵖ} (x y : ((schemeYoneda S).obj V).obj T) (hxy : a.app T x = a.app T y) :
    ∃ r : ((schemeYoneda S).obj R).obj T,
      ((schemeYoneda S).map t).app T r = x ∧ ((schemeYoneda S).map s).app T r = y := by
  have h' := h.map ((evaluation (Over S)ᵒᵖ (Type (u + 1))).obj T)
  exact Types.exists_of_isPullback h' x y hxy

/-- Sections of `h_V` with the same image under `a` have the same image under any `b` with
`h_t ≫ b = h_s ≫ b`. -/
theorem app_eq_of_isPullback {V R : Over S} {F G : Presheaf S}
    {a : (schemeYoneda S).obj V ⟶ F} {t s : R ⟶ V}
    (h : IsPullback ((schemeYoneda S).map t) ((schemeYoneda S).map s) a a)
    (b : (schemeYoneda S).obj V ⟶ G)
    (hb : (schemeYoneda S).map t ≫ b = (schemeYoneda S).map s ≫ b)
    {T : (Over S)ᵒᵖ} (x y : ((schemeYoneda S).obj V).obj T) (hxy : a.app T x = a.app T y) :
    b.app T x = b.app T y := by
  obtain ⟨r, rfl, rfl⟩ := exists_section_of_isPullback h x y hxy
  exact ConcreteCategory.congr_hom (NatTrans.congr_app hb T) r

/-- Descent along a locally surjective map with represented kernel pair. -/
theorem exists_desc {V R : Over S} {F G : FppfSheaf S}
    (a : (schemeYoneda S).obj V ⟶ F.obj)
    (ha : Presheaf.IsLocallySurjective (fppfTopology S) a) {t s : R ⟶ V}
    (h : IsPullback ((schemeYoneda S).map t) ((schemeYoneda S).map s) a a)
    (b : (schemeYoneda S).obj V ⟶ G.obj)
    (hb : (schemeYoneda S).map t ≫ b = (schemeYoneda S).map s ≫ b) :
    ∃ c : F.obj ⟶ G.obj, a ≫ c = b := by
  let aS : (schemeSheaf S).obj V ⟶ F := ObjectProperty.homMk a
  let bS : (schemeSheaf S).obj V ⟶ G := ObjectProperty.homMk b
  have : Sheaf.IsLocallySurjective aS := ha
  have : IsRegularEpi aS := IsRegularEpiCategory.regularEpiOfEpi aS
  have hab : ∀ {Z : FppfSheaf S} (g₁ g₂ : Z ⟶ (schemeSheaf S).obj V),
      g₁ ≫ aS = g₂ ≫ aS → g₁ ≫ bS = g₂ ≫ bS := by
    intro Z g₁ g₂ hg
    apply ObjectProperty.hom_ext
    ext T z
    have hz := ConcreteCategory.congr_hom
      (NatTrans.congr_app ((sheafToPresheaf (fppfTopology S) (Type (u + 1))).congr_map hg) T) z
    exact app_eq_of_isPullback h b hb _ _ hz
  exact ⟨(EffectiveEpi.desc aS bS hab).hom,
    congrArg (fun k => k.hom) (EffectiveEpi.fac aS bS hab)⟩

/-- Maps out of an fppf sheaf that agree after a locally surjective map from a scheme are
equal. -/
theorem hom_ext_of_isLocallySurjective {V : Over S} {F G : FppfSheaf S}
    (a : (schemeYoneda S).obj V ⟶ F.obj)
    (ha : Presheaf.IsLocallySurjective (fppfTopology S) a) {c c' : F.obj ⟶ G.obj}
    (h : a ≫ c = a ≫ c') : c = c' := by
  let aS : (schemeSheaf S).obj V ⟶ F := ObjectProperty.homMk a
  have : Sheaf.IsLocallySurjective aS := ha
  have : (ObjectProperty.homMk c : F ⟶ G) = ObjectProperty.homMk c' := by
    rw [← cancel_epi aS]
    exact ObjectProperty.hom_ext _ h
  exact congrArg (fun k => k.hom) this

/-- If `t, s` represent the kernel pairs of both `a` and `a ≫ c`, with `a` locally surjective,
then `c` is injective on sections. -/
theorem injective_of_isPullback {V R : Over S} {F G : FppfSheaf S}
    (a : (schemeYoneda S).obj V ⟶ F.obj)
    (ha : Presheaf.IsLocallySurjective (fppfTopology S) a) {t s : R ⟶ V}
    (h : IsPullback ((schemeYoneda S).map t) ((schemeYoneda S).map s) a a)
    (c : F.obj ⟶ G.obj)
    (hc : IsPullback ((schemeYoneda S).map t) ((schemeYoneda S).map s) (a ≫ c) (a ≫ c))
    (T : (Over S)ᵒᵖ) : Function.Injective (c.app T) := by
  let cS : F ⟶ G := ObjectProperty.homMk c
  have : Sheaf.IsLocallyInjective cS := by
    refine ⟨fun {X} x y hxy => ?_⟩
    refine (fppfTopology S).superset_covering ?_
      ((fppfTopology S).intersection_covering
        (Presheaf.imageSieve_mem (fppfTopology S) a x)
        (Presheaf.imageSieve_mem (fppfTopology S) a y))
    rintro W f ⟨⟨x', hx'⟩, ⟨y', hy'⟩⟩
    change F.obj.map f.op x = F.obj.map f.op y
    rw [← hx', ← hy']
    have hc' : (a ≫ c).app (op W) x' = (a ≫ c).app (op W) y' := by
      simp only [NatTrans.comp_app, types_comp_apply, hx', hy']
      rw [NatTrans.naturality_apply c, NatTrans.naturality_apply c]
      exact congrArg _ hxy
    exact app_eq_of_isPullback hc a h.w _ _ hc'
  exact (Sheaf.isLocallyInjective_iff_injective cS).mp this T

end Langlands.AlgebraicGeometry.AlgebraicSpace.KernelPairDescent
