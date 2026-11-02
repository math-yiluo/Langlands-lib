import Langlands.AlgebraicGeometry.AlgebraicSpace.Basic
import Mathlib.CategoryTheory.Sites.LocallySurjective
import Mathlib.CategoryTheory.Sites.RegularEpi

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- A single surjective flat locally finitely presented morphism is a cover
in the actual slice fppf topology. -/
theorem generate_singleton_mem_fppfTopology {W M : Over S} (q : W ⟶ M)
    [Flat q.left] [LocallyOfFinitePresentation q.left] [Surjective q.left] :
    Sieve.generate (Presieve.singleton q) ∈ fppfTopology S M := by
  change Sieve.overEquiv M (Sieve.generate (Presieve.singleton q)) ∈
    Scheme.fppfTopology M.left
  rw [← Presieve.ofArrows_pUnit.{0} q, ← Sieve.ofArrows,
    Sieve.overEquiv_ofArrows, Sieve.ofArrows, Presieve.ofArrows_pUnit]
  exact Precoverage.generate_mem_toGrothendieck q.left.singleton_mem_fppfPrecoverage

/-- A represented fppf scheme cover is locally surjective on points. -/
theorem isLocallySurjective_schemeYoneda_map {W M : Over S} (q : W ⟶ M)
    [Flat q.left] [LocallyOfFinitePresentation q.left] [Surjective q.left] :
    CategoryTheory.Presheaf.IsLocallySurjective (fppfTopology S)
      ((schemeYoneda S).map q) := by
  constructor
  intro T x
  apply (fppfTopology S).superset_covering ?_
    ((fppfTopology S).pullback_stable x.down (generate_singleton_mem_fppfTopology q))
  intro V g hg
  obtain ⟨Z, t, q', hq', hcomp⟩ := hg
  cases hq'
  refine ⟨⟨t⟩, ?_⟩
  apply ULift.ext
  exact hcomp

/-- Represented fppf projections give local surjectivity of a presheaf map. -/
theorem isLocallySurjective_of_fppf_projections
    {F G : Presheaf S} (a : F ⟶ G) (ha : IsRepresentableMorphism a)
    (hp : ∀ {T V : Over S} (g : (schemeYoneda S).obj T ⟶ G)
      (b : (schemeYoneda S).obj V ⟶ F) (p : V ⟶ T),
      IsPullback b ((schemeYoneda S).map p) a g →
        Flat p.left ∧ LocallyOfFinitePresentation p.left ∧ Surjective p.left) :
    CategoryTheory.Presheaf.IsLocallySurjective (fppfTopology S) a := by
  constructor
  intro T x
  let g : (schemeYoneda S).obj T ⟶ G := uliftYonedaEquiv.symm x
  let p := ha.snd g
  obtain ⟨hflat, hlfp, hsurj⟩ := hp g (ha.fst g) p (ha.isPullback g)
  have : Flat p.left := hflat
  have : LocallyOfFinitePresentation p.left := hlfp
  have : Surjective p.left := hsurj
  apply (fppfTopology S).superset_covering ?_ (generate_singleton_mem_fppfTopology p)
  rw [Sieve.generate_le_iff, Presieve.singleton_le_iff]
  refine ⟨(ha.fst g).app (op (ha.pullback g)) ⟨𝟙 _⟩, ?_⟩
  simpa [g] using congrArg
    (fun z : (schemeYoneda S).obj (ha.pullback g) ⟶ G =>
      z.app (op (ha.pullback g)) ⟨𝟙 _⟩) (ha.isPullback g).w

/-- A geometrically surjective etale map is locally surjective for the fppf topology. -/
theorem isLocallySurjective_of_isEtale_isSurjective
    {F G : Presheaf S} (a : F ⟶ G) (ha : IsEtale a) (hs : IsSurjective a) :
    CategoryTheory.Presheaf.IsLocallySurjective (fppfTopology S) a := by
  apply isLocallySurjective_of_fppf_projections a ha.representable
  intro T V g b p h
  have : Etale p.left := ha.projection g b p h
  exact ⟨inferInstance, inferInstance, hs.projection g b p h⟩

/-- Two locally surjective presentations with the same sectionwise kernel
identify a sheaf with the functor of points of the scheme quotient. -/
theorem exists_iso_of_locallySurjective_of_same_kernel
    {F : FppfSheaf S} {W M : Over S}
    (a : (schemeYoneda S).obj W ⟶ F.obj) (q : W ⟶ M)
    (ha : CategoryTheory.Presheaf.IsLocallySurjective (fppfTopology S) a)
    (hq : CategoryTheory.Presheaf.IsLocallySurjective (fppfTopology S)
      ((schemeYoneda S).map q))
    (hker : ∀ (T : Over S) (w₁ w₂ : T ⟶ W),
      a.app (op T) ⟨w₁⟩ = a.app (op T) ⟨w₂⟩ ↔ w₁ ≫ q = w₂ ≫ q) :
    ∃ e : (schemeYoneda S).obj M ≅ F.obj,
      (schemeYoneda S).map q ≫ e.hom = a := by
  let a' : (schemeSheaf S).obj W ⟶ F := ObjectProperty.homMk a
  let q' : (schemeSheaf S).obj W ⟶ (schemeSheaf S).obj M := (schemeSheaf S).map q
  have : Sheaf.IsLocallySurjective a' := ha
  have : Sheaf.IsLocallySurjective q' := hq
  have : Epi a' := inferInstance
  have : Epi q' := inferInstance
  have : IsRegularEpi a' := IsRegularEpiCategory.regularEpiOfEpi a'
  have : IsRegularEpi q' := IsRegularEpiCategory.regularEpiOfEpi q'
  have hqa : ∀ {Z : FppfSheaf S} (g₁ g₂ : Z ⟶ (schemeSheaf S).obj W),
      g₁ ≫ q' = g₂ ≫ q' → g₁ ≫ a' = g₂ ≫ a' := by
    intro Z g₁ g₂ h
    apply ObjectProperty.hom_ext
    ext T x
    apply (hker T.unop (g₁.hom.app T x).down (g₂.hom.app T x).down).mpr
    exact congrArg ULift.down
      (ConcreteCategory.congr_hom (NatTrans.congr_app
        ((sheafToPresheaf (fppfTopology S) (Type (u + 1))).congr_map h) T) x)
  have haq : ∀ {Z : FppfSheaf S} (g₁ g₂ : Z ⟶ (schemeSheaf S).obj W),
      g₁ ≫ a' = g₂ ≫ a' → g₁ ≫ q' = g₂ ≫ q' := by
    intro Z g₁ g₂ h
    apply ObjectProperty.hom_ext
    ext T x
    apply ULift.ext
    apply (hker T.unop (g₁.hom.app T x).down (g₂.hom.app T x).down).mp
    exact ConcreteCategory.congr_hom (NatTrans.congr_app
      ((sheafToPresheaf (fppfTopology S) (Type (u + 1))).congr_map h) T) x
  let b := EffectiveEpi.desc q' a' hqa
  let c := EffectiveEpi.desc a' q' haq
  have hb : q' ≫ b = a' := EffectiveEpi.fac q' a' hqa
  have hc : a' ≫ c = q' := EffectiveEpi.fac a' q' haq
  let e : (schemeSheaf S).obj M ≅ F :=
    { hom := b
      inv := c
      hom_inv_id := (cancel_epi q').mp (by simp [← Category.assoc, hb, hc])
      inv_hom_id := (cancel_epi a').mp (by simp [← Category.assoc, hb, hc]) }
  exact ⟨(sheafToPresheaf (fppfTopology S) (Type (u + 1))).mapIso e,
    (sheafToPresheaf (fppfTopology S) (Type (u + 1))).congr_map hb⟩

/-- The sheaf in a common-kernel presentation is represented by the given quotient scheme. -/
theorem representableBy_of_locallySurjective_of_same_kernel
    {F : FppfSheaf S} {W M : Over S}
    (a : (schemeYoneda S).obj W ⟶ F.obj) (q : W ⟶ M)
    (ha : CategoryTheory.Presheaf.IsLocallySurjective (fppfTopology S) a)
    (hq : CategoryTheory.Presheaf.IsLocallySurjective (fppfTopology S)
      ((schemeYoneda S).map q))
    (hker : ∀ (T : Over S) (w₁ w₂ : T ⟶ W),
      a.app (op T) ⟨w₁⟩ = a.app (op T) ⟨w₂⟩ ↔ w₁ ≫ q = w₂ ≫ q) :
    Nonempty (F.obj.RepresentableBy M) := by
  obtain ⟨e, _⟩ := exists_iso_of_locallySurjective_of_same_kernel a q ha hq hker
  exact ⟨(Functor.RepresentableBy.equivUliftYonedaIso.{u + 1} F.obj M).symm e⟩

/-- A locally surjective common-kernel presentation is represented by its actual
surjective flat locally finitely presented scheme quotient. -/
theorem representableBy_of_fppf_quotient
    {F : FppfSheaf S} {W M : Over S}
    (a : (schemeYoneda S).obj W ⟶ F.obj) (q : W ⟶ M)
    [Flat q.left] [LocallyOfFinitePresentation q.left] [Surjective q.left]
    (ha : CategoryTheory.Presheaf.IsLocallySurjective (fppfTopology S) a)
    (hker : ∀ (T : Over S) (w₁ w₂ : T ⟶ W),
      a.app (op T) ⟨w₁⟩ = a.app (op T) ⟨w₂⟩ ↔ w₁ ≫ q = w₂ ≫ q) :
    Nonempty (F.obj.RepresentableBy M) :=
  representableBy_of_locallySurjective_of_same_kernel a q ha
    (isLocallySurjective_schemeYoneda_map q) hker

end Langlands.AlgebraicGeometry.AlgebraicSpace
