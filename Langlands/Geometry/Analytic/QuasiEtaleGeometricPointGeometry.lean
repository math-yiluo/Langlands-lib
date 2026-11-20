import Langlands.Geometry.Analytic.QuasiEtaleStabilityStatement
import Langlands.Geometry.Analytic.QuasiEtaleGeometricPointStatement
import Langlands.Geometry.Analytic.LocalizedQuasiEtalePullbackExistence
import Langlands.CategoryTheory.Sites.PointwiseCovering
import Mathlib.CategoryTheory.Limits.Types.Pullbacks

/-! # Geometric inputs for points of the analytic quasi-étale site -/

noncomputable section

universe u v uL uC vC w

namespace Langlands.Analytic.SaturatedAtlasPresentation

open _root_.CategoryTheory Limits Topology

/-! ## Localized inputs -/

/-- Quasi-étale morphisms of the localized category are stable under composition
(Berkovich 1994, Lemma 3.1(i)). -/
def LocalizedQuasiEtaleCompositionStatement
    (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] : Prop :=
  QuasiEtaleCompStatement.{u, v} K

/-- Quasi-étale morphisms of the localized category are stable under base change along every
morphism: in every pullback square whose right leg is quasi-étale, the left leg is quasi-étale
(Berkovich 1994, Lemma 3.1(i)). Pullbacks along quasi-étale morphisms exist by
`exists_localizedPullback_of_quasiEtale`. -/
def LocalizedQuasiEtaleBaseChangeStatement
    (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] : Prop :=
  QuasiEtaleBaseChangeStatement.{u, v} K

/-- A morphism over `X` between spaces quasi-étale over `X` is quasi-étale: if `g` and `f ≫ g`
are quasi-étale, so is `f` (Berkovich 1994, Lemma 3.1(ii)). -/
def LocalizedQuasiEtaleCancellationStatement
    (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] : Prop :=
  QuasiEtaleOverMorphismStatement.{u, v} K

/-- The functor of `L`-valued points preserves pullback squares having a quasi-étale leg. -/
def LocalizedQuasiEtaleFieldPointPullbackStatement
    (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (L : Type uL) [NormedField L] [IsUltrametricDist L] [CompleteSpace L] [IsAlgClosed L]
    [NormedAlgebra K L] : Prop :=
  ∀ {P A B X : LocalizedCategory.{u, v, v} (K := K)}
    (p : P ⟶ A) (q : P ⟶ B) (f : A ⟶ X) (g : B ⟶ X),
    quasiEtale f → IsPullback p q f g →
    IsPullback ((localizedFieldPointFunctor L).map p)
      ((localizedFieldPointFunctor L).map q)
      ((localizedFieldPointFunctor L).map f)
      ((localizedFieldPointFunctor L).map g)

/-- An `L`-valued point of the target of a quasi-étale morphism lifts to the source whenever
its underlying point lies in the image of the morphism. -/
def LocalizedQuasiEtaleFieldPointImageLiftStatement
    (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (L : Type uL) [NormedField L] [IsUltrametricDist L] [CompleteSpace L] [IsAlgClosed L]
    [NormedAlgebra K L] : Prop :=
  ∀ {A B : LocalizedCategory.{u, v, v} (K := K)} (f : A ⟶ B), quasiEtale f →
    ∀ p : (localizedFieldPointFunctor L).obj B,
      ((localizedFieldPointProjection L).app B p).down ∈
        Set.range (localizedSpaceFunctor.map f) →
      ∃ q : (localizedFieldPointFunctor L).obj A, (localizedFieldPointFunctor L).map f q = p

namespace QuasiEtaleSite

/-! ## Site-level inputs -/

/-- Compatible `L`-valued points of two objects of `Qét(X)` have a common refinement in
`Qét(X)` carrying an `L`-valued point over both. -/
def GeometricPointRefinementStatement : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (L : Type uL) [NormedField L] [IsUltrametricDist L] [CompleteSpace L] [IsAlgClosed L]
    [NormedAlgebra K L] (X : LocalizedCategory.{u, v, v} (K := K))
    (U V : QuasiEtaleSite X) (p : (localizedFieldPointFunctor L).obj U.left)
    (q : (localizedFieldPointFunctor L).obj V.left),
    (localizedFieldPointFunctor L).map U.hom p =
      (localizedFieldPointFunctor L).map V.hom q →
    ∃ (W : QuasiEtaleSite X) (f : W ⟶ U) (g : W ⟶ V)
      (r : (localizedFieldPointFunctor L).obj W.left),
      (localizedFieldPointFunctor L).map f.left r = p ∧
        (localizedFieldPointFunctor L).map g.left r = q

/-- Parallel arrows of `Qét(X)` that agree on an `L`-valued point of their source are equalized
by an arrow of `Qét(X)` through which that point lifts. -/
def GeometricPointEqualizationStatement : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (L : Type uL) [NormedField L] [IsUltrametricDist L] [CompleteSpace L] [IsAlgClosed L]
    [NormedAlgebra K L] (X : LocalizedCategory.{u, v, v} (K := K))
    (U V : QuasiEtaleSite X) (f g : U ⟶ V)
    (p : (localizedFieldPointFunctor L).obj U.left),
    (localizedFieldPointFunctor L).map f.left p =
      (localizedFieldPointFunctor L).map g.left p →
    ∃ (W : QuasiEtaleSite X) (h : W ⟶ U)
      (q : (localizedFieldPointFunctor L).obj W.left),
      h ≫ f = h ≫ g ∧ (localizedFieldPointFunctor L).map h.left q = p

/-- An `L`-valued point lifts through an arrow of `Qét(X)` whenever its underlying point lies in
the image of that arrow. -/
def GeometricPointImageLiftStatement : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (L : Type uL) [NormedField L] [IsUltrametricDist L] [CompleteSpace L] [IsAlgClosed L]
    [NormedAlgebra K L] (X : LocalizedCategory.{u, v, v} (K := K))
    (U V : QuasiEtaleSite X) (f : V ⟶ U)
    (p : (localizedFieldPointFunctor L).obj U.left),
    ((localizedFieldPointProjection L).app U.left p).down ∈
      Set.range (localizedSpaceFunctor.map f.left) →
    ∃ q : (localizedFieldPointFunctor L).obj V.left,
      (localizedFieldPointFunctor L).map f.left q = p

/-- The three site-level geometric inputs. -/
def GeometricPointGeometryStatement : Prop :=
  GeometricPointRefinementStatement.{u, v, uL} ∧
    GeometricPointEqualizationStatement.{u, v, uL} ∧
      GeometricPointImageLiftStatement.{u, v, uL}

/-! ## The point axioms from the site-level inputs -/

/-- A cofiltered category of elements supplies pointwise lifting squares. -/
theorem hasPointwiseLiftingSquares_of_cofiltered
    {C : Type uC} [Category.{vC} C] (F : C ⥤ Type w) [IsCofiltered F.Elements] :
    Langlands.CategoryTheory.PointwiseCovering.HasPointwiseLiftingSquares F := by
  intro X Y S f g x y h
  let ex := Functor.elementsMk F X x
  let ey := Functor.elementsMk F Y y
  let es := Functor.elementsMk F S (F.map f x)
  let ef : ex ⟶ es := ⟨f, rfl⟩
  let eg : ey ⟶ es := ⟨g, h.symm⟩
  obtain ⟨T, p, q, hpq⟩ := IsCofiltered.cospan ef eg
  exact ⟨T.obj, p.hom, q.hom, congrArg Functor.Elements.Hom.hom hpq,
    T.val, p.map_val, q.map_val⟩

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  (L : Type uL) [NormedField L] [IsUltrametricDist L] [CompleteSpace L] [IsAlgClosed L]
  [NormedAlgebra K L] {X : LocalizedCategory.{u, v, v} (K := K)}

omit [IsUltrametricDist L] [CompleteSpace L] [IsAlgClosed L] in
/-- The identity of `X` with the point `x` is an element of the fibre functor. -/
theorem pointFibre_elements_nonempty (x : (localizedFieldPointFunctor L).obj X) :
    Nonempty (pointFibre L x).Elements := by
  let U : QuasiEtaleSite X :=
    MorphismProperty.Over.mk ⊤ (𝟙 X) ((quasiEtale (K := K)).id_mem X)
  exact ⟨Functor.elementsMk _ U ⟨x, (localizedFieldPointFunctor L).map_id_apply X x⟩⟩

/-- Common refinements and local equalization make the category of elements cofiltered. -/
theorem pointFibre_isCofiltered_of_geometry
    (hR : GeometricPointRefinementStatement.{u, v, uL})
    (hE : GeometricPointEqualizationStatement.{u, v, uL})
    (x : (localizedFieldPointFunctor L).obj X) :
    IsCofiltered (pointFibre L x).Elements where
  nonempty := pointFibre_elements_nonempty L x
  cone_objs a b := by
    obtain ⟨W, f, g, r, hf, hg⟩ := hR K L X a.obj b.obj a.val.1 b.val.1
      (a.val.2.trans b.val.2.symm)
    have hr : (localizedFieldPointFunctor L).map W.hom r = x := by
      rw [← MorphismProperty.Over.w f, Functor.map_comp_apply, hf]
      exact a.val.2
    exact ⟨Functor.elementsMk _ W ⟨r, hr⟩,
      ⟨f, Subtype.ext hf⟩, ⟨g, Subtype.ext hg⟩, trivial⟩
  cone_maps {a b} f g := by
    have hfg : (localizedFieldPointFunctor L).map f.hom.left a.val.1 =
        (localizedFieldPointFunctor L).map g.hom.left a.val.1 :=
      (congrArg Subtype.val f.map_val).trans (congrArg Subtype.val g.map_val).symm
    obtain ⟨W, h, q, heq, hq⟩ := hE K L X a.obj b.obj f.hom g.hom a.val.1 hfg
    have hqx : (localizedFieldPointFunctor L).map W.hom q = x := by
      rw [← MorphismProperty.Over.w h, Functor.map_comp_apply, hq]
      exact a.val.2
    refine ⟨Functor.elementsMk _ W ⟨q, hqx⟩, ⟨h, Subtype.ext hq⟩, ?_⟩
    exact Functor.Elements.Hom.ext heq

/-- The underlying point of an `L`-valued point of `U` lies in the image of some arrow of a
quasi-étale covering of `U`: it lies in the finite union of chart images forming its
neighbourhood. -/
theorem exists_mem_range_of_mem_quasiEtalePrecoverage {U : QuasiEtaleSite X}
    {R : Presieve U} (hR : R ∈ quasiEtalePrecoverage X U)
    (y : localizedSpaceFunctor.obj U.left) :
    ∃ (V : QuasiEtaleSite X) (f : V ⟶ U), R f ∧
      y ∈ Set.range (localizedSpaceFunctor.map f.left) := by
  obtain ⟨σ, -, hn, hT⟩ := mem_quasiEtalePrecoverage_iff.mp hR y
  obtain ⟨T, hTσ, hyT⟩ := Set.mem_sUnion.mp (mem_of_mem_nhds hn)
  obtain ⟨V, f, i, hf, rfl⟩ := hT T hTσ
  obtain ⟨z, -, hz⟩ := hyT
  exact ⟨V, f, hf, z, hz⟩

/-- Under image lifting, every element of the fibre over the target of a quasi-étale covering
comes from an element over a member of the covering. -/
theorem pointFibre_cover_lifting_of_imageLift
    (hL : GeometricPointImageLiftStatement.{u, v, uL})
    (x : (localizedFieldPointFunctor L).obj X) {U : QuasiEtaleSite X}
    (R : Presieve U) (hR : R ∈ quasiEtalePrecoverage X U)
    (p : (pointFibre L x).obj U) :
    ∃ (V : QuasiEtaleSite X) (f : V ⟶ U), R f ∧
      p ∈ Set.range ((pointFibre L x).map f) := by
  obtain ⟨V, f, hf, hpoint⟩ := exists_mem_range_of_mem_quasiEtalePrecoverage hR
    ((localizedFieldPointProjection L).app U.left p.1).down
  obtain ⟨q, hq⟩ := hL K L X U V f p.1 hpoint
  have hqx : (localizedFieldPointFunctor L).map V.hom q = x := by
    rw [← MorphismProperty.Over.w f, Functor.map_comp_apply, hq]
    exact p.2
  exact ⟨V, f, hf, ⟨q, hqx⟩, Subtype.ext hq⟩

/-- Cofilteredness and image lifting give joint surjectivity for every covering sieve of the
quasi-étale topology, including those obtained by pullback and transitivity. -/
theorem pointFibre_jointlySurjective_of_geometry
    (hL : GeometricPointImageLiftStatement.{u, v, uL})
    (x : (localizedFieldPointFunctor L).obj X)
    [IsCofiltered (pointFibre L x).Elements] {U : QuasiEtaleSite X} (R : Sieve U)
    (hR : R ∈ quasiEtaleTopology X U) :
    ∀ p : (pointFibre L x).obj U,
      ∃ (V : QuasiEtaleSite X) (f : V ⟶ U) (_ : R f)
        (q : (pointFibre L x).obj V), (pointFibre L x).map f q = p := by
  have hpre : quasiEtalePrecoverage X ≤
      Types.jointlySurjectivePrecoverage.comap (pointFibre L x) := by
    intro U S hS
    exact (Presieve.mem_comap_jointlySurjectivePrecoverage_iff _).mpr
      (pointFibre_cover_lifting_of_imageLift L hL x S hS)
  have hgeo :=
    Langlands.CategoryTheory.PointwiseCovering.isJointlySurjective_of_mem_toGrothendieck
      (hasPointwiseLiftingSquares_of_cofiltered (pointFibre L x))
      (Precoverage.toGrothendieck_mono hpre _ hR)
  intro p
  obtain ⟨V, f, hf, q, hq⟩ := hgeo p
  exact ⟨V, f, hf, q, hq⟩

/-- The three site-level geometric inputs imply the published target. -/
theorem geometricPointStatement_of_geometry
    (h : GeometricPointGeometryStatement.{u, v, uL}) :
    GeometricPointStatement.{u, v, uL} := by
  intro K _ _ _ L _ _ _ _ _ X x
  let := pointFibre_isCofiltered_of_geometry L h.1 h.2.1 x
  exact ⟨inferInstance, pointFibre_jointlySurjective_of_geometry L h.2.2 x⟩

/-! ## The site-level inputs from the localized inputs -/

section Localized

variable [(quasiEtale (K := K) :
    MorphismProperty (LocalizedCategory.{u, v, v} (K := K))).IsStableUnderComposition]
  [(quasiEtale (K := K) :
    MorphismProperty (LocalizedCategory.{u, v, v} (K := K))).IsStableUnderBaseChange]

/-- The fibre product `U ×_X V`, with the pair of `L`-valued points supplied by the field-point
compatibility of quasi-étale pullbacks, is a common refinement. -/
theorem exists_refinement_of_pullbacks
    (hF : LocalizedQuasiEtaleFieldPointPullbackStatement.{u, v, uL} K L)
    (U V : QuasiEtaleSite X) (p : (localizedFieldPointFunctor L).obj U.left)
    (q : (localizedFieldPointFunctor L).obj V.left)
    (hpq : (localizedFieldPointFunctor L).map U.hom p =
      (localizedFieldPointFunctor L).map V.hom q) :
    ∃ (W : QuasiEtaleSite X) (f : W ⟶ U) (g : W ⟶ V)
      (r : (localizedFieldPointFunctor L).obj W.left),
      (localizedFieldPointFunctor L).map f.left r = p ∧
        (localizedFieldPointFunctor L).map g.left r = q := by
  obtain ⟨P, a, b, hP⟩ := exists_localizedPullback_of_quasiEtale U.hom V.hom U.prop
  have hb : quasiEtale b := MorphismProperty.of_isPullback hP U.prop
  let W : QuasiEtaleSite X := MorphismProperty.Over.mk ⊤ (b ≫ V.hom)
    ((quasiEtale (K := K)).comp_mem b V.hom hb V.prop)
  let a' : W ⟶ U := MorphismProperty.Over.homMk a hP.w
  let b' : W ⟶ V := MorphismProperty.Over.homMk b
  obtain ⟨r, hr₁, hr₂⟩ := Types.exists_of_isPullback
    (hF a b U.hom V.hom U.prop hP) p q hpq
  exact ⟨W, a', b', r, hr₁, hr₂⟩

/-- Pulling back the diagonal of `V → X` along `(f, g) : U → V ×_X V` equalizes `f` and `g`,
and the field-point compatibility of quasi-étale pullbacks lifts the point on which they
agree. -/
theorem exists_equalization_of_pullbacks
    [(quasiEtale (K := K) : MorphismProperty (LocalizedCategory.{u, v, v} (K := K))).HasOfPostcompProperty
      (quasiEtale (K := K))]
    (hF : LocalizedQuasiEtaleFieldPointPullbackStatement.{u, v, uL} K L)
    (U V : QuasiEtaleSite X) (f g : U ⟶ V)
    (p : (localizedFieldPointFunctor L).obj U.left)
    (hfg : (localizedFieldPointFunctor L).map f.left p =
      (localizedFieldPointFunctor L).map g.left p) :
    ∃ (W : QuasiEtaleSite X) (h : W ⟶ U)
      (q : (localizedFieldPointFunctor L).obj W.left),
      h ≫ f = h ≫ g ∧ (localizedFieldPointFunctor L).map h.left q = p := by
  let F := localizedFieldPointFunctor (K := K) L
  obtain ⟨P, a, b, hP⟩ := exists_localizedPullback_of_quasiEtale V.hom V.hom V.prop
  obtain ⟨d, hd₁, hd₂⟩ := hP.exists_lift (𝟙 V.left) (𝟙 V.left) rfl
  have hb : quasiEtale b := MorphismProperty.of_isPullback hP V.prop
  have hd : quasiEtale d := by
    apply (quasiEtale (K := K)).of_postcomp d b hb
    rw [hd₂]
    exact (quasiEtale (K := K)).id_mem V.left
  obtain ⟨c, hc₁, hc₂⟩ := hP.exists_lift f.left g.left
    ((MorphismProperty.Over.w f).trans (MorphismProperty.Over.w g).symm)
  have he : F.map d (F.map f.left p) = F.map c p := by
    apply Types.ext_of_isPullback (hF a b V.hom V.hom V.prop hP)
    · rw [← F.map_comp_apply, hd₁, F.map_id_apply,
        ← F.map_comp_apply, hc₁]
    · rw [← F.map_comp_apply, hd₂, F.map_id_apply,
        ← F.map_comp_apply, hc₂]
      exact hfg
  obtain ⟨E, s, t, hE⟩ := exists_localizedPullback_of_quasiEtale d c hd
  have ht : quasiEtale t := MorphismProperty.of_isPullback hE hd
  obtain ⟨q, -, hq⟩ := Types.exists_of_isPullback
    (hF s t d c hd hE) (F.map f.left p) p he
  let W : QuasiEtaleSite X := MorphismProperty.Over.mk ⊤ (t ≫ U.hom)
    ((quasiEtale (K := K)).comp_mem t U.hom ht U.prop)
  let k : W ⟶ U := MorphismProperty.Over.homMk t
  refine ⟨W, k, q, ?_, hq⟩
  apply MorphismProperty.Over.Hom.ext
  change t ≫ f.left = t ≫ g.left
  have ht₁ : t ≫ f.left = s := by
    rw [← hc₁, ← Category.assoc, ← hE.w, Category.assoc, hd₁, Category.comp_id]
  have ht₂ : t ≫ g.left = s := by
    rw [← hc₂, ← Category.assoc, ← hE.w, Category.assoc, hd₂, Category.comp_id]
  exact ht₁.trans ht₂.symm

end Localized

/-- Under right cancellation, arrows of `Qét(X)` are quasi-étale, so the localized image lift
applies to them. -/
theorem exists_imageLift_of_localized
    [(quasiEtale (K := K) : MorphismProperty (LocalizedCategory.{u, v, v} (K := K))).HasOfPostcompProperty
      (quasiEtale (K := K))]
    (hI : LocalizedQuasiEtaleFieldPointImageLiftStatement.{u, v, uL} K L)
    (U V : QuasiEtaleSite X) (f : V ⟶ U) (p : (localizedFieldPointFunctor L).obj U.left)
    (hp : ((localizedFieldPointProjection L).app U.left p).down ∈
      Set.range (localizedSpaceFunctor.map f.left)) :
    ∃ q : (localizedFieldPointFunctor L).obj V.left,
      (localizedFieldPointFunctor L).map f.left q = p := by
  have hf : quasiEtale f.left := by
    apply (quasiEtale (K := K)).of_postcomp f.left U.hom U.prop
    simpa only [MorphismProperty.Over.w] using V.prop
  exact hI f.left hf p hp

/-- The localized inputs, for every base field `K` and every complete algebraically closed `L`:
composition, base change and right cancellation of quasi-étale morphisms, and the field-point
compatibility of quasi-étale pullbacks and images. -/
def GeometricPointLocalizedInputsStatement : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K],
    LocalizedQuasiEtaleCompositionStatement.{u, v} K ∧
      LocalizedQuasiEtaleBaseChangeStatement.{u, v} K ∧
      LocalizedQuasiEtaleCancellationStatement.{u, v} K ∧
      ∀ (L : Type uL) [NormedField L] [IsUltrametricDist L] [CompleteSpace L] [IsAlgClosed L]
        [NormedAlgebra K L],
        LocalizedQuasiEtaleFieldPointPullbackStatement.{u, v, uL} K L ∧
          LocalizedQuasiEtaleFieldPointImageLiftStatement.{u, v, uL} K L

/-- The localized inputs imply the three site-level inputs. -/
theorem geometricPointGeometry_of_localized
    (h : GeometricPointLocalizedInputsStatement.{u, v, uL}) :
    GeometricPointGeometryStatement.{u, v, uL} := by
  refine ⟨?_, ?_, ?_⟩
  · intro K _ _ _ L _ _ _ _ _ X U V p q hpq
    obtain ⟨hC, hB, -, hFI⟩ := h K
    have : (quasiEtale (K := K) :
        MorphismProperty (LocalizedCategory.{u, v, v} (K := K))).IsStableUnderComposition := hC
    have : (quasiEtale (K := K) :
        MorphismProperty (LocalizedCategory.{u, v, v} (K := K))).IsStableUnderBaseChange := hB
    exact exists_refinement_of_pullbacks L (hFI L).1 U V p q hpq
  · intro K _ _ _ L _ _ _ _ _ X U V f g p hfg
    obtain ⟨hC, hB, hX, hFI⟩ := h K
    have : (quasiEtale (K := K) :
        MorphismProperty (LocalizedCategory.{u, v, v} (K := K))).IsStableUnderComposition := hC
    have : (quasiEtale (K := K) :
        MorphismProperty (LocalizedCategory.{u, v, v} (K := K))).IsStableUnderBaseChange := hB
    have : (quasiEtale (K := K) : MorphismProperty
        (LocalizedCategory.{u, v, v} (K := K))).HasOfPostcompProperty (quasiEtale (K := K)) := hX
    exact exists_equalization_of_pullbacks L (hFI L).1 U V f g p hfg
  · intro K _ _ _ L _ _ _ _ _ X U V f p hp
    obtain ⟨-, -, hX, hFI⟩ := h K
    have : (quasiEtale (K := K) : MorphismProperty
        (LocalizedCategory.{u, v, v} (K := K))).HasOfPostcompProperty (quasiEtale (K := K)) := hX
    exact exists_imageLift_of_localized L (hFI L).2 U V f p hp

/-- The localized inputs imply the published target. -/
theorem geometricPointStatement_of_localized
    (h : GeometricPointLocalizedInputsStatement.{u, v, uL}) :
    GeometricPointStatement.{u, v, uL} :=
  geometricPointStatement_of_geometry (geometricPointGeometry_of_localized h)

end QuasiEtaleSite

end Langlands.Analytic.SaturatedAtlasPresentation
