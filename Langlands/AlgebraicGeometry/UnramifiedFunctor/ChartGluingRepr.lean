import Langlands.AlgebraicGeometry.UnramifiedFunctor.ChartGluingLocus
import Langlands.CategoryTheory.OverTotalPresheaf
import Mathlib.AlgebraicGeometry.Sites.Representability
import Mathlib.CategoryTheory.ShrinkYoneda

/-! # Gluing monomorphic étale charts (SGA 3, XI 3.5; Murre's Lemma 3)

Let `S` be locally noetherian and let `F` be a presheaf on `Over S` with `u`-small values
satisfying (F1a), (F1b), (F2) and (F3). Let `ξᵢ ∈ F(Uᵢ)` be monomorphisms `Uᵢ → F`, each
infinitesimally étale at every point, with `Uᵢ` locally of finite type over `S`, such that every
point of `F` with values in a field factors through some `ξᵢ`. Then `F` is representable by a
scheme `Y` locally of finite type over `S`, glued from the `Uᵢ` along open subschemes.

We shrink `F` to a presheaf `G` with values in `Type u`, pass to the total presheaf
`T ↦ Σ (t : T ⟶ S), G(T, t)` on all schemes, which is a Zariski sheaf by (F1a), and apply
Mathlib's local representability criterion
(`AlgebraicGeometry.Scheme.LocalRepresentability.representableBy`). The charts
`yoneda Uᵢ ⟶ G_tot` are relatively representable open immersions by SGA 3, XI 3.1
(`ChartGluingLocus`), and they are jointly locally surjective by the hypothesis on points with
values in fields. -/

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

noncomputable section

namespace Langlands.AlgebraicGeometry.UnramifiedFunctor.ChartGluing

/-! ### The total presheaf of a Zariski sheaf on `Over S` -/

section TotalSheaf

variable {S : Scheme.{u}}

lemma total_eq_of_fibre_eq {P : (Over S)ᵒᵖ ⥤ Type u} (T : Over S) (x y : P.OverTotal T.left)
    (hx : x.1 = T.hom) (hy : y.1 = T.hom)
    (h : Functor.OverTotal.toFibre T x hx = Functor.OverTotal.toFibre T y hy) : x = y := by
  rw [← Functor.OverTotal.ofFibre_toFibre T x hx, ← Functor.OverTotal.ofFibre_toFibre T y hy, h]

/-- The total presheaf of a presheaf satisfying (F1a) is a sheaf for every open cover. -/
lemma overTotal_isSheafFor_openCover (P : (Over S)ᵒᵖ ⥤ Type u) (hP : ZariskiSheaf P)
    (X : Scheme.{u}) (𝒰 : Scheme.OpenCover.{u} X) :
    Presieve.IsSheafFor P.overTotal (Presieve.ofArrows 𝒰.X 𝒰.f) := by
  apply (Presieve.isSheafFor_arrows_iff _ _).mpr
  intro q hq
  have hc (i j : 𝒰.I₀) :
      pullback.fst (𝒰.f i) (𝒰.f j) ≫ (q i).1 = pullback.snd (𝒰.f i) (𝒰.f j) ≫ (q j).1 :=
    congrArg (fun z => z.1) (hq i j _ _ _ pullback.condition)
  let t := 𝒰.glueMorphisms (fun i => (q i).1) hc
  have ht (i : 𝒰.I₀) : 𝒰.f i ≫ t = (q i).1 := 𝒰.ι_glueMorphisms _ hc i
  let T : Over S := Over.mk t
  let C (i : 𝒰.I₀) : Over S := Over.mk (𝒰.f i ≫ T.hom)
  let m (i : 𝒰.I₀) : C i ⟶ T := Over.homMk (𝒰.f i)
  have hb (i : 𝒰.I₀) : (q i).1 = (C i).hom := (ht i).symm
  let r (i : 𝒰.I₀) := Functor.OverTotal.toFibre (C i) (q i) (hb i)
  have hr : Presieve.Arrows.Compatible P m r := by
    intro i j A a b hab
    have hai : (P.overTotal.map a.left.op (q i)).1 = A.hom := by
      rw [Functor.overTotal_map_fst, hb i]
      exact Over.w a
    have hbj : (P.overTotal.map b.left.op (q j)).1 = A.hom := by
      rw [Functor.overTotal_map_fst, hb j]
      exact Over.w b
    have hab' : a.left ≫ 𝒰.f i = b.left ≫ 𝒰.f j := congrArg (fun f => f.left) hab
    calc
      P.map a.op (r i) = Functor.OverTotal.toFibre A (P.overTotal.map a.left.op (q i)) hai :=
        (Functor.OverTotal.toFibre_naturality a (q i) (hb i) hai).symm
      _ = Functor.OverTotal.toFibre A (P.overTotal.map b.left.op (q j)) hbj :=
        Functor.OverTotal.toFibre_congr A (hq i j A.left a.left b.left hab') hai hbj
      _ = P.map b.op (r j) := Functor.OverTotal.toFibre_naturality b (q j) (hb j) hbj
  obtain ⟨r₀, hr₀, hur₀⟩ := (Presieve.isSheafFor_arrows_iff _ _).mp (hP T 𝒰) r hr
  let y := Functor.OverTotal.ofFibre T r₀
  refine ⟨y, ?_, ?_⟩
  · intro i
    have hy : (P.overTotal.map (𝒰.f i).op y).1 = (C i).hom := rfl
    apply total_eq_of_fibre_eq (C i) _ _ hy (hb i)
    calc
      _ = P.map (m i).op (Functor.OverTotal.toFibre T y rfl) :=
        Functor.OverTotal.toFibre_naturality (m i) y rfl hy
      _ = P.map (m i).op r₀ := congrArg _ (Functor.OverTotal.toFibre_ofFibre T r₀)
      _ = r i := hr₀ i
  · intro y' hy'
    have hbase : y'.1 = T.hom := by
      apply 𝒰.hom_ext
      intro i
      exact (congrArg (fun z => z.1) (hy' i)).trans (ht i).symm
    have hri : ∀ i, P.map (m i).op (Functor.OverTotal.toFibre T y' hbase) = r i := by
      intro i
      have hi : (P.overTotal.map (𝒰.f i).op y').1 = (C i).hom := by
        rw [Functor.overTotal_map_fst, hbase]
        rfl
      calc
        _ = Functor.OverTotal.toFibre (C i) (P.overTotal.map (𝒰.f i).op y') hi :=
          (Functor.OverTotal.toFibre_naturality (m i) y' hbase hi).symm
        _ = r i := Functor.OverTotal.toFibre_congr (C i) (hy' i) hi (hb i)
    apply total_eq_of_fibre_eq T y' y hbase rfl
    rw [Functor.OverTotal.toFibre_ofFibre]
    exact hur₀ _ hri

/-- A presheaf on schemes that is a sheaf for every open cover is a Zariski sheaf. -/
lemma isSheaf_zariski_of_openCover (P : Scheme.{u}ᵒᵖ ⥤ Type u)
    (hP : ∀ (X : Scheme.{u}) (𝒰 : Scheme.OpenCover.{u} X),
      Presieve.IsSheafFor P (Presieve.ofArrows 𝒰.X 𝒰.f)) :
    Presieve.IsSheaf Scheme.zariskiTopology P := by
  intro X R hR
  obtain ⟨𝒰, h𝒰⟩ := Scheme.exists_cover_of_mem_grothendieckTopology hR
  apply Presieve.isSheafFor_subsieve_aux P
    ((Sieve.generate_le_iff (Presieve.ofArrows 𝒰.X 𝒰.f) R).mpr h𝒰)
    ((Presieve.isSheafFor_iff_generate _).mp (hP X 𝒰))
  intro Y g _ x t₁ t₂ ht₁ ht₂
  apply (hP Y (𝒰.pullback₁ g)).isSeparatedFor.ext
  rintro _ _ ⟨i⟩
  have hm : (Sieve.generate (Presieve.ofArrows 𝒰.X 𝒰.f)).pullback g ((𝒰.pullback₁ g).f i) :=
    ⟨_, 𝒰.pullbackHom g i, 𝒰.f i, ⟨i⟩, 𝒰.pullbackHom_map g i⟩
  exact (ht₁ _ hm).trans (ht₂ _ hm).symm

lemma isSheaf_overTotal (P : (Over S)ᵒᵖ ⥤ Type u) (hP : ZariskiSheaf P) :
    Presheaf.IsSheaf Scheme.zariskiTopology P.overTotal :=
  (isSheaf_iff_isSheaf_of_type _ _).mpr
    (isSheaf_zariski_of_openCover _ (overTotal_isSheafFor_openCover P hP))

end TotalSheaf

/-! ### Shrinking the values of `F` -/

section Shrink

variable {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type v} [FunctorToTypes.Small.{u} F]

lemma shrink_map_equivShrink {X Y : (Over S)ᵒᵖ} (f : X ⟶ Y) (x : F.obj X) :
    (FunctorToTypes.shrink.{u} F).map f (equivShrink _ x) = equivShrink _ (F.map f x) := by
  simp

lemma zariskiSheaf_shrink (hZ : ZariskiSheaf F) : ZariskiSheaf (FunctorToTypes.shrink.{u} F) :=
  fun T 𝒰 ↦ Presieve.isSheafFor_of_nat_equiv (fun X ↦ equivShrink (F.obj (op X)))
    (fun _ _ f x ↦ (shrink_map_equivShrink f.op x).symm) (hZ T 𝒰)

/-- A representation of the shrunk presheaf is a representation of `F`. -/
def representableByOfShrink {Y : Over S}
    (e : (FunctorToTypes.shrink.{u} F).RepresentableBy Y) : F.RepresentableBy Y where
  homEquiv := e.homEquiv.trans (equivShrink _).symm
  homEquiv_comp f g := by
    rw [Equiv.trans_apply, Equiv.trans_apply, e.homEquiv_comp, Equiv.symm_apply_eq,
      ← shrink_map_equivShrink, Equiv.apply_symm_apply]

/-- The section of the total presheaf of the shrunk presheaf given by `x ∈ F(X)`. -/
def pt (X : Over S) (x : F.obj (op X)) :
    (FunctorToTypes.shrink.{u} F).overTotal.obj (op X.left) :=
  Functor.OverTotal.ofFibre X (equivShrink _ x)

lemma pt_fst (X : Over S) (x : F.obj (op X)) : (pt X x).1 = X.hom := rfl

lemma overTotal_map_pt {Z X : Over S} (c : Z ⟶ X) (x : F.obj (op X)) :
    (FunctorToTypes.shrink.{u} F).overTotal.map c.left.op (pt X x) = pt Z (F.map c.op x) := by
  have hb : ((FunctorToTypes.shrink.{u} F).overTotal.map c.left.op (pt X x)).1 = Z.hom :=
    Over.w c
  apply total_eq_of_fibre_eq Z _ _ hb rfl
  rw [Functor.OverTotal.toFibre_naturality c _ rfl hb]
  unfold pt
  rw [Functor.OverTotal.toFibre_ofFibre, Functor.OverTotal.toFibre_ofFibre,
    shrink_map_equivShrink]

lemma pt_injective (X : Over S) : Function.Injective (pt (F := F) X) := by
  intro x y h
  have := Functor.OverTotal.toFibre_congr X h rfl rfl
  unfold pt at this
  rw [Functor.OverTotal.toFibre_ofFibre, Functor.OverTotal.toFibre_ofFibre] at this
  exact (equivShrink _).injective this

lemma eq_pt {T : Scheme.{u}} (b : (FunctorToTypes.shrink.{u} F).overTotal.obj (op T)) :
    b = pt (Over.mk b.1) ((equivShrink _).symm (Functor.OverTotal.toFibre (Over.mk b.1) b rfl)) := by
  unfold pt
  rw [Equiv.apply_symm_apply]
  exact (Functor.OverTotal.ofFibre_toFibre (Over.mk b.1) b rfl).symm

end Shrink

/-! ### The charts -/

section Charts

variable {S : Scheme.{u}} [IsLocallyNoetherian S] {F : (Over S)ᵒᵖ ⥤ Type v}
  [FunctorToTypes.Small.{u} F] {ι : Type u} {U : ι → Over S} (ξ : ∀ i, F.obj (op (U i)))

/-- The chart `yoneda Uᵢ ⟶ G_tot` given by `ξᵢ`. -/
def chart (i : ι) : yoneda.obj (U i).left ⟶ (FunctorToTypes.shrink.{u} F).overTotal :=
  yonedaEquiv.symm (pt (U i) (ξ i))

omit [IsLocallyNoetherian S] in
lemma chart_app (i : ι) {T : Scheme.{u}} (c : T ⟶ (U i).left) :
    (chart ξ i).app (op T) c = (FunctorToTypes.shrink.{u} F).overTotal.map c.op (pt (U i) (ξ i)) :=
  (map_yonedaEquiv (chart ξ i) c).symm.trans (by rw [chart, Equiv.apply_symm_apply])

omit [IsLocallyNoetherian S] in
/-- On an open `V` of `T` on which `η` factors through `ξᵢ` by `φ`, the chart composed with `φ`
is the restriction of `η`. -/
lemma chart_app_comp (i : ι) {T : Scheme.{u}} (t : T ⟶ S) (η : F.obj (op (Over.mk t)))
    (V : T.Opens) (φ : Over.mk (V.ι ≫ t) ⟶ U i)
    (hφ : F.map φ.op (ξ i) = F.map (ιOver (Over.mk t) V).op η) {T' : Scheme.{u}} (c : T' ⟶ V) :
    (chart ξ i).app (op T') (c ≫ φ.left) =
      (FunctorToTypes.shrink.{u} F).overTotal.map (c ≫ V.ι).op (pt (Over.mk t) η) := by
  let c' : Over.mk (c ≫ V.ι ≫ t) ⟶ Over.mk (V.ι ≫ t) := Over.homMk c
  rw [chart_app]
  refine (overTotal_map_pt (c' ≫ φ) (ξ i)).trans
    (Eq.trans ?_ (overTotal_map_pt (c' ≫ ιOver (Over.mk t) V) η).symm)
  rw [op_comp, op_comp, Functor.map_comp_apply, Functor.map_comp_apply, hφ]

variable {ξ} (hZ : ZariskiSheaf F) (hF : FaithfullyFlatSheaf F) (h2 : FilteredColimits F)
  (hA : AdicLimits F) (hlft : ∀ i, LocallyOfFiniteType (U i).hom)
  (hmono : ∀ i, IsMonoElement F (ξ i)) (hét : ∀ i y, InfinitesimallyEtaleAt F (ξ i) y)
include hZ hF h2 hA hlft hmono hét

/-- The open subscheme of `T` on which `η` factors through `ξᵢ`. -/
def locus (i : ι) {T : Over S} (η : F.obj (op T)) : T.left.Opens :=
  ⟨W (ξ i) η, have := hlft i; isOpen_W' (hmono i) hZ hF h2 hA (hét i) η⟩

omit [FunctorToTypes.Small.{u} F] in
lemma fac_locus (i : ι) {T : Over S} (η : F.obj (op T)) :
    Fac (ξ i) η (ιOver T (locus hZ hF h2 hA hlft hmono hét i η)) := by
  have := hlft i
  refine (fac_iff_range_subset_W (hmono i) hZ hF h2 hA (hét i) η _).mpr ?_
  rw [show (ιOver T (locus hZ hF h2 hA hlft hmono hét i η)).left =
    (locus hZ hF h2 hA hlft hmono hét i η).ι from rfl, Scheme.Opens.range_ι]
  exact fun _ h ↦ h

/-- The chart given by `ξᵢ` is a relatively representable open immersion: its pullback along
`yoneda T ⟶ G_tot` is the open subscheme `locus` of `T`. -/
theorem isOpenImmersion_presheaf_chart (i : ι) : IsOpenImmersion.presheaf (chart ξ i) := by
  apply MorphismProperty.relative.of_exists
  intro T g
  let b := yonedaEquiv g
  let Tt : Over S := Over.mk b.1
  let η : F.obj (op Tt) := (equivShrink _).symm (Functor.OverTotal.toFibre Tt b rfl)
  have hb : b = pt Tt η := eq_pt b
  have hg : ∀ {T' : Scheme.{u}} (a : T' ⟶ T),
      g.app (op T') a = (FunctorToTypes.shrink.{u} F).overTotal.map a.op (pt Tt η) :=
    fun a ↦ (map_yonedaEquiv g a).symm.trans (by rw [← hb])
  let V := locus hZ hF h2 hA hlft hmono hét i η
  obtain ⟨φ, hφ⟩ := fac_locus hZ hF h2 hA hlft hmono hét i η
  refine ⟨V, yoneda.map φ.left, V.ι, ?_, inferInstance⟩
  apply IsPullback.of_forall_isPullback_app
  rintro ⟨T'⟩
  rw [Types.isPullback_iff]
  refine ⟨?_, ?_, ?_⟩
  · ext c
    change (chart ξ i).app (op T') (c ≫ φ.left) = g.app (op T') (c ≫ V.ι)
    rw [hg]
    exact chart_app_comp ξ i b.1 η V φ hφ c
  · rintro c c' ⟨-, h⟩
    exact (cancel_mono V.ι).mp h
  · intro x₂ x₃ hx
    change T' ⟶ (U i).left at x₂
    change T' ⟶ T at x₃
    change (chart ξ i).app (op T') x₂ = g.app (op T') x₃ at hx
    rw [chart_app, hg] at hx
    have hbase : x₂ ≫ (U i).hom = x₃ ≫ Tt.hom := congrArg (fun z ↦ z.1) hx
    let Z : Over S := Over.mk (x₃ ≫ Tt.hom)
    let x₃' : Z ⟶ Tt := Over.homMk x₃
    let x₂' : Z ⟶ U i := Over.homMk x₂ hbase
    have hfac : F.map x₂'.op (ξ i) = F.map x₃'.op η :=
      pt_injective Z ((overTotal_map_pt x₂' (ξ i)).symm.trans (hx.trans (overTotal_map_pt x₃' η)))
    have hrange : Set.range x₃ ⊆ Set.range V.ι := by
      rw [Scheme.Opens.range_ι]
      exact range_subset_W_of_fac (hmono i) hF ⟨x₂', hfac⟩
    let x := IsOpenImmersion.lift V.ι x₃ hrange
    have hxι : x ≫ V.ι = x₃ := IsOpenImmersion.lift_fac _ _ _
    refine ⟨x, ?_, hxι⟩
    change x ≫ φ.left = x₂
    let x' : Z ⟶ Over.mk (V.ι ≫ Tt.hom) := Over.homMk x (by
      change x ≫ V.ι ≫ Tt.hom = x₃ ≫ Tt.hom
      rw [← Category.assoc, hxι])
    have hx' : x' ≫ ιOver Tt V = x₃' := Over.OverMorphism.ext hxι
    have : x' ≫ φ = x₂' := hmono i _ _ (by
      rw [op_comp, Functor.map_comp_apply, hφ, ← Functor.map_comp_apply, ← op_comp, hx', hfac])
    exact congrArg CommaMorphism.left this

/-- If every point of `F` with values in a field factors through some `ξᵢ`, the charts are
jointly locally surjective. -/
theorem isLocallySurjective_chart
    (hcov : ∀ (K : Type u) [Field K] (f : Spec (CommRingCat.of K) ⟶ S)
      (η : F.obj (op (Over.mk f))), ∃ i, ∃ h : Over.mk f ⟶ U i, F.map h.op (ξ i) = η) :
    Presheaf.IsLocallySurjective Scheme.zariskiTopology (Sigma.desc (chart ξ)) := by
  constructor
  intro T b
  let Tt : Over S := Over.mk b.1
  let η : F.obj (op Tt) := (equivShrink _).symm (Functor.OverTotal.toFibre Tt b rfl)
  have hb : b = pt Tt η := eq_pt b
  have hcov' : ∀ x : T, ∃ i, x ∈ W (ξ i) η := fun x ↦ by
    obtain ⟨i, h, hh⟩ := hcov (T.residueField x) (T.fromSpecResidueField x ≫ b.1)
      (F.map (resPt Tt x).op η)
    exact ⟨i, h, hh⟩
  let V : ι → T.Opens := fun i ↦ locus hZ hF h2 hA hlft hmono hét i η
  let 𝒲 : T.OpenCover := Scheme.Cover.mkOfCovers ι (fun i ↦ ((V i : T.Opens) : Scheme.{u}))
    (fun i ↦ (V i).ι) (fun x ↦ by
      obtain ⟨i, hi⟩ := hcov' x
      exact ⟨i, ⟨x, hi⟩, rfl⟩)
  refine GrothendieckTopology.superset_covering _ ?_ 𝒲.mem_grothendieckTopology
  intro Y g hg
  obtain ⟨i, a, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ g).mp hg
  let a' : Y ⟶ (V i : Scheme.{u}) := a
  obtain ⟨φ, hφ⟩ := fac_locus hZ hF h2 hA hlft hmono hét i η
  have h1 : Sigma.ι (fun i ↦ yoneda.obj (U i).left) i ≫ Sigma.desc (chart ξ) = chart ξ i :=
    Sigma.ι_comp_desc _ _
  refine ⟨(Sigma.ι (fun i ↦ yoneda.obj (U i).left) i).app (op Y) (a' ≫ φ.left), ?_⟩
  change (Sigma.ι (fun i ↦ yoneda.obj (U i).left) i ≫ Sigma.desc (chart ξ)).app (op Y)
    (a' ≫ φ.left) = (FunctorToTypes.shrink.{u} F).overTotal.map (a' ≫ (V i).ι).op b
  rw [h1, hb]
  exact chart_app_comp ξ i b.1 η (V i) φ hφ a'

end Charts

/-! ### Murre's Lemma 3 -/

/-- Murre's Lemma 3 (SGA 3, XI, Proposition 3.5). -/
theorem murreChartGluing : MurreChartGluingStatement.{u, v} := by
  intro S _ F hS hZ hF h2 hA ι U ξ hlft hmono hét hcov
  have : FunctorToTypes.Small.{u} F := fun T ↦ hS T.unop
  let Gs : Sheaf Scheme.zariskiTopology.{u} (Type u) :=
    ⟨(FunctorToTypes.shrink.{u} F).overTotal,
      isSheaf_overTotal _ (zariskiSheaf_shrink hZ)⟩
  have hf : ∀ i, IsOpenImmersion.presheaf (show yoneda.obj (U i).left ⟶ Gs.1 from chart ξ i) :=
    isOpenImmersion_presheaf_chart hZ hF h2 hA hlft hmono hét
  have : Presheaf.IsLocallySurjective Scheme.zariskiTopology
      (Sigma.desc (fun i ↦ (show yoneda.obj (U i).left ⟶ Gs.1 from chart ξ i))) :=
    isLocallySurjective_chart hZ hF h2 hA hlft hmono hét hcov
  let eT : (FunctorToTypes.shrink.{u} F).overTotal.RepresentableBy _ :=
    Scheme.LocalRepresentability.representableBy (F := Gs) hf
  let j : ∀ i, (U i).left ⟶ (Scheme.LocalRepresentability.glueData (F := Gs) hf).glued :=
    fun i ↦ Scheme.LocalRepresentability.toGlued (F := Gs) hf i
  have hej : ∀ i, eT.homEquiv (j i) = pt (U i) (ξ i) := fun i ↦ by
    have h1 : eT.homEquiv (j i) = yonedaEquiv (chart ξ i) :=
      Scheme.LocalRepresentability.yonedaGluedToSheaf_app_toGlued (F := Gs) hf
    rw [h1, chart, Equiv.apply_symm_apply]
  let q := eT.overTotalBase
  have hjq : ∀ i, j i ≫ q = (U i).hom := fun i ↦ by
    rw [← eT.overTotal_homEquiv_fst, hej]
    rfl
  let e : F.RepresentableBy (Over.mk q) := representableByOfShrink eT.ofOverTotal
  have hji : ∀ i, (e.homEquiv.symm (ξ i)).left = j i := fun i ↦ by
    change eT.homEquiv.symm (pt (U i) (ξ i)) = j i
    rw [Equiv.symm_apply_eq, hej]
  refine ⟨_, q, e, ?_, fun i ↦ ?_, fun y ↦ ?_⟩
  · have : IsZariskiLocalAtSource @LocallyOfFiniteType.{u} :=
      HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.FiniteType)
    refine IsZariskiLocalAtSource.of_openCover (P := @LocallyOfFiniteType)
      (Scheme.LocalRepresentability.glueData (F := Gs) hf).openCover fun i ↦ ?_
    change LocallyOfFiniteType (j i ≫ q)
    have h := hlft i
    rw [← hjq i] at h
    exact h
  · rw [hji]
    infer_instance
  · obtain ⟨i, z, hz⟩ := (Scheme.LocalRepresentability.glueData (F := Gs) hf).ι_jointly_surjective y
    refine ⟨i, ?_⟩
    have hi := hji i
    rw [hi]
    exact ⟨z, hz⟩

end Langlands.AlgebraicGeometry.UnramifiedFunctor.ChartGluing
