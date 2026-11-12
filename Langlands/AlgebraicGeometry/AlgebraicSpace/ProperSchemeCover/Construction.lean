import Langlands.AlgebraicGeometry.AlgebraicSpace.ProperSchemeCover.CompleteTuples
import Langlands.AlgebraicGeometry.AlgebraicSpace.ProperSchemeCover.OpenGluing
import Langlands.AlgebraicGeometry.AlgebraicSpace.ProperSchemeCover.SpacePullback
import Langlands.AlgebraicGeometry.AlgebraicSpace.ReducedClosedSubspaceProof
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! # The weak Chow construction

Let `X` be a separated algebraic space over `S` with an étale surjective chart `π : h_W → X`.
Suppose given a fibre power `P` of `W` over `X` with `n + 1` factors in which every point of
`W` is the first coordinate of a complete point (`completeLocus`), an immersion
`W ⟶ O ⟶ Y` (closed, then open) into a scheme `Y` separated over `S`, and a scheme `M`
proper over `S` with maps `p i : M ⟶ Y` and `ε : P ⟶ M` with `ε ≫ p i = pr i ≫ (W ⟶ Y)`.
These are packaged as `ChowData`.

From this we build:
- `Z`: the reduced closed subscheme of `M` on the closure of `ε(G)`, `G` the complete locus;
- the opens `opens i = (p i)⁻¹(O)` of `Z`, and their union `X'`;
- morphisms `fac i : opens i ⟶ W` lifting `p i` through `W ⟶ Y`;
- the glued morphism `φ : h_{X'} → X`, which restricts to `π ∘ fac i` on `opens i`.

The main results are that `φ` is surjective (`isSurjective_φ`) and the finiteness properties of
`X' → S`. Represented properness of `φ` is proved in later modules.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace.ProperSchemeCover

open ReducedClosedSubspace

variable {S : Scheme.{u}}

/-- Morphisms to an algebraic space defined on the members of an open cover of an open `V`,
agreeing on pairwise intersections, glue to a morphism on `V`. -/
theorem exists_glue_hom_le (X : AlgebraicSpace S) {ι : Type*} (T : Over S) (V : T.left.Opens)
    (U : ι → T.left.Opens) (hle : ∀ i, U i ≤ V) (hU : ⨆ i, U i = V)
    (φ : ∀ i, (schemeYoneda S).obj (openOver T (U i)) ⟶ X.presheaf)
    (hφ : ∀ i j,
      (schemeYoneda S).map (openOverHomOfLE T (inf_le_left : U i ⊓ U j ≤ U i)) ≫ φ i =
        (schemeYoneda S).map (openOverHomOfLE T (inf_le_right : U i ⊓ U j ≤ U j)) ≫ φ j) :
    ∃ ψ : (schemeYoneda S).obj (openOver T V) ⟶ X.presheaf,
      ∀ i, (schemeYoneda S).map (openOverHomOfLE T (hle i)) ≫ ψ = φ i := by
  obtain ⟨y, hy⟩ := exists_glue_le X.toSheaf T V U hle hU
    (fun i => uliftYonedaEquiv.{u + 1} (φ i)) (fun i j => by
      rw [uliftYonedaEquiv_naturality, uliftYonedaEquiv_naturality]
      exact congrArg _ (hφ i j))
  refine ⟨uliftYonedaEquiv.{u + 1}.symm y, fun i => ?_⟩
  apply uliftYonedaEquiv.{u + 1}.injective
  rw [← hy i]
  conv_rhs => rw [← Equiv.apply_symm_apply uliftYonedaEquiv.{u + 1} y]
  rw [uliftYonedaEquiv_naturality]
  rfl

instance (T : Over S) (V : T.left.Opens) :
    _root_.AlgebraicGeometry.IsOpenImmersion (openOverι T V).left :=
  inferInstanceAs (_root_.AlgebraicGeometry.IsOpenImmersion V.ι)

instance (T : Over S) [IsReduced T.left] (V : T.left.Opens) : IsReduced (openOver T V).left :=
  inferInstanceAs (IsReduced V)

/-- A morphism over `S` whose range lies in the range of an open immersion factors through it. -/
theorem exists_lift_openImmersion {T A B : Over S} (o : A ⟶ B)
    [_root_.AlgebraicGeometry.IsOpenImmersion o.left] (f : T ⟶ B)
    (h : Set.range f.left ⊆ Set.range o.left) : ∃ g : T ⟶ A, g ≫ o = f := by
  refine ⟨Over.homMk (_root_.AlgebraicGeometry.IsOpenImmersion.lift o.left f.left h) ?_, ?_⟩
  · rw [← Over.w o, ← Category.assoc, _root_.AlgebraicGeometry.IsOpenImmersion.lift_fac, Over.w f]
  · apply Over.OverMorphism.ext
    exact _root_.AlgebraicGeometry.IsOpenImmersion.lift_fac _ _ _

/-- A lift of a morphism with dense range to an open subscheme still has dense range. -/
theorem dense_range_of_comp_openOverι {T' T : Over S} (V : T.left.Opens) (e : T' ⟶ T)
    (he : Dense (Set.range e.left)) (g : T' ⟶ openOver T V) (hg : g ≫ openOverι T V = e) :
    Dense (Set.range g.left) := by
  have hr : Set.range g.left = V.ι ⁻¹' Set.range e.left := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, by rw [← hg]; rfl⟩
    · rintro ⟨x, hx⟩
      refine ⟨x, V.ι.isOpenEmbedding.injective ?_⟩
      rw [← hx, ← hg]
      rfl
  rw [hr]
  exact he.preimage V.ι.isOpenEmbedding.isOpenMap

/-- **Lifting through a closed immersion by density.** A morphism `f` from a reduced scheme to
`B` factors through a closed immersion `j : A ⟶ B` as soon as `e ≫ f` does for some `e` with
dense range. -/
theorem exists_lift_of_dense {T' T A B : Over S} [IsReduced T.left] (j : A ⟶ B)
    [_root_.AlgebraicGeometry.IsClosedImmersion j.left] (f : T ⟶ B) (e : T' ⟶ T)
    (he : Dense (Set.range e.left))
    (g : T' ⟶ A) (hg : g ≫ j = e ≫ f) : ∃ f' : T ⟶ A, f' ≫ j = f := by
  apply exists_lift_isClosedImmersion_over j f
  have hcl : IsClosed (f.left ⁻¹' Set.range j.left) :=
    j.left.isClosedEmbedding.isClosed_range.preimage f.left.continuous
  have hsub : Set.range e.left ⊆ f.left ⁻¹' Set.range j.left := by
    rintro _ ⟨x, rfl⟩
    refine ⟨g.left x, ?_⟩
    change (g ≫ j).left x = (e ≫ f).left x
    rw [hg]
  have h := closure_minimal hsub hcl
  rw [he.closure_eq] at h
  rintro _ ⟨y, rfl⟩
  exact h (Set.mem_univ y)

/-- **Input of the weak Chow construction.** An étale surjective chart `π : h_W → X` of a
separated algebraic space, a fibre power `P` of `W` over `X` with `n + 1` factors in which
every point of `W` is the first coordinate of a complete point, an immersion of `W` into a
scheme `Y` separated over `S`, factored as a closed immersion `ι : W ⟶ O` followed by an open
immersion `o : O ⟶ Y` with `O` quasi-compact, and a scheme `M` proper over `S` with morphisms
`p i : M ⟶ Y` and `ε : P ⟶ M` such that `ε ≫ p i = pr i ≫ ι ≫ o`. -/
structure ChowData (X : AlgebraicSpace S) where
  /-- The space is separated. -/
  separated : IsSeparated X
  /-- The chart. -/
  W : Over S
  /-- The chart morphism. -/
  π : (schemeYoneda S).obj W ⟶ X.presheaf
  etale : IsEtale π
  surjective : IsSurjective π
  quasiCompact_W : QuasiCompact W.hom
  /-- The number of factors of the fibre power, minus one. -/
  n : ℕ
  /-- The fibre power of the chart. -/
  P : ChartFibrePower π (Fin (n + 1))
  complete : ∀ w : W.left, ∃ t ∈ completeLocus etale.1 P, (P.pr 0).left t = w
  /-- The separated target of the immersion of the chart. -/
  Y : Over S
  isSeparated_Y : _root_.AlgebraicGeometry.IsSeparated Y.hom
  /-- The open subscheme of `Y` containing the chart as a closed subscheme. -/
  O : Over S
  /-- The open immersion `O ⟶ Y`. -/
  o : O ⟶ Y
  isOpenImmersion_o : _root_.AlgebraicGeometry.IsOpenImmersion o.left
  compactSpace_O : CompactSpace O.left
  /-- The closed immersion `W ⟶ O`. -/
  ι : W ⟶ O
  isClosedImmersion_ι : _root_.AlgebraicGeometry.IsClosedImmersion ι.left
  /-- The proper scheme receiving the fibre power. -/
  M : Over S
  isProper_M : _root_.AlgebraicGeometry.IsProper M.hom
  /-- The projections of `M` to `Y`. -/
  p : Fin (n + 1) → (M ⟶ Y)
  /-- The map from the fibre power to `M`. -/
  ε : P.obj ⟶ M
  ε_p : ∀ i, ε ≫ p i = P.pr i ≫ ι ≫ o

namespace ChowData

variable {X : AlgebraicSpace S} (D : ChowData X)

attribute [instance] isSeparated_Y isOpenImmersion_o compactSpace_O isClosedImmersion_ι
  isProper_M quasiCompact_W

instance : Mono D.o := Over.mono_of_mono_left _

instance : Mono D.ι := Over.mono_of_mono_left _

/-- The complete locus of the fibre power. -/
abbrev G : Set D.P.obj.left := completeLocus D.etale.1 D.P

/-- The reduced closed subscheme of `M` on the closure of the image of the complete locus. -/
def Z : Over S := reducedOver D.M (Closeds.closure (D.ε.left '' D.G))

/-- The closed immersion `Z ⟶ M`. -/
def ζ : D.Z ⟶ D.M := reducedOverι D.M _

instance : _root_.AlgebraicGeometry.IsClosedImmersion D.ζ.left :=
  inferInstanceAs (_root_.AlgebraicGeometry.IsClosedImmersion (reducedOverι D.M _).left)

instance : IsReduced D.Z.left := by
  unfold Z; infer_instance

theorem range_ζ : Set.range D.ζ.left = closure (D.ε.left '' D.G) :=
  range_reducedOverι _ _

theorem Z_hom : D.Z.hom = D.ζ.left ≫ D.M.hom := (Over.w D.ζ).symm

instance : _root_.AlgebraicGeometry.IsProper D.Z.hom := by
  rw [Z_hom]; infer_instance

/-- The reduced closed subscheme of the fibre power on the closure of the complete locus. -/
def Gbar : Over S := reducedOver D.P.obj (Closeds.closure D.G)

/-- The closed immersion `Gbar ⟶ P`. -/
def gbar : D.Gbar ⟶ D.P.obj := reducedOverι _ _

instance : IsReduced D.Gbar.left := by
  unfold Gbar; infer_instance

theorem range_gbar : Set.range D.gbar.left = closure D.G :=
  range_reducedOverι _ _

theorem exists_εbar : ∃ e : D.Gbar ⟶ D.Z, e ≫ D.ζ = D.gbar ≫ D.ε :=
  exists_lift_reducedOver (D.gbar ≫ D.ε) _ (by
    rintro _ ⟨x, rfl⟩
    have hx : D.gbar.left x ∈ closure D.G := D.range_gbar ▸ ⟨x, rfl⟩
    exact image_closure_subset_closure_image D.ε.left.continuous ⟨_, hx, rfl⟩)

/-- The map `Gbar ⟶ Z` induced by `ε`. -/
def εbar : D.Gbar ⟶ D.Z := D.exists_εbar.choose

@[reassoc]
theorem εbar_ζ : D.εbar ≫ D.ζ = D.gbar ≫ D.ε := D.exists_εbar.choose_spec

/-- The points of `Z` lying over the image of the complete locus. -/
def A : Set D.Z.left := D.ζ.left ⁻¹' (D.ε.left '' D.G)

theorem dense_A : Dense D.A := by
  rw [dense_iff_closure_eq, A,
    D.ζ.left.isClosedEmbedding.toIsEmbedding.toIsInducing.closure_eq_preimage_closure_image,
    Set.image_preimage_eq_of_subset (by rw [D.range_ζ]; exact subset_closure), ← D.range_ζ,
    Set.preimage_range]

theorem A_subset : D.A ⊆ D.εbar.left '' (D.gbar.left ⁻¹' D.G) := by
  intro z hz
  obtain ⟨t, ht, hz⟩ := hz
  obtain ⟨x, rfl⟩ : t ∈ Set.range D.gbar.left := by
    rw [D.range_gbar]; exact subset_closure ht
  refine ⟨x, ht, D.ζ.left.isClosedEmbedding.injective ?_⟩
  rw [← hz]
  change (D.εbar ≫ D.ζ).left x = (D.gbar ≫ D.ε).left x
  rw [D.εbar_ζ]

theorem dense_range_εbar : Dense (Set.range D.εbar.left) :=
  D.dense_A.mono (D.A_subset.trans (Set.image_subset_range _ _))

/-- The open subscheme `(p i)⁻¹(O)` of `Z`. -/
def opens (i : Fin (D.n + 1)) : D.Z.left.Opens := (D.ζ ≫ D.p i).left ⁻¹ᵁ D.o.left.opensRange

theorem range_εbar_subset (i : Fin (D.n + 1)) :
    Set.range D.εbar.left ⊆ (D.opens i : Set D.Z.left) := by
  rintro _ ⟨x, rfl⟩
  have h : (D.ζ ≫ D.p i).left (D.εbar.left x) =
      D.o.left ((D.gbar ≫ D.P.pr i ≫ D.ι).left x) := by
    change (D.εbar ≫ D.ζ ≫ D.p i).left x = (D.gbar ≫ D.P.pr i ≫ D.ι ≫ D.o).left x
    rw [D.εbar_ζ_assoc, D.ε_p]
  change (D.ζ ≫ D.p i).left (D.εbar.left x) ∈ D.o.left.opensRange
  rw [h]
  exact ⟨_, rfl⟩

/-- A morphism to `opens i` composed with `fac i` is determined by its composite with
`ζ ≫ p i`. -/
theorem exists_fac (i : Fin (D.n + 1)) : ∃ f : openOver D.Z (D.opens i) ⟶ D.W,
    f ≫ D.ι ≫ D.o = openOverι D.Z (D.opens i) ≫ D.ζ ≫ D.p i := by
  obtain ⟨g, hg⟩ := exists_lift_openImmersion D.o (openOverι D.Z (D.opens i) ≫ D.ζ ≫ D.p i) (by
    rintro _ ⟨y, rfl⟩
    exact y.2)
  obtain ⟨e, he⟩ := exists_lift_openImmersion (openOverι D.Z (D.opens i)) D.εbar (by
    change _ ⊆ Set.range (D.opens i).ι
    rw [Scheme.Opens.range_ι]
    exact D.range_εbar_subset i)
  obtain ⟨f, hf⟩ := exists_lift_of_dense D.ι g e
    (dense_range_of_comp_openOverι _ _ D.dense_range_εbar e he) (D.gbar ≫ D.P.pr i) (by
      rw [← cancel_mono D.o, Category.assoc, Category.assoc, Category.assoc, hg, reassoc_of% he,
        D.εbar_ζ_assoc, D.ε_p])
  exact ⟨f, by rw [← Category.assoc, hf, hg]⟩

/-- The factorization of `ζ ≫ p i` on `opens i` through the chart `W`. -/
def fac (i : Fin (D.n + 1)) : openOver D.Z (D.opens i) ⟶ D.W := (D.exists_fac i).choose

@[reassoc]
theorem fac_spec (i : Fin (D.n + 1)) :
    D.fac i ≫ D.ι ≫ D.o = openOverι D.Z (D.opens i) ≫ D.ζ ≫ D.p i :=
  (D.exists_fac i).choose_spec

theorem comp_fac_eq {T : Over S} (i : Fin (D.n + 1)) (g : T ⟶ openOver D.Z (D.opens i))
    (w : T ⟶ D.W) (h : g ≫ openOverι D.Z (D.opens i) ≫ D.ζ ≫ D.p i = w ≫ D.ι ≫ D.o) :
    g ≫ D.fac i = w := by
  rw [← cancel_mono (D.ι ≫ D.o), Category.assoc, fac_spec, h]

theorem comp_fac_eq_of_εbar {T : Over S} (i : Fin (D.n + 1)) (g : T ⟶ openOver D.Z (D.opens i))
    (e : T ⟶ D.Gbar) (h : g ≫ openOverι D.Z (D.opens i) = e ≫ D.εbar) :
    g ≫ D.fac i = e ≫ D.gbar ≫ D.P.pr i := by
  apply D.comp_fac_eq
  rw [reassoc_of% h, D.εbar_ζ_assoc, D.ε_p]
  simp only [Category.assoc]

/-- On `opens i ⊓ opens j`, the factorizations `fac i` and `fac j` have the same image in `X`. -/
theorem fac_agree (i j : Fin (D.n + 1)) :
    (schemeYoneda S).map (openOverHomOfLE D.Z (inf_le_left : D.opens i ⊓ D.opens j ≤ _)) ≫
        (schemeYoneda S).map (D.fac i) ≫ D.π =
      (schemeYoneda S).map (openOverHomOfLE D.Z (inf_le_right : D.opens i ⊓ D.opens j ≤ _)) ≫
        (schemeYoneda S).map (D.fac j) ≫ D.π := by
  let a := openOverHomOfLE D.Z (inf_le_left : D.opens i ⊓ D.opens j ≤ _) ≫ D.fac i
  let b := openOverHomOfLE D.Z (inf_le_right : D.opens i ⊓ D.opens j ≤ _) ≫ D.fac j
  have := isClosedImmersion_spacePullbackLift D.π D.π D.separated
  obtain ⟨e, he⟩ := exists_lift_openImmersion (openOverι D.Z (D.opens i ⊓ D.opens j)) D.εbar (by
    change _ ⊆ Set.range (D.opens i ⊓ D.opens j).ι
    rw [Scheme.Opens.range_ι, TopologicalSpace.Opens.coe_inf]
    exact Set.subset_inter (D.range_εbar_subset i) (D.range_εbar_subset j))
  have hea : e ≫ a = D.gbar ≫ D.P.pr i := by
    have h := D.comp_fac_eq_of_εbar i
      (e ≫ openOverHomOfLE D.Z (inf_le_left : D.opens i ⊓ D.opens j ≤ _)) (𝟙 _)
      (by rw [Category.assoc, openOverHomOfLE_ι, he, Category.id_comp])
    rw [Category.id_comp, Category.assoc] at h
    exact h
  have heb : e ≫ b = D.gbar ≫ D.P.pr j := by
    have h := D.comp_fac_eq_of_εbar j
      (e ≫ openOverHomOfLE D.Z (inf_le_right : D.opens i ⊓ D.opens j ≤ _)) (𝟙 _)
      (by rw [Category.assoc, openOverHomOfLE_ι, he, Category.id_comp])
    rw [Category.id_comp, Category.assoc] at h
    exact h
  obtain ⟨l, hl⟩ := exists_lift_of_dense
    (lift (spacePullbackFst D.π D.π) (spacePullbackSnd D.π D.π)) (lift a b) e
    (dense_range_of_comp_openOverι _ _ D.dense_range_εbar e he)
    (spacePullbackLift (D.gbar ≫ D.P.pr i) (D.gbar ≫ D.P.pr j)
      (by rw [Functor.map_comp_assoc, Functor.map_comp_assoc, D.P.w i j])) (by
      apply CartesianMonoidalCategory.hom_ext
      · rw [Category.assoc, lift_fst, spacePullbackLift_fst, Category.assoc, lift_fst, hea]
      · rw [Category.assoc, lift_snd, spacePullbackLift_snd, Category.assoc, lift_snd, heb])
  have h₁ : l ≫ spacePullbackFst D.π D.π = a := by
    rw [← lift_fst (spacePullbackFst D.π D.π) (spacePullbackSnd D.π D.π), ← Category.assoc, hl,
      lift_fst]
  have h₂ : l ≫ spacePullbackSnd D.π D.π = b := by
    rw [← lift_snd (spacePullbackFst D.π D.π) (spacePullbackSnd D.π D.π), ← Category.assoc, hl,
      lift_snd]
  rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc]
  change (schemeYoneda S).map a ≫ D.π = (schemeYoneda S).map b ≫ D.π
  rw [← h₁, ← h₂, Functor.map_comp_assoc, Functor.map_comp_assoc, spacePullback_w]

/-- The union of the opens `opens i` of `Z`. -/
abbrev X' : D.Z.left.Opens := ⨆ i, D.opens i

/-- The scheme of the weak Chow cover: the open subscheme `X'` of `Z`. -/
abbrev U : Over S := openOver D.Z D.X'

theorem exists_φ : ∃ φ : (schemeYoneda S).obj D.U ⟶ X.presheaf, ∀ i,
    (schemeYoneda S).map (openOverHomOfLE D.Z (le_iSup D.opens i)) ≫ φ =
      (schemeYoneda S).map (D.fac i) ≫ D.π :=
  exists_glue_hom_le X D.Z D.X' D.opens (le_iSup D.opens) rfl _ D.fac_agree

/-- The cover `h_U → X`, glued from the morphisms `π ∘ fac i`. -/
def φ : (schemeYoneda S).obj D.U ⟶ X.presheaf := D.exists_φ.choose

theorem φ_spec (i : Fin (D.n + 1)) :
    (schemeYoneda S).map (openOverHomOfLE D.Z (le_iSup D.opens i)) ≫ D.φ =
      (schemeYoneda S).map (D.fac i) ≫ D.π :=
  D.exists_φ.choose_spec i

theorem range_εbar_subset_X' : Set.range D.εbar.left ⊆ Set.range (openOverι D.Z D.X').left := by
  change _ ⊆ Set.range D.X'.ι
  rw [Scheme.Opens.range_ι]
  exact (D.range_εbar_subset 0).trans (le_iSup D.opens 0)

/-- The map `Gbar ⟶ U` induced by `ε`. -/
def εU : D.Gbar ⟶ D.U :=
  (exists_lift_openImmersion (openOverι D.Z D.X') D.εbar D.range_εbar_subset_X').choose

@[reassoc]
theorem εU_ι : D.εU ≫ openOverι D.Z D.X' = D.εbar :=
  (exists_lift_openImmersion (openOverι D.Z D.X') D.εbar D.range_εbar_subset_X').choose_spec

instance : Mono (openOverι D.Z D.X') := Over.mono_of_mono_left _

theorem εU_φ : (schemeYoneda S).map D.εU ≫ D.φ =
    (schemeYoneda S).map (D.gbar ≫ D.P.pr 0) ≫ D.π := by
  obtain ⟨e, he⟩ := exists_lift_openImmersion (openOverι D.Z (D.opens 0)) D.εbar (by
    change _ ⊆ Set.range (D.opens 0).ι
    rw [Scheme.Opens.range_ι]
    exact D.range_εbar_subset 0)
  have h : D.εU = e ≫ openOverHomOfLE D.Z (le_iSup D.opens 0) := by
    rw [← cancel_mono (openOverι D.Z D.X'), εU_ι, Category.assoc, openOverHomOfLE_ι, he]
  rw [h, Functor.map_comp_assoc, φ_spec, ← Functor.map_comp_assoc,
    D.comp_fac_eq_of_εbar 0 e (𝟙 _) (by rw [he, Category.id_comp]), Category.id_comp]

/-- **The cover is surjective.** -/
theorem isSurjective_φ : IsSurjective D.φ := by
  refine isSurjective_of_isPullback (X.representable_from_scheme D.φ) D.surjective
    (spacePullback_isPullback D.φ D.π) ⟨fun w => ?_⟩
  obtain ⟨t, ht, rfl⟩ := D.complete w
  obtain ⟨x, rfl⟩ : t ∈ Set.range D.gbar.left := by
    rw [D.range_gbar]; exact subset_closure ht
  refine ⟨(spacePullbackLift D.εU (D.gbar ≫ D.P.pr 0) D.εU_φ).left x, ?_⟩
  change (spacePullbackLift D.εU (D.gbar ≫ D.P.pr 0) D.εU_φ ≫ spacePullbackSnd D.φ D.π).left x = _
  rw [spacePullbackLift_snd]
  rfl

theorem U_hom : D.U.hom = D.X'.ι ≫ D.ζ.left ≫ D.M.hom := by
  change D.X'.ι ≫ D.Z.hom = _
  rw [Z_hom]

instance : LocallyOfFiniteType D.U.hom := by
  rw [U_hom]
  have : LocallyOfFiniteType D.M.hom := inferInstance
  have : LocallyOfFiniteType D.ζ.left := inferInstance
  have : LocallyOfFiniteType D.X'.ι := inferInstance
  infer_instance

instance : _root_.AlgebraicGeometry.IsSeparated D.U.hom := by
  rw [U_hom]
  have : _root_.AlgebraicGeometry.IsSeparated D.M.hom := inferInstance
  have : _root_.AlgebraicGeometry.IsSeparated D.ζ.left := inferInstance
  have : _root_.AlgebraicGeometry.IsSeparated D.X'.ι := inferInstance
  infer_instance

end ChowData

end Langlands.AlgebraicGeometry.AlgebraicSpace.ProperSchemeCover
