import Langlands.AlgebraicGeometry.Picard.NoetherianOpenPiecesGluingStatement
import Langlands.AlgebraicGeometry.PointTopology.QuasiProjectiveWeilRestriction
import Langlands.AlgebraicGeometry.PointTopology.FiniteAffineNeighborhoodsDirectedCover
import Langlands.AlgebraicGeometry.PointTopology.FiniteAffineNeighborhoodsOpenShrinking
import Langlands.AlgebraicGeometry.ProjectiveSpace.Structure
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Sites.Pretopology

/-! # Gluing a Zariski sheaf from quasi-projective open pieces: the proof -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard.NoetherianOpenPiecesGluing

/-- Index of the pieces: pairs `(c, m)`, with `(c, m) ≤ (c', m')` iff `c = c'` and `m ≤ m'`. -/
def Idx (κ : Type) : Type := κ × ℕ

instance (κ : Type) : Preorder (Idx κ) where
  le i j := i.1 = j.1 ∧ i.2 ≤ j.2
  le_refl _ := ⟨rfl, le_rfl⟩
  le_trans _ _ _ hij hjk := ⟨hij.1.trans hjk.1, hij.2.trans hjk.2⟩

/-- The index `(c, m)`. -/
def Idx.mk {κ : Type} (c : κ) (m : ℕ) : Idx κ := (c, m)

/-- The hypotheses of `NoetherianOpenPiecesGluingStatement`, bundled. -/
structure Data (A : Type u) [CommRing A] [IsNoetherianRing A] where
  /-- The Zariski sheaf. -/
  F : (Over (Spec (CommRingCat.of A)))ᵒᵖ ⥤ Type (u + 1)
  hF : Presheaf.IsSheaf (Scheme.zariskiTopology.over (Spec (CommRingCat.of A))) F
  /-- The index type of the strata. -/
  κ : Type
  /-- The open pieces. -/
  V : ∀ T : Over (Spec (CommRingCat.of A)), F.obj (op T) → κ → ℕ → T.left.Opens
  /-- The representing schemes. -/
  Q : κ → ℕ → Over (Spec (CommRingCat.of A))
  /-- The maps to `F`. -/
  β : ∀ (c : κ) (m : ℕ), uliftYoneda.{u + 1}.obj (Q c m) ⟶ F
  base : ∀ (T T' : Over (Spec (CommRingCat.of A))) [IsLocallyNoetherian T.left]
      [IsLocallyNoetherian T'.left] (h : T' ⟶ T) (ξ : F.obj (op T)) (c : κ) (m : ℕ),
      V T' (F.map h.op ξ) c m = h.left ⁻¹ᵁ V T ξ c m
  shape : ∀ (T : Over (Spec (CommRingCat.of A))) [IsLocallyNoetherian T.left]
      (ξ : F.obj (op T)),
      (∀ (c : κ) (m : ℕ), V T ξ c m ≤ V T ξ c (m + 1)) ∧
      (∀ (c c' : κ) (m m' : ℕ), c ≠ c' → Disjoint (V T ξ c m) (V T ξ c' m')) ∧
      (⨆ (c : κ) (m : ℕ), V T ξ c m) = ⊤
  imm : ∀ (c : κ) (m : ℕ), ∃ (n : ℕ) (i : (Q c m).left ⟶ ProjectiveSpace A n),
      IsImmersion i ∧ i ≫ projectiveSpaceToSpec A n = (Q c m).hom
  rep : ∀ (c : κ) (m : ℕ) (T : Over (Spec (CommRingCat.of A))) [IsLocallyNoetherian T.left],
      Function.Injective ((β c m).app (op T)) ∧
        ∀ ξ : F.obj (op T), V T ξ c m = ⊤ ↔ ξ ∈ Set.range ((β c m).app (op T))


/-- The restriction of an `S`-scheme to an open subscheme. -/
abbrev res {S : Scheme.{u}} (T : Over S) (U : T.left.Opens) : Over S := Over.mk (U.ι ≫ T.hom)

/-- The inclusion of the restriction. -/
abbrev resι {S : Scheme.{u}} (T : Over S) (U : T.left.Opens) : res T U ⟶ T := Over.homMk U.ι

lemma range_subset_of_le {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Z ⟶ Y) [IsOpenImmersion g]
    (U : X.Opens)
    (hU : U ≤ f ⁻¹ᵁ g.opensRange) : Set.range (U.ι ≫ f) ⊆ Set.range g := by
  rintro _ ⟨z, rfl⟩
  have hz : U.ι z ∈ (U : Set X) := by rw [← Scheme.Opens.range_ι]; exact ⟨z, rfl⟩
  rw [Scheme.Hom.comp_apply]
  exact hU hz

namespace Data

variable {A : Type u} [CommRing A] [IsNoetherianRing A] (D : Data A)

/-- The representing scheme of the piece with index `i`. -/
abbrev QI (i : Idx D.κ) : Over (Spec (CommRingCat.of A)) := D.Q i.1 i.2

/-- The open piece with index `i`. -/
abbrev VI (T : Over (Spec (CommRingCat.of A))) (ξ : D.F.obj (op T)) (i : Idx D.κ) :
    T.left.Opens :=
  D.V T ξ i.1 i.2

lemma locallyOfFiniteType_hom (i : Idx D.κ) : LocallyOfFiniteType (D.QI i).hom := by
  obtain ⟨n, f, hf, hfh⟩ := D.imm i.1 i.2
  have := hf
  rw [← hfh]
  infer_instance

instance isLocallyNoetherian_QI (i : Idx D.κ) : IsLocallyNoetherian (D.QI i).left := by
  have := D.locallyOfFiniteType_hom i
  exact LocallyOfFiniteType.isLocallyNoetherian (D.QI i).hom

lemma locallyOfFinitePresentation_hom (i : Idx D.κ) :
    LocallyOfFinitePresentation (D.QI i).hom := by
  have := D.locallyOfFiniteType_hom i
  exact LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr inferInstance

lemma hasFiniteAffineNeighborhoods_QI (i : Idx D.κ) :
    PointTopology.HasFiniteAffineNeighborhoods (D.QI i).left := by
  obtain ⟨n, f, hf, -⟩ := D.imm i.1 i.2
  have := hf
  exact PointTopology.hasFiniteAffineNeighborhoods_of_projectiveImmersion A n f

/-- The universal element of the piece with index `i`. -/
def x (i : Idx D.κ) : D.F.obj (op (D.QI i)) := uliftYonedaEquiv (D.β i.1 i.2)

lemma β_app {T : Over (Spec (CommRingCat.of A))} (i : Idx D.κ) (g : T ⟶ D.QI i) :
    (D.β i.1 i.2).app (op T) (ULift.up g) = D.F.map g.op (D.x i) := by
  rw [x, uliftYonedaEquiv_naturality, uliftYonedaEquiv_comp]
  simp [uliftYonedaEquiv_uliftYoneda_map]

lemma map_x_injective (i : Idx D.κ) (T : Over (Spec (CommRingCat.of A)))
    [IsLocallyNoetherian T.left] {g g' : T ⟶ D.QI i}
    (h : D.F.map g.op (D.x i) = D.F.map g'.op (D.x i)) : g = g' := by
  rw [← D.β_app, ← D.β_app] at h
  exact congrArg ULift.down ((D.rep i.1 i.2 T).1 h)

lemma exists_map_x (i : Idx D.κ) (T : Over (Spec (CommRingCat.of A)))
    [IsLocallyNoetherian T.left] (ξ : D.F.obj (op T)) (h : D.VI T ξ i = ⊤) :
    ∃ g : T ⟶ D.QI i, D.F.map g.op (D.x i) = ξ := by
  obtain ⟨⟨g⟩, hg⟩ := ((D.rep i.1 i.2 T).2 ξ).mp h
  exact ⟨g, (D.β_app i g).symm.trans hg⟩

lemma V_map_x (i : Idx D.κ) (T : Over (Spec (CommRingCat.of A)))
    [IsLocallyNoetherian T.left] (g : T ⟶ D.QI i) : D.VI T (D.F.map g.op (D.x i)) i = ⊤ :=
  ((D.rep i.1 i.2 T).2 _).mpr ⟨ULift.up g, D.β_app i g⟩

lemma V_x_self (i : Idx D.κ) : D.VI (D.QI i) (D.x i) i = ⊤ := by
  simpa using D.V_map_x i (D.QI i) (𝟙 _)

lemma V_mono (T : Over (Spec (CommRingCat.of A))) [IsLocallyNoetherian T.left]
    (ξ : D.F.obj (op T)) (c : D.κ) {m m' : ℕ} (h : m ≤ m') : D.V T ξ c m ≤ D.V T ξ c m' :=
  monotone_nat_of_le_succ (fun n ↦ (D.shape T ξ).1 c n) h

lemma V_x_of_le {i j : Idx D.κ} (h : i ≤ j) : D.VI (D.QI i) (D.x i) j = ⊤ := by
  have h1 : j.1 = i.1 := h.1.symm
  have := D.V_mono (D.QI i) (D.x i) i.1 h.2
  rw [VI, h1]
  exact top_le_iff.mp ((D.V_x_self i).symm.le.trans this)

/-- The transition map between pieces with the same first index. -/
def τ {i j : Idx D.κ} (h : i ≤ j) : D.QI i ⟶ D.QI j :=
  (D.exists_map_x j (D.QI i) (D.x i) (D.V_x_of_le h)).choose

lemma map_τ_x {i j : Idx D.κ} (h : i ≤ j) : D.F.map (D.τ h).op (D.x j) = D.x i :=
  (D.exists_map_x j (D.QI i) (D.x i) (D.V_x_of_le h)).choose_spec

lemma τ_id (i : Idx D.κ) : D.τ (le_refl i) = 𝟙 _ :=
  D.map_x_injective i _ (by rw [D.map_τ_x]; simp)

lemma τ_comp {i j k : Idx D.κ} (hij : i ≤ j) (hjk : j ≤ k) :
    D.τ hij ≫ D.τ hjk = D.τ (hij.trans hjk) :=
  D.map_x_injective k _ (by
    rw [op_comp, Functor.map_comp, types_comp_apply, D.map_τ_x, D.map_τ_x, D.map_τ_x])

lemma preimage_τ {i j : Idx D.κ} (h : i ≤ j) :
    (D.τ h).left ⁻¹ᵁ D.VI (D.QI j) (D.x j) i = ⊤ := by
  have hb := D.base (D.QI j) (D.QI i) (D.τ h) (D.x j) i.1 i.2
  rw [D.map_τ_x] at hb
  rw [VI, ← hb]
  exact D.V_x_self i

/-- The open piece `V (Q j) (x j) i` of `Q j`, as an `S`-scheme. -/
abbrev Wτ {i j : Idx D.κ} (_ : i ≤ j) : Over (Spec (CommRingCat.of A)) :=
  Over.mk ((D.VI (D.QI j) (D.x j) i).ι ≫ (D.QI j).hom)

/-- The inclusion of the open piece. -/
abbrev ιWτ {i j : Idx D.κ} (h : i ≤ j) : D.Wτ h ⟶ D.QI j :=
  Over.homMk (D.VI (D.QI j) (D.x j) i).ι

instance {i j : Idx D.κ} (h : i ≤ j) : IsLocallyNoetherian (D.Wτ h).left := by
  dsimp [Wτ]; infer_instance

lemma VI_Wτ {i j : Idx D.κ} (h : i ≤ j) :
    D.VI (D.Wτ h) (D.F.map (D.ιWτ h).op (D.x j)) i = ⊤ := by
  rw [VI, D.base (D.QI j) (D.Wτ h) (D.ιWτ h) (D.x j) i.1 i.2]
  exact Scheme.Opens.ι_preimage_self _

instance isOpenImmersion_τ {i j : Idx D.κ} (h : i ≤ j) : IsOpenImmersion (D.τ h).left := by
  set W := D.VI (D.QI j) (D.x j) i with hW
  have H' : Set.range (D.τ h).left ⊆ Set.range W.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨y, rfl⟩
    have : y ∈ (D.τ h).left ⁻¹ᵁ W := by rw [D.preimage_τ h]; trivial
    exact this
  obtain ⟨k, hk⟩ := D.exists_map_x i (D.Wτ h) _ (D.VI_Wτ h)
  let g' : D.QI i ⟶ D.Wτ h := Over.homMk (IsOpenImmersion.lift W.ι (D.τ h).left H') (by
    simp only [Over.mk_hom, Wτ]
    rw [IsOpenImmersion.lift_fac_assoc, Over.w])
  have hg' : g' ≫ D.ιWτ h = D.τ h := by
    ext1; simp only [g', Over.comp_left, Over.homMk_left]; exact IsOpenImmersion.lift_fac _ _ _
  have hkg : k ≫ D.τ h = D.ιWτ h := D.map_x_injective j _ (by
    rw [op_comp, Functor.map_comp, types_comp_apply, D.map_τ_x, hk])
  have h1 : g' ≫ k = 𝟙 _ := D.map_x_injective i _ (by
    rw [op_comp, Functor.map_comp, types_comp_apply, hk, ← types_comp_apply (D.F.map _)
      (D.F.map _), ← Functor.map_comp, ← op_comp, hg', D.map_τ_x]; simp)
  have : Mono (D.ιWτ h) := by
    have : Mono (D.ιWτ h).left := by dsimp [ιWτ]; infer_instance
    exact Over.mono_of_mono_left _
  have h2 : k ≫ g' = 𝟙 _ := by
    rw [← cancel_mono (D.ιWτ h), Category.assoc, hg', hkg, Category.id_comp]
  have : IsIso g' := ⟨⟨k, h1, h2⟩⟩
  have : IsIso g'.left := inferInstanceAs (IsIso ((Over.forget _).map g'))
  have e : (D.τ h).left = g'.left ≫ W.ι := by
    rw [← hg']; rfl
  rw [e]
  infer_instance

/-- The diagram of pieces. -/
@[simps]
def diagram : Idx D.κ ⥤ Over (Spec (CommRingCat.of A)) where
  obj i := D.QI i
  map f := D.τ (leOfHom f)
  map_id i := D.τ_id i
  map_comp _ _ := (D.τ_comp _ _).symm

instance : Small.{u} (Idx D.κ) := small_zero _

instance : Quiver.IsThin (Idx D.κ) := fun _ _ ↦ inferInstance

/-- The diagram of pieces, as schemes. -/
abbrev G : Idx D.κ ⥤ Scheme.{u} := D.diagram ⋙ Over.forget _

instance isOpenImmersion_G {i j : Idx D.κ} (f : i ⟶ j) : IsOpenImmersion (D.G.map f) :=
  D.isOpenImmersion_τ (leOfHom f)

lemma G_map_injective {i j : Idx D.κ} (f : i ⟶ j) : Function.Injective (D.G.map f) :=
  (D.G.map f).isOpenEmbedding.injective

lemma G_map_comp_apply {i j k : Idx D.κ} (f : i ⟶ j) (g : j ⟶ k) (h : i ⟶ k)
    (y : D.G.obj i) : D.G.map g (D.G.map f y) = D.G.map h y := by
  rw [← Scheme.Hom.comp_apply, ← Functor.map_comp, Subsingleton.elim (f ≫ g) h]

instance isLocallyDirected : (D.G ⋙ Scheme.forget).IsLocallyDirected := by
  constructor
  intro i j k fi fj xi xj hx
  change D.G.map fi xi = D.G.map fj xj at hx
  have hi := leOfHom fi
  have hj := leOfHom fj
  rcases le_total i.2 j.2 with h | h
  · have hij : i ≤ j := ⟨hi.1.trans hj.1.symm, h⟩
    refine ⟨i, 𝟙 i, homOfLE hij, xi, by rw [CategoryTheory.Functor.map_id]; rfl, ?_⟩
    apply D.G_map_injective fj
    change D.G.map fj (D.G.map (homOfLE hij) xi) = D.G.map fj xj
    rw [D.G_map_comp_apply _ _ fi, hx]
  · have hji : j ≤ i := ⟨hj.1.trans hi.1.symm, h⟩
    refine ⟨j, homOfLE hji, 𝟙 j, xj, ?_, by rw [CategoryTheory.Functor.map_id]; rfl⟩
    apply D.G_map_injective fi
    change D.G.map fi (D.G.map (homOfLE hji) xj) = D.G.map fi xi
    rw [D.G_map_comp_apply _ _ fj, hx]

/-- The structure maps of the pieces, as a cocone. -/
def cocone : Cocone D.G where
  pt := Spec (CommRingCat.of A)
  ι :=
    { app i := (D.QI i).hom
      naturality := fun _ _ f ↦ (Over.w (D.τ (leOfHom f))).trans (Category.comp_id _).symm }

/-- The glued scheme, as an `S`-scheme. -/
def P : Over (Spec (CommRingCat.of A)) :=
  Over.mk (colimit.desc D.G D.cocone)

lemma P_left : D.P.left = colimit D.G := rfl

/-- The inclusion of the piece with index `i` into the glued scheme. -/
def ι (i : Idx D.κ) : D.QI i ⟶ D.P :=
  Over.homMk (colimit.ι D.G i) (colimit.ι_desc D.cocone i)

@[simp]
lemma ι_left (i : Idx D.κ) : (D.ι i).left = colimit.ι D.G i := rfl

instance isOpenImmersion_colimit_ι (i : Idx D.κ) : IsOpenImmersion (colimit.ι D.G i) :=
  inferInstance

instance isOpenImmersion_ι (i : Idx D.κ) : IsOpenImmersion (D.ι i).left :=
  D.isOpenImmersion_colimit_ι i

instance mono_ι (i : Idx D.κ) : Mono (D.ι i) := Over.mono_of_mono_left _

lemma τ_ι {i j : Idx D.κ} (h : i ≤ j) : D.τ h ≫ D.ι j = D.ι i := by
  ext1
  exact colimit.w D.G (homOfLE h)

lemma le_of_ι_eq {i j : Idx D.κ} {yi : D.G.obj i} {yj : D.G.obj j}
    (h : colimit.ι D.G i yi = colimit.ι D.G j yj) : i.1 = j.1 := by
  obtain ⟨k, fi, fj, -, -, -⟩ := (Scheme.IsLocallyDirected.ι_eq_ι_iff D.G).mp h
  exact (leOfHom fi).1.symm.trans (leOfHom fj).1

/-- Two points over the same locally noetherian base, with values in different strata, force
the base to be empty. -/
lemma isEmpty_of_ne (O : Over (Spec (CommRingCat.of A))) [IsLocallyNoetherian O.left]
    (ζ : D.F.obj (op O)) {i j : Idx D.κ} (hij : i.1 ≠ j.1) (hi : D.VI O ζ i = ⊤)
    (hj : D.VI O ζ j = ⊤) : IsEmpty O.left := by
  have hd := (D.shape O ζ).2.1 i.1 j.1 i.2 j.2 hij
  change Disjoint (D.VI O ζ i) (D.VI O ζ j) at hd
  rw [hi, hj, disjoint_self] at hd
  refine ⟨fun y ↦ ?_⟩
  have : y ∈ (⊤ : O.left.Opens) := trivial
  rw [hd] at this
  exact this

/-- Agreement: two maps into pieces that pull back the universal elements to the same element
agree in the glued scheme. -/
lemma agree (O : Over (Spec (CommRingCat.of A))) [IsLocallyNoetherian O.left]
    {i j : Idx D.κ} (h1 : O ⟶ D.QI i) (h2 : O ⟶ D.QI j)
    (h : D.F.map h1.op (D.x i) = D.F.map h2.op (D.x j)) : h1 ≫ D.ι i = h2 ≫ D.ι j := by
  by_cases hij : i.1 = j.1
  · let k : Idx D.κ := (i.1, max i.2 j.2)
    have hik : i ≤ k := ⟨rfl, le_max_left _ _⟩
    have hjk : j ≤ k := ⟨hij.symm, le_max_right _ _⟩
    have : h1 ≫ D.τ hik = h2 ≫ D.τ hjk := D.map_x_injective k O (by
      rw [op_comp, Functor.map_comp, types_comp_apply, D.map_τ_x, op_comp, Functor.map_comp,
        types_comp_apply, D.map_τ_x, h])
    rw [← D.τ_ι hik, ← D.τ_ι hjk, ← Category.assoc, this, Category.assoc]
  · have := D.isEmpty_of_ne O (D.F.map h1.op (D.x i)) hij (D.V_map_x i O h1)
      (by rw [h]; exact D.V_map_x j O h2)
    ext1
    exact (isInitialOfIsEmpty (X := O.left)).hom_ext _ _

lemma eq_of_isEmpty (Z : Over (Spec (CommRingCat.of A))) [IsEmpty Z.left]
    (a b : D.F.obj (op Z)) : a = b := by
  have hF := (isSheaf_iff_isSheaf_of_type _ _).mp D.hF
  have hbot : (⊥ : Sieve Z) ∈ (Scheme.zariskiTopology.over (Spec (CommRingCat.of A))) Z := by
    rw [GrothendieckTopology.mem_over_iff]
    have : Sieve.overEquiv Z (⊥ : Sieve Z) = ⊥ := (Sieve.overEquiv Z).map_bot
    rw [this]
    exact Scheme.bot_mem_grothendieckTopology Z.left
  exact (hF _ hbot).isSeparatedFor.ext (fun _ _ h ↦ h.elim)

lemma isSheafFor_ofArrows {T : Over (Spec (CommRingCat.of A))} {I : Type*}
    (Z : I → Over (Spec (CommRingCat.of A))) (π : ∀ i, Z i ⟶ T)
    (h : Sieve.ofArrows (fun i ↦ (Z i).left) (fun i ↦ (π i).left) ∈
      Scheme.zariskiTopology T.left) :
    Presieve.IsSheafFor D.F (Presieve.ofArrows Z π) := by
  have hF := (isSheaf_iff_isSheaf_of_type _ _).mp D.hF
  rw [Presieve.isSheafFor_iff_generate]
  apply hF
  rw [GrothendieckTopology.mem_over_iff]
  change Sieve.overEquiv T (Sieve.ofArrows Z π) ∈ _
  rw [Sieve.overEquiv_ofArrows]
  exact h

lemma isSheafFor_openCover {T : Over (Spec (CommRingCat.of A))} (𝒰 : T.left.OpenCover) :
    Presieve.IsSheafFor D.F (Presieve.ofArrows (fun i ↦ Over.mk (𝒰.f i ≫ T.hom))
      (fun i ↦ (Over.homMk (𝒰.f i) : Over.mk (𝒰.f i ≫ T.hom) ⟶ T))) :=
  D.isSheafFor_ofArrows _ _ 𝒰.mem_grothendieckTopology

lemma compatible_x : Presieve.Arrows.Compatible D.F D.ι D.x := by
  intro i j Z gi gj hg
  by_cases hij : i.1 = j.1
  · let k : Idx D.κ := (i.1, max i.2 j.2)
    have hik : i ≤ k := ⟨rfl, le_max_left _ _⟩
    have hjk : j ≤ k := ⟨hij.symm, le_max_right _ _⟩
    have : gi ≫ D.τ hik = gj ≫ D.τ hjk := by
      rw [← cancel_mono (D.ι k), Category.assoc, Category.assoc, D.τ_ι, D.τ_ι, hg]
    rw [← D.map_τ_x hik, ← D.map_τ_x hjk, ← types_comp_apply (D.F.map _) (D.F.map gi.op),
      ← types_comp_apply (D.F.map _) (D.F.map gj.op), ← Functor.map_comp, ← Functor.map_comp,
      ← op_comp, ← op_comp, this]
  · have : IsEmpty Z.left := by
      refine ⟨fun z ↦ hij ?_⟩
      have h2 := congrArg (fun f ↦ f.left z) hg
      simp only [Over.comp_left, ι_left] at h2
      exact D.le_of_ι_eq h2
    exact D.eq_of_isEmpty Z _ _

lemma exists_ξP : ∃ t : D.F.obj (op D.P), ∀ i, D.F.map (D.ι i).op t = D.x i := by
  have hcov : Sieve.ofArrows (fun i ↦ (D.QI i).left) (fun i ↦ (D.ι i).left) ∈
      Scheme.zariskiTopology D.P.left :=
    ofArrows_ι_mem_zariskiTopology_of_isColimit D.G _ (colimit.isColimit D.G)
  obtain ⟨t, ht, -⟩ := (Presieve.isSheafFor_arrows_iff _ _).mp
    (D.isSheafFor_ofArrows D.QI D.ι hcov) D.x D.compatible_x
  exact ⟨t, ht⟩

/-- The glued element of `F` over the glued scheme. -/
def ξP : D.F.obj (op D.P) := D.exists_ξP.choose

lemma map_ι_ξP (i : Idx D.κ) : D.F.map (D.ι i).op D.ξP = D.x i :=
  D.exists_ξP.choose_spec i

lemma exists_factor (T : Over (Spec (CommRingCat.of A))) (g : T ⟶ D.P) (i : Idx D.κ)
    (U : T.left.Opens) (hU : U ≤ g.left ⁻¹ᵁ (D.ι i).left.opensRange) :
    ∃ a : res T U ⟶ D.QI i, a ≫ D.ι i = resι T U ≫ g := by
  have H := range_subset_of_le g.left (D.ι i).left U hU
  refine ⟨Over.homMk (IsOpenImmersion.lift (D.ι i).left (U.ι ≫ g.left) H) ?_, ?_⟩
  · rw [← Over.w (D.ι i), IsOpenImmersion.lift_fac_assoc, Category.assoc, Over.w g]
    rfl
  · ext1
    exact IsOpenImmersion.lift_fac _ _ _

lemma map_x_of_factor {T : Over (Spec (CommRingCat.of A))} (g : T ⟶ D.P) {i : Idx D.κ}
    {U : T.left.Opens} {a : res T U ⟶ D.QI i} (ha : a ≫ D.ι i = resι T U ≫ g) :
    D.F.map a.op (D.x i) = D.F.map (resι T U).op (D.F.map g.op D.ξP) := by
  rw [← D.map_ι_ξP i, ← types_comp_apply (D.F.map _) (D.F.map a.op),
    ← types_comp_apply (D.F.map _) (D.F.map (resι T U).op), ← Functor.map_comp,
    ← Functor.map_comp, ← op_comp, ← op_comp, ha]

lemma map_ξP_injective (T : Over (Spec (CommRingCat.of A))) [IsLocallyNoetherian T.left]
    {g1 g2 : T ⟶ D.P} (h : D.F.map g1.op D.ξP = D.F.map g2.op D.ξP) : g1 = g2 := by
  ext1
  apply Scheme.hom_ext_of_forall
  intro y
  obtain ⟨i, yi, hyi⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective D.G (g1.left y)
  obtain ⟨j, yj, hyj⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective D.G (g2.left y)
  let U : T.left.Opens :=
    g1.left ⁻¹ᵁ (D.ι i).left.opensRange ⊓ g2.left ⁻¹ᵁ (D.ι j).left.opensRange
  refine ⟨U, ⟨⟨yi, hyi⟩, ⟨yj, hyj⟩⟩, ?_⟩
  obtain ⟨a, ha⟩ := D.exists_factor T g1 i U inf_le_left
  obtain ⟨b, hb⟩ := D.exists_factor T g2 j U inf_le_right
  have : IsLocallyNoetherian (res T U).left := by dsimp; infer_instance
  have hab := D.agree (res T U) a b (by
    rw [D.map_x_of_factor g1 ha, D.map_x_of_factor g2 hb, h])
  rw [ha, hb] at hab
  exact congrArg (fun f ↦ f.left) hab

lemma exists_map_ξP (T : Over (Spec (CommRingCat.of A))) [IsLocallyNoetherian T.left]
    (ξ : D.F.obj (op T)) : ∃ g : T ⟶ D.P, D.F.map g.op D.ξP = ξ := by
  let U : Idx D.κ → T.left.Opens := D.VI T ξ
  have hU : IsOpenCover U := by
    have := (D.shape T ξ).2.2
    rw [IsOpenCover, ← this]
    exact iSup_prod
  let 𝒰 := T.left.openCoverOfIsOpenCover U hU
  have hk : ∀ i, ∃ k : res T (U i) ⟶ D.QI i,
      D.F.map k.op (D.x i) = D.F.map (resι T (U i)).op ξ := fun i ↦ by
    have : IsLocallyNoetherian (res T (U i)).left := by dsimp; infer_instance
    refine D.exists_map_x i _ _ ?_
    rw [VI, D.base T (res T (U i)) (resι T (U i)) ξ]
    exact Scheme.Opens.ι_preimage_self _
  choose k hk using hk
  let f : ∀ i : Idx D.κ, (U i).toScheme ⟶ D.P.left := fun i ↦ (k i).left ≫ (D.ι i).left
  have hf : ∀ i j : Idx D.κ,
      pullback.fst (U i).ι (U j).ι ≫ f i = pullback.snd (U i).ι (U j).ι ≫ f j := by
    intro i j
    let O : Over (Spec (CommRingCat.of A)) :=
      Over.mk (pullback.fst (U i).ι (U j).ι ≫ (U i).ι ≫ T.hom)
    have : IsLocallyNoetherian O.left := by dsimp [O]; infer_instance
    let p1 : O ⟶ res T (U i) := Over.homMk (pullback.fst (U i).ι (U j).ι)
    let p2 : O ⟶ res T (U j) := Over.homMk (pullback.snd (U i).ι (U j).ι) (by
      dsimp [O]; rw [pullback.condition_assoc])
    have hp : p1 ≫ resι T (U i) = p2 ≫ resι T (U j) := by
      ext1; exact pullback.condition
    have hki := hk i
    have hkj := hk j
    have := D.agree O (p1 ≫ k i) (p2 ≫ k j) (by
      rw [op_comp, Functor.map_comp, types_comp_apply, hki, op_comp, Functor.map_comp,
        types_comp_apply, hkj, ← types_comp_apply (D.F.map _) (D.F.map p1.op),
        ← types_comp_apply (D.F.map _) (D.F.map p2.op), ← Functor.map_comp,
        ← Functor.map_comp, ← op_comp, ← op_comp, hp])
    have := congrArg (fun f ↦ f.left) this
    simpa [f, p1, p2] using this
  let g0 : T.left ⟶ D.P.left := 𝒰.glueMorphisms f hf
  have hg0 : ∀ i : Idx D.κ, (U i).ι ≫ g0 = f i := fun i ↦ 𝒰.ι_glueMorphisms f hf i
  have hg0' : g0 ≫ D.P.hom = T.hom := by
    refine 𝒰.hom_ext _ _ (fun (i : Idx D.κ) ↦ ?_)
    change (U i).ι ≫ g0 ≫ D.P.hom = (U i).ι ≫ T.hom
    rw [← Category.assoc, hg0 i]
    simp only [f, Category.assoc]
    rw [Over.w (D.ι i), Over.w (k i)]
    rfl
  let g : T ⟶ D.P := Over.homMk g0 hg0'
  refine ⟨g, ?_⟩
  have hsh := D.isSheafFor_ofArrows (fun i : Idx D.κ ↦ res T (U i)) (fun i ↦ resι T (U i))
    𝒰.mem_grothendieckTopology
  apply hsh.isSeparatedFor.ext
  rintro _ _ ⟨i⟩
  have hki : k i ≫ D.ι i = resι T (U i) ≫ g := by
    ext1; exact (hg0 i).symm
  rw [← D.map_x_of_factor g hki, hk i]

lemma locallyOfFinitePresentation_P : LocallyOfFinitePresentation D.P.hom := by
  have := HasRingHomProperty.instIsZariskiLocalAtSource (P := @LocallyOfFinitePresentation.{u})
  change LocallyOfFinitePresentation (colimit.desc D.G D.cocone)
  rw [IsZariskiLocalAtSource.iff_of_openCover (P := @LocallyOfFinitePresentation)
    (Scheme.IsLocallyDirected.openCover D.G)]
  intro (i : Idx D.κ)
  change LocallyOfFinitePresentation (colimit.ι D.G i ≫ colimit.desc D.G D.cocone)
  rw [colimit.ι_desc]
  exact D.locallyOfFinitePresentation_hom i

/-- The union of the pieces with first index `c`. -/
def Uc (c : D.κ) : D.P.left.Opens := ⨆ m : ℕ, (D.ι (Idx.mk c m)).left.opensRange

lemma opensRange_mono (c : D.κ) {m m' : ℕ} (h : m ≤ m') :
    (D.ι (Idx.mk c m)).left.opensRange ≤ (D.ι (Idx.mk c m')).left.opensRange := by
  have hle : Idx.mk c m ≤ Idx.mk c m' := ⟨rfl, h⟩
  rintro _ ⟨y, rfl⟩
  refine ⟨(D.τ hle).left y, ?_⟩
  rw [← Scheme.Hom.comp_apply, ← Over.comp_left, D.τ_ι]

lemma hasFiniteAffineNeighborhoods_Uc (c : D.κ) :
    PointTopology.HasFiniteAffineNeighborhoods (D.Uc c).toScheme := by
  let W : ℕ → (D.Uc c).toScheme.Opens := fun m ↦ (D.Uc c).ι ⁻¹ᵁ (D.ι (Idx.mk c m)).left.opensRange
  refine PointTopology.hasFiniteAffineNeighborhoods_of_directed_openCover W ?_ ?_ ?_
  · simp only [W]
    rw [← Scheme.Hom.preimage_iSup]
    exact Scheme.Opens.ι_preimage_self _
  · exact Monotone.directed_le (fun m m' h ↦ Scheme.Hom.preimage_mono _ (D.opensRange_mono c h))
  · intro m
    have H := range_subset_of_le (D.Uc c).ι (D.ι (Idx.mk c m)).left (W m) le_rfl
    let ℓ := IsOpenImmersion.lift (D.ι (Idx.mk c m)).left ((W m).ι ≫ (D.Uc c).ι) H
    have e : ℓ ≫ (D.ι (Idx.mk c m)).left = (W m).ι ≫ (D.Uc c).ι := IsOpenImmersion.lift_fac _ _ _
    have : IsOpenImmersion (ℓ ≫ (D.ι (Idx.mk c m)).left) := by
      rw [e]; infer_instance
    have : IsOpenImmersion ℓ := IsOpenImmersion.of_comp ℓ (D.ι (Idx.mk c m)).left
    exact PointTopology.hasFiniteAffineNeighborhoods_of_isOpenImmersion ℓ
      (D.hasFiniteAffineNeighborhoods_QI (Idx.mk c m))

lemma hasFiniteAffineNeighborhoods_P : PointTopology.HasFiniteAffineNeighborhoods D.P.left := by
  refine PointTopology.hasFiniteAffineNeighborhoods_of_disjoint_openCover D.Uc ?_ ?_
    D.hasFiniteAffineNeighborhoods_Uc
  · rw [eq_top_iff]
    intro y _
    obtain ⟨i, yi, hyi⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective D.G y
    simp only [Uc, TopologicalSpace.Opens.mem_iSup]
    exact ⟨i.1, i.2, yi, hyi⟩
  · intro c c' hcc'
    rw [disjoint_iff, ← SetLike.coe_set_eq, TopologicalSpace.Opens.coe_inf,
      TopologicalSpace.Opens.coe_bot, Set.eq_empty_iff_forall_notMem]
    rintro y ⟨h1, h2⟩
    simp only [Uc, SetLike.mem_coe, TopologicalSpace.Opens.mem_iSup] at h1 h2
    obtain ⟨m, y1, hy1⟩ := h1
    obtain ⟨m', y2, hy2⟩ := h2
    exact hcc' (D.le_of_ι_eq (i := Idx.mk c m) (j := Idx.mk c' m') (hy1.trans hy2.symm))

/-- The comparison map on noetherian affine tests is bijective. -/
lemma bijective_app (T : (ObjectProperty.FullSubcategory
    (fun T : Over (Spec (CommRingCat.of A)) => IsAffine T.left ∧ IsNoetherian T.left))) :
    Function.Bijective (fun g : ULift.{u + 1} (T.obj ⟶ D.P) ↦ D.F.map g.down.op D.ξP) := by
  have : IsNoetherian T.obj.left := T.property.2
  refine ⟨fun g1 g2 h ↦ ULift.ext _ _ (D.map_ξP_injective T.obj h), fun ξ ↦ ?_⟩
  obtain ⟨g, hg⟩ := D.exists_map_ξP T.obj ξ
  exact ⟨ULift.up g, hg⟩

/-- The natural isomorphism on noetherian affine tests. -/
def isoNoeth : (noetherianAffineOverι (Spec (CommRingCat.of A))).op ⋙
      yoneda.obj D.P ⋙ uliftFunctor.{u + 1} ≅
    (noetherianAffineOverι (Spec (CommRingCat.of A))).op ⋙ D.F :=
  NatIso.ofComponents
    (fun T ↦ (Equiv.ofBijective _ (D.bijective_app T.unop)).toIso)
    (fun {T T'} h ↦ by
      ext g
      change D.F.map ((noetherianAffineOverι _).map h.unop ≫ g.down).op D.ξP =
        D.F.map ((noetherianAffineOverι _).map h.unop).op (D.F.map g.down.op D.ξP)
      rw [op_comp, Functor.map_comp, types_comp_apply])

end Data

end Langlands.AlgebraicGeometry.Picard.NoetherianOpenPiecesGluing

namespace Langlands.AlgebraicGeometry.Picard

open NoetherianOpenPiecesGluing in
/-- Proof of `NoetherianOpenPiecesGluingStatement`: glue the pieces along their transition open
immersions. -/
theorem noetherianOpenPiecesGluing : NoetherianOpenPiecesGluingStatement.{u} := by
  intro A _ _ F hF κ V Q β base shape imm rep
  let D : Data A := ⟨F, hF, κ, V, Q, β, base, shape, imm, rep⟩
  exact ⟨D.P, D.locallyOfFinitePresentation_P, D.hasFiniteAffineNeighborhoods_P, ⟨D.isoNoeth⟩⟩

end Langlands.AlgebraicGeometry.Picard
