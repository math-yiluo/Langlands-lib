import Langlands.AlgebraicGeometry.Modules.OpenCoverHomGluing

/-! # Gluing morphisms of module sheaves from a basis of opens -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace


universe u

noncomputable section

namespace Langlands.Scheme.Modules.BasisHomGluing

open OpenCoverHomGluing

variable {Y : AlgebraicGeometry.Scheme.{u}} {P : Y.Opens → Prop}

/-- The opens satisfying `P` and contained in `O`. -/
abbrev BasicSub (P : Y.Opens → Prop) (O : Y.Opens) : Type u := {W : Y.Opens // P W ∧ W ≤ O}

lemma le_iSup_basicSub (hP : ∀ (y : Y) (U : Y.Opens), y ∈ U → ∃ V, P V ∧ y ∈ V ∧ V ≤ U)
    (O : Y.Opens) : O ≤ ⨆ W : BasicSub P O, W.1 := by
  intro y hy
  obtain ⟨V, hV, hyV, hVO⟩ := hP y O hy
  exact Opens.mem_iSup.mpr ⟨⟨V, hV, hVO⟩, hyV⟩

/-- Sections of a module agreeing on every `P`-open inside `O` agree, when the `P`-opens form a
basis. -/
lemma eq_of_basis (hP : ∀ (y : Y) (U : Y.Opens), y ∈ U → ∃ V, P V ∧ y ∈ V ∧ V ≤ U)
    {N : Y.Modules} {O : Y.Opens} (s t : Γ(N, O))
    (h : ∀ (W : Y.Opens) (_ : P W) (hWO : W ≤ O),
      N.presheaf.map (homOfLE hWO).op s = N.presheaf.map (homOfLE hWO).op t) : s = t :=
  TopCat.Sheaf.eq_of_locally_eq' (sheafAb N) (fun W : BasicSub P O => W.1) O
    (fun W => homOfLE W.2.2) (le_iSup_basicSub hP O) s t (fun W => h W.1 W.2.1 W.2.2)

/-- Morphisms of modules agreeing on every `P`-open agree, when the `P`-opens form a basis. -/
lemma hom_ext_of_basis (hP : ∀ (y : Y) (U : Y.Opens), y ∈ U → ∃ V, P V ∧ y ∈ V ∧ V ≤ U)
    {N M : Y.Modules} (f g : N ⟶ M) (h : ∀ V : Y.Opens, P V → f.app V = g.app V) : f = g := by
  ext O x
  apply eq_of_basis hP
  intro W hW hWO
  rw [hom_map_app, hom_map_app, h W hW]

section Glue

variable (hP : ∀ (y : Y) (U : Y.Opens), y ∈ U → ∃ V, P V ∧ y ∈ V ∧ V ≤ U)
  {N M : Y.Modules} (θ : ∀ V : Y.Opens, P V → (Γ(N, V) →ₗ[Γ(Y, V)] Γ(M, V)))
  (hθ : ∀ (V V' : Y.Opens) (hV : P V) (hV' : P V') (h : V' ≤ V) (s : Γ(N, V)),
    M.presheaf.map (homOfLE h).op (θ V hV s) = θ V' hV' (N.presheaf.map (homOfLE h).op s))

include hP hθ in
lemma exists_glue (O : Y.Opens) (x : Γ(N, O)) :
    ∃ s : Γ(M, O), ∀ W : BasicSub P O, M.presheaf.map (homOfLE W.2.2).op s =
      θ W.1 W.2.1 (N.presheaf.map (homOfLE W.2.2).op x) := by
  refine (TopCat.Sheaf.existsUnique_gluing' (sheafAb M) (fun W : BasicSub P O => W.1) O
    (fun W => homOfLE W.2.2) (le_iSup_basicSub hP O)
    (fun W => θ W.1 W.2.1 (N.presheaf.map (homOfLE W.2.2).op x)) ?_).exists
  intro W W'
  change M.presheaf.map (homOfLE inf_le_left).op _ = M.presheaf.map (homOfLE inf_le_right).op _
  apply eq_of_basis hP
  intro Z hZ hZW
  rw [map_map_eq _ _ (hZW.trans inf_le_left), map_map_eq _ _ (hZW.trans inf_le_right), hθ _ _ _ hZ, hθ _ _ _ hZ,
    map_map_eq _ _ (hZW.trans (inf_le_left.trans W.2.2)),
    map_map_eq _ _ (hZW.trans (inf_le_left.trans W.2.2))]

/-- The glued section. -/
def glue (O : Y.Opens) (x : Γ(N, O)) : Γ(M, O) := (exists_glue hP θ hθ O x).choose

lemma glue_spec {O W : Y.Opens} (hW : P W) (hWO : W ≤ O) (x : Γ(N, O)) :
    M.presheaf.map (homOfLE hWO).op (glue hP θ hθ O x) =
      θ W hW (N.presheaf.map (homOfLE hWO).op x) :=
  (exists_glue hP θ hθ O x).choose_spec ⟨W, hW, hWO⟩

lemma glue_add (O : Y.Opens) (x y : Γ(N, O)) :
    glue hP θ hθ O (x + y) = glue hP θ hθ O x + glue hP θ hθ O y := by
  apply eq_of_basis hP
  intro W hW hWO
  rw [map_add, glue_spec hP θ hθ hW, glue_spec hP θ hθ hW, glue_spec hP θ hθ hW, map_add,
    map_add]

lemma glue_smul (O : Y.Opens) (r : Γ(Y, O)) (x : Γ(N, O)) :
    glue hP θ hθ O (r • x) = r • glue hP θ hθ O x := by
  apply eq_of_basis hP
  intro W hW hWO
  rw [Scheme.Modules.map_smul, glue_spec hP θ hθ hW, glue_spec hP θ hθ hW,
    Scheme.Modules.map_smul, LinearMap.map_smul]

lemma glue_map {O O' : Y.Opens} (h : O' ≤ O) (x : Γ(N, O)) :
    glue hP θ hθ O' (N.presheaf.map (homOfLE h).op x) =
      M.presheaf.map (homOfLE h).op (glue hP θ hθ O x) := by
  apply eq_of_basis hP
  intro W hW hWO
  rw [glue_spec hP θ hθ hW, map_map_eq _ _ (hWO.trans h), map_map_eq _ _ (hWO.trans h),
    glue_spec hP θ hθ hW]

/-- The glued morphism of abelian presheaves. -/
def presheafHom : N.presheaf ⟶ M.presheaf where
  app O := AddCommGrpCat.ofHom (AddMonoidHom.mk' (glue hP θ hθ O.unop) (glue_add hP θ hθ O.unop))
  naturality O O' g := by
    ext x
    exact glue_map hP θ hθ (leOfHom g.unop) x

/-- The morphism of modules glued from linear maps on the `P`-opens. -/
def hom : N ⟶ M :=
  ⟨PresheafOfModules.homMk (presheafHom hP θ hθ) fun O r x => glue_smul hP θ hθ O.unop r x⟩

lemma hom_app_apply (O : Y.Opens) (x : Γ(N, O)) : (hom hP θ hθ).app O x = glue hP θ hθ O x :=
  rfl

/-- On a `P`-open `V`, the glued morphism is `θ V`. -/
lemma hom_app_basis (V : Y.Opens) (hV : P V) (s : Γ(N, V)) :
    (hom hP θ hθ).app V s = θ V hV s := by
  rw [hom_app_apply]
  apply eq_of_basis hP
  intro W hW hWV
  rw [glue_spec hP θ hθ hW, hθ _ _ _ hW]

include hP hθ in
/-- Linear maps on the sections over a basis of opens, compatible with restriction, come from a
morphism of modules. -/
theorem exists_hom_of_basis :
    ∃ φ : N ⟶ M, ∀ (V : Y.Opens) (hV : P V) (s : Γ(N, V)), φ.app V s = θ V hV s :=
  ⟨hom hP θ hθ, hom_app_basis hP θ hθ⟩

end Glue

end Langlands.Scheme.Modules.BasisHomGluing
