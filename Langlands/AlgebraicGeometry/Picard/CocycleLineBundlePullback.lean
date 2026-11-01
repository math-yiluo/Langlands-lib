import Langlands.AlgebraicGeometry.Picard.CocycleLineBundleProof
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_pullbackLocalSection
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isIso_of_isFrameOn_of_iSup_eq_top

/-! # Pullback of line bundles glued from unit cocycles

For a morphism of schemes `q : Y ⟶ X`, opens `T i` of `X` and a unit cocycle `g` on the
pairwise overlaps, the pulled-back cocycle `pullbackCocycle q g` on the opens `q ⁻¹ᵁ T i` is
obtained by applying `q.appLE` to each `g i j`. The comparison morphism
`pullbackHom q g : q^* (glued g) ⟶ glued (pullbackCocycle q g)` is the adjunction transpose of
the morphism `glued g ⟶ q_* (glued (pullbackCocycle q g))` that applies `q.appLE` to each
component. When the `T i` cover `X` and `g` is a cocycle it is an isomorphism `pullbackIso`,
and it sends the pullback of the local generator `genSec g i` to `genSec (pullbackCocycle q g) i`.
-/

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

set_option backward.isDefEq.respectTransparency false

namespace Langlands.AlgebraicGeometry.Picard.CocycleGluing

variable {X Y : Scheme.{u}} (q : Y ⟶ X)

section AppLE

/-- Restricting the image of a function under `q.appLE`. -/
lemma res_appLE {U : X.Opens} {V V' : Y.Opens} (e : V ≤ q ⁻¹ᵁ U) (hV : V' ≤ V) (a : Γ(X, U)) :
    Y.presheaf.map (homOfLE hV).op (q.appLE U V e a) = q.appLE U V' (hV.trans e) a := by
  rw [← ConcreteCategory.comp_apply, Scheme.Hom.appLE_map]

/-- Applying `q.appLE` to a restricted function. -/
lemma appLE_res {U U' : X.Opens} {V : Y.Opens} (hU : U' ≤ U) (e : V ≤ q ⁻¹ᵁ U')
    (a : Γ(X, U)) :
    q.appLE U' V e (X.presheaf.map (homOfLE hU).op a) =
      q.appLE U V (e.trans (q.preimage_mono hU)) a := by
  rw [← ConcreteCategory.comp_apply, Scheme.Hom.map_appLE]

/-- Restricting the image of a function under `q.app`. -/
lemma res_app {U : X.Opens} {V : Y.Opens} (hV : V ≤ q ⁻¹ᵁ U) (a : Γ(X, U)) :
    Y.presheaf.map (homOfLE hV).op (q.app U a) = q.appLE U V hV a := by
  rw [Scheme.Hom.app_eq_appLE, res_appLE]

end AppLE

variable {ι : Type u} {T : ι → X.Opens}

section Cocycle

/-- The unit cocycle on the opens `q ⁻¹ᵁ T i` obtained by applying `q.appLE` to `g`. -/
noncomputable def pullbackCocycle (g : ∀ i j : ι, (Γ(X, T i ⊓ T j))ˣ) (i j : ι) :
    (Γ(Y, q ⁻¹ᵁ T i ⊓ q ⁻¹ᵁ T j))ˣ :=
  Units.map (q.appLE (T i ⊓ T j) (q ⁻¹ᵁ T i ⊓ q ⁻¹ᵁ T j) le_rfl).hom.toMonoidHom (g i j)

lemma pullbackCocycle_val (g : ∀ i j : ι, (Γ(X, T i ⊓ T j))ˣ) (i j : ι) :
    (pullbackCocycle q g i j : Γ(Y, q ⁻¹ᵁ T i ⊓ q ⁻¹ᵁ T j)) =
      q.appLE (T i ⊓ T j) (q ⁻¹ᵁ T i ⊓ q ⁻¹ᵁ T j) le_rfl (g i j : Γ(X, T i ⊓ T j)) :=
  rfl

/-- Restrictions of the pulled-back cocycle are images of `g i j` under `q.appLE`. -/
lemma res_pullbackCocycle (g : ∀ i j : ι, (Γ(X, T i ⊓ T j))ˣ) {i j : ι} {V : Y.Opens}
    (hV : V ≤ q ⁻¹ᵁ T i ⊓ q ⁻¹ᵁ T j) :
    Y.presheaf.map (homOfLE hV).op (pullbackCocycle q g i j : Γ(Y, q ⁻¹ᵁ T i ⊓ q ⁻¹ᵁ T j)) =
      q.appLE (T i ⊓ T j) V hV (g i j : Γ(X, T i ⊓ T j)) :=
  res_appLE q _ hV _

/-- The pulled-back cocycle satisfies the cocycle identity. -/
lemma IsCocycle.pullback {g : ∀ i j : ι, (Γ(X, T i ⊓ T j))ˣ} (hg : IsCocycle g) :
    IsCocycle (pullbackCocycle q g) := by
  intro i j k
  have h := congrArg (fun z ↦ q.appLE (T i ⊓ T j ⊓ T k)
    (q ⁻¹ᵁ T i ⊓ q ⁻¹ᵁ T j ⊓ q ⁻¹ᵁ T k) le_rfl z) (hg i j k)
  simp only [map_mul, appLE_res] at h
  rw [res_pullbackCocycle, res_pullbackCocycle, res_pullbackCocycle]
  exact h

end Cocycle

section Fam

/-- Applying `q.appLE` to each component of a family on the pieces `U ⊓ T i` gives a family on
the pieces `q ⁻¹ᵁ U ⊓ q ⁻¹ᵁ T i`. -/
noncomputable def pullbackFam {U : X.Opens} (b : Fam T U) :
    Fam (fun i ↦ q ⁻¹ᵁ T i) (q ⁻¹ᵁ U) :=
  fun i ↦ q.appLE (U ⊓ T i) (q ⁻¹ᵁ U ⊓ q ⁻¹ᵁ T i) le_rfl (b i)

lemma pullbackFam_apply {U : X.Opens} (b : Fam T U) (i : ι) :
    pullbackFam q b i = q.appLE (U ⊓ T i) (q ⁻¹ᵁ U ⊓ q ⁻¹ᵁ T i) le_rfl (b i) :=
  rfl

lemma pullbackFam_add {U : X.Opens} (b c : Fam T U) :
    pullbackFam q (b + c) = pullbackFam q b + pullbackFam q c :=
  funext fun i ↦ map_add _ (b i) (c i)

lemma pullbackFam_smul {U : X.Opens} (r : Γ(X, U)) (b : Fam T U) :
    pullbackFam q (r • b) = q.app U r • pullbackFam q b := by
  funext i
  rw [pullbackFam_apply, Fam.smul_apply, Fam.smul_apply, pullbackFam_apply, map_mul, appLE_res,
    res_app]

lemma famRes_pullbackFam {U V : X.Opens} (h : V ≤ U) (b : Fam T U) :
    famRes (fun i ↦ q ⁻¹ᵁ T i) (q.preimage_mono h) (pullbackFam q b) =
      pullbackFam q (famRes T h b) := by
  funext i
  rw [famRes_apply, pullbackFam_apply, pullbackFam_apply, famRes_apply, res_appLE, appLE_res]

variable (g : ∀ i j : ι, (Γ(X, T i ⊓ T j))ˣ)

/-- `q.appLE` carries families satisfying the cocycle relation for `g` to families satisfying
the cocycle relation for the pulled-back cocycle. -/
lemma compat_pullbackFam {U : X.Opens} {b : Fam T U} (hb : Compat g b) :
    Compat (pullbackCocycle q g) (pullbackFam q b) := by
  intro i j V hi hj
  have hW : V ≤ q ⁻¹ᵁ (U ⊓ (T i ⊓ T j)) :=
    le_inf (hi.trans inf_le_left) (le_inf (hi.trans inf_le_right) (hj.trans inf_le_right))
  have h := congrArg (fun z ↦ q.appLE (U ⊓ (T i ⊓ T j)) V hW z)
    (hb i j (U ⊓ (T i ⊓ T j)) (inf_le_inf_left U inf_le_left) (inf_le_inf_left U inf_le_right))
  simp only [map_mul, appLE_res] at h
  rw [pullbackFam_apply, pullbackFam_apply, res_appLE, res_appLE, res_pullbackCocycle]
  exact h

lemma pullbackFam_gen (i : ι) {V : X.Opens} (hV : V ≤ T i) :
    pullbackFam q (gen g i hV) = gen (pullbackCocycle q g) i (q.preimage_mono hV) := by
  funext j
  rw [pullbackFam_apply, gen_apply, gen_apply, appLE_res, res_pullbackCocycle]

end Fam

variable (g : ∀ i j : ι, (Γ(X, T i ⊓ T j))ˣ)

/-- The morphism `glued g ⟶ q_* (glued (pullbackCocycle q g))` applying `q.appLE` to each
component. -/
noncomputable def toPushforward :
    glued g ⟶ (Scheme.Modules.pushforward q).obj (glued (pullbackCocycle q g)) where
  val :=
    { app := fun U ↦ ModuleCat.ofHom (X := ↑((glued g).val.obj U))
        (Y := ↑(((Scheme.Modules.pushforward q).obj (glued (pullbackCocycle q g))).val.obj U))
        { toFun := fun m ↦ mk (pullbackCocycle q g) (pullbackFam q (m.1 : Fam T U.unop))
            (compat_pullbackFam q g (compat_of_mem g m))
          map_add' := fun m m' ↦ Subtype.ext (pullbackFam_add q m.1 m'.1)
          map_smul' := fun r m ↦ Subtype.ext (pullbackFam_smul q r m.1) }
      naturality := by
        intro U V f
        ext m
        apply Subtype.ext
        exact (famRes_pullbackFam q (leOfHom f.unop) m.1).symm }

lemma toPushforward_app {U : X.Opens} (m : Γ(glued g, U)) :
    ((toPushforward q g).app U m : Γ(glued (pullbackCocycle q g), q ⁻¹ᵁ U)) =
      mk (pullbackCocycle q g) (pullbackFam q (m.1 : Fam T U))
        (compat_pullbackFam q g (compat_of_mem g m)) :=
  rfl

/-- The comparison morphism `q^* (glued g) ⟶ glued (pullbackCocycle q g)`: the adjunction
transpose of `toPushforward q g`. -/
noncomputable def pullbackHom :
    (Scheme.Modules.pullback q).obj (glued g) ⟶ glued (pullbackCocycle q g) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction q).homEquiv _ _).symm (toPushforward q g)

/-- On the pullback of a section `m`, the comparison morphism applies `q.appLE` to each
component of `m`. -/
lemma pullbackHom_app_pullbackLocalSection {U : X.Opens} (m : Γ(glued g, U)) :
    (pullbackHom q g).app (q ⁻¹ᵁ U) (Scheme.Modules.pullbackLocalSection q m) =
      mk (pullbackCocycle q g) (pullbackFam q (m.1 : Fam T U))
        (compat_pullbackFam q g (compat_of_mem g m)) :=
  Scheme.Modules.homEquiv_symm_app_pullbackLocalSection q (toPushforward q g) m

/-- Component formula for the comparison morphism on pulled-back sections. -/
lemma comp_pullbackHom_app_pullbackLocalSection {U : X.Opens} (m : Γ(glued g, U)) (i : ι) :
    comp (pullbackCocycle q g)
        ((pullbackHom q g).app (q ⁻¹ᵁ U) (Scheme.Modules.pullbackLocalSection q m)) i =
      q.appLE (U ⊓ T i) (q ⁻¹ᵁ U ⊓ q ⁻¹ᵁ T i) le_rfl (comp g m i) := by
  rw [pullbackHom_app_pullbackLocalSection]
  rfl

/-- The comparison morphism sends the pullback of the local generator `genSec g i` to the local
generator `genSec (pullbackCocycle q g) i`. -/
lemma pullbackHom_app_genSec (hg : IsCocycle g) (i : ι) {V : X.Opens} (hV : V ≤ T i) :
    (pullbackHom q g).app (q ⁻¹ᵁ V)
        (Scheme.Modules.pullbackLocalSection q (genSec g hg i hV)) =
      genSec (pullbackCocycle q g) (hg.pullback q) i (q.preimage_mono hV) := by
  rw [pullbackHom_app_pullbackLocalSection]
  exact mk_eq_mk _ _ _ (pullbackFam_gen q g i hV)

/-- The local generator `genSec g i` is a frame of the glued sheaf on `T i`. -/
lemma isFrameOn_genSec (hg : IsCocycle g) (i : ι) :
    Scheme.Modules.IsFrameOn (genSec g hg i (le_refl (T i))) (T i) := by
  intro W hWU _
  rw [map_genSec g hg i hWU le_rfl]
  exact smul_genSec_bijective g hg i _

/-- When the `T i` cover `X`, the comparison morphism is an isomorphism. -/
lemma isIso_pullbackHom (hT : (⨆ i, T i) = ⊤) (hg : IsCocycle g) : IsIso (pullbackHom q g) :=
  Scheme.Modules.isIso_of_isFrameOn_of_iSup_eq_top (pullbackHom q g) (fun i ↦ q ⁻¹ᵁ T i)
    (q.iSup_preimage_eq_top hT)
    (fun i ↦ Scheme.Modules.pullbackLocalSection q (genSec g hg i le_rfl))
    (fun i ↦ genSec (pullbackCocycle q g) (hg.pullback q) i le_rfl)
    (fun i ↦ (isFrameOn_genSec g hg i).pullbackLocalSection q)
    (fun i ↦ isFrameOn_genSec (pullbackCocycle q g) (hg.pullback q) i)
    (fun i ↦ pullbackHom_app_genSec q g hg i le_rfl)

/-- The pullback of the line bundle glued from `g` is the line bundle glued from the
pulled-back cocycle. Its forward morphism is `pullbackHom q g`. -/
noncomputable def pullbackIso (hT : (⨆ i, T i) = ⊤) (hg : IsCocycle g) :
    (Scheme.Modules.pullback q).obj (glued g) ≅ glued (pullbackCocycle q g) :=
  @asIso _ _ _ _ (pullbackHom q g) (isIso_pullbackHom q g hT hg)

lemma pullbackIso_hom (hT : (⨆ i, T i) = ⊤) (hg : IsCocycle g) :
    (pullbackIso q g hT hg).hom = pullbackHom q g :=
  rfl

/-- Component formula for the pullback isomorphism on pulled-back sections. -/
lemma comp_pullbackIso_hom_app_pullbackLocalSection (hT : (⨆ i, T i) = ⊤) (hg : IsCocycle g)
    {U : X.Opens} (m : Γ(glued g, U)) (i : ι) :
    comp (pullbackCocycle q g)
        ((pullbackIso q g hT hg).hom.app (q ⁻¹ᵁ U) (Scheme.Modules.pullbackLocalSection q m)) i =
      q.appLE (U ⊓ T i) (q ⁻¹ᵁ U ⊓ q ⁻¹ᵁ T i) le_rfl (comp g m i) :=
  comp_pullbackHom_app_pullbackLocalSection q g m i

/-- The pullback isomorphism sends the pullback of `genSec g i` to
`genSec (pullbackCocycle q g) i`. -/
lemma pullbackIso_hom_app_genSec (hT : (⨆ i, T i) = ⊤) (hg : IsCocycle g) (i : ι) {V : X.Opens}
    (hV : V ≤ T i) :
    (pullbackIso q g hT hg).hom.app (q ⁻¹ᵁ V)
        (Scheme.Modules.pullbackLocalSection q (genSec g hg i hV)) =
      genSec (pullbackCocycle q g) (hg.pullback q) i (q.preimage_mono hV) :=
  pullbackHom_app_genSec q g hg i hV

/-- The inverse of the pullback isomorphism sends `genSec (pullbackCocycle q g) i` to the
pullback of `genSec g i`. -/
lemma pullbackIso_inv_app_genSec (hT : (⨆ i, T i) = ⊤) (hg : IsCocycle g) (i : ι)
    {V : X.Opens} (hV : V ≤ T i) :
    (pullbackIso q g hT hg).inv.app (q ⁻¹ᵁ V)
        (genSec (pullbackCocycle q g) (hg.pullback q) i (q.preimage_mono hV)) =
      Scheme.Modules.pullbackLocalSection q (genSec g hg i hV) := by
  rw [← pullbackIso_hom_app_genSec q g hT hg i hV]
  change ((pullbackIso q g hT hg).hom.app (q ⁻¹ᵁ V) ≫ (pullbackIso q g hT hg).inv.app (q ⁻¹ᵁ V))
    (Scheme.Modules.pullbackLocalSection q (genSec g hg i hV)) = _
  rw [← Scheme.Modules.Hom.comp_app, Iso.hom_inv_id, Scheme.Modules.Hom.id_app]
  rfl

end Langlands.AlgebraicGeometry.Picard.CocycleGluing
